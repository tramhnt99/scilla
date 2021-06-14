(*
  This file is part of scilla.

  Copyright (c) 2018 - present Zilliqa Research Pvt. Ltd.
  
  scilla is free software: you can redistribute it and/or modify it under the
  terms of the GNU General Public License as published by the Free Software
  Foundation, either version 3 of the License, or (at your option) any later
  version.
 
  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
 
  You should have received a copy of the GNU General Public License along with
*)

open Core_kernel
open Result.Let_syntax
open TypeUtil
open Literal
open Syntax
open ErrorUtils
open MonadUtil
open ContractUtil.MessagePayload

module ScillaSanityChecker
    (SR : Rep) (ER : sig
      include Rep

      val get_type : rep -> PlainTypes.t inferred_type
    end) =
struct
  module SER = SR
  module EER = ER
  module SCLiteral = GlobalLiteral
  module SCType = SCLiteral.LType
  module SCIdentifier = SCType.TIdentifier
  module SCName = SCIdentifier.Name
  module SCSyntax = ScillaSyntax (SR) (ER) (SCLiteral)
  module TU = TypeUtilities
  module SCU = ContractUtil.ScillaContractUtil (SR) (ER)
  open SCIdentifier
  open SCSyntax
  open SCU

  (* Warning level to use when contract loads/stores entire Maps. *)
  let warning_level_map_load_store = 1

  (* Warning level to use when warning about shadowing of contract parameters and fields. *)
  let warning_level_name_shadowing = 2

  (* Warning level for dead code detection *)
  let warning_level_dead_code = 3

  (* ************************************** *)
  (* ******** Basic Sanity Checker ******** *)
  (* ************************************** *)

  (* Basic sanity tests on the contract. *)
  let basic_sanity (cmod : cmodule) =
    let contr = cmod.contr in

    (* Check if there are duplicate entries in "ilist". *)
    let check_duplicate_ident gloc ilist =
      let rec recurser ilist' e =
        match ilist' with
        | i :: rem ->
            let e' =
              if is_mem_id i rem then
                e
                @ mk_error1
                    (sprintf "Identifier %s used more than once\n"
                       (as_error_string i))
                    (gloc @@ get_rep i)
              else e
            in
            recurser rem e'
        | [] -> e
      in
      recurser ilist []
    in

    (* No repeating names for params. *)
    let e =
      check_duplicate_ident ER.get_loc
        (List.map contr.cparams ~f:(fun (i, _) -> i))
    in
    (* No repeating field names. *)
    let e =
      e
      @ check_duplicate_ident ER.get_loc
          (List.map contr.cfields ~f:(fun (i, _, _) -> i))
    in
    (* No repeating component names. *)
    let e =
      e
      @ check_duplicate_ident SR.get_loc
          (List.map contr.ccomps ~f:(fun c -> c.comp_name))
    in
    (* No repeating component parameter names. *)
    let e =
      List.fold_left contr.ccomps ~init:e ~f:(fun e t ->
          e
          @ check_duplicate_ident ER.get_loc
              (List.map t.comp_params ~f:(fun (i, _) -> i)))
    in

    (* Message literals must either be for "send" or "event" and well formed. *)
    let check_message eloc msg e =
      (* No repeating message field. *)
      let e =
        e
        @ check_duplicate_ident
            (fun _ -> eloc)
            (List.map msg ~f:(fun (s, _) ->
                 mk_id (SCName.parse_simple_name s) SR.string_rep))
      in

      (* Either "_tag" or "_eventname" must be present. *)
      let e =
        if List.Assoc.mem msg tag_label ~equal:String.( = ) then
          (* This is a "send" Message. Ensure "_amount" and "_recipient" provided. *)
          if
            List.Assoc.mem msg amount_label ~equal:String.( = )
            && List.Assoc.mem msg recipient_label ~equal:String.( = )
          then e
          else
            e
            @ mk_error1
                ("Missing " ^ amount_label ^ " or " ^ recipient_label
               ^ " in Message\n")
                eloc
        else if
          (* It must be an event or an exception. *)
          List.exists msg ~f:(fun (s, _) ->
              String.(s = eventname_label || s = exception_label))
        then e
        else e @ mk_error1 "Invalid message construct." eloc
      in
      pure e
      (* as required by "fold_over_messages" *)
    in
    let%bind e = fold_over_messages cmod ~init:e ~f:check_message in

    (* Component parameters cannot have names as that of implicit ones. *)
    let e =
      List.fold_left contr.ccomps ~init:e ~f:(fun e c ->
          match
            List.find c.comp_params ~f:(fun (s, _) ->
                String.(
                  as_string s = amount_label
                  || as_string s = sender_label
                  || as_string s = origin_label))
          with
          | Some (s, _) ->
              e
              @ mk_error1
                  (sprintf "Parameter %s in %s %s cannot be explicit.\n"
                     (as_error_string s)
                     (component_type_to_string c.comp_type)
                     (as_error_string c.comp_name))
                  (SR.get_loc @@ get_rep c.comp_name)
          | None -> e)
    in

    (* Contract parameters cannot have names of implicit ones. *)
    let e =
      match
        List.find contr.cparams ~f:(fun (s, _) ->
            let open ContractUtil in
            [%equal: SCName.t] (get_id s) creation_block_label
            || [%equal: SCName.t] (get_id s) scilla_version_label
            || [%equal: SCName.t] (get_id s) this_address_label)
      with
      | Some (s, _) ->
          e
          @ mk_error1
              (sprintf "Contract parameter %s cannot be explicit.\n"
                 (as_error_string s))
              (ER.get_loc @@ get_rep s)
      | None -> e
    in

    (* Look for any statement that is loading/storing a full Map and warn. *)
    let check_typ_warn s =
      let t = (ER.get_type (get_rep s)).tp in
      let lc = ER.get_loc (get_rep s) in
      let warn () =
        warn1 "Consider using in-place Map access" warning_level_map_load_store
          lc
      in
      match t with
      | MapType _ -> warn ()
      (* The result of a <- a[][], i.e., "a" is an Option type. *)
      | ADT (adt_name, [ MapType _ ])
        when Datatypes.is_option_adt_name (get_id adt_name) ->
          warn ()
      | _ -> ()
    in
    List.iter cmod.contr.ccomps ~f:(fun comp ->
        let rec stmt_iter stmts =
          List.iter stmts ~f:(fun (stmt, _) ->
              match stmt with
              (* Recursion basis. *)
              | Load (_, s) | MapGet (s, _, _, _) -> check_typ_warn s
              | MapUpdate (_, _, vopt) -> (
                  match vopt with Some s -> check_typ_warn s | None -> ())
              (* Recurse through match statements. *)
              | MatchStmt (_, pat_stmts) ->
                  List.iter pat_stmts ~f:(fun (_, stmts) -> stmt_iter stmts)
              | _ -> ())
        in
        stmt_iter comp.comp_body);
    if List.is_empty e then pure () else fail e

  (* ************************************** *)
  (* ******** Check name shadowing ******** *)
  (* ************************************** *)

  module CheckShadowing = struct
    (* A utility function that checks if "id" is shadowing cparams, cfields or pnames. *)
    let check_warn_redef cparams cfields pnames stmts_defs id =
      if List.mem cparams (get_id id) ~equal:[%equal: SCName.t] then
        warn1
          (Printf.sprintf "Name %s shadows a contract parameter."
             (as_error_string id))
          warning_level_name_shadowing
          (ER.get_loc (get_rep id))
      else if List.mem cfields (get_id id) ~equal:[%equal: SCName.t] then
        warn1
          (Printf.sprintf "Name %s shadows a field declaration."
             (as_error_string id))
          warning_level_name_shadowing
          (ER.get_loc (get_rep id))
      else if List.mem pnames (get_id id) ~equal:[%equal: SCName.t] then
        warn1
          (Printf.sprintf "Name %s shadows a transition parameter."
             (as_error_string id))
          warning_level_name_shadowing
          (ER.get_loc (get_rep id))
      else if List.mem stmts_defs (get_id id) ~equal:[%equal: SCName.t] then
        warn1
          (Printf.sprintf
             "%s is a new variable. It does not reassign the previously \
              defined variable."
             (as_error_string id))
          warning_level_name_shadowing
          (ER.get_loc (get_rep id))

    (* Check for shadowing in patterns. *)
    let pattern_iter pat cparams cfields pnames =
      (* Check if any variable bound in this pattern shadows cparams/cfields/pnames *)
      let rec outer_scope_iter = function
        | Wildcard -> ()
        | Binder i -> check_warn_redef cparams cfields pnames [] i
        | Constructor (_, plist) -> List.iter plist ~f:outer_scope_iter
      in
      outer_scope_iter pat;
      (* Check for shadowing of names within this pattern and warn that it is
       * deprecated. This will be disallowed (i.e., an error) in future versions.
       * https://github.com/Zilliqa/scilla/issues/687. To close this Issue:
       * Make this an error by just using fail1 below instead of warn1. *)
      let bounds = get_pattern_bounds pat in
      match List.find_a_dup ~compare:SCIdentifier.compare bounds with
      | Some v ->
          warn1
            (Printf.sprintf
               "Deprecated: variable %s shadows a previous binding in the same \
                pattern."
               (as_error_string v))
            warning_level_name_shadowing
            (ER.get_loc (get_rep v));
          pure ()
      | None -> pure ()

    (* Check for shadowing in expressions. *)
    let rec expr_iter (e, _) cparams cfields pnames =
      match e with
      | Literal _ | Builtin _ | Constr _ | App _ | Message _ | Var _ | TApp _ ->
          pure ()
      | GasExpr (_, e) -> expr_iter e cparams cfields pnames
      | Let (i, _, e_lhs, e_rhs) ->
          check_warn_redef cparams cfields pnames [] i;
          let%bind () = expr_iter e_lhs cparams cfields pnames in
          expr_iter e_rhs cparams cfields pnames
      | Fun (i, _, e_body) | Fixpoint (i, _, e_body) | TFun (i, e_body) ->
          (* "i" being a type variable shouldn't be shadowing contract parameters,
             fields or component parameters. This is just a conservative check. *)
          check_warn_redef cparams cfields pnames [] i;
          expr_iter e_body cparams cfields pnames
      | MatchExpr (_, clauses) ->
          forallM
            ~f:(fun (pat, mbody) ->
              let%bind () = pattern_iter pat cparams cfields pnames in
              expr_iter mbody cparams cfields pnames)
            clauses

    let shadowing_libentries lentries =
      forallM
        ~f:(fun lentry ->
          match lentry with
          | LibTyp _ -> pure ()
          | LibVar (_, _, vexp) -> expr_iter vexp [] [] [])
        lentries

    let rec shadowing_libtree ltree =
      let%bind () = forallM ~f:(fun dep -> shadowing_libtree dep) ltree.deps in
      shadowing_libentries ltree.libn.lentries

    let shadowing_cmod (cmod : cmodule) =
      (* Check for match pattern shadowing in library functions. *)
      let%bind () =
        match cmod.libs with
        | Some lib -> shadowing_libentries lib.lentries
        | None -> pure ()
      in

      let cparams = List.map cmod.contr.cparams ~f:(fun (p, _) -> get_id p) in

      (* Check for shadowing in contract constraint *)
      let%bind () = expr_iter cmod.contr.cconstraint cparams [] [] in

      (* Check if a field shadows any contract parameter. *)
      let%bind () =
        forallM
          ~f:(fun (f, _, finit_expr) ->
            check_warn_redef cparams [] [] [] f;
            expr_iter finit_expr cparams [] [])
          cmod.contr.cfields
      in

      let cfields =
        List.map cmod.contr.cfields ~f:(fun (f, _, _) -> get_id f)
      in

      (* Go through each component. *)
      forallM
        ~f:(fun c ->
          (* 1. If a parameter name shadows one of cparams or cfields, warn. *)
          List.iter c.comp_params ~f:(fun (p, _) ->
              check_warn_redef cparams cfields [] [] p);
          let pnames = List.map c.comp_params ~f:(fun (p, _) -> get_id p) in
          (* Check for shadowing in statements. *)
          let rec stmt_iter stmts stmt_defs =
            foldM stmts ~init:stmt_defs ~f:(fun acc_stmt_defs (s, _) ->
                match s with
                | Load (x, _)
                | RemoteLoad (x, _, _)
                | MapGet (x, _, _, _)
                | RemoteMapGet (x, _, _, _, _)
                | ReadFromBC (x, _) ->
                    check_warn_redef cparams cfields pnames stmt_defs x;
                    pure (get_id x :: acc_stmt_defs)
                | Store _ | MapUpdate _ | SendMsgs _ | AcceptPayment | GasStmt _
                | CreateEvnt _ | Throw _ | CallProc _ | Iterate _ ->
                    pure acc_stmt_defs
                | Bind (x, e) ->
                    check_warn_redef cparams cfields pnames stmt_defs x;
                    let%bind () = expr_iter e cparams cfields pnames in
                    pure (get_id x :: acc_stmt_defs)
                | MatchStmt (_, clauses) ->
                    let%bind () =
                      forallM
                        ~f:(fun (pat, mbody) ->
                          let%bind () =
                            pattern_iter pat cparams cfields pnames
                          in
                          Result.ignore_m @@ stmt_iter mbody acc_stmt_defs)
                        clauses
                    in
                    pure acc_stmt_defs)
          in
          (* Go through all statements and see if any of cparams, cfields or pnames are redefined. *)
          Result.ignore_m @@ stmt_iter c.comp_body [])
        cmod.contr.ccomps

    let shadowing_lmod (lmod : lmodule) =
      (* Check for match pattern shadowing in library functions. *)
      shadowing_libentries lmod.libs.lentries
  end

  (* ************************************** *)
  (* ******** Dead Code Detector ********** *)
  (* ************************************** *)
  module DeadCodeDetect = struct
  (* Dead Code Detector for Contracts *)
  open AssocDictionary
  (* TODO:
  - Check if procedures, mutable fields, immutable contracts parameters are used
  - Check if procedures' parameters are used
  - Check pattern-matching binders
  - Check functions defined in the library of the file are used
  - Check if function params are used

  - Check for useless library imports

  - Change from storing as strings to storing as Identifiers
  - go through syntax to see predefined useful functions
  *)

    (* Update a dictionary that a value is used, return whether we updated a dict *)
    let mark_used dict_ref name =
      let sname = as_error_string name in
      let v = lookup (sname) !dict_ref in
      match v with 
      | Some (false, rep) -> 
        dict_ref := update_all (as_error_string name) (true, rep) !dict_ref;
        true
      | _ -> false
    
    (* Clear dictionary *)
    let clear_dict dict_ref = 
      dict_ref := make_dict ()

    (* Add to dict *)
    let add_dict dict_ref name =
      dict_ref := insert_unique (as_error_string name) (false, get_rep name) !dict_ref

    (* Filter through dictionary to find unused identifiers *)
    let find_unused_ER dict warn_msg =
      let unused_list = List.map (List.filter (to_list dict) ~f:(fun (_, (v, _)) -> not v))
        ~f:(fun (name, (_, rep)) -> (name, rep)) 
      in
      if not (List.is_empty unused_list) then 
      List.iter unused_list ~f:( fun (name, rep) ->
        warn1 (warn_msg ^ name) warning_level_dead_code (ER.get_loc rep);
      )

    let find_unused_SR dict warn_msg =
      let unused_list = List.map (List.filter (to_list dict) ~f:(fun (_, (v, _)) -> not v))
        ~f:(fun (name, (_, rep)) -> (name, rep)) 
      in
      if not (List.is_empty unused_list) then 
      List.iter unused_list ~f:( fun (name, rep) ->
        warn1 (warn_msg ^ name) warning_level_dead_code (SR.get_loc rep);
      )


    (* Dead Code Detector of a Contract Module *)
    let dc_cmod (cmod: cmodule) (elibs: libtree list) =

      (**************** ASSERTIONS ***************)

      (* Checking elibs and cmod.elib are the same *)
      let cmod_elib_list = List.map cmod.elibs fst in 
      let elibs_list = List.map elibs ~f:(fun libt -> libt.libn.lname) in
      if (List.length cmod_elib_list) <> (List.length elibs_list) then 
        warn1 ("Bug in imported libraries - imported libraries might be incorrect") warning_level_dead_code (SR.get_loc SR.dummy_rep);
      List.iter cmod_elib_list ~f:(fun elib -> 
        let find = List.find elibs_list ~f:(fun e -> SCIdentifier.equal e elib) in
        match find with 
        | None ->  warn1 ((as_error_string elib) ^ " not found in elib") warning_level_dead_code (SR.get_loc SR.dummy_rep)
        | Some _ -> ()
      );
      List.iter elibs_list ~f:(fun elib -> 
        let find = List.find cmod_elib_list ~f:(fun e -> SCIdentifier.equal e elib) in
        match find with 
        | None ->  warn1 ((as_error_string elib) ^ " not found in cmod_elib_list") warning_level_dead_code (SR.get_loc SR.dummy_rep)
        | Some _ -> ()
      );
    

      (************** DC Detector ***************)
      (* Global dictionaries: fields, contract parameters, procedures *)
      (* Global refers to being global in the contract *)
      let cfields_dict = ref (make_dict ()) in
      let cparams_dict = ref (make_dict ()) in
      let proc_dict = ref (make_dict ()) in

      (* Library entries *)
      let libvar_dict = ref (make_dict ()) in
      let libty_dict = ref (make_dict ()) in

      (* Library imports *)
      let elibs_dict = ref (make_dict ()) in


      (********* Populate library imports ***********)
      List.iter cmod.elibs ~f:(fun (lib_name, _) ->
        add_dict elibs_dict lib_name
      );

      (* "The scope of variables in an imported library is restricted to 
         the immediate importer." *)
      (* Check if var or type exists in library *)
      let exists_in_lib x elib = 
        let iter_lib_entry lentries x =
          let found = ref false in
          List.iter lentries ~f:(fun lentry ->
            match lentry with 
            | LibVar (iden, _, _) -> 
              (* TODO: remove *)
              (* warn1 ("libvar " ^ (as_error_string iden)) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
              if SCIdentifier.equal iden x then
                found := true;
            | LibTyp (iden, _) -> 
              (* safe to check with var cause rep would be unique *)
              if SCIdentifier.equal iden x then 
                found := true
          );
          !found
        in
        iter_lib_entry elib.libn.lentries x
      in

      let mark_used_elibs f =
        (* find all elibs that have not been used *)
        let unused_elibs = List.filter elibs ~f:(fun elib ->
          (* warn1 ("Checking for unused_elib : " ^ (as_error_string elib.libn.lname)) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
          match AssocDictionary.lookup (as_error_string elib.libn.lname) !elibs_dict with
          | None -> false (* shouldn't happen *)
          | Some (is_used, _) -> not is_used)
        in
        let res = ref false in
        (* iterate through elibs, check if they have been used, find the f function in them, mark if found*)
        List.iter unused_elibs ~f:(fun elib ->  
          if exists_in_lib f elib then 
            let _ = mark_used elibs_dict elib.libn.lname in
            (* let msg = sprintf "Found def in lib: %s" (as_error_string elib.libn.lname) in   *)
            (* warn1 (msg) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
            res := true;
        );
        !res
      in

      (* Marking use of ADTs *)
      let rec mark_used_ty ty =
          match ty with 
          | SCType.ADT (iden, _) -> 
            let _ = mark_used libty_dict iden in 
            let _ = mark_used_elibs iden in
            ()
          | SCType.MapType (ty1, ty2) | SCType.FunType (ty1, ty2) -> 
            mark_used_ty ty1;
            mark_used_ty ty2;
          | _ -> ()
          (* TODO: TEST *)
      in   


      (******* Populate library dictionaries *******)
      let pop_lib_dict () =
        match cmod.libs with 
        | None -> ()
        | Some lib -> 
          List.iter lib.lentries ~f:( fun lib_entry ->
            match lib_entry with 
            | LibVar (name, _, e) -> 
              (* warn1 ("Added to libvar_dict " ^ (as_error_string name)) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
              add_dict libvar_dict name;
            | LibTyp (name, _) -> add_dict libty_dict name
          );
      in 
      pop_lib_dict ();


      (******* Populate contract dictionaries *******)
      List.iter cmod.contr.cfields ~f:( fun (iden, ty, expr) ->
        add_dict cfields_dict iden;
        (* Mark the use of ADT *)
        let _ = mark_used_ty ty in ()
      );

      List.iter cmod.contr.cparams ~f:(
        fun (cparam, _) -> 
          add_dict cparams_dict cparam;
      );

      List.iter cmod.contr.ccomps ~f:(fun comp -> 
        match comp.comp_type with 
        | CompTrans -> ()
        | CompProc -> 
          (* Populate the procedure dictionary *)
          proc_dict := insert_unique (as_error_string comp.comp_name) (false, ER.dummy_rep) !proc_dict;
      );


      (**************** Iterators ****************)
      (* Iterate through expressions to look for use of 
      - Contract parameters
      - Contract parameters/Pattern binders/Local variables
      - Defined libraries' functions/types
      - Imported libraries
      *)
      let rec expr_iter expr local_dicts = 

        let mark_used' x = 
          if not @@ mark_used cparams_dict x then
            if not @@ mark_used libvar_dict x then     
              if not @@ mark_used_elibs x then          
                List.iter local_dicts ~f:(fun dict -> 
                  let _ = mark_used dict x in ());
        in

        (* warn1 (pp_expr @@ fst expr) warning_level_dead_code (SR.get_loc SR.dummy_rep);  *)
        
        match fst expr with 
        | Literal l -> 
          begin
            match l with 
            | Msg msg ->
              List.iter msg ~f:(fun (_, ty, _) -> mark_used_ty ty)
            | Map ((ty1, ty2), _) -> 
              mark_used_ty ty1;
              mark_used_ty ty2
            | ADTValue (_, tys, _) -> List.iter tys ~f:mark_used_ty 
            | _ -> ()
          end
        | Var x -> mark_used' x;
        | Let (i, ty_o, e1, e2) ->
          begin 
            (match ty_o with 
            | None -> ();
            | Some ty -> mark_used_ty ty);
            let local_dict = ref (make_dict ()) in
            local_dict := insert_unique (as_error_string i) (false, get_rep i) !local_dict;
            expr_iter e1 local_dicts;
            expr_iter e2 (local_dict :: local_dicts);
            find_unused_ER !local_dict "Unused local variable: ";
            (* TODO: TEST *)
          end
        | Message sl ->
          List.iter sl ~f:( fun (_, payload) ->
            match payload with
            | MLit _ -> () 
            | MVar x -> mark_used' x;
          )
        | Constr (iden, tys, es) ->
          (* warn1 ("Constr " ^ (as_error_string iden)) warning_level_dead_code (SR.get_loc SR.dummy_rep);  *)
          List.iter tys ~f:(fun ty -> mark_used_ty ty);
          List.iter es ~f:(fun e -> mark_used' e)
        | App (f, actuals) ->
          mark_used' f;
          (* warn1 ("App " ^ (as_error_string f)) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
          List.iter actuals ~f:(fun act -> 
          (* warn1 (as_error_string act) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
          mark_used' act)
        | TApp (f, tys) -> 
          mark_used' f;
          List.iter tys mark_used_ty;
          (* warn1 ("TApp " ^ (as_error_string f)) warning_level_dead_code (SR.get_loc SR.dummy_rep);  *)
        | MatchExpr (x, plist) ->
          begin
            mark_used' x;
            List.iter (plist) ~f:(fun (pat, exp') -> 
              let bounds = get_pattern_bounds pat in
              let local_dict = ref (make_dict ()) in
              List.iter bounds ~f:(fun bound ->
                local_dict := insert_unique (as_error_string bound) (false, get_rep bound) !local_dict;
              );
              expr_iter exp' (local_dict :: local_dicts);
              find_unused_ER !local_dict "Unused Variable: "
            ) (* TODO: TEST *)
          end
        | Builtin (builtin, tys, actuals) -> 
          (* warn1 ("Builtin " ^ (pp_builtin @@ fst builtin)) warning_level_dead_code (SR.get_loc SR.dummy_rep);  *)
          List.iter tys mark_used_ty;
          (* warn1 ("Builtin") warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
          List.iter actuals ~f:(fun act -> 
          (* warn1 (as_error_string act) warning_level_dead_code (ER.get_loc ER.dummy_rep); *)
          mark_used' act);
        | Fixpoint (_, ty, e) 
        | Fun (_, ty, e) -> expr_iter e local_dicts; mark_used_ty ty;
        | TFun (_, e) | GasExpr (_, e) -> expr_iter e local_dicts
      in

      (* Iterate through stmts to look for use of 
      - Mutable fields
      - Pattern binders/Local variables
      - Defined libraries' functions
      - Imported libraries
      *)
      let rec stmt_iter stmts local_dicts =
        let mark_used' x = 
          if not @@ mark_used cfields_dict x then
            if not @@ mark_used libvar_dict x then
              if not @@ mark_used_elibs x then
                List.iter local_dicts ~f:(fun dict -> 
                  let _ = mark_used dict x in ())
          
        in
        List.iter stmts ~f:(fun (s, _) -> 
          match s with 
          | Load (_, f) -> mark_used' f 
          | RemoteLoad (_, f1, f2)
          | Store (f1, f2) -> mark_used' f1; mark_used' f2
          | MapUpdate (f, i1, i2) ->
            begin
              mark_used' f; 
              List.iter i1 mark_used';
              match i2 with 
              | Some i -> mark_used' i;
              | None -> ()
            end
          | MapGet (_, f, i1, _) | RemoteMapGet (_, _, f, i1, _) ->
            mark_used' f;
            List.iter i1 mark_used'
          | Bind (x, expr) -> expr_iter expr local_dicts (* TODO: check for use of x *)
          | CallProc (p, actuals) -> 
            let _ = mark_used proc_dict p in ();
            List.iter actuals mark_used';
          | MatchStmt (x, plist) ->
            begin
              mark_used' x;
              List.iter plist ~f:(fun (pat, stmts') ->
                let bounds = get_pattern_bounds pat in 
                let local_dict = ref (make_dict ()) in
                List.iter bounds ~f:( fun bound ->
                  local_dict := insert_unique (as_error_string bound) (false, get_rep bound) !local_dict;
                );
                stmt_iter stmts' (local_dict :: local_dicts);
                find_unused_ER !local_dict "Unused Variable: "
              );
            end
          | Iterate (l, p) -> 
            let _ = mark_used proc_dict p in ();
            mark_used' l
          | SendMsgs m -> mark_used' m
          | ReadFromBC (x, _) | CreateEvnt x -> mark_used' x
          | Throw x_o -> (match x_o with | Some x -> mark_used' x | _ -> ())
          | AcceptPayment
          | GasStmt _ -> ()
        )

      in

      (* Iterate through body of components *)
      List.iter cmod.contr.ccomps ~f:(fun c ->
        (* Create local dictionaries: component params *)
        let param_dict = ref (make_dict ()) in
        List.iter c.comp_params ~f:(
          fun (param, ty) -> 
            param_dict := insert_unique (as_error_string param) (false, get_rep param) !param_dict;
            mark_used_ty ty;
        );
        stmt_iter c.comp_body [param_dict];
        find_unused_ER !param_dict "Unused local component parameter: "
      );

      (* Iterate through expressions of fields *)
      List.iter cmod.contr.cfields ~f:(fun (_, ty, exp) ->
        expr_iter exp [];
        mark_used_ty ty;
      );

      (* Check constraints through expressions *)
      expr_iter cmod.contr.cconstraint [];

      (* Check use of contract identifiers *)
      find_unused_ER !proc_dict "Unused procedures: ";
      find_unused_ER !cfields_dict "Unused fields: ";
      find_unused_ER !cparams_dict "Unused contract params: ";

      (* Clear contract dictionaries for checking libraries *)
      clear_dict proc_dict;
      clear_dict cfields_dict;
      clear_dict cparams_dict;

      (* Check exp from libraries *)
      match cmod.libs with 
      | None -> ()
      | Some lib ->
        List.iter lib.lentries ~f:( fun l_entry ->
          match l_entry with 
          | LibTyp _ -> ()
          | LibVar (iden, _, e) -> 
            (* warn1 ("Lib entry " ^ (as_error_string iden)) warning_level_dead_code (SR.get_loc SR.dummy_rep); *)
            expr_iter e [];
        );

    (* Libraries can be imported just for the new lmodule definition *)
    find_unused_SR !elibs_dict "Unused imported libraries: ";
    find_unused_ER !libvar_dict "Unused library var: ";
    find_unused_ER !libty_dict "Unused user defined ADT: ";

  end

  (* ************************************** *)
  (* ******** Interface to Checker ******** *)
  (* ************************************** *)

  let contr_sanity (cmod : cmodule) (rlibs : lib_entry list)
      (elibs : libtree list) =
    let%bind () = basic_sanity cmod in
    let%bind () = CheckShadowing.shadowing_libentries rlibs in
    let%bind () = forallM ~f:CheckShadowing.shadowing_libtree elibs in
    let%bind () = CheckShadowing.shadowing_cmod cmod in
    DeadCodeDetect.dc_cmod cmod elibs;
    pure ()

  let lmod_sanity (lmod : lmodule) (rlibs : lib_entry list)
      (elibs : libtree list) =
    let%bind () = CheckShadowing.shadowing_libentries rlibs in
    let%bind () = forallM ~f:CheckShadowing.shadowing_libtree elibs in
    let%bind () = CheckShadowing.shadowing_lmod lmod in
    pure ()
end
