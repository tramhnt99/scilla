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
  - Don't forget to check the contraints
  *)

    let dead_code_cmod (cmod : cmodule) = 

      (* Update a dictionary that a value is used *)
      let mark_used dict_ref name =
        dict_ref := update_all (as_error_string name) true !dict_ref
      in

      let dead_proc () =

        (* Dictionaries of procedures, fields, and contract parameters *)
        let proc_dict = ref (make_dict ()) in
        let cfields_dict = ref (make_dict ()) in
        let cparams_dict = ref (make_dict ()) in

        (* Populate the dictionary with existing procedures *)
        List.iter 
          (List.filter cmod.contr.ccomps ~f:(fun comp -> 
              match comp.comp_type with
              | CompTrans -> false
              | CompProc -> true
          )) ~f:(fun comp -> 
          proc_dict := insert_unique (as_error_string comp.comp_name) false !proc_dict
          );

        (* Populate the dictionary with cfields *)
        List.iter 
          (List.map cmod.contr.cfields ~f:( fun (a, b, c) -> a))
            ~f:(fun cfield ->
              cfields_dict := insert_unique (as_error_string cfield) false !cfields_dict
            );

        (* Populate the dictionary with cparams *)
        List.iter 
          (List.map cmod.contr.cparams ~f:fst)
            ~f:(fun cparam -> 
              cparams_dict := insert_unique (as_error_string cparam) false !cparams_dict
            );

        (* Expressions iterator that
          - Logs used parameters
          - ...
         *)

        (* TODO: Might not need to be recursive *)
        let rec expr_iter expr = 
            match fst expr with
            | Var x -> 
              (* if x is not ppart of param, it is not added to dict 
              - from implementation of List.Assoc.add *)
              mark_used cparams_dict x;
              let msg = sprintf "Var %s" (as_error_string x) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep);
            | App (f, actuals) ->
              (* Can parameters be declared as functions? *)
              mark_used cparams_dict f;
              List.iter actuals ~f:(
                fun act -> 
                  mark_used cparams_dict act;
                  let msg = sprintf "Application of actual %s" (as_error_string act) in
                  warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep);
              )
            | Builtin (_, _, actuals) -> 
              List.iter actuals ~f:(
                fun act ->
                  mark_used cparams_dict act;
              )
            (* | Fun (f, _, _ ) -> 
              let msg = sprintf "Function %s" (as_error_string f) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep);
            | TFun (tv, _) -> 
              let msg = sprintf "TFunction %s" (as_error_string tv) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep);
            | Constr (n, _, _) ->
              let msg = sprintf "Constr %s" (as_error_string n) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep); *)
            (* | Let (i, _, _, _)-> 
              let msg = sprintf "Let %s" (as_error_string i) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep);
            | Fixpoint (f, _, _) ->
              let msg = sprintf "Fixpoint %s" (as_error_string f) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep);
            | TApp (tf, _) ->
              let msg = sprintf "TApp %s" (as_error_string tf) in
              warn1 msg warning_level_map_load_store (ER.get_loc ER.dummy_rep); *)
            | _ -> ()
        in
        
        (* Finds all used procedures *)
        List.iter ~f:(fun c -> 
          let rec stmt_iter stmts = 
            List.iter ~f:(fun (s, _) -> 
              match s with
              | Load (_, f') | RemoteLoad (_, _, f') 
              | MapGet (_, f', _, _) | RemoteMapGet (_, _, f', _, _)
              | MapUpdate (f', _, _)
              | Store (f', _) -> (* TODO: storing/updating without using prev value is also dead code *)
                mark_used cfields_dict f';
              | Bind (_, expr) -> expr_iter expr
              | CallProc (p, _ ) -> mark_used proc_dict p;
              | MatchStmt (_, clauses) ->
                (List.iter ~f:(fun (_, mbody) ->
                  stmt_iter mbody
                ) clauses)
              | _ -> ()
            ) stmts
          in stmt_iter c.comp_body
        ) cmod.contr.ccomps;
        
        let warn_msg1 = 
          let proc_list = to_list !proc_dict in
          let unused_proc = List.map (List.filter proc_list ~f:(fun (_, v) -> not v)) fst in 
          sprintf "\nUnused procedures: %s\n" (String.concat ~sep:", " unused_proc)
        in
        warn1 warn_msg1 warning_level_map_load_store (ER.get_loc ER.dummy_rep);

        let warn_msg2 =
          let fields_list = to_list !cfields_dict in
          let unused_fields = List.map (List.filter fields_list ~f:(fun (_, v) -> not v)) fst in 
          sprintf "\nUnused fields: %s\n" (String.concat ~sep:", " unused_fields)
        in
        warn1 warn_msg2 warning_level_map_load_store (ER.get_loc ER.dummy_rep);

        let warn_msg3 = 
          let cparam_list = to_list !cparams_dict in
          let unused_cparam = List.map (List.filter cparam_list ~f:(fun (_, v) -> not v)) fst in 
          sprintf "\nUnused contract params: %s\n" (String.concat ~sep:", " unused_cparam)
        in
        warn1 warn_msg3 warning_level_map_load_store (ER.get_loc ER.dummy_rep);
      in

    dead_proc ();
    (* dead_cfields () *)
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
    DeadCodeDetect.dead_code_cmod cmod;
    pure ()

  let lmod_sanity (lmod : lmodule) (rlibs : lib_entry list)
      (elibs : libtree list) =
    let%bind () = CheckShadowing.shadowing_libentries rlibs in
    let%bind () = forallM ~f:CheckShadowing.shadowing_libtree elibs in
    let%bind () = CheckShadowing.shadowing_lmod lmod in
    pure ()
end
