;;  This file is part of scilla.
;;
;;  Copyright (c) 2018 - present Zilliqa Research Pvt. Ltd.
;;  
;;  scilla is free software: you can redistribute it and/or modify it under the
;;  terms of the GNU General Public License as published by the Free Software
;;  Foundation, either version 3 of the License, or (at your option) any later
;;  version.
;; 
;;  scilla is distributed in the hope that it will be useful, but WITHOUT ANY
;;  WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
;;  A PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;; 
;;  You should have received a copy of the GNU General Public License along with
;;  scilla.  If not, see <http://www.gnu.org/licenses/>.

;; This is an Emacs major mode for the Scilla language.
;; Include the below lines (with path set properly) in ~/.emacs
;;    ;; For enabling flycheck mode for Scilla.
;;    (setq scilla-mode-path "/absolute/path/to/scilla-mode.el")
;;    (setq scilla-bin-path "/absolute/path/to/scilla-checkers-and-runners/bin")
;;    (setq scilla-stdlib-path "/absolute/path/to/scilla/stdlib")
;;
;;    Note that `dune install` command, which executes when you do `make install`,
;;    issues the paths where it installs things. You may use that information
;;    to setup some of the paths mentioned above.
;;
;;    ;; Load the Scilla major mode.
;;    (load-file scilla-mode-path)
;;
;; or via use-package, e.g.:
;;
;; (use-package scilla
;;   :require flycheck
;;   :load-path (lambda () scilla-mode-path))

(defvar scilla-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for `scilla-mode'.")

(defvar scilla-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "w" st)
    st)
  "Syntax table for `scilla-mode'.")

(defvar scilla-constants
  '("BLOCKNUMBER"))

;; We can't define a simple list of scilla-types as we want
;; a regexp for ByStr[0-9]*, and that won't work with regexp-opt later.
(defvar scilla-types
  "\\b\\(String\\|Int32\\|Int64\\|Int128\\|Uint32\\|Uint64\\|Uint128\\|Int256\\|Uint256\\|BNum\\|ByStr[0-9]*\\|Message\\|Event\\|Map\\|ADT\\)\\b")

(defvar scilla-keywords
  '("builtin" "library" "let" "in" "match" "with" "end" "event"
    "fun" "tfun" "contract" "transition" "procedure" "send" "field" "accept"
    "Emp" "import" "type" "exists" "delete" "forall" "try" "catch" "as" "throw" "Map"
    "scilla_version" "of"))

(defvar scilla-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\( ". 1" st)
    (modify-syntax-entry ?* ". 23" st)
    (modify-syntax-entry ?\) ". 4" st)
    st)
  "Syntax table for `scilla-mode'.")

(defvar scilla-font-lock-keywords
  `(
    ("\(\\*.*\\*\)" 0 font-lock-comment-face t)
    ;; stuff between double quotes
    ("\"\\.\\*\\?" . font-lock-string-face)
    ;; ; : , ; { } =>  @ $ = are all special elements
    ;; (":\\|,\\|;\\|{\\|}\\|=>\\|@\\|$\\|=" . font-lock-keyword-face)
    ( ,(regexp-opt scilla-keywords 'words) . font-lock-keyword-face)
    ( ,scilla-types . font-lock-type-face)
    ;; Some known constants like BLOCKNUMBER etc.
    ( ,(regexp-opt scilla-constants 'words) . font-lock-constant-face)
    ;; Numerical constants. Decimal or Hexadecimal integers.
    ("\\(\\b[0-9]+\\b\\|\\b0x[0-9a-fA-F]+\\b\\)" . font-lock-constant-face)
    ;; Match variable names
    ("\\b[a-z_]+[a-zA-Z0-9]*\\b" . font-lock-variable-name-face)
    ;; Match constructors and type variables
    ("\\b[A-Z]+[a-zA-Z0-9]*\\b" . font-lock-function-name-face)

    ))

;;; Indentation
;; Set to use only spaces for indentation, no tabs.
(setq-default indent-tabs-mode nil)
(setq default-tab-width 2)

;; Rule 1: Beginning of buffer: column 0
;; Rule 2: Previous line contains "(let.*=|transition|procedure)"
;;             indent forward
;; Rule 3: If previous line has "end|send": indent back
;; Rule 4: If line begins with "|", find matching "match" and indent to that.
;; Rule 5: If previous line has "{" but not "}", indent forward and if
;;         previous line has "}" but not "{",
;;         find matching "{" and indent to that line
;; Rule 6: If previous line contains "*=>[ \t]*$"
;;         but current line is not fun:
;;            indent forward.
;; Rule 7: If line begins with "end", find matching "match/transition/procedure"
;; Else: Same as previous line.

(defun scilla-indent-line ()
  "Return the column to which the current line should be indented."
  (interactive)
  (setq cur-col (current-column))
  (beginning-of-line)
  (if (bobp)  ; Check for rule 1
      (indent-line-to 0)
    (let ((indented nil) cur-indent (cur-line (+ (count-lines 1 (point)) 1)) (cur-is nil))
      (save-excursion
        (progn
          ;; Match Rule 4
          (if (looking-at "[ \t]*[|]")
              (let ((ends-seen 0) (matches-seen 0) (lines-seen 0))
                (while (and (not indented) (< lines-seen 100))
                   (progn
                     (if (looking-at "[ \t]*end") (setq ends-seen (+ ends-seen 1)))
                     (if (looking-at "[ \t]*match")(setq matches-seen (+ matches-seen 1)))
                     ;; (message "Line %d: %d matches and %d ends seen" cur-line matches-seen ends-seen)
                     (if (> matches-seen ends-seen)
                         (progn
                           ;; (message "Line %d: rule 4 matched" cur-line)
                           (setq cur-indent (current-indentation))
                           (setq indented 1)
                           )
                       )
                     (forward-line -1)
                     (setq lines-seen (+ lines-seen 1))
                     )
                   )
                )
            )
          ;; Match Rule 7
          (if (looking-at "[ \t]*end")
              (let ((ends-seen 0) (matches-seen 0) (lines-seen 0))
                (while (and (not indented) (< lines-seen 1000))
                  (progn
                    (forward-line -1)
                    (setq lines-seen (+ lines-seen 1))
                    (if (looking-at "[ \t]*end") (setq ends-seen (+ ends-seen 1)))
                    (if (looking-at "[ \t]*\\(match\\|transition|procedure\\)")(setq matches-seen (+ matches-seen 1)))
                    ;; (message "Line %d: %d matches and %d ends seen" cur-line matches-seen ends-seen)
                    (if (> matches-seen ends-seen)
                        (progn
                          ;; (message "Line %d: rule 7 matched" cur-line)
                          (setq cur-indent (current-indentation))
                          (setq indented 1)
                          )
                      )
                    )
                  )
                )
            )
          (if (looking-at "[ \t]*fun")
              (setq cur-is 'fun)
            )
          (forward-line -1)
          ;; Match Rule 2
          (if (and (not indented) (looking-at "[ \t]*\\(transition\\|procedure\\|let.*=[ \t]*$\\)"))
              (progn
                ;; (message "Line %d: rule 2 matched" cur-line)
                (setq cur-indent (+ (current-indentation) default-tab-width))
                (setq indented 1)
                )
            )
          ;; Match Rule 6
          (if (and
               (looking-at ".*=>[ \t]*$")
               (not (eq cur-is 'fun))
               )
              (progn
                ;; (message "Line %d: rule 6 matched" cur-line)
                (setq cur-indent (+ (current-indentation) default-tab-width))
                (setq indented 1)
                )
            )
          ;; Match Rule 3
          (if (and (not indented) (looking-at "[ \t]*s?end"))
              (progn
                ;; (message "Line %d: rule 3 matched" cur-line)
                (setq cur-indent (- (current-indentation) default-tab-width))
                (setq indented 1)
                )
            )
          ;; Match Rule 5
          (if (and (not indented) (looking-at ".*{.*") (not (looking-at "^.*}.*$")))
              (progn
                ;; (message "Line %d: Rule 5a matched. \"{\" seen in previous line." cur-line)
                ;; Find location of "{".
                (re-search-forward "{")
                (setq cur-indent (current-column ))
                (setq indented 1)
                )
            (if (and (not indented) (looking-at "^.*}.*$") (not (looking-at ".*{.*")))
                ;; We have a "}". Search upwards for "{"
                (let ((num-lines 0))
                  (while (and (not indented) (< num-lines 100))
                    (progn
                      (forward-line -1)
                      (if (looking-at ".*{")
                          (progn
                            ;; (message "Line %d: Rule 5b matched. Indenting to \"{\" found." cur-line)
                            (setq cur-indent (current-indentation))
                            (setq indented 1)
                            )
                        )
                      )
                    )
                  )
                )
            )
          ;; No match, just set to previous line.
          (if (not indented)
              (progn
                ;; (message "Line %d: no match, setting to previous line" cur-line)
                (setq cur-indent (current-indentation))
                (setq indented 1)
                )
            )
          )
        )
      ;; Take action.
      (let ((d))
        (progn
          (setq d (- cur-col (current-indentation)))
          (if indented
              (indent-line-to cur-indent)
            (indent-line-to 0)
            )
          (if (> d 0)
              (forward-char d)
            )
          ;; If we're before the first non-white character, move forward
          (if (< (current-column) cur-indent)
              (move-to-column cur-indent)
            )
          )
        )
      )
    )
  )

 ;;;###autoload
(define-derived-mode scilla-mode fundamental-mode "Scilla"
  "A major mode for editing scilla files."
  :syntax-table scilla-mode-syntax-table
  (setq-local comment-start "(*")
  (setq-local comment-end "*)")
  (setq-local font-lock-defaults '(scilla-font-lock-keywords))
  (setq-local indent-line-function 'scilla-indent-line)
  )
(provide 'scilla-mode)
(add-to-list 'auto-mode-alist '("\\.scilla\\'" . scilla-mode))
(add-to-list 'auto-mode-alist '("\\.scillib\\'" . scilla-mode))

;; autoload scilexp files, treat it same as Scilla files.
(define-derived-mode scilexp-mode fundamental-mode "Scilla Expressions"
  "A major mode for editing scilla files."
  :syntax-table scilla-mode-syntax-table
  (setq-local comment-start "(*")
  (setq-local comment-end "*)")
  (setq-local font-lock-defaults '(scilla-font-lock-keywords))
  (setq-local indent-line-function 'scilla-indent-line)
  )
(provide 'scilexp-mode)
(add-to-list 'auto-mode-alist '("\\.scilexp\\'" . scilexp-mode))

;; This is different from (current-column).
;; See https://stackoverflow.com/a/52391495/2128804
(defun column-number-at-pos (point)
  (save-excursion
    (goto-char point)
    (beginning-of-line)
    ;; count columns from 1 instead of emacs default 0.
    (+ 1 (- point (point)))))

(defun get-scilla-type (checker-bin libdir-path filename pos)
  "Given a checker and a filename, Run and extract from the checker output the type of the current variable."
  (condition-case nil
    (progn
      (setq cmd (string-join (list checker-bin filename "-typeinfo" "-gaslimit" "10000" "-libdir" libdir-path) " "))
      (setq checker-output (shell-command-to-string cmd))
      (setq linn (line-number-at-pos pos))
      (setq coln (column-number-at-pos pos))
      (let* ((json-object-type 'hash-table)
             (json-array-type 'list)
             (json-key-type 'string)
             (json (json-read-from-string checker-output)))
        (progn
          ;; The checker output looks like this:
          ;;{
          ;;   "type_info": [
          ;;   {
          ;;      "vname": "one_msg",
          ;;      "type": "Message -> List (Message)",
          ;;      "start_location": {
          ;;        "file": "tests/contracts/crowdfunding.scilla",
          ;;        "line": 11,
          ;;        "column": 5
          ;;      },
          ;;      "end_location": {
          ;;        "file": "tests/contracts/crowdfunding.scilla",
          ;;        "line": 11,
          ;;        "column": 12
          ;;      }
          ;;   },
          ;;   ...
          ;;   ]
          ;;}
          (setq tilist (gethash "type_info" json))
          (if tilist
              (catch 'vtype               ;; If the loop finds an appropriate entry, it'll throw.
                (progn
                  (dolist (vari tilist)
                    (progn
                      (setq startloc (gethash "start_location" vari))
                      (setq endloc (gethash "end_location" vari))
                      (if (and startloc endloc)
                          (progn
                            (setq startline (gethash "line" startloc))
                            (setq startcol (gethash "column" startloc))
                            (setq endline (gethash "line" endloc))
                            (setq endcol (gethash "column" endloc))
                            (if (and startline startcol endline endcol)
                                (when (and (= startline linn) (>= coln startcol) (< coln endcol))
                                  (setq type (gethash "type" vari))
                                  (if type
                                      (throw 'vtype type)
                                    "field type missing in checker output"
                                    )
                                  )
                              "start/end line/column not found"
                              )
                            )
                        "(start/end)_location not found"
                        )
                      )
                    )
                  "type not found for variable"
                  )
                )
            "type_info not found in checker output"
            )
          )
        )
      )
    ;; This error is thrown by the json.el library when it cannot parser the output JSON of the
    ;; checker. This usually happens if the checker found an error, and hence doesn't print a JSON.
    (json-readtable-error "Error inferring type information from the checker. Check the contract.")
    )
  )

;; Global variables set when type-inference can be done.
(defvar checker-bin)
(defvar libdir-path)

(defun print-scilla-type ()
  "Print the type of the variable at current cursor position."
  (interactive)
  (when (and (boundp 'checker-bin) (boundp 'libdir-path))
    (setq type (get-scilla-type checker-bin libdir-path buffer-file-name (point)))
    (message "%s" type)
    )
  )

;; Set scilla paths (see file header) in your ~/.emacs file.
;; Note: make sure to set the paths *before* loading this file (scilla-mode.el)
;; If the paths have been set and flycheck is available, enable flycheck.
(if (and (boundp 'scilla-mode-path)
         (boundp 'scilla-bin-path)
         (boundp 'scilla-stdlib-path))
    (progn
      (setq lib-dir scilla-stdlib-path)
      (setq scilla-checker-bin (concat scilla-bin-path "/scilla-checker"))
      ;; See comment later on why we have two flycheck modes.
      (setq type-checker-bin (concat scilla-bin-path "/type-checker"))
      (if (and (file-directory-p lib-dir)
               (file-exists-p scilla-checker-bin)
               (file-exists-p type-checker-bin))
        (progn
          (if (require 'flycheck nil t)
              (progn
                (flycheck-define-checker scilla
                  "A Scilla syntax checker using scilla-checker. See URL `https://www.scilla-lang.org/'."
                  :command ("scilla-checker" "-gaslimit" "999999999" "-libdir" (eval lib-dir) source)
                  :error-patterns
                  (
                   (error line-start (file-name) ":" line ":" column ": error: " (message) line-end)
                   (warning line-start (file-name) ":" line ":" column ": warning: [" (id (one-or-more alnum)) "] " (message) line-end)
                   )
                  :modes scilla-mode
                  )
                (setq flycheck-scilla-executable scilla-checker-bin)
                (add-to-list 'flycheck-checkers 'scilla)
                (add-hook 'scilla-mode-hook 'flycheck-mode)
                ;; This flycheck mode is created and finalized before we load a source file (static).
                ;; So *-checker-bin cannot be defined conditionally. We need to define two flycheck modes.
                ;; Querying buffer-file-name anywhere here returns nil.
                (flycheck-define-checker scilexp
                  "A Scilla expression syntax checker using type-checker. See URL `https://www.scilla-lang.org/'."
                  :command ("type-checker" "-gaslimit" "999999999" "-libdir" (eval lib-dir) source)
                  :error-patterns
                  (
                   (error line-start (file-name) ":" line ":" column ": error: " (message) line-end)
                   (warning line-start (file-name) ":" line ":" column ": warning: [" (id (one-or-more alnum)) "] " (message) line-end)
                   )
                  :modes scilexp-mode
                  )
                (setq flycheck-scilexp-executable type-checker-bin)
                (add-to-list 'flycheck-checkers 'scilexp)
                (add-hook 'scilexp-mode-hook 'flycheck-mode)
                ;;(flycheck-mode 1)
                )
            (message "Flycheck-mode not available")
            )
          ;; If there's a JSON library available, use it to deserialize and print type information.
          (if (require 'json nil t)
              (progn
                (add-hook 'scilla-mode-hook
                    (lambda ()
                      (progn
                        (setq checker-bin scilla-checker-bin)
                        (setq libdir-path lib-dir)
                        (local-set-key (kbd "C-c C-t") 'print-scilla-type)
                        )
                      )
                  )
                (add-hook 'scilexp-mode-hook
                    (lambda ()
                      (progn
                        (setq checker-bin type-checker-bin)
                        (setq libdir-path lib-dir)
                        (local-set-key (kbd "C-c C-t") 'print-scilla-type)
                        )
                      )
                  )
                )
            (message "json package not available")
            )
          )
        (message "Scilla-Flycheck: scilla paths set incorrectly or one of stdlib or bin/(scilla/type)-checker missing.")
        )
      )
  (message "Scilla-FlyCheck: scilla paths not set.")
  )

 ;;; scilla-mode.el ends here
