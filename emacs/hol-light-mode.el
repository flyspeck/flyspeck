
;; modified  from svn rev 66
;; URL: http://seanmcl-ocaml-lib.googlecode.com/svn/trunk/workshop/software/emacs 
;; author Sean McLaughlin

;; TODO

;; Eval buffer centering
;; Folding
;; Subterm typing
;; Push/pop proofs?
;; backup n steps

(require 'folding)
(require 'hol-light)

;;----------------------------------------------------------------------------;;
;; Center                                                                     ;;
;;----------------------------------------------------------------------------;;

(defun hol-light-center-window()
  (interactive)
  (other-window 1)
  (goto-char (point-max))
  (recenter)
  (other-window 1))

;;----------------------------------------------------------------------------;;
;; Fix Hol-Light Mode                                                         ;;
;;----------------------------------------------------------------------------;;

(defun hol-light-run-process-if-needed ()
  (if (not (comint-check-proc hol-light-interactive-buffer-name))
      (let ((hol-light-interactive-program 
             (read-shell-command "Caml toplevel to run: "
                                 "hol_light")))
        (set-buffer (make-comint "hol-light-toplevel" 
                                 hol-light-interactive-program))
        (hol-light-interactive-mode)
        )))

(defun hol-light-eval-string (s)
  "Eval the string in the Caml toplevel."
  (interactive "s")
  (save-excursion (hol-light-run-process-if-needed))
  (comint-preinput-scroll-to-bottom)
  (save-excursion
    (set-buffer hol-light-interactive-buffer-name)
    (comint-send-string hol-light-interactive-buffer-name
                        (concat s ";;"))
    (let ((pos (point)))
      (comint-send-input)
      (if hol-light-interactive-echo-phrase
          (save-excursion
            (goto-char pos)
            (insert (concat s ";;"))))))
  (when hol-light-display-buffer-on-eval
    (display-buffer hol-light-interactive-buffer-name)))

(defun hol-light-eval-region (start end)
  "Eval the current region in the Caml toplevel."
  (interactive "r")
  (save-excursion (hol-light-run-process-if-needed))
  (comint-preinput-scroll-to-bottom)
  (setq hol-light-interactive-last-phrase-pos-in-source start)
  (save-excursion
    (goto-char start)
    (hol-light-skip-blank-and-comments)
    (setq start (point))
    (goto-char end)
    (hol-light-skip-to-end-of-phrase)
    (setq end (point))
    (let ((text (buffer-substring-no-properties start end)))
      (hol-light-eval-string text))))

(defun hol-light-eval-line()
  (interactive) 
  (save-excursion 
    (beginning-of-line)
    (let ((beg (point)))
      (end-of-line)
      (hol-light-eval-region beg (point))
      )))

(defun hol-light-eval-line-and-continue()
  (interactive) 
  (hol-light-eval-line)
  (forward-line 1))

;;--------------------------------------------------------------------------
;; Send                                                                     
;;--------------------------------------------------------------------------

(defun hol-light-get-line()
  "Get a line as a string"
  (save-excursion
    (beginning-of-line)
    (let ((beg (point)))
      (end-of-line)
      (buffer-substring beg (point))
)))

(defun hol-light-de-in(s)
  "If s is a single line take the 'in' off a string.  
   Useful for stepping through programs" 
  (if (string-match "\n" s) s 
    (let ((s1 (if (string-match ".*\n" s)
                  (substring s 0 (- (length s) 1)) 
                s)))
      (let* ((last-line (string-match "[^\n]+\\'" s1))
             (match (string-match " in[ \t]*$" s last-line))) 
        (if match 
            (substring s1 0 match)
          s1)))))

(defun hol-light-de-and(s)
  "Take 'and' off a string."
  (let* ((loc (string-match "^[ \t]*and"  s)))
    (if loc
        (replace-match "let" nil nil s) 
      s)))

;; Match the last occurrance of a regexp
(defun _string-match-last(regexp string ind)
  (let ((match (string-match regexp string ind)))
    (cond 
     ((null match) ind) 
     ((= match (length string)) ind) 
     (t (_string-match-last regexp string (+ match 1)))
)))

(defun string-match-last(regexp string) 
  (let ((last (_string-match-last regexp string 0)))
    (if (= last 0) (length string)
      (-  last 1))))

(defun hol-light-de-semi(s)
  "Take ;; off"
  (let ((end (string-match-last ";;[ \t]*$" s)))
    (substring s 0 end)
))

(defun hol-light-seval-string(s)
  "Evaluate a string after removing and, in and ;; from the end"
  (hol-light-eval-string
   (hol-light-de-and 
    (hol-light-de-in
     (hol-light-de-semi s))))
  (hol-light-center-window))

(defun hol-light-seval-region(beg end)
  (interactive "r")
  (hol-light-seval-string (buffer-substring beg end)))

(defun hol-light-seval-line()
  (interactive)
  (hol-light-seval-string (hol-light-get-line)))

(defun hol-light-seval-newline()
  (interactive)
  (hol-light-seval-line)
  (forward-line 1))

(defun hol-light-get-word(n)
  (save-excursion
    (if (looking-at "[a-zA-Z0-9_]") (forward-word 1) nil)
    (let ((end (point)))
      (backward-word n)
      (buffer-substring (point) end)
)))

(defun hol-light-seval-word(n)
  (interactive "p") 
  (hol-light-seval-string (hol-light-get-word n)))

;;--------------------------------------------------------------------------
;; Quote Eval                                                                     
;;--------------------------------------------------------------------------

(defun hol-light-quote-seval-string(s)
  (hol-light-seval-string (concat "`(" s ")`")))

(defun hol-light-quote-seval-region(beg end)
  (interactive "r") 
  (hol-light-quote-seval-string (buffer-substring beg end)))

(defun hol-light-quote-seval-word(n)
  (interactive "p") 
  (hol-light-quote-seval-string (hol-light-get-word n)))

(defun hol-light-get-marked-area(beg-mark end-mark)
  (save-excursion
    (let ((beg (search-backward beg-mark)))
      (forward-char (length beg-mark))
      (search-forward end-mark)
      (buffer-substring beg (point))
)))

(defun hol-light-quote-seval-quote()
  (interactive)
  (hol-light-quote-seval-string (hol-light-get-marked-area "`" "`")))

;;--------------------------------------------------------------------------
;; Typing                                                                   
;;--------------------------------------------------------------------------

(defun hol-light-type-region(beg end)
  (interactive "r")
  (hol-light-seval-string (concat "type_of `(" (buffer-substring beg end) ")`")))

(defun hol-light-type-word(n)
  (interactive "p")
  (hol-light-seval-string (concat "type_of `(" (hol-light-get-word ne) ")`")))

;; (defun hol-light-type-assum(n)
;;   (interactive "p")
;;   (hol-light-seval-string (concat "assum_types " (int-to-string n))))

(defun hol-light-goal-types()
  (interactive)
  (hol-light-seval-string "goal_types()"))

;; (defun hol-type-last-expr()
;;   (interactive)
;;   (let ((window (selected-window)))
;;     (select-window (get-buffer-window (program-buffer-name)))
;;     (end-of-buffer)
;;     (insert "it;;")
;;     (comint-send-input)
;;     (search-backward "val it : ")
;;     (search-forward "val it : ")
;;     (let ((type (cond ((looking-at "thm") "thm")
;;                       ((looking-at "term") "term")
;;                       ((looking-at "goalstack") "goalstack"))))
;;       (end-of-buffer)
;;       (cond ((equal type "thm") 
;;              (insert "print_thm_types it;;"))
;;             ((equal type "term") 
;;              (insert "print_term_types it;;"))
;;             ((equal type "goalstack") 
;;              (insert "goal_types();;"))
;;             (t (message "not at a type/term/goal")))
;;       (comint-send-input))
;;     (select-window window)))

;;----------------------------------------------------------------------
;; Goalstack                                                            
;;----------------------------------------------------------------------

(setq current-goal "T")

(defun hol-light-make-goal()
  "cursor must be inside goal"
  (interactive)
  (let ((goal (hol-light-get-marked-area "`" "`")))
    (setq current-goal goal)
    (hol-light-seval-string (concat "g " goal ))))

(defun hol-light-restart-goal()
  (interactive)
  (hol-light-seval-string (concat "g " current-goal)))

(defun hol-light-backup()
  (interactive)
  (hol-light-seval-string "b()"))

(defun hol-light-print()
  (interactive)
  (hol-light-seval-string "p()"))

(defun hol-light-rotate(n)
  (interactive "p")
  (hol-light-seval-string (concat "r " (number-to-string n))))

;;----------------------------------------------------------------------
;; Tactics                                                              
;;----------------------------------------------------------------------

(defun hol-light-de-then(s)
  (let* ((end (string-match " THEN[L]?\[?[ \t\n]*\\'" s))
         (ret (substring s 0 end)))
    ret
    ))

(defun hol-light-de-bracket(s)
  (let* ((has-brack (string-match "^[ \t\n]*\\[" s))
         (brack (if has-brack (string-match "\\[" s) -1))
         (ret (substring s (+ brack 1))))
    ret
    ))

(defun hol-light-tactic-region(beg end)
  (interactive "r")
  (hol-light-seval-string (concat "e (" (hol-light-de-then (buffer-substring beg end)) ")")))

(defun hol-light-tactic-line()
  (interactive)
  (hol-light-seval-string (concat "e (" (hol-light-de-bracket
				     (hol-light-de-then 
				      (hol-light-get-line))) ")")))

(defun hol-light-tactic-newline()
  (interactive)
  (hol-light-tactic-line)
  (forward-line 1))

(defun hol-light-tactic-word(n)
  (interactive "p")
  (hol-light-seval-string (concat "e (" (hol-light-de-then (hol-light-get-word n)) ")")))

;;----------------------------------------------------------------------------;;
;; Help                                                                       ;;
;;----------------------------------------------------------------------------;;

(defun hol-light-help-word(n)
  (interactive "p")
  (hol-light-seval-string (concat "help (\"" (hol-light-get-word n) "\")")))

;; (defun hol-light-help-region(beg end)
;;   (interactive "r")
;;   (hol-light-seval-string (concat "help (\"" (buffer-substring beg end) "\")")))

;;----------------------------------------------------------------------
;; Folding                                                             
;;----------------------------------------------------------------------

(defun hol-light-fold-string(beg end string)
  (goto-char end)
  (insert "(* }}} *)\n")
  (goto-char beg)
  (insert (concat "(* {{{ " string " *)\n"))
  (folding-hide-current-entry))

(defun hol-light-fold-test(beg end)
  (interactive "r")
  (hol-light-fold-string beg end "Test"))

(defun hol-light-fold-lemmas(beg end)
  (interactive "r")
  (hol-light-fold-string beg end "Lemmas"))

(defun hol-light-fold-proof(beg end)
  (interactive "r")
  (hol-light-fold-string beg end "Proof"))

(defun hol-light-fold-doc(beg end)
  (interactive "r")
  (hol-light-fold-string beg end "Doc"))

(defun hol-light-fold-examples(beg end)
  (interactive "r")
  (hol-light-fold-string beg end "Examples"))

;;-------------------------------------------------------------------------;
;; Free Variables                                                          ;
;;-------------------------------------------------------------------------;

(defun hol-light-frees()
  (interactive)
  (let ((term (hol-light-get-marked-area "`" "`")))
    (hol-light-seval-string (concat "frees " term))))

;;---------------------------------------------------------------------------;;
;; Define the Major Mode                                                     ;;
;;---------------------------------------------------------------------------;;

(folding-add-to-marks-list 'hol-light-mode "(* {{{ " "(* }}} *)" " *)" )

(add-hook 'hol-light-mode-hook
  (function (lambda ()
    (message "hello from hol-light-mode hook")
    
    ;; syntax
    (modify-syntax-entry ?_  "w" hol-light-mode-syntax-table)
    (modify-syntax-entry ?`  "\"" hol-light-mode-syntax-table)

    ;; keybindings
    (local-unset-key "\C-x\C-e")          
    (local-unset-key "\C-c")

    ;; non-c bindings
    (local-set-key [(meta return)] 'hol-light-seval-line)
    (local-set-key [(control return)] 'hol-light-seval-region)
    (local-set-key [(control meta return)] 'hol-light-seval-newline)
   
    (local-set-key "\C-fl" 'folding-toggle-enter-exit)
    (local-set-key "\C-f\C-l" 'folding-toggle-show-hide)
    (local-set-key "\C-g" 'keyboard-quit)

    ;;; c bindings

    ;; a
    (local-set-key "\C-c\C-a" 'hol-light-type-assum)

    ;; b
    (local-set-key "\C-c\C-b" 'hol-light-backup)

    ;; c 
    (local-set-key "\C-c\C-c" 'hol-light-interrupt-caml)
    (local-set-key "\C-cc" 'hol-light-center-window)

    ;; e
    (local-set-key "\C-c\C-e" 'hol-light-eval-phrase)

    ;; f
    (local-set-key "\C-c\C-f\C-d" 'hol-light-fold-doc)
    (local-set-key "\C-c\C-f\C-e" 'hol-light-fold-examples)
    (local-set-key "\C-c\C-f\C-l" 'hol-light-fold-lemmas)
    (local-set-key "\C-c\C-f\C-p" 'hol-light-fold-proof)
    (local-set-key "\C-c\C-f\C-t" 'hol-light-fold-test)

    ;; g
    (local-set-key "\C-cg" 'hol-light-goal-types)
    (local-set-key "\C-c\C-g" 'hol-light-make-goal)

    ;; h
    (local-set-key "\C-c\C-h" 'hol-light-help-word)
;;    (local-set-key "\C-ch" 'hol-light-help-region)

    ;; k
    (local-unset-key "\C-c\C-k") ;; set to kill-ocaml

    ;; l
    (local-set-key "\C-c\C-l" 'hol-light-tactic-newline)
    (local-set-key "\C-cl" 'hol-light-tactic-line)

    ;; o 
    (local-set-key "\C-c\C-o" 'hol-light-rotate)

    ;; p
    (local-set-key "\C-c\C-p" 'hol-light-print)
    (local-set-key "\C-cp" 'hol-type-last-expr)

    ;; q
    (local-set-key "\C-c\C-q" 'hol-light-quote-seval-quote)
    (local-set-key "\C-cq" 'hol-light-quote-seval-region)

    ;; r
    (local-set-key "\C-c\C-r" 'hol-light-tactic-region)
    (local-set-key "\C-cr" 'hol-light-restart-goal)

    ;; s
    (local-set-key "\C-c\C-s" 'hol-light-frees)

    ;; t
    (local-set-key "\C-c\C-t\C-l" 'hol-light-tactic-line)
    (local-set-key "\C-c\C-t\C-r" 'hol-light-tactic-region)
    (local-set-key "\C-c\C-t\C-w" 'hol-light-tactic-word)

    ;; v

    ;; w
    (local-set-key "\C-cw" 'hol-light-quote-seval-word)

    ;; y 
    (local-set-key "\C-c\C-y" 'hol-light-type-region)

    ;; z

)))
;; (setq hol-light-light-mode-hook nil)

;; (provide 'hol-light-mode)

;;============================================================================;;
;; Under development                                                          ;;
;;============================================================================;;


;;----------------------------------------------------------------------
;; Saving Stack State                                                   
;;----------------------------------------------------------------------

(setq goalstack-name "saved_stack")

(defun hol-light-save-stack(n)
  (interactive "p")
  (hol-light-seval-string (concat "let " goalstack-name 
                               (number-to-string n) " = !current_goalstack")))

(defun hol-light-back-to-saved-stack(n)
  (interactive "p")
  (hol-light-seval-string (concat "current_goalstack := " goalstack-name 
                               (number-to-string n) "; p();;")))

;; (defun hol-light-push-proof()
;;   (interactive)
;;   (hol-light-seval-string (program-get-marked-area "`" "`") "push_proof " ";;"))

;; (defun hol-light-pop-proof()
;;   (interactive)
;;   (program-send-string "pop_proof();;"))
