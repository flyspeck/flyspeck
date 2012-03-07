;
; Color theme: Charcoal black.
;
; C-x C-e to evaluate

(load "hol-light-mode.el") ; to reload when changes are made.

(hol-light-run-process-if-needed)

(setq hol-light-interactive-buffer-name "*hol-light-toplevel*")
(setq hol-light-interactive-buffer-name "*hol-jun3*")
(setq hol-light-interactive-buffer-name "*jun4*")

; thackmac

(print hol-light-interactive-buffer-name)

(hol-light-interactive-get-old-input)

; process control 
(signal-process 6592 9)

; (* custom *)
(hol-light-display-buffer-on-eval)

(defun insert-date()
  "insert the current date into current buffer"
  (interactive)
  (shell-command "date" t))

; insert date no time
(insert (format-time-string "%D %T %a" (current-time)))

; M-x customize-face RET mode-line, foreground blue, background #E3e889

; was 1024.
; .emacs suggestions:
;(setq comint-buffer-maximum-size 5000)
; keep shell buffer to  5000
;
(custom-set-variables
 '(comint-buffer-maximum-size 8000) ; limit buffer size.
)

;; run a few shells.
(shell "*search*")

; C-5, to switch to shells
(global-set-key [(control 5)]
  (lambda () (interactive) (switch-to-buffer "*search*")))

;(remove-hook 'comint-output-filter-functions
;          'comint-truncate-buffer)


(global-set-key "\C-cy" '(lambda ()
   (interactive)
   (popup-menu 'yank-menu)))

; (setq xxxx yank-menu) 

; scratch
(replace-regexp-in-string "a"  "Q" "abc")
(replace-regexp-in-string "\\\\" "\\\\\\\\" "\\abc")
(replace-regexp-in-string "\"" "\\\\\"" "\"abc")
(string-to-char "\\\\")
(string-to-char "\"")
(info "(elisp) Clickable Text") 

(defun f (button)
    (call-interactively 'find-file))

(defun myfun (button)
  (message (format "Button [%s]" (button-label button))))

(define-button-type 'my-button
  'action 'myfun
  'follow-link t
  'help-echo "Click button")

(insert-text-button "xyz" :type 'my-button)  xyz


