;;; hol-light.el --- Caml mode for (X)Emacs.   -*- coding: latin-1 -*-
   
;;        Copyright © 1997-2008 Albert Cohen, all rights reserved.
;;        Licensed under the GNU General Public License.

;;    This program is free software; you can redistribute it and/or modify
;;    it under the terms of the GNU General Public License as published by
;;    the Free Software Foundation; either version 2 of the License, or
;;    (at your option) any later version.

;;    This program is distributed in the hope that it will be useful,
;;    but WITHOUT ANY WARRANTY; without even the implied warranty of
;;    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;;    GNU General Public License for more details.

;;; Commentary:

;;; Code:

(require 'cl)
(require 'easymenu)

(defconst hol-light-mode-version "HOL Light Version 1.45.6"
  "        Copyright © 1997-2008 Albert Cohen, all rights reserved.
         Copying is covered by the GNU General Public License.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
    GNU General Public License for more details.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                        Emacs versions support

(defconst hol-light-with-xemacs (featurep 'xemacs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                      Compatibility functions

;; inserted tch dec 2015.

(defalias 'make-local-hook 'ignore)

(defalias 'hol-light-match-string
  (if (fboundp 'match-string-no-properties)
      'match-string-no-properties
    'match-string))

(if (not (fboundp 'read-shell-command))
    (defun read-shell-command  (prompt &optional initial-input history)
      "Read a string from the minibuffer, using `shell-command-history'."
      (read-from-minibuffer prompt initial-input nil nil
			    (or history 'shell-command-history))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Import types and help features

(defvar hol-light-with-caml-mode-p
  (condition-case nil
      (and (require 'caml-types) (require 'caml-help))
    (error nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                       User customizable variables

;; Use the standard `customize' interface or `hol-light-mode-hook' to
;; Configure these variables

(require 'custom)

(defgroup hol-light nil
  "Support for the Objective Caml language."
  :group 'languages)

;; Comments

(defcustom hol-light-indent-leading-comments t
  "*If true, indent leading comment lines (starting with `(*') like others."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-indent-comments t
  "*If true, automatically align multi-line comments."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-comment-end-extra-indent 0
  "*How many spaces to indent a leading comment end `*)'.
If you expect comments to be indented like
	(*
          ...
	 *)
even without leading `*', use `hol-light-comment-end-extra-indent' = 1."
  :group 'hol-light
  :type '(radio :extra-offset 8
		:format "%{Comment End Extra Indent%}:
   Comment alignment:\n%v"
		(const :tag "align with `(' in comment opening" 0)
		(const :tag "align with `*' in comment opening" 1)
		(integer :tag "custom alignment" 0)))

(defcustom hol-light-support-leading-star-comments t
  "*Enable automatic intentation of comments of the form
        (*
         * ...
         *)
Documentation comments (** *) are not concerned by this variable
unless `hol-light-leading-star-in-doc' is also set.

If you do not set this variable and still expect comments to be
indented like
	(*
          ...
	 *)
\(without leading `*'), set `hol-light-comment-end-extra-indent' to 1."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-leading-star-in-doc nil
  "*Enable automatic intentation of documentation comments of the form
        (**
         * ...
         *)"
  :group 'hol-light :type 'boolean)

;; Indentation defaults

(defcustom hol-light-default-indent 2
  "*Default indentation.

Global indentation variable (large values may lead to indentation overflows).
When no governing keyword is found, this value is used to indent the line
if it has to."
  :group 'hol-light :type 'integer)

(defcustom hol-light-lazy-paren nil
  "*If true, indent parentheses like a standard keyword."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-support-camllight nil
  "*If true, handle Caml Light character syntax (incompatible with labels)."
  :group 'hol-light :type 'boolean
  :set '(lambda (var val)
	  (setq hol-light-support-camllight val)
	  (if (boundp 'hol-light-mode-syntax-table)
	      (modify-syntax-entry ?` (if val "\"" ".")
				   hol-light-mode-syntax-table))))

(defcustom hol-light-support-metaocaml nil
  "*If true, handle MetaOCaml character syntax."
  :group 'hol-light :type 'boolean
  :set '(lambda (var val)
	  (setq hol-light-support-metaocaml val)
	  (if (boundp 'hol-light-font-lock-keywords)
	      (hol-light-install-font-lock))))

(defcustom hol-light-let-always-indent t
  "*If true, enforce indentation is at least `hol-light-let-indent' after a `let'.

As an example, set it to false when you have `hol-light-with-indent' set to 0,
and you want `let x = match ... with' and `match ... with' indent the
same way."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-|-extra-unindent hol-light-default-indent
  "*Extra backward indent for Caml lines starting with the `|' operator.

It is NOT the variable controlling the indentation of the `|' itself:
this value is automatically added to `function', `with', `parse' and
some cases of `type' keywords to leave enough space for `|' backward
indentation.

For exemple, setting this variable to 0 leads to the following indentation:
  match ... with
    X -> ...
    | Y -> ...
    | Z -> ...

To modify the indentation of lines lead by `|' you need to modify the
indentation variables for `with', `function' and `parse', and possibly
for `type' as well. For example, setting them to 0 (and leaving
`hol-light-|-extra-unindent' to its default value) yields:
  match ... with
    X -> ...
  | Y -> ...
  | Z -> ..."
  :group 'hol-light :type 'integer)

(defcustom hol-light-class-indent hol-light-default-indent
  "*How many spaces to indent from a `class' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-sig-struct-align t
  "*Align `sig' and `struct' keywords with `module'."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-sig-struct-indent hol-light-default-indent
  "*How many spaces to indent from a `sig' or `struct' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-method-indent hol-light-default-indent
  "*How many spaces to indent from a `method' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-begin-indent hol-light-default-indent
  "*How many spaces to indent from a `begin' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-for-while-indent hol-light-default-indent
  "*How many spaces to indent from a `for' or `while' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-do-indent hol-light-default-indent
  "*How many spaces to indent from a `do' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-fun-indent hol-light-default-indent
  "*How many spaces to indent from a `fun' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-function-indent hol-light-default-indent
  "*How many spaces to indent from a `function' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-if-then-else-indent hol-light-default-indent
  "*How many spaces to indent from an `if', `then' or `else' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-let-indent hol-light-default-indent
  "*How many spaces to indent from a `let' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-in-indent hol-light-default-indent
  "*How many spaces to indent from a `in' keyword.
A lot of people like formatting `let' ... `in' expressions whithout
indentation:
        let x = 0 in
        blah x
Set this variable to 0 to get this behaviour.
However, nested declarations are always correctly handled:
        let x = 0 in                             let x = 0
        let y = 0 in              or             in let y = 0
        let z = 0 ...                            in let z = 0 ..."
  :group 'hol-light :type 'integer)

(defcustom hol-light-match-indent hol-light-default-indent
  "*How many spaces to indent from a `match' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-try-indent hol-light-default-indent
  "*How many spaces to indent from a `try' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-with-indent hol-light-default-indent
  "*How many spaces to indent from a `with' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-rule-indent hol-light-default-indent
  "*How many spaces to indent from a `rule' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-parse-indent hol-light-default-indent
  "*How many spaces to indent from a `parse' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-parser-indent hol-light-default-indent
  "*How many spaces to indent from a `parser' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-type-indent hol-light-default-indent
  "*How many spaces to indent from a `type' keyword."
  :group 'hol-light :type 'integer)

(defcustom hol-light-val-indent hol-light-default-indent
  "*How many spaces to indent from a `val' keyword."
  :group 'hol-light :type 'integer)

;; Automatic indentation
;; Using abbrev-mode and electric keys

(defcustom hol-light-use-abbrev-mode t
  "*Non-nil means electrically indent lines starting with leading keywords.
Leading keywords are such as `end', `done', `else' etc.
It makes use of `abbrev-mode'.

Many people find eletric keywords irritating, so you can disable them by
setting this variable to nil."
  :group 'hol-light :type 'boolean
  :set '(lambda (var val)
	  (setq hol-light-use-abbrev-mode val)
	  (abbrev-mode val)))

(defcustom hol-light-electric-indent t
  "*Non-nil means electrically indent lines starting with `|', `)', `]' or `}'.

Many people find eletric keys irritating, so you can disable them in
setting this variable to nil."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-electric-close-vector t
  "*Non-nil means electrically insert `|' before a vector-closing `]' or
`>' before an object-closing `}'.

Many people find eletric keys irritating, so you can disable them in
setting this variable to nil. You should probably have this on,
though, if you also have `hol-light-electric-indent' on."
  :group 'hol-light :type 'boolean)

;; HOL Light-Interactive
;; Configure via `hol-light-mode-hook'

(defcustom hol-light-skip-after-eval-phrase t
  "*Non-nil means skip to the end of the phrase after evaluation in the
Caml toplevel."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-interactive-read-only-input nil
  "*Non-nil means input sent to the Caml toplevel is read-only."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-interactive-echo-phrase t
  "*Non-nil means echo phrases in the toplevel buffer when sending
them to the Caml toplevel."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-interactive-input-font-lock t
  "*Non nil means Font-Lock for toplevel input phrases."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-interactive-output-font-lock t
  "*Non nil means Font-Lock for toplevel output messages."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-interactive-error-font-lock t
  "*Non nil means Font-Lock for toplevel error messages."
  :group 'hol-light :type 'boolean)

(defcustom hol-light-display-buffer-on-eval t
  "*Non nil means pop up the Caml toplevel when evaluating code."
  :group 'hol-light :type 'boolean)

(setq local-doc '"/usr/share/doc/ocaml-doc/docs/ocaml.html/index.html")
(defcustom hol-light-manual-url
  (if (file-readable-p local-doc)
      (concat "file:" local-doc)
      "http://pauillac.inria.fr/ocaml/htmlman/index.html")
  "*URL to the Caml reference manual."
  :group 'hol-light :type 'string)

(defcustom hol-light-browser 'hol-light-netscape-manual
  "*Name of function that displays the Caml reference manual.
Valid names are `hol-light-netscape-manual', `hol-light-mmm-manual'
and `hol-light-xemacs-w3-manual' (XEmacs only)."
  :group 'hol-light)

(defcustom hol-light-library-path "/usr/lib/ocaml/"
  "*Path to the Caml library."
  :group 'hol-light :type 'string)

(defcustom hol-light-definitions-max-items 30
  "*Maximum number of items a definitions menu can contain."
  :group 'hol-light :type 'integer)

(defvar hol-light-options-list
  '(("Lazy parentheses indentation" . 'hol-light-lazy-paren)
    ("Force indentation after `let'" . 'hol-light-let-always-indent)
    "---"
    ("Automatic indentation of leading keywords" . 'hol-light-use-abbrev-mode)
    ("Electric indentation of ), ] and }" . 'hol-light-electric-indent)
    ("Electric matching of [| and {<" . 'hol-light-electric-close-vector)
    "---"
    ("Indent body of comments" . 'hol-light-indent-comments)
    ("Indent first line of comments" . 'hol-light-indent-leading-comments)
    ("Leading-`*' comment style" . 'hol-light-support-leading-star-comments))
  "*List of menu-configurable HOL Light options.")

(defvar hol-light-interactive-options-list
  '(("Skip phrase after evaluation" . 'hol-light-skip-after-eval-phrase)
    ("Echo phrase in interactive buffer" . 'hol-light-interactive-echo-phrase)
    "---"
    ("Font-lock interactive input" . 'hol-light-interactive-input-font-lock)
    ("Font-lock interactive output" . 'hol-light-interactive-output-font-lock)
    ("Font-lock interactive error" . 'hol-light-interactive-error-font-lock)
    "---"
    ("Read only input" . 'hol-light-interactive-read-only-input))
  "*List of menu-configurable HOL Light options.")

(defvar hol-light-interactive-program "hol_light"
  "*Default program name for invoking a Caml toplevel from Emacs.")
;; Could be interesting to have this variable buffer-local
;;   (e.g., ocaml vs. metaocaml buffers)
;; (make-variable-buffer-local 'hol-light-interactive-program)

;; Backtrack to custom parsing and caching by default, until stable
;;(defvar hol-light-use-syntax-ppss (fboundp 'syntax-ppss)
(defconst hol-light-use-syntax-ppss nil
  "*If nil, use our own parsing and caching.")

(defgroup hol-light-faces nil
  "Special faces for the HOL Light mode."
  :group 'hol-light)

(defconst hol-light-faces-inherit-p
  (if (boundp 'face-attribute-name-alist)
      (assq :inherit face-attribute-name-alist)))

(defface hol-light-font-lock-governing-face
  (if hol-light-faces-inherit-p
      '((t :inherit font-lock-keyword-face))
    '((((background light)) (:foreground "darkorange3" :bold t))
      (t (:foreground "orange" :bold t))))
  "Face description for governing/leading keywords."
  :group 'hol-light-faces)
(defvar hol-light-font-lock-governing-face
  'hol-light-font-lock-governing-face)

(defface hol-light-font-lock-multistage-face
  '((((background light))
     (:foreground "darkblue" :background "lightgray" :bold t))
    (t (:foreground "steelblue" :background "darkgray" :bold t)))
  "Face description for MetaOCaml staging operators."
  :group 'hol-light-faces)
(defvar hol-light-font-lock-multistage-face
  'hol-light-font-lock-multistage-face)

(defface hol-light-font-lock-operator-face
  (if hol-light-faces-inherit-p
      '((t :inherit font-lock-keyword-face))
    '((((background light)) (:foreground "brown"))
      (t (:foreground "khaki"))))
  "Face description for all operators."
  :group 'hol-light-faces)
(defvar hol-light-font-lock-operator-face
  'hol-light-font-lock-operator-face)

(defface hol-light-font-lock-error-face
  '((t (:foreground "yellow" :background "red" :bold t)))
  "Face description for all errors reported to the source."
  :group 'hol-light-faces)
(defvar hol-light-font-lock-error-face
  'hol-light-font-lock-error-face)

(defface hol-light-font-lock-interactive-output-face
  '((((background light))
     (:foreground "blue4"))
    (t (:foreground "cyan")))
  "Face description for all toplevel outputs."
  :group 'hol-light-faces)
(defvar hol-light-font-lock-interactive-output-face
  'hol-light-font-lock-interactive-output-face)

(defface hol-light-font-lock-interactive-error-face
  (if hol-light-faces-inherit-p
      '((t :inherit font-lock-warning-face))
    '((((background light)) (:foreground "red3"))
      (t (:foreground "red2"))))
  "Face description for all toplevel errors."
  :group 'hol-light-faces)
(defvar hol-light-font-lock-interactive-error-face
  'hol-light-font-lock-interactive-error-face)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            Support definitions

(defun hol-light-leading-star-p ()
  (and hol-light-support-leading-star-comments
       (save-excursion ; this function does not make sense outside of a comment
	 (hol-light-beginning-of-literal-or-comment)
	 (and (or hol-light-leading-star-in-doc
		  (not (looking-at "(\\*[Tt][Ee][Xx]\\|(\\*\\*")))
	      (progn
		(forward-line 1)
		(back-to-indentation)
		(looking-at "\\*[^)]"))))))

(defun hol-light-auto-fill-insert-leading-star (&optional leading-star)
  (let ((point-leading-comment (looking-at "(\\*")) (return-leading nil))
    (save-excursion
      (back-to-indentation)
      (if hol-light-electric-indent
	  (progn
	    (if (and (hol-light-in-comment-p)
		     (or leading-star
			 (hol-light-leading-star-p)))
		(progn
		  (if (not (looking-at "(?\\*"))
		      (insert-before-markers "* "))
		  (setq return-leading t)))
	    (if (not point-leading-comment)
		;; Use optional argument to break recursion
		(hol-light-indent-command t)))))
    return-leading))

(defun hol-light-auto-fill-function ()
  (if (hol-light-in-literal-p) ()
    (let ((leading-star
	   (if (not (char-equal ?\n last-command-char))
	       (hol-light-auto-fill-insert-leading-star)
	     nil)))
      (do-auto-fill)
      (if (not (char-equal ?\n last-command-char))
	  (hol-light-auto-fill-insert-leading-star leading-star)))))

(defun hol-light-forward-char (&optional step)
  (if step (goto-char (+ (point) step))
    (goto-char (1+ (point)))))

(defun hol-light-backward-char (&optional step)
  (if step (goto-char (- (point) step))
    (goto-char (1- (point)))))

(defun hol-light-in-indentation-p ()
  "Return non-nil if all chars between beginning of line and point are blanks."
  (save-excursion
    (skip-chars-backward " \t")
    (bolp)))

(defvar hol-light-cache-stop (point-min))
(make-variable-buffer-local 'hol-light-cache-stop)
(defvar hol-light-cache nil)
(make-variable-buffer-local 'hol-light-cache)
(defvar hol-light-cache-local nil)
(make-variable-buffer-local 'hol-light-cache-local)
(defvar hol-light-cache-last-local nil)
(make-variable-buffer-local 'hol-light-cache-last-local)
(defvar hol-light-last-loc (cons nil nil))
  
(if hol-light-use-syntax-ppss
    (progn
      (defun hol-light-in-literal-p ()
	"Returns non-nil if point is inside a Caml literal."
	(nth 3 (syntax-ppss)))
      (defun hol-light-in-comment-p ()
	"Returns non-nil if point is inside a Caml comment."
	(nth 4 (syntax-ppss)))
      (defun hol-light-in-literal-or-comment-p ()
	"Returns non-nil if point is inside a Caml literal or comment."
	(nth 8 (syntax-ppss)))
      (defun hol-light-beginning-of-literal-or-comment ()
	"Skips to the beginning of the current literal or comment (or buffer)."
	(interactive)
	(goto-char (or (nth 8 (syntax-ppss)) (point))))
      (defun hol-light-beginning-of-literal-or-comment-fast ()
	(goto-char (or (nth 8 (syntax-ppss)) (point-min))))
      ;; FIXME: not clear if moving out of a string/comment counts as 1 or no.
      (defalias 'hol-light-backward-up-list 'backward-up-list))

  (defun hol-light-before-change-function (begin end)
    (setq hol-light-cache-stop
	  (if (save-excursion (beginning-of-line) (= (point) (point-min)))
	      (point-min)
	    (min hol-light-cache-stop (1- begin)))))
  
  (defun hol-light-in-literal-p ()
    "Return non-nil if point is inside a Caml literal."
    (car (hol-light-in-literal-or-comment)))
  (defun hol-light-in-comment-p ()
    "Return non-nil if point is inside a Caml comment."
    (cdr (hol-light-in-literal-or-comment)))
  (defun hol-light-in-literal-or-comment-p ()
    "Return non-nil if point is inside a Caml literal or comment."
    (hol-light-in-literal-or-comment)
    (or (car hol-light-last-loc) (cdr hol-light-last-loc)))
  (defun hol-light-in-literal-or-comment ()
    "Return the pair `((hol-light-in-literal-p) . (hol-light-in-comment-p))'."
    (if (and (<= (point) hol-light-cache-stop) hol-light-cache)
	(progn
	  (if (or (not hol-light-cache-local) (not hol-light-cache-last-local)
		  (and (>= (point) (caar hol-light-cache-last-local))))
	      (setq hol-light-cache-local hol-light-cache))
	  (while (and hol-light-cache-local (< (point) (caar hol-light-cache-local)))
	    (setq hol-light-cache-last-local hol-light-cache-local
		  hol-light-cache-local (cdr hol-light-cache-local)))
	  (setq hol-light-last-loc
		(if hol-light-cache-local
		    (cons (eq (cadar hol-light-cache-local) 'b)
			  (> (cddar hol-light-cache-local) 0))
		  (cons nil nil))))
      (let ((flag t) (op (point)) (mp (min (point) (1- (point-max))))
	    (balance 0) (end-of-comment nil))
	(while (and hol-light-cache (<= hol-light-cache-stop (caar hol-light-cache)))
	  (setq hol-light-cache (cdr hol-light-cache)))
	(if hol-light-cache
	    (if (eq (cadar hol-light-cache) 'b)
		(progn
		  (setq hol-light-cache-stop (1- (caar hol-light-cache)))
		  (goto-char hol-light-cache-stop)
		  (setq balance (cddar hol-light-cache))
		  (setq hol-light-cache (cdr hol-light-cache)))
	      (setq balance (cddar hol-light-cache))
	      (setq hol-light-cache-stop (caar hol-light-cache))
	      (goto-char hol-light-cache-stop)
	      (skip-chars-forward "("))
	  (goto-char (point-min)))
	(skip-chars-backward "\\\\*")
	(while flag
	  (if end-of-comment (setq balance 0 end-of-comment nil))
	  (skip-chars-forward "^\\\\'`\"(\\*")
	  (cond
	   ((looking-at "\\\\")
	    (hol-light-forward-char 2))
	   ((looking-at "'\\([^\n\\']\\|\\\\[^ \t\n][^ \t\n]?[^ \t\n]?\\)'")
	    (setq hol-light-cache (cons (cons (1+ (point)) (cons 'b balance))
				     hol-light-cache))
	    (goto-char (match-end 0))
	    (setq hol-light-cache (cons (cons (point) (cons 'e balance))
				     hol-light-cache)))
	   ((and
	     hol-light-support-camllight
	     (looking-at "`\\([^\n\\']\\|\\\\[^ \t\n][^ \t\n]?[^ \t\n]?\\)`"))
	    (setq hol-light-cache (cons (cons (1+ (point)) (cons 'b balance))
				     hol-light-cache))
	    (goto-char (match-end 0))
	    (setq hol-light-cache (cons (cons (point) (cons 'e balance))
				     hol-light-cache)))
	   ((looking-at "\"")
	    (hol-light-forward-char)
	    (setq hol-light-cache (cons (cons (point) (cons 'b balance))
				     hol-light-cache))
	    (skip-chars-forward "^\\\\\"")
	    (while (looking-at "\\\\")
	      (hol-light-forward-char 2) (skip-chars-forward "^\\\\\""))
	    (hol-light-forward-char)
	    (setq hol-light-cache (cons (cons (point) (cons 'e balance))
				     hol-light-cache)))
	   ((looking-at "(\\*")
	    (setq balance (1+ balance))
	    (setq hol-light-cache (cons (cons (point) (cons nil balance))
				     hol-light-cache))
	    (hol-light-forward-char 2))
	   ((looking-at "\\*)")
	    (hol-light-forward-char 2)
	    (if (> balance 1)
		(progn
		  (setq balance (1- balance))
		  (setq hol-light-cache (cons (cons (point) (cons nil balance))
					   hol-light-cache)))
	      (setq end-of-comment t)
	      (setq hol-light-cache (cons (cons (point) (cons nil 0))
				       hol-light-cache))))
	   (t (hol-light-forward-char)))
	  (setq flag (<= (point) mp)))
	(setq hol-light-cache-local hol-light-cache
	      hol-light-cache-stop (point))
	(goto-char op)
	(if hol-light-cache (hol-light-in-literal-or-comment) 
	  (setq hol-light-last-loc (cons nil nil))
	  hol-light-last-loc))))
  
  (defun hol-light-beginning-of-literal-or-comment ()
    "Skips to the beginning of the current literal or comment (or buffer)."
    (interactive)
    (if (hol-light-in-literal-or-comment-p)
	(hol-light-beginning-of-literal-or-comment-fast)))
  
  (defun hol-light-beginning-of-literal-or-comment-fast ()
    (while (and hol-light-cache-local
		(or (eq 'b (cadar hol-light-cache-local))
		    (> (cddar hol-light-cache-local) 0)))
      (setq hol-light-cache-last-local hol-light-cache-local
	    hol-light-cache-local (cdr hol-light-cache-local)))
    (if hol-light-cache-last-local
	(goto-char (caar hol-light-cache-last-local))
      (goto-char (point-min)))
    (if (eq 'b (cadar hol-light-cache-last-local)) (hol-light-backward-char)))
  
  (defun hol-light-backward-up-list ()
    "Safe up-list regarding comments, literals and errors."
    (let ((balance 1) (op (point)) (oc nil))
      (hol-light-in-literal-or-comment)
      (while (and (> (point) (point-min)) (> balance 0))
	(setq oc (if hol-light-cache-local (caar hol-light-cache-local) (point-min)))
	(condition-case nil (up-list -1) (error (goto-char (point-min))))
	(if (>= (point) oc) (setq balance (1- balance))
	  (goto-char op)
	  (skip-chars-backward "^[]{}()") (hol-light-backward-char)
	  (if (not (hol-light-in-literal-or-comment-p))
	      (cond
	       ((looking-at "[[{(]")
		(setq balance (1- balance)))
	       ((looking-at "[]})]")
		(setq balance (1+ balance))))
	    (hol-light-beginning-of-literal-or-comment-fast)))
	(setq op (point)))))) ;; End of (if hol-light-use-syntax-ppss

(defun hol-light-false-=-p ()
  "Is the underlying `=' the first/second letter of an operator?"
  (or (memq (preceding-char) '(?: ?> ?< ?=))
      (char-equal ?= (char-after (1+ (point))))))

(defun hol-light-at-phrase-break-p ()
  "Is the underlying `;' a phrase break?"
  (and (char-equal ?\; (following-char))
       (or (and (not (eobp))
		(char-equal ?\; (char-after (1+ (point)))))
	   (char-equal ?\; (preceding-char)))))

(defun hol-light-assoc-indent (kwop &optional look-for-let-or-and)
  "Return relative indentation of the keyword given in argument."
  (let ((ind (symbol-value (cdr (assoc kwop hol-light-keyword-alist))))
	(looking-let-or-and (and look-for-let-or-and
				 (looking-at "\\<\\(let\\|and\\)\\>"))))
    (if (string-match "\\<\\(with\\|function\\|parser?\\)\\>" kwop)
	(+ (if (and hol-light-let-always-indent
		    looking-let-or-and (< ind hol-light-let-indent))
	       hol-light-let-indent ind)
	   hol-light-|-extra-unindent)
      ind)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                           Sym-lock in Emacs

;; By Stefan Monnier

(defcustom hol-light-font-lock-symbols nil
  "Display fun and -> and such using symbols in fonts.
This may sound like a neat trick, but note that it can change the
alignment and can thus lead to surprises."
  :type 'bool)

(defvar hol-light-font-lock-symbols-alist
  (append
   ;; The symbols can come from a JIS0208 font.
   (and (fboundp 'make-char) (fboundp 'charsetp) (charsetp 'japanese-jisx0208)
	(list (cons "fun" (make-char 'japanese-jisx0208 38 75))
	      (cons "sqrt" (make-char 'japanese-jisx0208 34 101))
	      (cons "not" (make-char 'japanese-jisx0208 34 76))
	      (cons "or" (make-char 'japanese-jisx0208 34 75))
	      (cons "||" (make-char 'japanese-jisx0208 34 75))
	      (cons "&&" (make-char 'japanese-jisx0208 34 74))
	      ;; (cons "*." (make-char 'japanese-jisx0208 33 95))
	      ;; (cons "/." (make-char 'japanese-jisx0208 33 96))
	      (cons "->" (make-char 'japanese-jisx0208 34 42))
	      (cons "=>" (make-char 'japanese-jisx0208 34 77))
	      (cons "<-" (make-char 'japanese-jisx0208 34 43))
	      (cons "<>" (make-char 'japanese-jisx0208 33 98))
	      (cons "==" (make-char 'japanese-jisx0208 34 97))
	      (cons ">=" (make-char 'japanese-jisx0208 33 102))
	      (cons "<=" (make-char 'japanese-jisx0208 33 101))
	      ;; Some greek letters for type parameters.
	      (cons "'a" (make-char 'japanese-jisx0208 38 65))
	      (cons "'b" (make-char 'japanese-jisx0208 38 66))
	      (cons "'c" (make-char 'japanese-jisx0208 38 67))
	      (cons "'d" (make-char 'japanese-jisx0208 38 68))))
   ;; Or a unicode font.
   (and (fboundp 'decode-char)
	(list (cons "fun" (decode-char 'ucs 955))
	      (cons "sqrt" (decode-char 'ucs 8730))
	      (cons "not" (decode-char 'ucs 172))
	      (cons "or" (decode-char 'ucs 8897))
	      (cons "&&" (decode-char 'ucs 8896))
	      (cons "||" (decode-char 'ucs 8897))
	      ;; (cons "*." (decode-char 'ucs 215))
	      ;; (cons "/." (decode-char 'ucs 247))
	      (cons "->" (decode-char 'ucs 8594))
	      (cons "<-" (decode-char 'ucs 8592))
	      (cons "<=" (decode-char 'ucs 8804))
	      (cons ">=" (decode-char 'ucs 8805))
	      (cons "<>" (decode-char 'ucs 8800))
	      (cons "==" (decode-char 'ucs 8801))
	      ;; Some greek letters for type parameters.
	      (cons "'a" (decode-char 'ucs 945))
	      (cons "'b" (decode-char 'ucs 946))
	      (cons "'c" (decode-char 'ucs 947))
	      (cons "'d" (decode-char 'ucs 948))
	      ))))

(defun hol-light-font-lock-compose-symbol (alist)
  "Compose a sequence of ascii chars into a symbol.
Regexp match data 0 points to the chars."
  ;; Check that the chars should really be composed into a symbol.
  (let* ((start (match-beginning 0))
	 (end (match-end 0))
	 (syntaxes (if (eq (char-syntax (char-after start)) ?w)
		       '(?w) '(?. ?\\))))
    (if (or (memq (char-syntax (or (char-before start) ?\ )) syntaxes)
	    (memq (char-syntax (or (char-after end) ?\ )) syntaxes)
	    (memq (get-text-property start 'face)
		  '(hol-light-doc-face font-lock-string-face
		    font-lock-comment-face)))
	;; No composition for you. Let's actually remove any composition
	;; we may have added earlier and which is now incorrect.
	(remove-text-properties start end '(composition))
      ;; That's a symbol alright, so add the composition.
      (compose-region start end (cdr (assoc (match-string 0) alist)))))
  ;; Return nil because we're not adding any face property.
  nil)

(defun hol-light-font-lock-symbols-keywords ()
  (when (fboundp 'compose-region)
    (let ((alist nil))
      (dolist (x hol-light-font-lock-symbols-alist)
	(when (and (if (fboundp 'char-displayable-p)
		       (char-displayable-p (cdr x))
		     t)
		   (not (assoc (car x) alist)))	;Not yet in alist.
	  (push x alist)))
      (when alist
	`((,(regexp-opt (mapcar 'car alist) t)
	   (0 (hol-light-font-lock-compose-symbol ',alist))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  Font-Lock

(unless hol-light-use-syntax-ppss

(defun hol-light-fontify-buffer ()
  (font-lock-default-fontify-buffer)
  (hol-light-fontify (point-min) (point-max)))

(defun hol-light-fontify-region (begin end &optional verbose)
  (font-lock-default-fontify-region begin end verbose)
  (hol-light-fontify begin end))

(defun hol-light-fontify (begin end)
  (if (eq major-mode 'hol-light-mode)
      (save-excursion
	(let ((modified (buffer-modified-p))) ; Emacs hack (see below)
	  (goto-char begin)
	  (beginning-of-line)
	  (setq begin (point))
	  (goto-char (1- end))
	  (end-of-line)
	  ;; Dirty hack to trick `font-lock-default-unfontify-region'
	  (if (not hol-light-with-xemacs) (forward-line 2))
	  (setq end (point))
	  (while (> end begin)
	    (goto-char (1- end))
	    (hol-light-in-literal-or-comment)
	    (cond
	     ((cdr hol-light-last-loc)
	      (hol-light-beginning-of-literal-or-comment)
	      (put-text-property (max begin (point)) end 'face
				 (if (looking-at
				      "(\\*[Tt][Ee][Xx]\\|(\\*\\*[^*]")
				     hol-light-doc-face
				   'font-lock-comment-face))
	      (setq end (1- (point))))
	     ((car hol-light-last-loc)
	      (hol-light-beginning-of-literal-or-comment)
	      (put-text-property (max begin (point)) end 'face
				 'font-lock-string-face)
	      (setq end (point)))
	     (t (while (and hol-light-cache-local
			    (or (> (caar hol-light-cache-local) end)
				(eq 'b (cadar hol-light-cache-local))))
		  (setq hol-light-cache-local (cdr hol-light-cache-local)))
		(setq end (if hol-light-cache-local
			      (caar hol-light-cache-local) begin)))))
	  (if (not (or hol-light-with-xemacs modified)) ; properties taken
	      (set-buffer-modified-p nil))))))       ; too seriously...

;; XEmacs and Emacs have different documentation faces...
(defvar hol-light-doc-face (if (facep 'font-lock-doc-face)
			    'font-lock-doc-face
			  'font-lock-doc-string-face))

) ;; End of (unless hol-light-use-syntax-ppss
  
;; By Stefan Monnier: redesigned font-lock installation and use char classes

;; When char classes are not available, character ranges only span
;; ASCII characters for MULE compatibility
(defconst hol-light-use-char-classes (string-match "[[:alpha:]]" "x"))
(defconst hol-light-lower (if hol-light-use-char-classes "[:lower:]" "a-z"))
(defconst hol-light-alpha (if hol-light-use-char-classes "[:alpha:]" "a-zA-Z"))

(defconst hol-light-font-lock-syntactic-keywords
  ;; Char constants start with ' but ' can also appear in identifiers.
  ;; Beware not to match things like '*)hel' or '"hel' since the first '
  ;; might be inside a string or comment.
  '(("\\<\\('\\)\\([^'\\\n]\\|\\\\.[^\\'\n \")]*\\)\\('\\)"
     (1 '(7)) (3 '(7)))))

(defun hol-light-font-lock-syntactic-face-function (state)
  (if (nth 3 state) font-lock-string-face
    (let ((start (nth 8 state)))
      (if (and (> (point-max) (+ start 2))
	       (eq (char-after (+ start 2)) ?*)
	       (not (eq (char-after (+ start 3)) ?*)))
	  ;; This is a documentation comment
	  hol-light-doc-face
	font-lock-comment-face))))

(when (facep 'font-lock-reference-face)
  (defvar font-lock-constant-face)
  (if (facep 'font-lock-constant-face) ()
    (defvar font-lock-constant-face font-lock-reference-face)
    (copy-face font-lock-reference-face 'font-lock-constant-face)))
(when (facep 'font-lock-keyword-face)
  (defvar font-lock-preprocessor-face)
  (if (facep 'font-lock-preprocessor-face) ()
    (defvar font-lock-preprocessor-face font-lock-keyword-face)
    (copy-face font-lock-keyword-face 'font-lock-preprocessor-face)))

;; Initially empty, set in `hol-light-install-font-lock'
(defvar hol-light-font-lock-keywords
  ()
  "Font-Lock patterns for HOL Light mode.")

(when (featurep 'sym-lock)
  (make-face 'hol-light-font-lock-lambda-face
	     "Face description for fun keywords (lambda operator).")
  (set-face-parent 'hol-light-font-lock-lambda-face
		   font-lock-function-name-face)
  (set-face-font 'hol-light-font-lock-lambda-face
		 sym-lock-font-name)
  
  ;; To change this table, xfd -fn '-adobe-symbol-*--12-*' may be
  ;; used to determine the symbol character codes.
  (defvar hol-light-sym-lock-keywords
    '(("<-" 0 1 172 nil)
      ("->" 0 1 174 nil)
      ("<=" 0 1 163 nil)
      (">=" 0 1 179 nil)
      ("<>" 0 1 185 nil)
      ("==" 0 1 186 nil)
      ("||" 0 1 218 nil)
      ("&&" 0 1 217 nil)
      ("[^*]\\(\\*\\)\\." 1 8 180 nil)
      ("\\(/\\)\\." 1 3 184 nil)
      (";;" 0 1 191 nil)
      ("\\<sqrt\\>" 0 3 214 nil)
      ("\\<fun\\>" 0 3 108 hol-light-font-lock-lambda-face)
      ("\\<or\\>" 0 3 218 nil)
      ("\\<not\\>" 0 3 216 nil))
    "If non nil: Overrides default Sym-Lock patterns for HOL Light."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                    Keymap

(defvar hol-light-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "|" 'hol-light-electric)
    (define-key map ")" 'hol-light-electric-rp)
    (define-key map "}" 'hol-light-electric-rc)
    (define-key map "]" 'hol-light-electric-rb)
    (define-key map "\M-q" 'hol-light-indent-phrase)
    (define-key map "\C-c\C-q" 'hol-light-indent-phrase)
    (define-key map "\M-\C-\\" 'indent-region)
    (define-key map "\C-c\C-a" 'hol-light-find-alternate-file)
    (define-key map "\C-c\C-c" 'compile)
    (define-key map "\C-xnd" 'hol-light-narrow-to-phrase)
    (define-key map "\M-\C-x" 'hol-light-eval-phrase)
    (define-key map "\C-x\C-e" 'hol-light-eval-phrase)
    (define-key map "\C-c\C-e" 'hol-light-eval-phrase)
    (define-key map "\C-c\C-r" 'hol-light-eval-region)
    (define-key map "\C-c\C-b" 'hol-light-eval-buffer)
    (define-key map "\C-c\C-s" 'hol-light-run-caml)
    (define-key map "\C-c\C-i" 'hol-light-interrupt-caml)
    (define-key map "\C-c\C-k" 'hol-light-kill-caml)
    (define-key map "\C-c\C-n" 'hol-light-next-phrase)
    (define-key map "\C-c\C-p" 'hol-light-previous-phrase)
    (define-key map [(control c) (home)] 'hol-light-move-inside-block-opening)
    (define-key map [(control c) (control down)] 'hol-light-next-phrase)
    (define-key map [(control c) (control up)] 'hol-light-previous-phrase)
    (define-key map [(meta control down)]  'hol-light-next-phrase)
    (define-key map [(meta control up)] 'hol-light-previous-phrase)
    (define-key map [(meta control h)] 'hol-light-mark-phrase)
    (define-key map "\C-c`" 'hol-light-interactive-next-error-source)
    (define-key map "\C-c?" 'hol-light-interactive-next-error-source)
    (define-key map "\C-c.c" 'hol-light-insert-class-form)
    (define-key map "\C-c.b" 'hol-light-insert-begin-form)
    (define-key map "\C-c.f" 'hol-light-insert-for-form)
    (define-key map "\C-c.w" 'hol-light-insert-while-form)
    (define-key map "\C-c.i" 'hol-light-insert-if-form)
    (define-key map "\C-c.l" 'hol-light-insert-let-form)
    (define-key map "\C-c.m" 'hol-light-insert-match-form)
    (define-key map "\C-c.t" 'hol-light-insert-try-form)
    (when hol-light-with-caml-mode-p
      ;; Trigger caml-types
      (define-key map [?\C-c ?\C-t] 'caml-types-show-type)
      ;; To prevent misbehavior in case of error during exploration.
      (define-key map [(control mouse-2)] 'caml-types-mouse-ignore)
      (define-key map [(control down-mouse-2)] 'caml-types-explore)
      ;; Trigger caml-help
      (define-key map [?\C-c ?i] 'ocaml-add-path)
      (define-key map [?\C-c ?\[] 'ocaml-open-module)
      (define-key map [?\C-c ?\]] 'ocaml-close-module)
      (define-key map [?\C-c ?h] 'caml-help)
      (define-key map [?\C-c ?\t] 'caml-complete))
    map)
  "Keymap used in HOL Light mode.")
  
(defvar hol-light-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?? ". p" st)
    (modify-syntax-entry ?~ ". p" st)
    (modify-syntax-entry ?: "." st)
    (modify-syntax-entry ?' "w" st)	; ' is part of words (for primes).
    (modify-syntax-entry
     ;; ` is punctuation or character delimiter (Caml Light compatibility).
     ?` (if hol-light-support-camllight "\"" ".") st)
    (modify-syntax-entry ?\" "\"" st)	; " is a string delimiter
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?*  ". 23" st)
    (condition-case nil
	(progn
	  (modify-syntax-entry ?\( "()1n" st)
	  (modify-syntax-entry ?\) ")(4n" st))
      (error		   ;XEmacs signals an error instead of ignoring `n'.
       (modify-syntax-entry ?\( "()1" st)
       (modify-syntax-entry ?\) ")(4" st)))
    st)
  "Syntax table in use in HOL Light mode buffers.")

(defconst hol-light-font-lock-syntax
  `((?_ . "w") (?` . ".")
    ,@(unless hol-light-use-syntax-ppss
	'((?\" . ".") (?\( . ".") (?\) . ".") (?* . "."))))
  "Syntax changes for Font-Lock.")

(defvar hol-light-mode-abbrev-table ()
  "Abbrev table used for HOL Light mode buffers.")
(defun hol-light-define-abbrev (keyword)
  (define-abbrev hol-light-mode-abbrev-table keyword keyword 'hol-light-abbrev-hook))
(if hol-light-mode-abbrev-table ()
  (setq hol-light-mode-abbrev-table (make-abbrev-table))
  (mapcar 'hol-light-define-abbrev
	  '("module" "class" "functor" "object" "type" "val" "inherit"
	    "include" "virtual" "constraint" "exception" "external" "open"
	    "method" "and" "initializer" "to" "downto" "do" "done" "else"
	    "begin" "end" "let" "in" "then" "with"))
  (setq abbrevs-changed nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                              The major mode

;;;###autoload (add-to-list 'auto-mode-alist '("\\.ml[ily]?\\'" . hol-light-mode))

;;;###autoload
(defun hol-light-mode ()
  "Major mode for editing Caml code.

Dedicated to Emacs and XEmacs, version 21 and higher. Provides
automatic indentation and compilation interface. Performs font/color
highlighting using Font-Lock. It is designed for Objective Caml but
handles Objective Labl and Caml Light as well.

Report bugs, remarks and questions to Albert.Cohen@prism.uvsq.fr.

The Font-Lock minor-mode is used according to your customization
options. Within XEmacs (non-MULE versions only) you may also want to
use Sym-Lock:

\(if (and (boundp 'window-system) window-system)
    (when (string-match \"XEmacs\" emacs-version)
       	(if (not (and (boundp 'mule-x-win-initted) mule-x-win-initted))
            (require 'sym-lock))
       	(require 'font-lock)))

You have better byte-compile hol-light.el (and sym-lock.el if you use it)
because symbol highlighting is very time consuming.

For customization purposes, you should use `hol-light-mode-hook'
\(run for every file) or `hol-light-load-hook' (run once) and not patch
the mode itself. You should add to your configuration file something like:
  (add-hook 'hol-light-mode-hook
            (lambda ()
               ... ; your customization code
            ))
For example you can change the indentation of some keywords, the
`electric' flags, Font-Lock colors... Every customizable variable is
documented, use `C-h-v' or look at the mode's source code.

A special case is Sym-Lock customization: You may set
`hol-light-sym-lock-keywords' in your `.emacs' configuration file
to override default Sym-Lock patterns.

`custom-hol-light.el' is a sample customization file for standard changes.
You can append it to your `.emacs' or use it as a tutorial.

`M-x camldebug' FILE starts the Caml debugger camldebug on the executable
FILE, with input and output in an Emacs buffer named *camldebug-FILE*.

A HOL Light Interactive Mode to evaluate expressions in a toplevel is included.
Type `M-x hol-light-run-caml' or see special-keys below.

Some elementary rules have to be followed in order to get the best of
indentation facilities.
  - Because the `function' keyword has a special indentation (to handle
    case matches) use the `fun' keyword when no case match is performed.
  - In OCaml, `;;' is no longer necessary for correct indentation,
    except before top level phrases not introduced by `type', `val', `let'
    etc. (i.e., phrases used for their side-effects or to be executed
    in a top level.)
  - Long sequences of `and's may slow down indentation slightly, since
    some computations (few) require to go back to the beginning of the
    sequence. Some very long nested blocks may also lead to slow
    processing of `end's, `else's, `done's...
  - Multiline strings are handled properly, but the string concatenation `^'
    is preferred to break long strings (the C-j keystroke can help).

Known bugs:
  - When writting a line with mixed code and comments, avoid putting
    comments at the beginning or middle of the text. More precisely, 
    writing comments immediately after `=' or parentheses then writing
    some more code on the line leads to indentation errors. You may write
    `let x (* blah *) = blah' but should avoid `let x = (* blah *) blah'.

Special keys for HOL Light mode:\\{hol-light-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'hol-light-mode)
  (setq mode-name "HOL Light")
  (use-local-map hol-light-mode-map)
  (set-syntax-table hol-light-mode-syntax-table)
  (setq local-abbrev-table hol-light-mode-abbrev-table)

  (hol-light-build-menu)

  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^[ \t]*$\\|\\*)$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline t)
  (make-local-variable 'comment-start)
  (setq comment-start "(* ")
  (make-local-variable 'comment-end)
  (setq comment-end " *)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+[ \t]*")
  (make-local-variable 'comment-multi-line)
  (setq comment-multi-line t)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'hol-light-indent-command)
  (unless hol-light-use-syntax-ppss
    (make-local-hook 'before-change-functions)
    (add-hook 'before-change-functions 'hol-light-before-change-function nil t))
  (make-local-variable 'normal-auto-fill-function)
  (setq normal-auto-fill-function 'hol-light-auto-fill-function)
	 
  ;; Hooks for hol-light-mode, use them for hol-light-mode configuration
  (hol-light-install-font-lock)
  (run-hooks 'hol-light-mode-hook)
  (if hol-light-use-abbrev-mode (abbrev-mode 1))
  (message
   (concat "Major mode for editing and running Caml programs, "
	   hol-light-mode-version ".")))

(defun hol-light-install-font-lock (&optional no-sym-lock)
  (setq
   hol-light-font-lock-keywords
   (append
    (list
     (list "\\<\\(external\\|open\\|include\\|rule\\|s\\(ig\\|truct\\)\\|module\\|functor\\|with[ \t\n]+\\(type\\|module\\)\\|val\\|type\\|method\\|virtual\\|constraint\\|class\\|in\\|inherit\\|initializer\\|let\\|rec\\|and\\|begin\\|object\\|end\\)\\>"
	   0 'hol-light-font-lock-governing-face nil nil))
    (if hol-light-support-metaocaml
	(list (list "\\.<\\|>\\.\\|\\.~\\|\\.!"
		    0 'hol-light-font-lock-multistage-face nil nil))
      ())
    (list
     (list "\\<\\(false\\|true\\)\\>"
	   0 'font-lock-constant-face nil nil)
     (list "\\<\\(as\\|do\\(ne\\|wnto\\)?\\|else\\|for\\|if\\|m\\(atch\\|utable\\)\\|new\\|p\\(arser\\|rivate\\)\\|t\\(hen\\|o\\|ry\\)\\|w\\(h\\(en\\|ile\\)\\|ith\\)\\|lazy\\|exception\\|raise\\|failwith\\|exit\\|assert\\|fun\\(ction\\)?\\)\\>"
	   0 'font-lock-keyword-face nil nil)
     (list "[][;,()|{}]\\|[@^!:*=<>&/%+~?#---]\\.?\\|\\.\\.\\.*\\|\\<\\(asr\\|asl\\|lsr\\|lsl\\|l?or\\|l?and\\|xor\\|not\\|mod\\|of\\|ref\\)\\>"
	   0 'hol-light-font-lock-operator-face nil nil)
     (list (concat "\\<\\(\\(method\\([ \t\n]+\\(private\\|virtual\\)\\)?\\)\\([ \t\n]+virtual\\)?\\|val\\([ \t\n]+mutable\\)?\\|external\\|and\\|class\\|let\\([ \t\n]+rec\\)?\\)\\>[ \t\n]*\\(['_" hol-light-lower "]\\(\\w\\|[._]\\)*\\)\\>[ \t\n]*\\(\\(\\w\\|[()_?~.'*:--->]\\)+\\|=[ \t\n]*fun\\(ction\\)?\\>\\)")
	   8 'font-lock-function-name-face 'keep nil)
     (list "\\<method\\([ \t\n]+\\(private\\|virtual\\)\\)?\\>[ \t\n]*\\(\\(\\w\\|[_,?~.]\\)*\\)"
	   3 'font-lock-function-name-face 'keep nil)
     (list "\\<\\(fun\\(ction\\)?\\)\\>[ \t\n]*\\(\\(\\w\\|[_ \t()*,]\\)+\\)"
	   3 'font-lock-variable-name-face 'keep nil)
     (list "\\<\\(val\\([ \t\n]+mutable\\)?\\|external\\|and\\|class\\|let\\([ \t\n]+rec\\)?\\)\\>[ \t\n]*\\(\\(\\w\\|[_,?~.]\\)*\\)"
	   4 'font-lock-variable-name-face 'keep nil)
     (list "\\<\\(val\\([ \t\n]+mutable\\)?\\|external\\|method\\|and\\|class\\|let\\([ \t\n]+rec\\)?\\)\\>[ \t\n]*\\(\\(\\w\\|[_,?~.]\\)*\\)\\>\\(\\(\\w\\|[->_ \t,?~.]\\|(\\(\\w\\|[--->_ \t,?~.=]\\)*)\\)*\\)"
	   6 'font-lock-variable-name-face 'keep nil)
     (list "\\<\\(open\\|\\(class\\([ \t\n]+type\\)?\\)\\([ \t\n]+virtual\\)?\\|inherit\\|include\\|module\\([ \t\n]+\\(type\\|rec\\)\\)?\\|type\\)\\>[ \t\n]*\\(['~?]*\\([_--->.* \t]\\|\\w\\|(['~?]*\\([_--->.,* \t]\\|\\w\\)*)\\)*\\)"
	   7 'font-lock-type-face 'keep nil)
     (list "[^:>=]:[ \t\n]*\\(['~?]*\\([_--->.* \t]\\|\\w\\|(['~?]*\\([_--->.,* \t]\\|\\w\\)*)\\)*\\)"
	   1 'font-lock-type-face 'keep nil)
     (list "\\<\\([A-Z]\\w*\\>\\)[ \t]*\\."
	   1 'font-lock-type-face 'keep nil)
     (list (concat "\\<\\([?~]?[_" hol-light-alpha "]\\w*\\)[ \t\n]*:[^:>=]")
	   1 'font-lock-variable-name-face 'keep nil)
     (list (concat "\\<exception\\>[ \t\n]*\\(\\<[_" hol-light-alpha "]\\w*\\>\\)")
	   1 'font-lock-variable-name-face 'keep nil)
     (list "^#\\w+\\>"
	   0 'font-lock-preprocessor-face t nil))
    (if hol-light-font-lock-symbols
	(hol-light-font-lock-symbols-keywords)
      ())))
  (if (and (not no-sym-lock)
	   (featurep 'sym-lock))
      (progn
	(setq sym-lock-color
	      (face-foreground 'hol-light-font-lock-operator-face))
	(if (not sym-lock-keywords)
	    (sym-lock hol-light-sym-lock-keywords))))
  (setq font-lock-defaults
	(list*
	 'hol-light-font-lock-keywords (not hol-light-use-syntax-ppss) nil
	 hol-light-font-lock-syntax nil
	 '(font-lock-syntactic-keywords
	   . hol-light-font-lock-syntactic-keywords)
	 '(parse-sexp-lookup-properties
	   . t)
	 '(font-lock-syntactic-face-function
	   . hol-light-font-lock-syntactic-face-function)
	 (unless hol-light-use-syntax-ppss
	   '((font-lock-fontify-region-function
	      . hol-light-fontify-region)))))
  (when (and (boundp 'font-lock-fontify-region-function)
	     (not hol-light-use-syntax-ppss))
  (make-local-variable 'font-lock-fontify-region-function)
      (setq font-lock-fontify-region-function 'hol-light-fontify-region)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Error processing

(require 'compile)

;; In some versions of Emacs, the regexps in
;; compilation-error-regexp-alist do not match the error messages when
;; the language is not English. Hence we add a regexp.

(defconst hol-light-error-regexp
  "^[^\0-@]+ \"\\([^\"\n]+\\)\", [^\0-@]+ \\([0-9]+\\)[-,:]"
  "Regular expression matching the error messages produced by (o)camlc.")

(if (boundp 'compilation-error-regexp-alist)
    (or (assoc hol-light-error-regexp
               compilation-error-regexp-alist)
        (setq compilation-error-regexp-alist
              (cons (list hol-light-error-regexp 1 2)
               compilation-error-regexp-alist))))

;; A regexp to extract the range info.

(defconst hol-light-error-chars-regexp
  ".*, .*, [^\0-@]+ \\([0-9]+\\)-\\([0-9]+\\):"
  "Regexp matching the char numbers in an error message produced by (o)camlc.")

;; Wrapper around next-error.

;; itz 04-21-96 instead of defining a new function, use defadvice
;; that way we get our effect even when we do \C-x` in compilation buffer  

(defadvice next-error (after hol-light-next-error activate)
 "Read the extra positional information provided by the Caml compiler.

Puts the point and the mark exactly around the erroneous program
fragment. The erroneous fragment is also temporarily highlighted if
possible."
 (if (eq major-mode 'hol-light-mode)
     (let ((beg nil) (end nil))
       (save-excursion
	 (set-buffer compilation-last-buffer)
	 (save-excursion
	   (goto-char (window-point (get-buffer-window (current-buffer) t)))
	   (if (looking-at hol-light-error-chars-regexp)
	       (setq beg (string-to-number (hol-light-match-string 1))
		     end (string-to-number (hol-light-match-string 2))))))
       (beginning-of-line)
       (if beg
	   (progn
	     (setq beg (+ (point) beg) end (+ (point) end))
	     (goto-char beg) (push-mark end t t))))))

(defvar hol-light-interactive-error-regexp
  (concat "\\(\\("
	  "Toplevel input:"
	  "\\|Entr.e interactive:"
	  "\\|Characters [0-9-]*:"
	  "\\|The global value [^ ]* is referenced before being defined."
	  "\\|La valeur globale [^ ]* est utilis.e avant d'.tre d.finie."
	  "\\|Reference to undefined global"
	  "\\|The C primitive \"[^\"]*\" is not available."
	  "\\|La primitive C \"[^\"]*\" est inconnue."
	  "\\|Cannot find \\(the compiled interface \\)?file"
	  "\\|L'interface compil.e [^ ]* est introuvable."
	  "\\|Le fichier [^ ]* est introuvable."
	  "\\|Exception non rattrap.e:"
	  "\\|Uncaught exception:"
	  "\\)[^#]*\\)" )
  "Regular expression matching the error messages produced by Caml.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Indentation stuff

(defconst hol-light-keyword-regexp "\\<\\(object\\|initializer\\|and\\|c\\(onstraint\\|lass\\)\\|m\\(atch\\|odule\\|ethod\\|utable\\)\\|s\\(ig\\|truct\\)\\|begin\\|e\\(lse\\|x\\(ception\\|ternal\\)\\)\\|t\\(o\\|hen\\|ry\\|ype\\)\\|v\\(irtual\\|al\\)\\|w\\(h\\(ile\\|en\\)\\|ith\\)\\|i\\(f\\|n\\(herit\\)?\\)\\|f\\(or\\|un\\(ct\\(or\\|ion\\)\\)?\\)\\|let\\|do\\(wnto\\)?\\|parser?\\|rule\\|of\\)\\>\\|->\\|[;,|]"
  "Regexp for all recognized keywords.")

(defconst hol-light-match-|-keyword-regexp
  "\\<\\(and\\|fun\\(ction\\)?\\|type\\|with\\|parser?\\)\\>\\|[[({|=]"
  "Regexp for keywords supporting case match.")

(defconst hol-light-operator-regexp "[---+*/=<>@^&|]\\|:>\\|::\\|\\<\\(or\\|l\\(and\\|x?or\\|s[lr]\\)\\|as[lr]\\|mod\\)\\>"
  "Regexp for all operators.")

(defconst hol-light-kwop-regexp (concat hol-light-keyword-regexp "\\|=")
  "Regexp for all keywords, and the = operator which is generally
considered as a special keyword.")

(defconst hol-light-matching-keyword-regexp
  "\\<\\(and\\|do\\(ne\\)?\\|e\\(lse\\|nd\\)\\|in\\|then\\|\\(down\\)?to\\)\\>\\|>\\."
  "Regexp matching Caml keywords which act as end block delimiters.")

(defconst hol-light-leading-kwop-regexp
  (concat hol-light-matching-keyword-regexp "\\|\\<with\\>\\|[|>]?\\]\\|>?}\\|[|)]\\|;;")
  "Regexp matching Caml keywords which need special indentation.")

(defconst hol-light-governing-phrase-regexp
  "\\<\\(val\\|type\\|m\\(ethod\\|odule\\)\\|c\\(onstraint\\|lass\\)\\|in\\(herit\\|itializer\\)\\|ex\\(ternal\\|ception\\)\\|open\\|let\\|object\\|include\\)\\>"
  "Regexp matching hol-light phrase delimitors.")

(defconst hol-light-governing-phrase-regexp-with-break
  (concat hol-light-governing-phrase-regexp "\\|;;"))

(defconst hol-light-keyword-alist
  '(("module" . hol-light-default-indent)
    ("class" . hol-light-class-indent)
    ("sig" . hol-light-sig-struct-indent)
    ("struct" . hol-light-sig-struct-indent)
    ("method" . hol-light-method-indent)
    ("object" . hol-light-begin-indent)
    ("begin" . hol-light-begin-indent)
    (".<" . hol-light-begin-indent)
    ("for" . hol-light-for-while-indent)
    ("while" . hol-light-for-while-indent)
    ("do" . hol-light-do-indent)
    ("type" . hol-light-type-indent) ; in some cases, `type' acts like a match
    ("val" . hol-light-val-indent)
    ("fun" . hol-light-fun-indent)
    ("if" . hol-light-if-then-else-indent)
    ("then" . hol-light-if-then-else-indent)
    ("else" . hol-light-if-then-else-indent)
    ("let" . hol-light-let-indent)
    ("match" . hol-light-match-indent)
    ("try" . hol-light-try-indent)
    ("rule" . hol-light-rule-indent)

    ;; Case match keywords
    ("function" . hol-light-function-indent)
    ("with" . hol-light-with-indent)
    ("parse" . hol-light-parse-indent)
    ("parser" . hol-light-parser-indent)

    ;; Default indentation keywords
    ("when" . hol-light-default-indent)
    ("functor" . hol-light-default-indent)
    ("exception" . hol-light-default-indent)
    ("inherit" . hol-light-default-indent)
    ("initializer" . hol-light-default-indent)
    ("constraint" . hol-light-default-indent)
    ("virtual" . hol-light-default-indent)
    ("mutable" . hol-light-default-indent)
    ("external" . hol-light-default-indent)
    ("in" . hol-light-in-indent)
    ("of" . hol-light-default-indent)
    ("to" . hol-light-default-indent)
    ("downto" . hol-light-default-indent)
    (".<" . hol-light-default-indent)
    ("[" . hol-light-default-indent)
    ("(" . hol-light-default-indent)
    ("{" . hol-light-default-indent)
    ("->" . hol-light-default-indent)
    ("|" . hol-light-default-indent))
"Association list of indentation values based on governing keywords.")

(defconst hol-light-leading-kwop-alist
  '(("|" . hol-light-find-|-match)
    ("}" . hol-light-find-match)
    (">}" . hol-light-find-match)
    (">." . hol-light-find-match)
    (")" . hol-light-find-match)
    ("]" . hol-light-find-match)
    ("|]" . hol-light-find-match)
    (">]" . hol-light-find-match)
    ("end" . hol-light-find-match)
    ("done" . hol-light-find-done-match)
    ("in"  . hol-light-find-in-match)
    ("with" . hol-light-find-with-match)
    ("else" . hol-light-find-else-match)
    ("then" . hol-light-find-match)
    ("do" . hol-light-find-do-match)
    ("to" . hol-light-find-match)
    ("downto" . hol-light-find-match)
    ("and" . hol-light-find-and-match))
  "Association list used in HOL Light mode for skipping back over nested blocks.")

(defun hol-light-find-meaningful-word ()
  "Look back for a word, skipping comments and blanks.
Returns the actual text of the word, if found."
  (let ((found nil) (kwop nil))
    (while
	(and (not found)
	     (re-search-backward
	      (concat
	       "[^ \t\n_0-9" hol-light-alpha "]\\|\\<\\(\\w\\|_\\)+\\>\\|\\*)")
	      (point-min) t))
      (setq kwop (hol-light-match-string 0))
      (if kwop
	  (if (hol-light-in-comment-p)
	      (hol-light-beginning-of-literal-or-comment-fast)
	    (setq found t))
	(setq found t)))
    (if found kwop (goto-char (point-min)) nil)))

(defconst hol-light-find-kwop-regexp
  (concat hol-light-matching-keyword-regexp
	  "\\|\\<\\(for\\|while\\|do\\|if\\|begin\\|s\\(ig\\|truct\\)\\|object\\)\\>\\|[][(){}]\\|\\*)"))

(defun hol-light-make-find-kwop-regexp (kwop-regexp)
  (concat hol-light-find-kwop-regexp "\\|" kwop-regexp))

(defun hol-light-find-kwop (kr &optional do-not-skip-regexp)
  "Look back for a Caml keyword or operator matching KWOP-REGEXP.
Skips blocks etc...

Ignore occurences inside literals and comments.
If found, return the actual text of the keyword or operator."
  (let ((found nil)
	(kwop nil)
	(kwop-regexp (if hol-light-support-metaocaml
			 (concat kr "\\|\\.<\\|>\\.") kr)))
    (while (and (not found)
		(re-search-backward kwop-regexp (point-min) t)
		(setq kwop (hol-light-match-string 0)))
      (cond
       ((hol-light-in-literal-or-comment-p)
	(hol-light-beginning-of-literal-or-comment-fast))
       ((looking-at "[]})]")
	(hol-light-backward-up-list))
       ((hol-light-at-phrase-break-p)
	(setq found t))
       ((and do-not-skip-regexp (looking-at do-not-skip-regexp))
	(if (and (string= kwop "|") (char-equal ?| (preceding-char)))
	    (backward-char)
	  (setq found t)))
       ((looking-at hol-light-matching-keyword-regexp)
	(funcall (cdr (assoc (hol-light-match-string 0)
			     hol-light-leading-kwop-alist))))
       (t (setq found t))))
    (if found kwop (goto-char (point-min)) nil)))

(defun hol-light-find-match ()
  (hol-light-find-kwop hol-light-find-kwop-regexp))

(defconst hol-light-find-comma-match-regexp
  (hol-light-make-find-kwop-regexp
   "\\<\\(and\\|match\\|begin\\|else\\|exception\\|then\\|try\\|with\\|or\\|fun\\|function\\|let\\|do\\)\\>\\|->\\|[[{(]"))
(defun hol-light-find-comma-match ()
  (hol-light-find-kwop hol-light-find-comma-match-regexp))

(defconst hol-light-find-with-match-regexp
  (hol-light-make-find-kwop-regexp
   "\\<\\(match\\|try\\|module\\|begin\\|with\\)\\>\\|[[{(]"))
(defun hol-light-find-with-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-with-match-regexp
				"\\<with\\>")))
    (if (string= kwop "with")
	(progn
	  (hol-light-find-with-match)
	  (hol-light-find-with-match)))
    kwop))

(defconst hol-light-find-in-match-regexp
  (hol-light-make-find-kwop-regexp "\\<let\\>"))
(defun hol-light-find-in-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-in-match-regexp "\\<and\\>")))
    (cond ((string= kwop "and") (hol-light-find-in-match))
	  (t kwop))))

(defconst hol-light-find-else-match-regexp
  (hol-light-make-find-kwop-regexp ";\\|->\\|\\<with\\>"))
(defun hol-light-find-else-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-else-match-regexp
				"->\\|\\<\\(with\\|then\\)\\>")))
    (cond
     ((string= kwop "then")
      (hol-light-find-match))
     ((string= kwop "with")
      (hol-light-find-with-match))
     ((string= kwop "->")
      (setq kwop (hol-light-find-->-match))
      (while (string= kwop "|")
	(setq kwop (hol-light-find-|-match)))
      (if (string= kwop "with")
	  (hol-light-find-with-match))
      (hol-light-find-else-match))
     ((string= kwop ";")
      (hol-light-find-semi-colon-match)
      (hol-light-find-else-match)))
    kwop))

(defun hol-light-find-do-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-kwop-regexp
				   "\\<\\(down\\)?to\\>")))
    (if (or (string= kwop "to") (string= kwop "downto"))
	(hol-light-find-match) kwop)))

(defun hol-light-find-done-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-kwop-regexp "\\<do\\>")))
    (if (string= kwop "do")
	(hol-light-find-do-match) kwop)))

(defconst hol-light-find-and-match-regexp
  "\\<\\(do\\(ne\\)?\\|e\\(lse\\|nd\\)\\|in\\|then\\|\\(down\\)?to\\)\\>\\|\\<\\(for\\|while\\|do\\|if\\|begin\\|s\\(ig\\|truct\\)\\|class\\)\\>\\|[][(){}]\\|\\*)\\|\\<\\(rule\\|exception\\|let\\|in\\|type\\|val\\|module\\)\\>")
(defconst hol-light-find-and-match-regexp-dnr
  (concat hol-light-find-and-match-regexp "\\|\\<and\\>"))
(defun hol-light-find-and-match (&optional do-not-recurse)
  (let* ((kwop (hol-light-find-kwop (if do-not-recurse
				     hol-light-find-and-match-regexp-dnr
				   hol-light-find-and-match-regexp)
				 "\\<and\\>"))
	 (old-point (point)))
    (cond ((or (string= kwop "type") (string= kwop "module"))
	   (let ((kwop2 (hol-light-find-meaningful-word)))
	     (cond ((string= kwop2 "with")
		    kwop2)
		   ((string= kwop2 "and")
		    (hol-light-find-and-match))
		   ((and (string= kwop "module")
			(string= kwop2 "let"))
		    kwop2)
		   (t (goto-char old-point) kwop))))
	  (t kwop))))

(defconst hol-light-find-=-match-regexp
  (hol-light-make-find-kwop-regexp "\\<\\(val\\|let\\|m\\(ethod\\|odule\\)\\|type\\|class\\|when\\|i[fn]\\)\\>\\|="))
(defun hol-light-find-=-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-=-match-regexp
				"\\<\\(and\\|in\\)\\>\\|=")))
    (cond
     ((string= kwop "and")
      (hol-light-find-and-match))
     ((and (string= kwop "=")
	   (not (hol-light-false-=-p)))
      (while (and (string= kwop "=")
		  (not (hol-light-false-=-p)))
	(setq kwop (hol-light-find-=-match)))
      kwop)
     (t kwop))))

(defun hol-light-if-when-= ()
  (save-excursion
    (hol-light-find-=-match)
    (looking-at "\\<\\(if\\|when\\)\\>")))

(defun hol-light-captive-= ()
  (save-excursion
    (hol-light-find-=-match)
    (looking-at "\\<\\(let\\|if\\|when\\|module\\|type\\|class\\)\\>")))

(defconst hol-light-find-|-match-regexp
  (hol-light-make-find-kwop-regexp
   "\\<\\(with\\|fun\\(ction\\)?\\|type\\|parser?\\)\\>\\|[=|]"))
(defun hol-light-find-|-match ()
  (let* ((kwop (hol-light-find-kwop hol-light-find-|-match-regexp
				 "\\<\\(and\\|with\\)\\>\\||"))
	 (old-point (point)))
    (cond ((string= kwop "and")
	   (setq old-point (point))
	   (setq kwop (hol-light-find-and-match))
	   (goto-char old-point)
	   kwop)
	  ((and (string= kwop "|")
		(looking-at "|[^|]")
		(hol-light-in-indentation-p))
	   kwop)
	  ((string= kwop "|") (hol-light-find-|-match))
	  ((and (string= kwop "=")
		(or (looking-at "=[ \t]*\\((\\*\\|$\\)")
		    (hol-light-false-=-p)
		    (not (string= (save-excursion (hol-light-find-=-match))
				  "type"))))
	   (hol-light-find-|-match))
	  ((string= kwop "parse")
	   (if (and (string-match "\\.mll" (buffer-name))
		    (save-excursion
		      (string= (hol-light-find-meaningful-word) "=")))
	       kwop (hol-light-find-|-match)))
	  (t kwop))))

(defconst hol-light-find-->-match-regexp
  (hol-light-make-find-kwop-regexp "\\<\\(external\\|val\\|method\\|let\\|with\\|fun\\(ction\\|ctor\\)?\\|parser\\)\\>\\|[|:;]"))
(defun hol-light-find-->-match ()
  (let ((kwop (hol-light-find-kwop hol-light-find-->-match-regexp "\\<with\\>")))
    (cond
     ((string= kwop "|")
      (if (hol-light-in-indentation-p)
	  kwop
	(progn (forward-char -1) (hol-light-find-->-match))))
     ((not (string= kwop ":")) kwop)
     ;; If we get this far, we know we're looking at a colon.
     ((or (char-equal (char-before) ?:)
	  (char-equal (char-after (1+ (point))) ?:)
	  (char-equal (char-after (1+ (point))) ?>))
      (hol-light-find-->-match))
     ;; Patch by T. Freeman
     (t (let ((oldpoint (point))
	      (match (hol-light-find-->-match)))
	  (if (looking-at ":")
	      match
	    (progn
	      ;; Go back to where we were before the recursive call.
	      (goto-char oldpoint)
	      kwop)))))))

(defconst hol-light-find-semi-colon-match-regexp
  (hol-light-make-find-kwop-regexp ";[ \t]*\\((\\*\\|$\\)\\|->\\|\\<\\(let\\|method\\|with\\|try\\|initializer\\)\\>"))
(defun hol-light-find-semi-colon-match (&optional leading-semi-colon)
  (hol-light-find-kwop hol-light-find-semi-colon-match-regexp
			 "\\<\\(in\\|end\\|and\\|do\\|with\\)\\>")
  ;; We don't need to find the keyword matching `and' since we know it's `let'!
  (cond
   ((looking-at ";[ \t]*\\((\\*\\|$\\)")
    (forward-line 1)
    (while (or (hol-light-in-comment-p)
	       (looking-at "^[ \t]*\\((\\*\\|$\\)"))
      (forward-line 1))
    (back-to-indentation)
    (current-column))
   ((and leading-semi-colon
	 (looking-at "\\((\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
	 (not (looking-at "[[{(][|<]?[ \t]*\\((\\*\\|$\\)")))
    (current-column))
   ((looking-at "\\((\\|\\[[<|]?\\|{<?\\)[ \t]*\\((\\*\\|$\\)")
    (hol-light-back-to-paren-or-indentation t)
    (+ (current-column) hol-light-default-indent))
   ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
    (hol-light-search-forward-paren)
    (current-column))
   ((looking-at "\\<method\\>[ \t]*\\((\\*\\|$\\)")
    (hol-light-back-to-paren-or-indentation)
    (+ (current-column) hol-light-method-indent))
   ((looking-at "\\<begin\\>[ \t]*\\((\\*\\|$\\)")
    (hol-light-back-to-paren-or-indentation t)
    (+ (current-column) hol-light-begin-indent))
   ((looking-at "->")
    (if (save-excursion
	  (hol-light-find-->-match)
	  (looking-at "\\<\\(with\\|fun\\(ction\\)?\\|parser\\)\\>\\||"))
	(progn
	  (hol-light-back-to-paren-or-indentation)
	  (+ (current-column) hol-light-default-indent))
      (hol-light-find-semi-colon-match)))
   ((looking-at "\\<end\\>")
    (hol-light-find-match)
    (hol-light-find-semi-colon-match))
   ((looking-at "\\<in\\>")
    (hol-light-find-in-match)
    (hol-light-back-to-paren-or-indentation)
    (+ (current-column) hol-light-in-indent))
   ((looking-at "\\<let\\>")
    (+ (current-column) hol-light-let-indent))
   (t (hol-light-back-to-paren-or-indentation t)
      (+ (current-column) hol-light-default-indent))))

(defconst hol-light-find-phrase-indentation-regexp
  (hol-light-make-find-kwop-regexp (concat hol-light-governing-phrase-regexp
					"\\|\\<and\\>")))
(defconst hol-light-find-phrase-indentation-regexp-pb
  (concat hol-light-find-phrase-indentation-regexp "\\|;;"))
(defconst hol-light-find-phrase-indentation-class-regexp
  (concat hol-light-matching-keyword-regexp "\\|\\<class\\>"))
(defun hol-light-find-phrase-indentation (&optional phrase-break)
  (if (and (looking-at "\\<\\(type\\|module\\)\\>") (> (point) (point-min))
	   (save-excursion
	     (hol-light-find-meaningful-word)
	     (looking-at "\\<\\(module\\|with\\|and\\|let\\)\\>")))
      (progn
	(hol-light-find-meaningful-word)
	(+ (current-column) hol-light-default-indent))
    (let ((looking-at-and (looking-at "\\<and\\>"))
	  (kwop (hol-light-find-kwop
		 (if phrase-break
		     hol-light-find-phrase-indentation-regexp-pb
		   hol-light-find-phrase-indentation-regexp)
		 "\\<\\(end\\|and\\|with\\|in\\)\\>"))
	  (tmpkwop nil) (curr nil))
      (if (and kwop (string= kwop "and"))
	  (setq kwop (hol-light-find-and-match)))
      (if (not kwop) (current-column)
	(cond
	 ((string= kwop "end")
	  (if (not (save-excursion
		     (setq tmpkwop (hol-light-find-match))
		     (setq curr (point))
		     (string= tmpkwop "object")))
	      (progn
		(hol-light-find-match)
		(hol-light-find-phrase-indentation phrase-break))
	    (hol-light-find-kwop hol-light-find-phrase-indentation-class-regexp)
	    (current-column)))
	 ((and (string= kwop "with")
	       (not (save-excursion
		      (setq tmpkwop (hol-light-find-with-match))
		      (setq curr (point))
		      (string= tmpkwop "module"))))
	  (goto-char curr)
	  (hol-light-find-phrase-indentation phrase-break))
	 ((and (string= kwop "in")
	       (not (save-excursion
		      (setq tmpkwop (hol-light-find-in-match))
		      (if (string= tmpkwop "and")
			  (setq tmpkwop (hol-light-find-and-match)))
		      (setq curr (point))
		      (and (string= tmpkwop "let")
			   (not (hol-light-looking-at-expression-let))))))
	  (goto-char curr)
	  (hol-light-find-phrase-indentation phrase-break))
	 ((hol-light-at-phrase-break-p)
	  (end-of-line)
	  (hol-light-skip-blank-and-comments)
	  (current-column))
	 ((string= kwop "let")
	  (if (hol-light-looking-at-expression-let)
	      (hol-light-find-phrase-indentation phrase-break)
	    (current-column)))
	 ((string= kwop "with")
	  (current-column))
	 ((string= kwop "end")
	  (current-column))
	 ((string= kwop "in")
	  (hol-light-find-in-match)
	  (current-column))
	 ((string= kwop "class")
	  (hol-light-back-to-paren-or-indentation)
	  (current-column))
	 ((looking-at "\\<\\(object\\|s\\(ig\\|truct\\)\\)\\>")
	  (hol-light-back-to-paren-or-indentation t)
	  (+ (hol-light-assoc-indent kwop) (current-column)))
	 ((or (string= kwop "type") (string= kwop "module"))
	  (if (or (hol-light-looking-at-false-type)
		  (hol-light-looking-at-false-module))
	      (if looking-at-and (current-column)
		(hol-light-find-meaningful-word)
		(if (looking-at "\\<and\\>")
		    (progn
		      (hol-light-find-and-match)
		      (hol-light-find-phrase-indentation phrase-break))
		  (hol-light-find-phrase-indentation phrase-break)))
	    (current-column)))
	 ((looking-at
	   "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*\\((\\*\\|$\\)")
	  (hol-light-back-to-paren-or-indentation)
	  (+ (current-column) hol-light-default-indent))
	 ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
	  (hol-light-search-forward-paren)
	  (current-column))
	 ((string= kwop "open") ; compatible with Caml Light `#open'
	  (hol-light-back-to-paren-or-indentation) (current-column))
	 (t (current-column)))))))

(defconst hol-light-back-to-paren-or-indentation-regexp
  "[][(){}]\\|\\.<\\|>\\.\\|\\*)\\|^[ \t]*\\(.\\|\n\\)")
(defconst hol-light-back-to-paren-or-indentation-in-regexp
  (concat "\\<in\\>\\|" hol-light-back-to-paren-or-indentation-regexp))
(defconst hol-light-back-to-paren-or-indentation-lazy-regexp
  "[])}]\\|\\.<\\|>\\.\\|\\*)\\|^[ \t]*\\(.\\|\n\\)")
(defconst hol-light-back-to-paren-or-indentation-lazy-in-regexp
  (concat "\\<in\\>\\|" hol-light-back-to-paren-or-indentation-regexp))
(defun hol-light-back-to-paren-or-indentation (&optional forward-in)
  "Search backwards for the first open paren in line, or skip to indentation.
Returns t iff skipped to indentation."
  (if (or (bolp) (hol-light-in-indentation-p)) (progn (back-to-indentation) t)
    (let ((kwop (hol-light-find-kwop
		 (if hol-light-lazy-paren
		     (if forward-in
			 hol-light-back-to-paren-or-indentation-lazy-in-regexp
		       hol-light-back-to-paren-or-indentation-lazy-regexp)
		   (if forward-in
		       hol-light-back-to-paren-or-indentation-in-regexp
		     hol-light-back-to-paren-or-indentation-regexp))
		 "\\<and\\|with\\|in\\>"))
	  (retval))
      (if (string= kwop "with")
	  (let ((with-point (point)))
	    (setq kwop (hol-light-find-with-match))
	    (if (or (string= kwop "match") (string= kwop "try"))
		(hol-light-find-kwop
		 hol-light-back-to-paren-or-indentation-regexp
		 "\\<and\\>")
	      (setq kwop "with") (goto-char with-point))))
      (setq retval
	    (cond
	     ((string= kwop "with") nil)
	     ((string= kwop "in") (hol-light-in-indentation-p))
	     ((looking-at "[[{(]") (hol-light-search-forward-paren) nil)
	     ((looking-at "\\.<")
	      (if hol-light-support-metaocaml
		  (progn
		    (hol-light-search-forward-paren) nil)
		(hol-light-back-to-paren-or-indentation forward-in)))
	     (t (back-to-indentation) t)))
      (cond
       ((looking-at "|[^|]")
	(re-search-forward "|[^|][ \t]*") nil)
       ((and forward-in (string= kwop "in"))
	(hol-light-find-in-match)
	(hol-light-back-to-paren-or-indentation forward-in)
	(if (looking-at "\\<\\(let\\|and\\)\\>")
	    (forward-char hol-light-in-indent)) nil)
       (t retval)))))

(defun hol-light-search-forward-paren ()
  (if hol-light-lazy-paren (hol-light-back-to-paren-or-indentation)
    (re-search-forward "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*")))

(defun hol-light-add-default-indent (leading-operator)
  (if leading-operator 0 hol-light-default-indent))

(defconst hol-light-compute-argument-indent-regexp
  (hol-light-make-find-kwop-regexp hol-light-kwop-regexp))
(defun hol-light-compute-argument-indent (leading-operator)
  (let ((old-point (save-excursion (beginning-of-line) (point)))
	(match-end-point) (kwop))
    (setq kwop (hol-light-find-kwop hol-light-compute-argument-indent-regexp
				 hol-light-keyword-regexp))
    (setq match-end-point (+ (point) (length kwop))) ; match-end is invalid !
    (cond
     ((and (string= kwop "->")
	   (not (looking-at "->[ \t]*\\((\\*.*\\)?$")))
      (let* (matching-kwop matching-pos)
	(save-excursion
	  (setq matching-kwop (hol-light-find-->-match))
	  (setq matching-pos (point)))
	(cond
	 ((string= matching-kwop ":")
	  (goto-char matching-pos)
	  (hol-light-find-->-match) ; matching `val' or `let'
	  (+ (current-column) hol-light-val-indent))
	 ((string= matching-kwop "|")
	  (goto-char matching-pos)
	  (+ (hol-light-add-default-indent leading-operator)
	     (current-column) hol-light-|-extra-unindent hol-light-default-indent))
	 (t
	  (hol-light-back-to-paren-or-indentation)
	  (+ (hol-light-add-default-indent leading-operator) (current-column))))))
     ((string= kwop "fun")
      (hol-light-back-to-paren-or-indentation t)
      (+ (current-column)
	 (hol-light-assoc-indent kwop)))
     ((<= old-point (point))
      (+ (hol-light-add-default-indent leading-operator) (current-column)))
     (t
      (forward-line 1)
      (beginning-of-line)
      (while (or (hol-light-in-comment-p) (looking-at "^[ \t]*\\((\\*.*\\)?$"))
	(forward-line 1))
      (hol-light-back-to-paren-or-indentation)
      (if (save-excursion (goto-char match-end-point)
			  (looking-at "[ \t]*\\((\\*.*\\)?$"))
	  (+ (hol-light-add-default-indent leading-operator)
	     (current-column))
	(current-column))))))

(defun hol-light-indent-from-paren (&optional leading-operator)
  (if (looking-at
       "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*\\((\\*\\|$\\)")
      (progn
	(hol-light-back-to-paren-or-indentation t)
	(+ hol-light-default-indent
	   (current-column))) ; parens do not operate
    (hol-light-search-forward-paren)
    (+ (hol-light-add-default-indent leading-operator)
       (current-column))))

(defconst hol-light-compute-normal-indent-regexp
  (concat hol-light-compute-argument-indent-regexp "\\|^.[ \t]*"))
(defun hol-light-compute-normal-indent ()
  (let ((leading-operator (looking-at hol-light-operator-regexp)))
    (beginning-of-line)
    ;; Operator ending previous line used to be considered leading
    ;; (save-excursion
    ;;  (hol-light-find-meaningful-word)
    ;;  (if (looking-at hol-light-operator-regexp)
    ;;	  (setq leading-operator t)))
    (save-excursion
      (let ((kwop (hol-light-find-kwop (if leading-operator
					hol-light-compute-argument-indent-regexp
				      hol-light-compute-normal-indent-regexp)
				    hol-light-keyword-regexp)))
	(if (string= kwop "and") (setq kwop (hol-light-find-and-match)))
	(while (or (and (string= kwop "=")
			(hol-light-false-=-p))
		   (and (looking-at "^[ \t]*\\((\\*.*\\)?$")
			(not (= (point) (point-min)))))
	  (setq kwop (hol-light-find-kwop hol-light-compute-normal-indent-regexp
				       hol-light-keyword-regexp))
	  (if (string= kwop "and") (setq kwop (hol-light-find-and-match))))
	(if (not kwop) (current-column)
	  (cond
	   ((hol-light-at-phrase-break-p)
	    (hol-light-find-phrase-indentation t))
	   ((and (string= kwop "|") (not  (char-equal ?\[ (preceding-char))))
	    (hol-light-backward-char)
	    (hol-light-back-to-paren-or-indentation)
	    (+ (current-column) hol-light-default-indent
	       (hol-light-add-default-indent leading-operator)))
	   ((or (looking-at "[[{(]")
		(and (looking-at "[<|]")
		     (char-equal ?\[ (preceding-char))
		     (progn (hol-light-backward-char) t))
		(and (looking-at "<")
		     (char-equal ?\{ (preceding-char))
		     (progn (hol-light-backward-char) t)))
	    (hol-light-indent-from-paren leading-operator))
	   ((looking-at "\\.<")
	    (hol-light-indent-from-paren leading-operator))
	   ((looking-at "->")
	    (let ((keyword-->-match (save-excursion (hol-light-find-->-match))))
	      (cond ((string= keyword-->-match "|")
		     (hol-light-find-->-match)
		     (re-search-forward "|[ \t]*")
		     (+ (current-column) hol-light-default-indent))
		    ((string= keyword-->-match ":")
		     (hol-light-find-->-match) ; slow, better to save the column
		     (hol-light-find-->-match) ; matching `val' or `let'
		     (+ (current-column) hol-light-val-indent))
		    (t (hol-light-back-to-paren-or-indentation)
		       (+ hol-light-default-indent (current-column))))))
	   ((looking-at hol-light-keyword-regexp)
	    (cond ((string= kwop ";")
		   (if (looking-at ";[ \t]*\\((\\*\\|$\\)")
		       (hol-light-find-semi-colon-match)
		     (hol-light-back-to-paren-or-indentation t)
		     (+ (current-column) hol-light-default-indent)))
		  ((string= kwop ",")
		   (if (looking-at ",[ \t]*\\((\\*\\|$\\)")
		       (progn
			 (setq kwop (hol-light-find-comma-match))
			 (if (or (looking-at "[[{(]\\|\\.<")
				 (and (looking-at "[<|]")
				      (char-equal ?\[ (preceding-char))
				      (progn (hol-light-backward-char) t))
				 (and (looking-at "<")
				      (char-equal ?\{ (preceding-char))
				      (progn (hol-light-backward-char) t)))
			     (hol-light-indent-from-paren t)
			   (hol-light-back-to-paren-or-indentation t)
			   (+ (current-column)
			      (hol-light-assoc-indent kwop))))
		     (hol-light-back-to-paren-or-indentation t)
		     (+ (current-column) hol-light-default-indent)))
		  ((and (looking-at "\\<\\(in\\|begin\\|do\\)\\>\\|->")
			(not (looking-at
			      "\\([a-z]+\\|->\\)[ \t]*\\((\\*\\|$\\)")))
		   (if (string= kwop "in")
		       (re-search-forward "\\<in\\>[ \t]*")
		     (hol-light-back-to-paren-or-indentation t))
		   (+ (current-column)
		      (hol-light-add-default-indent leading-operator)
		      (if (string= kwop "in") 0 ; aligned, do not indent
			(hol-light-assoc-indent kwop))))
		  ((string= kwop "with")
		   (if (save-excursion
			 (let ((tmpkwop (hol-light-find-with-match)))
			   (or (string= tmpkwop "module")
			       (string= tmpkwop "{"))))
		       (progn
			 (hol-light-back-to-paren-or-indentation)
			 (+ (current-column) hol-light-default-indent))
		     (hol-light-back-to-paren-or-indentation)
		     (+ (current-column)
			(hol-light-assoc-indent kwop t))))
		  ((string= kwop "in")
		   (hol-light-find-in-match)
		   (hol-light-back-to-paren-or-indentation)
		   (+ (current-column) hol-light-in-indent))
		  ((or (string= kwop "let") (string= kwop "and"))
		   (hol-light-back-to-paren-or-indentation t)
		   (+ (current-column)
		      hol-light-default-indent
		      (hol-light-assoc-indent kwop t)))
		  (t (hol-light-back-to-paren-or-indentation t)
		     (+ (current-column)
			(hol-light-assoc-indent kwop t)))))
	   ((and (looking-at "=") (not (hol-light-false-=-p)))
	    (let ((current-column-module-type nil))
	      (+
	       (progn
		 (hol-light-find-=-match)
		 (save-excursion
		   (if (looking-at "\\<and\\>") (hol-light-find-and-match))
		   (cond
		    ((looking-at "\\<type\\>")
		     (hol-light-find-meaningful-word)
		     (if (looking-at "\\<module\\>")
			 (progn
			   (setq current-column-module-type (current-column))
			   hol-light-default-indent)
		       (if (looking-at "\\<\\(with\\|and\\)\\>")
			   (progn
			     (hol-light-find-with-match)
			     (setq current-column-module-type (current-column))
			     hol-light-default-indent)
			 (re-search-forward "\\<type\\>")
			 (beginning-of-line)
			 (+ hol-light-type-indent
			    hol-light-|-extra-unindent))))
		    ((looking-at
		      "\\<\\(val\\|let\\|m\\(ethod\\|odule\\)\\|class\\|when\\|\\|for\\|if\\)\\>")
		     (let ((matched-string (hol-light-match-string 0)))
		       (hol-light-back-to-paren-or-indentation t)
		       (setq current-column-module-type (current-column))
		       (hol-light-assoc-indent matched-string)))
		    ((looking-at "\\<object\\>")
		     (hol-light-back-to-paren-or-indentation t)
		     (setq current-column-module-type (current-column))
		     (+ (hol-light-assoc-indent "object")
			hol-light-default-indent))
		    (t (hol-light-back-to-paren-or-indentation t)
		       (setq current-column-module-type
			     (+ (current-column) hol-light-default-indent))
		       hol-light-default-indent))))
	       (if current-column-module-type
		   current-column-module-type
		 (current-column)))))
	   (nil 0)
	   (t (hol-light-compute-argument-indent leading-operator))))))))

(defun hol-light-looking-at-expression-let ()
  (save-excursion
    (hol-light-find-meaningful-word)
    (and (not (hol-light-at-phrase-break-p))
	 (not (and hol-light-support-metaocaml
		   (looking-at "\\.")
		   (char-equal ?> (preceding-char))))
	 (or (looking-at "[[({;=]\\|\\<\\(begin\\|i[fn]\\|do\\|t\\(ry\\|hen\\)\\|else\\|match\\|wh\\(ile\\|en\\)\\)\\>")
	     (looking-at hol-light-operator-regexp)))))

(defun hol-light-looking-at-false-module ()
  (save-excursion (hol-light-find-meaningful-word)
		  (looking-at "\\<\\(let\\|with\\|and\\)\\>")))

(defun hol-light-looking-at-false-sig-struct ()
  (save-excursion (hol-light-find-module)
		  (looking-at "\\<module\\>")))

(defun hol-light-looking-at-false-type ()
  (save-excursion (hol-light-find-meaningful-word)
		  (looking-at "\\<\\(class\\|with\\|module\\|and\\)\\>")))

(defun hol-light-looking-at-in-let ()
  (save-excursion (string= (hol-light-find-meaningful-word) "in")))

(defconst hol-light-find-module-regexp
  (hol-light-make-find-kwop-regexp "\\<module\\>"))
(defun hol-light-find-module ()
  (hol-light-find-kwop hol-light-find-module-regexp))

(defun hol-light-modify-syntax ()
  "Switch to modified internal syntax."
  (modify-syntax-entry ?. "w" hol-light-mode-syntax-table)
  (modify-syntax-entry ?_ "w" hol-light-mode-syntax-table))

(defun hol-light-restore-syntax ()
  "Switch back to interactive syntax."
  (modify-syntax-entry ?. "." hol-light-mode-syntax-table)
  (modify-syntax-entry ?_ "_" hol-light-mode-syntax-table))

(defun hol-light-indent-command (&optional from-leading-star)
  "Indent the current line in HOL Light mode.

Compute new indentation based on Caml syntax."
  (interactive "*")
    (if (not from-leading-star)
	(hol-light-auto-fill-insert-leading-star))
  (let ((case-fold-search nil))
    (hol-light-modify-syntax)
    (save-excursion
      (back-to-indentation)
      (indent-line-to (hol-light-compute-indent)))
    (if (hol-light-in-indentation-p) (back-to-indentation))
    (hol-light-restore-syntax)))

(defun hol-light-compute-indent ()
  (save-excursion
    (cond
     ((hol-light-in-comment-p)
      (cond
       ((looking-at "(\\*")
	(if hol-light-indent-leading-comments
	    (save-excursion
	      (while (and (progn (beginning-of-line)
				 (> (point) 1))
			  (progn (forward-line -1)
				 (back-to-indentation)
				 (hol-light-in-comment-p))))
	      (if (looking-at "[ \t]*$")
		  (progn
		    (hol-light-skip-blank-and-comments)
		    (if (or (looking-at "$") (hol-light-in-comment-p))
			0
		      (hol-light-compute-indent)))
		(forward-line 1)
		(hol-light-compute-normal-indent)))
	  (current-column)))
       ((looking-at "\\*\\**)")
	(hol-light-beginning-of-literal-or-comment-fast)
	(if (hol-light-leading-star-p)
	    (+ (current-column)
	       (if (save-excursion
		     (forward-line 1)
		     (back-to-indentation)
		     (looking-at "*")) 1
		 hol-light-comment-end-extra-indent))
	  (+ (current-column) hol-light-comment-end-extra-indent)))
       (hol-light-indent-comments
	(let ((star (and (hol-light-leading-star-p)
			 (looking-at "\\*"))))
	  (hol-light-beginning-of-literal-or-comment-fast)
	  (if star (re-search-forward "(") (re-search-forward "(\\*+[ \t]*"))
	  (current-column)))
       (t (current-column))))
     ((hol-light-in-literal-p)
      (current-column))
     ((looking-at "\\<let\\>")
      (if (hol-light-looking-at-expression-let)
	  (if (hol-light-looking-at-in-let)
	      (progn
		(hol-light-find-meaningful-word)
		(hol-light-find-in-match)
		(hol-light-back-to-paren-or-indentation)
		(current-column))
	    (hol-light-compute-normal-indent))
	(hol-light-find-phrase-indentation)))
     ((looking-at hol-light-governing-phrase-regexp-with-break)
      (hol-light-find-phrase-indentation))
     ((and hol-light-sig-struct-align (looking-at "\\<\\(sig\\|struct\\)\\>"))
      (if (string= (hol-light-find-module) "module") (current-column)
	(hol-light-back-to-paren-or-indentation)
	(+ hol-light-default-indent (current-column))))
     ((looking-at ";") (hol-light-find-semi-colon-match t))
     ((or (looking-at "%\\|;;")
	  (and hol-light-support-camllight (looking-at "#"))
	  (looking-at "#\\<\\(open\\|load\\|use\\)\\>")) 0)
     ((or (looking-at hol-light-leading-kwop-regexp)
	  (and hol-light-support-metaocaml
	       (looking-at ">\\.")))
      (let ((kwop (hol-light-match-string 0)))
	(let* ((old-point (point))
	       (paren-match-p (looking-at "[|>]?[]})]\\|>\\."))
	       (need-not-back-kwop (string= kwop "and"))
	       (real-| (looking-at "|\\([^|]\\|$\\)"))
	       (matching-kwop
		(if (string= kwop "and")
		    (hol-light-find-and-match t)
		  (funcall (cdr (assoc kwop hol-light-leading-kwop-alist)))))
	       (match-|-keyword-p
		(and matching-kwop
		     (looking-at hol-light-match-|-keyword-regexp))))
	  (cond
	   ((and (string= kwop "|") real-|)
	    (cond
	     ((string= matching-kwop "|")
	      (if (not need-not-back-kwop)
		  (hol-light-back-to-paren-or-indentation))
	      (current-column))
	     ((and (string= matching-kwop "=")
		   (not (hol-light-false-=-p)))
	      (re-search-forward "=[ \t]*")
	      (current-column))
	     (match-|-keyword-p
	      (if (not need-not-back-kwop)
		  (hol-light-back-to-paren-or-indentation))
	      (- (+ (hol-light-assoc-indent
		     matching-kwop t)
		    (current-column))
		 (if (string= matching-kwop "type") 0
		   hol-light-|-extra-unindent)))
	     (t (goto-char old-point)
		(hol-light-compute-normal-indent))))
	   ((and (string= kwop "|") (not real-|))
	    (goto-char old-point)
	    (hol-light-compute-normal-indent))
	   ((and
	     (looking-at "\\(\\[|?\\|{<?\\|(\\|\\.<\\)[ \t]*[^ \t\n]")
	     (not (looking-at "\\([[{(][|<]?\\|\\.<\\)[ \t]*\\((\\*\\|$\\)")))
	    (if (and (string= kwop "|") real-|)
		(current-column)
	      (if (not paren-match-p)
		  (hol-light-search-forward-paren))
	      (if hol-light-lazy-paren
		  (hol-light-back-to-paren-or-indentation))
	      (current-column)))
	   ((and (string= kwop "with")
		 (or (string= matching-kwop "module")
		     (string= matching-kwop "struct")))
	    (hol-light-back-to-paren-or-indentation nil)
	    (+ (current-column) hol-light-default-indent))
	   ((not need-not-back-kwop)
	    (hol-light-back-to-paren-or-indentation (not (string= kwop "in")))
	    (current-column))
	   (t (current-column))))))
     (t (hol-light-compute-normal-indent)))))

(defun hol-light-split-string ()
  "Called whenever a line is broken inside a Caml string literal."
  (insert-before-markers "\" ^\"")
  (hol-light-backward-char))

(defadvice newline-and-indent (around
			       hol-light-newline-and-indent
			       activate)
  "Handle multi-line strings in HOL Light mode."
    (let ((hooked (and (eq major-mode 'hol-light-mode) (hol-light-in-literal-p)))
	  (split-mark))
      (if (not hooked) nil
	(setq split-mark (set-marker (make-marker) (point)))
	(hol-light-split-string))
      ad-do-it
      (if (not hooked) nil
	(goto-char split-mark)
	(set-marker split-mark nil))))

(defun hol-light-electric ()
  "If inserting a | operator at beginning of line, reindent the line."
  (interactive "*")
  (let ((electric (and hol-light-electric-indent
		       (hol-light-in-indentation-p)
		       (not (hol-light-in-literal-p))
		       (not (hol-light-in-comment-p)))))
    (self-insert-command 1)
    (if (and electric
	     (not (and (char-equal ?| (preceding-char))
		       (save-excursion
			 (hol-light-backward-char)
			 (hol-light-find-|-match)
			 (not (looking-at hol-light-match-|-keyword-regexp))))))
	(indent-according-to-mode))))

(defun hol-light-electric-rp ()
  "If inserting a ) operator or a comment-end at beginning of line,
reindent the line."
  (interactive "*")
  (let ((electric (and hol-light-electric-indent
		       (or (hol-light-in-indentation-p)
			   (char-equal ?* (preceding-char)))
		       (not (hol-light-in-literal-p))
		       (or (not (hol-light-in-comment-p))
			   (save-excursion
			     (back-to-indentation)
			     (looking-at "\\*"))))))
    (self-insert-command 1)
    (if electric
	(indent-according-to-mode))))

(defun hol-light-electric-rc ()
  "If inserting a } operator at beginning of line, reindent the line.

Reindent also if } is inserted after a > operator at beginning of line.
Also, if the matching { is followed by a < and this } is not preceded
by >, insert one >."
  (interactive "*")
  (let* ((prec (preceding-char))
	 (look-bra (and hol-light-electric-close-vector
			(not (hol-light-in-literal-or-comment-p))
			(not (char-equal ?> prec))))
	 (electric (and hol-light-electric-indent
			(or (hol-light-in-indentation-p)
			    (and (char-equal ?> prec)
				 (save-excursion (hol-light-backward-char)
						 (hol-light-in-indentation-p))))
			(not (hol-light-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (if look-bra
	(save-excursion
	  (let ((inserted-char
		 (save-excursion
		   (hol-light-backward-char)
		   (hol-light-backward-up-list)
		   (cond ((looking-at "{<") ">")
			 (t "")))))
	    (hol-light-backward-char)
	    (insert inserted-char))))
    (if electric (indent-according-to-mode))))

(defun hol-light-electric-rb ()
  "If inserting a ] operator at beginning of line, reindent the line.

Reindent also if ] is inserted after a | operator at beginning of line.
Also, if the matching [ is followed by a | and this ] is not preceded
by |, insert one |."
  (interactive "*")
  (let* ((prec (preceding-char))
	 (look-|-or-bra (and hol-light-electric-close-vector
			     (not (hol-light-in-literal-or-comment-p))
			     (not (and (char-equal ?| prec)
				       (not (char-equal
					     (save-excursion
					       (hol-light-backward-char)
					       (preceding-char)) ?\[))))))
	 (electric (and hol-light-electric-indent
			(or (hol-light-in-indentation-p)
			    (and (char-equal ?| prec)
				 (save-excursion (hol-light-backward-char)
						 (hol-light-in-indentation-p))))
			(not (hol-light-in-literal-or-comment-p)))))
    (self-insert-command 1)
    (if look-|-or-bra
	(save-excursion
	  (let ((inserted-char
		 (save-excursion
		   (hol-light-backward-char)
		   (hol-light-backward-up-list)
		   (cond ((looking-at "\\[|") "|")
			 (t "")))))
	    (hol-light-backward-char)
	    (insert inserted-char))))
    (if electric (indent-according-to-mode))))

(defun hol-light-abbrev-hook ()
  "If inserting a leading keyword at beginning of line, reindent the line."
  (if (not (hol-light-in-literal-or-comment-p))
      (let* ((bol (save-excursion (beginning-of-line) (point)))
	     (kw (save-excursion
		   (and (re-search-backward "^[ \t]*\\(\\w\\|_\\)+\\=" bol t)
			(hol-light-match-string 1)))))
	(if kw (progn
		   (insert " ")
		   (indent-according-to-mode)
		   (backward-delete-char-untabify 1))))))

(defun hol-light-skip-to-end-of-phrase ()
  (let ((old-point (point)))
    (if (and (string= (hol-light-find-meaningful-word) ";")
	     (char-equal (preceding-char) ?\;))
	(setq old-point (1- (point))))
    (goto-char old-point)
    (let ((kwop (hol-light-find-meaningful-word)))
      (goto-char (+ (point) (length kwop))))))

(defun hol-light-skip-blank-and-comments ()
  (skip-chars-forward " \t\n")
  (while (and (not (eobp)) (hol-light-in-comment-p)
	      (search-forward "*)" nil t))
    (skip-chars-forward " \t\n")))

(defun hol-light-skip-back-blank-and-comments ()
  (skip-chars-backward " \t\n")
  (while (save-excursion (hol-light-backward-char)
			 (and (> (point) (point-min)) (hol-light-in-comment-p)))
    (hol-light-backward-char)
    (hol-light-beginning-of-literal-or-comment) (skip-chars-backward " \t\n")))

(defconst hol-light-beginning-phrase-regexp
  "^#[ \t]*[a-z][_a-z]*\\>\\|\\<\\(end\\|type\\|module\\|sig\\|struct\\|class\\|exception\\|open\\|let\\)\\>\\|;;"
  "Regexp matching hol-light phrase delimitors.")
(defun hol-light-find-phrase-beginning ()
  "Find `real' phrase beginning and return point."
  (beginning-of-line)
  (hol-light-skip-blank-and-comments)
  (end-of-line)
  (hol-light-skip-to-end-of-phrase)
  (let ((old-point (point)))
    (hol-light-find-kwop hol-light-beginning-phrase-regexp)
    (while (and (> (point) (point-min)) (< (point) old-point)
		(or (not (looking-at hol-light-beginning-phrase-regexp))
		    (and (looking-at "\\<let\\>")
			 (hol-light-looking-at-expression-let))
		    (and (looking-at "\\<module\\>")
			 (hol-light-looking-at-false-module))
		    (and (looking-at "\\<\\(sig\\|struct\\)\\>")
			 (hol-light-looking-at-false-sig-struct))
		    (and (looking-at "\\<type\\>")
			 (hol-light-looking-at-false-type))))
      (if (looking-at "\\<end\\>")
	  (hol-light-find-match)
	(if (not (bolp)) (hol-light-backward-char))
	(setq old-point (point))
	(hol-light-find-kwop hol-light-beginning-phrase-regexp)))
    (if (hol-light-at-phrase-break-p)
	(progn (end-of-line) (hol-light-skip-blank-and-comments)))
    (back-to-indentation)
    (point)))

(defun hol-light-search-forward-end-iter (begin current)
  (let ((found) (move t))
    (while (and move (> (point) current))
      (if (re-search-forward "\\<end\\>" (point-max) t)
	  (when (not (hol-light-in-literal-or-comment-p))
	    (let ((kwop) (iter))
	      (save-excursion
		(hol-light-backward-char 3)
		(setq kwop (hol-light-find-match))
		(cond
		 ((looking-at "\\<\\(object\\)\\>")
		  (hol-light-find-phrase-beginning))
		 ((and (looking-at "\\<\\(struct\\|sig\\)\\>")
		       (hol-light-looking-at-false-sig-struct))
		  (hol-light-find-phrase-beginning)))
		(if (> (point) begin)
		    (setq iter t)))
	      (cond
	       ((or iter
		    (and
		     (string= kwop "sig")
		     (looking-at "[ \t\n]*\\(\\<with\\>[ \t\n]*\\<type\\>\\|=\\)")))
		(if (> (point) current)
		    (setq current (point))
		  (setq found nil move nil)))
	       (t (setq found t move nil)))))
	(setq found nil move nil)))
    found))

(defun hol-light-search-forward-end ()
  (hol-light-search-forward-end-iter (point) -1))

(defconst hol-light-inside-block-opening "\\<\\(struct\\|sig\\|object\\)\\>")
(defconst hol-light-inside-block-opening-full
  (concat hol-light-inside-block-opening "\\|\\<\\(module\\|class\\)\\>"))
(defconst hol-light-inside-block-regexp
  (concat hol-light-matching-keyword-regexp "\\|" hol-light-inside-block-opening))
(defun hol-light-inside-block-find-kwop ()
  (let ((kwop (hol-light-find-kwop hol-light-inside-block-regexp
				"\\<\\(and\\|end\\)\\>")))
    (if (string= kwop "and") (setq kwop (hol-light-find-and-match)))
    (if (string= kwop "with") (setq kwop nil))
    (if (string= kwop "end")
	(progn
	  (hol-light-find-match)
	  (hol-light-find-kwop hol-light-inside-block-regexp)
	  (hol-light-inside-block-find-kwop))
      kwop)))

(defun hol-light-inside-block-p ()
  (if (hol-light-in-literal-or-comment-p)
      (hol-light-beginning-of-literal-or-comment))
  (let ((begin) (end) (and-end) (and-iter t) (kwop t))
    (save-excursion
      (if (looking-at "\\<and\\>")
	  (hol-light-find-and-match))
      (setq begin (point))
      (if (or (and (looking-at "\\<class\\>")
		   (save-excursion
		     (re-search-forward "\\<object\\>"
					(point-max) t)
		     (while (hol-light-in-literal-or-comment-p)
		       (re-search-forward "\\<object\\>"
					  (point-max) t))
		     (hol-light-find-phrase-beginning)
		     (> (point) begin)))
	      (and (looking-at "\\<module\\>")
		   (save-excursion
		     (re-search-forward "\\<\\(sig\\|struct\\)\\>"
					(point-max) t)
		     (while (hol-light-in-literal-or-comment-p)
		       (re-search-forward "\\<\\(sig\\|struct\\)\\>"
					  (point-max) t))
		     (hol-light-find-phrase-beginning)
		     (> (point) begin)))) ()
	(if (not (looking-at hol-light-inside-block-opening-full))
	    (setq kwop (hol-light-inside-block-find-kwop)))
	(if (not kwop) ()
	  (setq begin (point))
	  (if (not (hol-light-search-forward-end)) ()
	    (hol-light-backward-char 3)
	    (if (not (looking-at "\\<end\\>")) ()
	      (hol-light-forward-char 3)
	      (setq end (point))
	      (setq and-end (point))
	      (hol-light-skip-blank-and-comments)
	      (while (and and-iter (looking-at "\\<and\\>"))
		(setq and-end (point))
		(if (not (hol-light-search-forward-end)) ()
		  (hol-light-backward-char 3)
		  (if (not (looking-at "\\<end\\>")) ()
		    (hol-light-forward-char 3)
		    (setq and-end (point))
		    (hol-light-skip-blank-and-comments)))
		(if (<= (point) and-end)
		    (setq and-iter nil)))
	      (list begin end and-end))))))))

(defun hol-light-move-inside-block-opening ()
  "Go to the beginning of the enclosing module or class.

Notice that white-lines (or comments) located immediately before a
module/class are considered enclosed in this module/class."
  (interactive)
  (let* ((old-point (point))
	 (kwop (hol-light-inside-block-find-kwop)))
    (if (not kwop)
	(goto-char old-point))
    (hol-light-find-phrase-beginning)))

(defun hol-light-discover-phrase (&optional quiet)
  (end-of-line)
  (let ((end (point)) (case-fold-search nil))
    (hol-light-modify-syntax)
    (hol-light-find-phrase-beginning)
    (if (> (point) end) (setq end (point)))
    (save-excursion
      (let ((begin (point)) (cpt 0) (lines-left 0) (stop)
	    (inside-block (hol-light-inside-block-p))
	    (looking-block (looking-at hol-light-inside-block-opening-full)))
	(if (and looking-block inside-block)
	    (progn
	      (setq begin (nth 0 inside-block))
	      (setq end (nth 2 inside-block))
	      (goto-char end))
	  (if inside-block
	      (progn
		(setq stop (save-excursion (goto-char (nth 1 inside-block))
					   (beginning-of-line) (point)))
		(if (< stop end) (setq stop (point-max))))
	    (setq stop (point-max)))
	  (save-restriction
	    (goto-char end)
	    (while (and (= lines-left 0)
			(or (not inside-block) (< (point) stop))
			(<= (save-excursion
			      (hol-light-find-phrase-beginning)) end))
	      (if (not quiet)
		  (progn
		    (setq cpt (1+ cpt))
		    (if (= 8 cpt)
			(message "Looking for enclosing phrase..."))))
	      (setq end (point))
	      (hol-light-skip-to-end-of-phrase)
	      (beginning-of-line)
	      (narrow-to-region (point) (point-max))
	      (goto-char end)
	      (setq lines-left (forward-line 1)))))
	(if (>= cpt 8) (message "Looking for enclosing phrase... done."))
	(save-excursion (hol-light-skip-blank-and-comments) (setq end (point)))
	(hol-light-skip-back-blank-and-comments)
	(hol-light-restore-syntax)
	(list begin (point) end)))))

(defun hol-light-mark-phrase ()
  "Put mark at end of this Caml phrase, point at beginning.
The Caml phrase is the phrase just before the point."
  (interactive)
  (let ((pair (hol-light-discover-phrase)))
    (goto-char (nth 1 pair)) (push-mark (nth 0 pair) t t)))

(defun hol-light-next-phrase (&optional quiet)
  "Skip to the beginning of the next phrase."
  (interactive "i")
  (goto-char (save-excursion (nth 2 (hol-light-discover-phrase quiet))))
  (if (looking-at "\\<end\\>")
      (hol-light-next-phrase quiet))
  (if (looking-at ";;")
      (progn
	(forward-char 2)
	(hol-light-skip-blank-and-comments))))

(defun hol-light-previous-phrase ()
  "Skip to the beginning of the previous phrase."
  (interactive)
  (beginning-of-line)
  (hol-light-skip-to-end-of-phrase)
  (hol-light-discover-phrase))

(defun hol-light-indent-phrase ()
  "Depending of the context: justify and indent a comment,
or indent all lines in the current phrase."
  (interactive)
  (save-excursion
    (back-to-indentation)
    (if (hol-light-in-comment-p)
	(let* ((cobpoint (save-excursion
			   (hol-light-beginning-of-literal-or-comment)
			   (point)))
	       (begpoint (save-excursion
			   (while (and (> (point) cobpoint)
				       (hol-light-in-comment-p)
				       (not (looking-at "^[ \t]*$")))
			     (forward-line -1))
			   (max cobpoint (point))))
	       (coepoint (save-excursion
			   (while (hol-light-in-comment-p)
			     (re-search-forward "\\*)"))
			   (point)))
	       (endpoint (save-excursion
			   (re-search-forward "^[ \t]*$" coepoint 'end)
			   (beginning-of-line)
			   (forward-line 1)
			   (point)))
	       (leading-star (hol-light-leading-star-p)))
	  (goto-char begpoint)
	  (while (and leading-star
		      (< (point) endpoint)
		      (not (looking-at "^[ \t]*$")))
	    (forward-line 1)
	    (back-to-indentation)
	    (if (looking-at "\\*\\**\\([^)]\\|$\\)")
		(progn
		  (delete-char 1)
		  (setq endpoint (1- endpoint)))))
	  (goto-char (min (point) endpoint))
	  (fill-region begpoint endpoint)
	  (re-search-forward "\\*)")
	  (setq endpoint (point))
	  (if leading-star
	      (progn
		(goto-char begpoint)
		(forward-line 1)
		(if (< (point) endpoint)
		    (hol-light-auto-fill-insert-leading-star t))))
	  (indent-region begpoint endpoint nil))
      (let ((pair (hol-light-discover-phrase)))
	(indent-region (nth 0 pair) (nth 1 pair) nil)))))

(defun hol-light-find-alternate-file ()
  "Switch Implementation/Interface."
  (interactive)
  (let ((name (buffer-file-name)))
    (if (string-match "\\`\\(.*\\)\\.ml\\(i\\)?\\'" name)
	(find-file (concat (hol-light-match-string 1 name)
			   (if (match-beginning 2) ".ml" ".mli"))))))

(defun hol-light-insert-class-form ()
  "Insert a nicely formatted class-end form, leaving a mark after end."
  (interactive "*")
  (let ((prec (preceding-char))) 
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
        (insert " ")))
  (let ((old (point)))
    (insert "class  = object (self)\ninherit  as super\nend;;\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)))

(defun hol-light-insert-begin-form ()
  "Insert a nicely formatted begin-end form, leaving a mark after end."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "begin\n\nend\n")
    (end-of-line)
    (indent-region old (point) nil)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)))

(defun hol-light-insert-for-form ()
  "Insert a nicely formatted for-to-done form, leaving a mark after done."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "for  do\n\ndone\n")
    (end-of-line)
    (indent-region old (point) nil)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)
    (beginning-of-line 1)
    (backward-char 4)))

(defun hol-light-insert-while-form ()
  "Insert a nicely formatted for-to-done form, leaving a mark after done."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "while  do\n\ndone\n")
    (end-of-line)
    (indent-region old (point) nil)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)
    (beginning-of-line 1)
    (backward-char 4)))

(defun hol-light-insert-if-form ()
  "Insert a nicely formatted if-then-else form, leaving a mark after else."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "if\n\nthen\n\nelse\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)
    (forward-line -2)
    (indent-according-to-mode)))

(defun hol-light-insert-match-form ()
  "Insert a nicely formatted math-with form, leaving a mark after with."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "match\n\nwith\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)))

(defun hol-light-insert-let-form ()
  "Insert a nicely formatted let-in form, leaving a mark after in."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "let  in\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (beginning-of-line)
    (backward-char 4)
    (indent-according-to-mode)))

(defun hol-light-insert-try-form ()
  "Insert a nicely formatted try-with form, leaving a mark after with."
  (interactive "*")
  (let ((prec (preceding-char)))
    (if (and prec (not (char-equal ?\  (char-syntax prec))))
	(insert " ")))
  (let ((old (point)))
    (insert "try\n\nwith\n")
    (end-of-line)
    (indent-region old (point) nil)
    (indent-according-to-mode)
    (push-mark)
    (forward-line -2)
    (indent-according-to-mode)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                            HOL Light interactive mode

;; Augment HOL Light mode with a Caml toplevel.

(require 'comint)

(defvar hol-light-interactive-mode-map
  (let ((map (copy-keymap comint-mode-map)))
    (define-key map "|" 'hol-light-electric)
    (define-key map ")" 'hol-light-electric-rp)
    (define-key map "}" 'hol-light-electric-rc)
    (define-key map "]" 'hol-light-electric-rb)
    (define-key map "\C-c\C-i" 'hol-light-interrupt-caml)
    (define-key map "\C-c\C-k" 'hol-light-kill-caml)
    (define-key map "\C-c`" 'hol-light-interactive-next-error-toplevel)
    (define-key map "\C-c?" 'hol-light-interactive-next-error-toplevel)
    (define-key map "\C-m" 'hol-light-interactive-send-input)
    (define-key map "\C-j" 'hol-light-interactive-send-input-or-indent)
    (define-key map "\M-\C-m" 'hol-light-interactive-send-input-end-of-phrase)
    (define-key map [kp-enter] 'hol-light-interactive-send-input-end-of-phrase)
    map))

(defconst hol-light-interactive-buffer-name "*hol-light-toplevel*")

(defconst hol-light-interactive-toplevel-error-regexp
  "[ \t]*Characters \\([0-9]+\\)-\\([0-9]+\\):"
  "Regexp matching the char numbers in ocaml toplevel's error messages.")
(defvar hol-light-interactive-last-phrase-pos-in-source 0)
(defvar hol-light-interactive-last-phrase-pos-in-toplevel 0)

(defun hol-light-interactive-filter (text)
  (when (eq major-mode 'hol-light-interactive-mode)
    (save-excursion
      (when (>= comint-last-input-end comint-last-input-start)
	(if hol-light-interactive-read-only-input
	    (add-text-properties
	     comint-last-input-start comint-last-input-end
	     (list 'read-only t)))
	(if (and font-lock-mode hol-light-interactive-input-font-lock)
	    (progn
	      (font-lock-fontify-region comint-last-input-start
					comint-last-input-end)
	      (if (featurep 'sym-lock)
		  (sym-lock-make-symbols-atomic comint-last-input-start
						comint-last-input-end))))
	(if hol-light-interactive-output-font-lock
	    (save-excursion
	      (goto-char (point-max))
	      (re-search-backward comint-prompt-regexp
				  comint-last-input-end t)
	      (add-text-properties
	       comint-last-input-end (point)
	       '(face hol-light-font-lock-interactive-output-face))))
	(if hol-light-interactive-error-font-lock
	    (save-excursion
	      (goto-char comint-last-input-end)
	      (while (re-search-forward hol-light-interactive-error-regexp () t)
		(let ((matchbeg (match-beginning 1))
		      (matchend (match-end 1)))
		  (save-excursion
		    (goto-char matchbeg)
		    (put-text-property
		     matchbeg matchend
		     'face 'hol-light-font-lock-interactive-error-face)
		    (if (looking-at hol-light-interactive-toplevel-error-regexp)
			(let ((beg (string-to-number (hol-light-match-string 1)))
			      (end (string-to-number (hol-light-match-string 2))))
			  (put-text-property
			   (+ comint-last-input-start beg)
			   (+ comint-last-input-start end)
			   'face 'hol-light-font-lock-error-face)
			  )))))))))))

(define-derived-mode hol-light-interactive-mode comint-mode "HOL-Light-Interactive"
  "Major mode for interacting with a Caml process.
Runs a Caml toplevel as a subprocess of Emacs, with I/O through an
Emacs buffer. A history of input phrases is maintained. Phrases can
be sent from another buffer in Caml mode.

Special keys for HOL Light interactive mode:\\{hol-light-interactive-mode-map}"
  (hol-light-install-font-lock t)
  (if (or hol-light-interactive-input-font-lock
	  hol-light-interactive-output-font-lock
	  hol-light-interactive-error-font-lock)
      (font-lock-mode 1))
  (add-hook 'comint-output-filter-functions 'hol-light-interactive-filter)
  (if (not (boundp 'after-change-functions)) ()
    (make-local-hook 'after-change-functions)
    (remove-hook 'after-change-functions 'font-lock-after-change-function t))
  (if (not (boundp 'pre-idle-hook)) ()
    (make-local-hook 'pre-idle-hook)
    (remove-hook 'pre-idle-hook 'font-lock-pre-idle-hook t))
  (setq comint-prompt-regexp "^#  *")
  (setq comint-process-echoes nil)
  (setq comint-get-old-input 'hol-light-interactive-get-old-input)
  (setq comint-scroll-to-bottom-on-output t)
  (set-syntax-table hol-light-mode-syntax-table)
  (setq local-abbrev-table hol-light-mode-abbrev-table)

  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'hol-light-indent-command)

  (easy-menu-add hol-light-interactive-mode-menu)
  (hol-light-update-options-menu))

(defun hol-light-run-caml ()
  "Run a Caml toplevel process. I/O via buffer `*hol-light-toplevel*'."
  (interactive)
  (hol-light-run-process-if-needed)
  (when hol-light-display-buffer-on-eval
    (display-buffer hol-light-interactive-buffer-name)))

(defun hol-light-run-process-if-needed (&optional cmd)
  "Run a Caml toplevel process if needed, with an optional command name.
I/O via buffer `*hol-light-toplevel*'."
  (if cmd
      (setq hol-light-interactive-program cmd)
    (if (not (comint-check-proc hol-light-interactive-buffer-name))
	(setq hol-light-interactive-program
	      (read-shell-command "Caml toplevel to run: "
				  hol-light-interactive-program))))
  (if (not (comint-check-proc hol-light-interactive-buffer-name))
      (let ((cmdlist (hol-light-args-to-list hol-light-interactive-program))
            (process-connection-type nil))
	(set-buffer (apply (function make-comint) "hol-light-toplevel"
			   (car cmdlist) nil (cdr cmdlist)))
	(hol-light-interactive-mode)
	(sleep-for 1))))

(defun hol-light-args-to-list (string)
  (let ((where (string-match "[ \t]" string)))
    (cond ((null where) (list string))
	  ((not (= where 0))
	   (cons (substring string 0 where)
		 (hol-light-args-to-list (substring string (+ 1 where)
						 (length string)))))
	  (t (let ((pos (string-match "[^ \t]" string)))
	       (if (null pos)
		   nil
		 (hol-light-args-to-list (substring string pos
						 (length string)))))))))

(defun hol-light-interactive-get-old-input ()
  (save-excursion
    (let ((end (point)))
      (re-search-backward comint-prompt-regexp (point-min) t)
      (if (looking-at comint-prompt-regexp)
	  (re-search-forward comint-prompt-regexp))
      (buffer-substring-no-properties (point) end))))

(defun hol-light-interactive-end-of-phrase ()
  (save-excursion
    (end-of-line)
    (hol-light-find-meaningful-word)
    (hol-light-find-meaningful-word)
    (looking-at ";;")))

(defun hol-light-interactive-send-input-end-of-phrase ()
  (interactive)
  (goto-char (point-max))
  (if (not (hol-light-interactive-end-of-phrase))
      (insert ";;"))
  (comint-send-input))

(defconst hol-light-interactive-send-warning
  "Note: toplevel processing requires a terminating `;;'")

(defun hol-light-interactive-send-input ()
  "Process if the current line ends with `;;' then send the
current phrase else insert a newline."
  (interactive)
  (if (hol-light-interactive-end-of-phrase)
      (progn
	(comint-send-input)
	(goto-char (point-max)))
    (insert "\n")
    (message hol-light-interactive-send-warning)))

(defun hol-light-interactive-send-input-or-indent ()
  "Process if the current line ends with `;;' then send the
current phrase else insert a newline and indent."
  (interactive)
  (if (hol-light-interactive-end-of-phrase)
      (progn
	(goto-char (point-max))
	(comint-send-input))
    (insert "\n")
    (indent-according-to-mode)
    (message hol-light-interactive-send-warning)))

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
      (goto-char end)
      (if (string= text "")
	  (message "Cannot send empty commands to Caml toplevel!")
	(set-buffer hol-light-interactive-buffer-name)
	(goto-char (point-max))
	(setq hol-light-interactive-last-phrase-pos-in-toplevel (point))
	(comint-send-string hol-light-interactive-buffer-name
			    (concat text ";;"))
	(let ((pos (point)))
	  (comint-send-input)
	  (if hol-light-interactive-echo-phrase
	      (save-excursion
		(goto-char pos)
		(insert (concat text ";;")))))))
    (when hol-light-display-buffer-on-eval
      (display-buffer hol-light-interactive-buffer-name))))

(defun hol-light-narrow-to-phrase ()
  "Narrow the editting window to the surrounding Caml phrase (or block)."
  (interactive)
  (save-excursion
    (let ((pair (hol-light-discover-phrase)))
      (narrow-to-region (nth 0 pair) (nth 1 pair)))))

(defun hol-light-eval-phrase ()
  "Eval the surrounding Caml phrase (or block) in the Caml toplevel."
  (interactive)
  (let ((end))
    (save-excursion
      (let ((pair (hol-light-discover-phrase)))
	(setq end (nth 2 pair))
	(hol-light-eval-region (nth 0 pair) (nth 1 pair))))
    (if hol-light-skip-after-eval-phrase
	(goto-char end))))

(defun hol-light-eval-buffer ()
  "Send the buffer to the HOL Light Interactive process."
  (interactive)
  (hol-light-eval-region (point-min) (point-max)))

(defun hol-light-interactive-next-error-source ()
  (interactive)
  (let ((error-pos) (beg 0) (end 0))
    (save-excursion
      (set-buffer hol-light-interactive-buffer-name)
      (goto-char hol-light-interactive-last-phrase-pos-in-toplevel)
      (setq error-pos
	    (re-search-forward hol-light-interactive-toplevel-error-regexp
			       (point-max) t))
      (if error-pos
	  (progn
	    (setq beg (string-to-number (hol-light-match-string 1))
		  end (string-to-number (hol-light-match-string 2))))))
    (if (not error-pos)
	(message "No syntax or typing error in last phrase.")
      (setq beg (+ hol-light-interactive-last-phrase-pos-in-source beg)
	    end (+ hol-light-interactive-last-phrase-pos-in-source end))
      (goto-char beg)
      (put-text-property beg end 'face 'hol-light-font-lock-error-face))))

(defun hol-light-interactive-next-error-toplevel ()
  (interactive)
  (let ((error-pos) (beg 0) (end 0))
    (save-excursion
      (goto-char hol-light-interactive-last-phrase-pos-in-toplevel)
      (setq error-pos
	    (re-search-forward hol-light-interactive-toplevel-error-regexp
			       (point-max) t))
      (if error-pos
	  (setq beg (string-to-number (hol-light-match-string 1))
		end (string-to-number (hol-light-match-string 2)))))
    (if (not error-pos)
	(message "No syntax or typing error in last phrase.")
      (setq beg (+ hol-light-interactive-last-phrase-pos-in-toplevel beg)
	    end (+ hol-light-interactive-last-phrase-pos-in-toplevel end))
      (put-text-property beg end 'face 'hol-light-font-lock-error-face)
      (goto-char beg))))

(defun hol-light-interrupt-caml ()
  (interactive)
  (if (comint-check-proc hol-light-interactive-buffer-name)
      (save-excursion
	(set-buffer hol-light-interactive-buffer-name)
	(comint-interrupt-subjob))))

(defun hol-light-kill-caml ()
  (interactive)
  (if (comint-check-proc hol-light-interactive-buffer-name)
      (save-excursion
	(set-buffer hol-light-interactive-buffer-name)
	(comint-kill-subjob))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                               Menu support

(defun hol-light-about () (interactive)
  (describe-variable 'hol-light-mode-version))
(defun hol-light-help () (interactive)
  (describe-function 'hol-light-mode))
(defun hol-light-interactive-help () (interactive)
  (describe-function 'hol-light-interactive-mode))

(defvar hol-light-definitions-menu-last-buffer nil)
(defvar hol-light-definitions-keymaps nil)

(defun hol-light-build-menu ()
  (easy-menu-define
   hol-light-mode-menu (list hol-light-mode-map)
   "HOL Light Mode Menu."
   '("HOL Light"
     ("Interactive Mode"
      ["Run Caml Toplevel" hol-light-run-caml t]
      ["Interrupt Caml Toplevel" hol-light-interrupt-caml
       :active (comint-check-proc hol-light-interactive-buffer-name)]
      ["Kill Caml Toplevel" hol-light-kill-caml
       :active (comint-check-proc hol-light-interactive-buffer-name)]
      ["Evaluate Region" hol-light-eval-region
       ;; Region-active-p for XEmacs and mark-active for Emacs
       :active (if (fboundp 'region-active-p) (region-active-p) mark-active)]
      ["Evaluate Phrase" hol-light-eval-phrase t]
      ["Evaluate Buffer" hol-light-eval-buffer t])
     ("Caml Forms"
      ["try .. with .." hol-light-insert-try-form t]
      ["match .. with .." hol-light-insert-match-form t]
      ["let .. in .." hol-light-insert-let-form t]
      ["if .. then .. else .." hol-light-insert-if-form t]
      ["while .. do .. done" hol-light-insert-while-form t]
      ["for .. do .. done" hol-light-insert-for-form t]
      ["begin .. end" hol-light-insert-begin-form t])
     ["Switch .ml/.mli" hol-light-find-alternate-file t]
     "---"
     ["Compile..." compile t]
     ["Reference Manual..." hol-light-browse-manual t]
     ["Caml Library..." hol-light-browse-library t]
     ("Definitions"
      ["Scan..." hol-light-list-definitions t])
     "---"
     [ "Show type at point" caml-types-show-type
       hol-light-with-caml-mode-p]
     "---"
     [ "Complete identifier" caml-complete
       hol-light-with-caml-mode-p]
     [ "Help for identifier" caml-help
       hol-light-with-caml-mode-p]
     [ "Add path for documentation" ocaml-add-path
       hol-light-with-caml-mode-p]
     [ "Open module for documentation" ocaml-open-module
       hol-light-with-caml-mode-p]
     [ "Close module for documentation" ocaml-close-module
       hol-light-with-caml-mode-p]
     "---"
     ["Customize HOL Light Mode..." (customize-group 'hol-light) t]
     ("HOL Light Options" ["Dummy" nil t])
     ("HOL Light Interactive Options" ["Dummy" nil t])
     "---"
     ["About" hol-light-about t]
     ["Help" hol-light-help t]))
  (easy-menu-add hol-light-mode-menu)
  (hol-light-update-options-menu)
  ;; Save and update definitions menu
  (if hol-light-with-xemacs
      (add-hook 'activate-menubar-hook 'hol-light-update-definitions-menu)
    (if (not (functionp 'easy-menu-create-keymaps)) ()
      ;; Patch for Emacs
      (add-hook 'menu-bar-update-hook
		'hol-light-with-emacs-update-definitions-menu)
      (make-local-variable 'hol-light-definitions-keymaps)
      (setq hol-light-definitions-keymaps
	    (cdr (easy-menu-create-keymaps
		  "Definitions" hol-light-definitions-menu)))
      (setq hol-light-definitions-menu-last-buffer nil))))

(easy-menu-define
  hol-light-interactive-mode-menu hol-light-interactive-mode-map
  "HOL Light Interactive Mode Menu."
  '("HOL Light"
    ("Interactive Mode"
     ["Run Caml Toplevel" hol-light-run-caml t]
     ["Interrupt Caml Toplevel" hol-light-interrupt-caml
      :active (comint-check-proc hol-light-interactive-buffer-name)]
     ["Kill Caml Toplevel" hol-light-kill-caml
      :active (comint-check-proc hol-light-interactive-buffer-name)]
     ["Evaluate Region" hol-light-eval-region :active (region-active-p)]
     ["Evaluate Phrase" hol-light-eval-phrase t]
     ["Evaluate Buffer" hol-light-eval-buffer t])
    "---"
    ["Customize HOL Light Mode..." (customize-group 'hol-light) t]
    ("HOL Light Options" ["Dummy" nil t])
    ("HOL Light Interactive Options" ["Dummy" nil t])
    "---"
    ["About" hol-light-about t]
    ["Help" hol-light-interactive-help t]))

(defun hol-light-update-definitions-menu ()
  (if (eq major-mode 'hol-light-mode)
      (easy-menu-change
       '("HOL Light") "Definitions"
       hol-light-definitions-menu)))

(defun hol-light-with-emacs-update-definitions-menu ()
  (if (current-local-map)
      (let ((keymap
	     (lookup-key (current-local-map) [menu-bar HOL Light Definitions])))
	(if (and
	     (keymapp keymap)
	     (not (eq hol-light-definitions-menu-last-buffer (current-buffer))))
	    (setcdr keymap hol-light-definitions-keymaps)
	  (setq hol-light-definitions-menu-last-buffer (current-buffer))))))

(defun hol-light-toggle-option (symbol)
  (interactive)
  (set symbol (not (symbol-value symbol)))
  (if (eq 'hol-light-use-abbrev-mode symbol)
      (abbrev-mode hol-light-use-abbrev-mode)) ; toggle abbrev minor mode
  (if hol-light-with-xemacs nil (hol-light-update-options-menu)))

(defun hol-light-update-options-menu ()
  (easy-menu-change
   '("HOL Light") "HOL Light Options"
   (mapcar (lambda (pair)
	     (if (consp pair)
		 (vector (car pair)
			 (list 'hol-light-toggle-option (cdr pair))
			 ':style 'toggle
			 ':selected (nth 1 (cdr pair))
			 ':active t)
	       pair)) hol-light-options-list))
  (easy-menu-change
   '("HOL Light") "HOL Light Interactive Options"
   (mapcar (lambda (pair)
	     (if (consp pair)
		 (vector (car pair)
			 (list 'hol-light-toggle-option (cdr pair))
			 ':style 'toggle
			 ':selected (nth 1 (cdr pair))
			 ':active t)
	       pair)) hol-light-interactive-options-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Browse Manual

;; From M. Quercia

(defun hol-light-browse-manual ()
  "*Browse Caml reference manual."
  (interactive)
  (setq hol-light-manual-url (read-from-minibuffer "URL: " hol-light-manual-url))
  (funcall hol-light-browser hol-light-manual-url))

(defun hol-light-xemacs-w3-manual (url)
  "*Browse Caml reference manual."
  (w3-fetch-other-frame url))

(defun hol-light-netscape-manual (url)
  "*Browse Caml reference manual."
  (start-process-shell-command
   "netscape" nil
   (concat "netscape -remote 'openURL ("
	   url ", newwindow)' || netscape " url)))

(defun hol-light-mmm-manual (url)
  "*Browse Caml reference manual."
  (start-process-shell-command
   "mmm" nil
   (concat "mmm_remote " url " || mmm -external " url)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Browse Library

;; From M. Quercia

(defun hol-light-browse-library()
  "Browse the Caml library."
  (interactive)
  (let ((buf-name "*caml-library*") (opoint)
	(dir (read-from-minibuffer "Library path: " hol-light-library-path)))
    (if (and (file-directory-p dir) (file-readable-p dir))
	(progn
	  (setq hol-light-library-path dir)
	  ;; List *.ml and *.mli files
	  (with-output-to-temp-buffer buf-name
	    (buffer-disable-undo standard-output)
	    (save-excursion
	      (set-buffer buf-name)
	      (kill-all-local-variables)
	      (make-local-variable 'hol-light-library-path)
	      (setq hol-light-library-path dir)
	      ;; Help
	      (insert "Directory \"" dir "\".\n") 
	      (insert "Select a file with middle mouse button or RETURN.\n\n")
	      (insert "Interface files (.mli):\n\n")
	      (insert-directory (concat dir "/*.mli") "-C" t nil)
	      (insert "\n\nImplementation files (.ml):\n\n")
	      (insert-directory (concat dir "/*.ml") "-C" t nil)
	      ;; '.', '-' and '_' are now letters
	      (modify-syntax-entry ?. "w")
	      (modify-syntax-entry ?_ "w")
	      (modify-syntax-entry ?- "w")
	      ;; Every file name is now mouse-sensitive
	      (goto-char (point-min))
	      (while (< (point) (point-max))
		(re-search-forward "\\.ml.?\\>")
		(setq opoint (point))
		(re-search-backward "\\<" (point-min) 1)
		(put-text-property (point) opoint 'mouse-face 'highlight)
		(goto-char (+ 1 opoint)))
	      ;; Activate hol-light-library mode
	      (setq major-mode 'hol-light-library-mode)
	      (setq mode-name "hol-light-library")
	      (use-local-map hol-light-library-mode-map)
	      (setq buffer-read-only t)))))))
  
(defvar hol-light-library-mode-map
  (let ((map (make-keymap)))
    (suppress-keymap map)
    (define-key map [return] 'hol-light-library-find-file)
    (define-key map [mouse-2] 'hol-light-library-mouse-find-file)
    map))

(defun hol-light-library-find-file ()
  "Load the file whose name is near point."
  (interactive)
  (save-excursion
    (if (text-properties-at (point))
	(let (beg)
	  (re-search-backward "\\<") (setq beg (point))
	  (re-search-forward "\\>")
	  (find-file-read-only (concat hol-light-library-path "/"
				       (buffer-substring-no-properties
					beg (point))))))))

(defun hol-light-library-mouse-find-file (event)
  "Visit the file name you click on."
  (interactive "e")
  (let ((owindow (selected-window)))
    (mouse-set-point event)
    (hol-light-library-find-file)
    (select-window owindow)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Definitions List

;; Designed from original code by M. Quercia

(defconst hol-light-definitions-regexp
  "\\<\\(and\\|val\\|type\\|module\\|class\\|exception\\|let\\)\\>"
  "Regexp matching definition phrases.")

(defconst hol-light-definitions-bind-skip-regexp
  (concat "\\<\\(rec\\|type\\|virtual\\)\\>\\|'[" hol-light-alpha "][0-9_'"
	  hol-light-alpha "]*\\|('.*)")
  "Regexp matching stuff to ignore after a binding keyword.")

(defvar hol-light-definitions-menu (list ["Scan..." hol-light-list-definitions t])
  "Initial content of the definitions menu.")
(make-variable-buffer-local 'hol-light-definitions-menu)

(defun hol-light-list-definitions ()
  "Parse the buffer and gather toplevel definitions for quick
jump via the definitions menu."
  (interactive)
  (message "Searching definitions...")
  (save-excursion
    (let ((cpt 0) (kw) (menu) (scan-error)
	  (value-list) (type-list) (module-list) (class-list) (misc-list))
      (goto-char (point-min))
      (hol-light-skip-blank-and-comments)
      (while (and (< (point) (point-max)) (not scan-error))
	(if (looking-at hol-light-definitions-regexp)
	    (progn
	      (setq kw (hol-light-match-string 0))
	      (if (string= kw "and")
		  (setq kw (save-match-data
			     (save-excursion (hol-light-find-and-match)))))
	      (if (or (string= kw "exception")
		      (string= kw "val")) (setq kw "let"))
	      ;; Skip optional elements
	      (goto-char (match-end 0))
	      (hol-light-skip-blank-and-comments)
	      (if (looking-at hol-light-definitions-bind-skip-regexp)
		  (goto-char (match-end 0)))
	      (hol-light-skip-blank-and-comments)
	      (if (looking-at
		   (concat "\\<[" hol-light-alpha "][0-9_'" hol-light-alpha "]*\\>"))
		  ;; Menu item : [name (goto-char ...) t]
		  (let* ((p (make-marker))
			 (ref (vector (hol-light-match-string 0)
				      (list 'hol-light-goto p) t)))
		    (setq cpt (1+ cpt))
		    (message (concat "Searching definitions... ("
				     (number-to-string cpt) ")"))
		    (set-marker p (point))
		    (cond
		     ((string= kw "let")
		      (setq value-list (cons ref value-list)))
		     ((string= kw "type")
		      (setq type-list (cons ref type-list)))
		     ((string= kw "module")
		      (setq module-list (cons ref module-list)))
		     ((string= kw "class")
		      (setq class-list (cons ref class-list)))
		     (t (setq misc-list (cons ref misc-list))))))))
	;; Skip to next phrase or next top-level `and'
	(hol-light-forward-char)
	(let ((old-point (point)) (last-and))
	  (hol-light-next-phrase t)
	  (setq last-and (point))
	  (if (< last-and old-point)
	      (setq scan-error t)
	    (save-excursion
	      (while (and (re-search-backward "\\<and\\>" old-point t)
			  (not (hol-light-in-literal-or-comment-p))
			  (save-excursion (hol-light-find-and-match)
					  (>= old-point (point))))
		(setq last-and (point)))))
	  (goto-char last-and)))
      (if scan-error
	  (message "Parse error when scanning definitions: line %s!"
		   (if hol-light-with-xemacs
		       (line-number)
		     (1+ (count-lines 1 (point)))))
	;; Sort and build lists
	(mapcar (lambda (pair)
		  (if (cdr pair)
		      (setq menu
			    (append (hol-light-split-long-list
				     (car pair) (hol-light-sort-definitions (cdr pair)))
				    menu))))
		(list (cons "Miscellaneous" misc-list)
		      (cons "Values" value-list)
		      (cons "Classes" class-list)
		      (cons "Types" type-list)
		      (cons "Modules" module-list)))
	;; Update definitions menu
	(setq hol-light-definitions-menu
	      (append menu (list "---"
				 ["Rescan..." hol-light-list-definitions t])))
	(if (or hol-light-with-xemacs
		(not (functionp 'easy-menu-create-keymaps))) ()
	  ;; Patch for Emacs
	  (setq hol-light-definitions-keymaps
		(cdr (easy-menu-create-keymaps 
		      "Definitions" hol-light-definitions-menu)))
	  (setq hol-light-definitions-menu-last-buffer nil))
	(message "Searching definitions... done"))))
  (hol-light-update-definitions-menu))

(defun hol-light-goto (pos)
  (goto-char pos)
  (recenter))

(defun hol-light-sort-definitions (list)
  (let* ((last "") (cpt 1)
	 (list (sort (nreverse list)
		     (lambda (p q) (string< (elt p 0) (elt q 0)))))
	 (tail list))
    (while tail
      (if (string= (elt (car tail) 0) last)
	  (progn
	    (setq cpt (1+ cpt))
	    (aset (car tail) 0 (format "%s (%d)" last cpt)))
	(setq cpt 1)
	(setq last (elt (car tail) 0)))
      (setq tail (cdr tail)))
    list))

;; Look for the (n-1)th or last element of a list
(defun hol-light-nth (n list)
  (if (or (<= n 1) (null list) (null (cdr list))) list
    (hol-light-nth (1- n) (cdr list))))
    
;; Split a definition list if it is too long
(defun hol-light-split-long-list (title list)
  (let ((tail (hol-light-nth hol-light-definitions-max-items list)))
    (if (or (null tail) (null (cdr tail)))
        ;; List not too long, cons the title
        (list (cons title list))
      ;; List too long, split and add initials to the title
      (let (lists)
        (while list
          (let ((beg (substring (elt (car list) 0) 0 1))
                (end (substring (elt (car tail) 0) 0 1)))
            (setq lists (cons
                         (cons (format "%s %s-%s" title beg end) list)
                         lists))
            (setq list (cdr tail))
            (setcdr tail nil)
            (setq tail (hol-light-nth hol-light-definitions-max-items list))))
        (nreverse lists)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                             Hooks and Exit

(condition-case nil
    (progn (require 'speedbar)
	   (speedbar-add-supported-extension
	    '(".ml" ".mli" ".mll" ".mly")))
  (error nil))

(defvar hol-light-load-hook nil
  "This hook is run when HOL Light is loaded in. It is a good place to put
key-bindings or hack Font-Lock keywords...")

(run-hooks 'hol-light-load-hook)

(provide 'hol-light)
;; For compatibility with caml support modes
;; you may also link caml.el to hol-light.el
(provide 'caml)


