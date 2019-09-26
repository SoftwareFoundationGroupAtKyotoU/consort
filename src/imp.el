;(require 'smie)

(defconst imp-mode-syntax-table
  (let ((st (make-syntax-table)))
	(modify-syntax-entry ?_ "_")
	(modify-syntax-entry ?\( "()" st)
    (modify-syntax-entry ?\) ")(" st)
	(modify-syntax-entry ?* ". 23b" st)
	(modify-syntax-entry ?/ ". 124" st)
	(modify-syntax-entry ?{ "(}" st)
	(modify-syntax-entry ?} "){" st)
	(modify-syntax-entry ?\n ">" st)
	(modify-syntax-entry ?: "_" st)
    st))

(defvar imp-highlights nil "first element for `font-lock-defaults'")

(setq imp-highlights
      '(("\\blet\\b\\|\\bmkarray\\b\\|\\bmkref\\b\\|\\bif\\b\\|\\bthen\\b\\|\\belse\\b\\|\\bifnull\\b\\|\\bin\\b\\|\\bassert\\b\\|\\balias\\b" . font-lock-keyword-face)
        ("\\btrue\\b\\|\\bfalse\\b\\|\\bnull\\b\\|\\blength\\b\\|\\b[0-9]+\\b" . font-lock-constant-face)))

; lifted ("inspired") heavily by tuareg
;; (defun imp-skip-blank-and-comments ()
;;   (forward-comment (point-max)))

;; (defconst imp-float-cont-re "\\.[0-9]*")

;; (defconst imp-float-full-re "-?[0-9]+\\.[0-9]*")

;; (defun imp--smie-forward-token ()
;;   (imp-skip-blank-and-comments)
;;   (let ((start (point)))
;; 	(if (zerop (skip-syntax-forward ".()"))
;; 		;; no symbol found
;; 		(progn
;; 		  (skip-syntax-forward "w_")
;; 		  (and
;; 		   (looking-at imp-float-cont-re)
;; 		   (goto-char (match-end 0))))
;; 	  nil)
;; 	(buffer-substring-no-properties start (point))))

;; (defun imp-lift-token (arg)
;;   (cond
;;    ((or (eq "<-" arg) (eq arg ":=") (eq arg "=")) arg)
;;    ((and
;; 	 (string-match "[+-*/%<>=!&^|#@]+" arg)
;; 	 (= (match-beginning 0) 0)) "<=>")
;;    (t arg)))

;; (defun imp--smie-backward-token ()
;;   (forward-comment (- (point)))
;;   (let ((end (point)))
;; 	(if (zerop (skip-syntax-backward ".()"))
;; 		;; no symbol found
;; 		(progn 
;; 		  (skip-syntax-backward "w_")
;; 		  (and
;; 		   (= (char-before) ?.)
;; 		   (save-excursion
;; 			 (forward-char -1)
;; 			 (skip-syntax-backward "w_")
;; 			 (looking-at imp-float-full-re))
;; 		   (goto-char (match-beginning 0))))
;; 	  nil)
;; 	(buffer-substring-no-properties (point) end)))

;; (defun imp-smie-forward-token ()
;;   (imp-lift-token (imp--smie-forward-token)))

;; (defun imp-smie-backward-token ()
;;   (imp-lift-token (imp--smie-backward-token)))

;; (defconst imp-smie-grammar
;;   (smie-prec2->grammar
;;    (smie-bnf->prec2
;; 	'((id)
;; 	  (expr
;; 	   (lhs)
;; 	   ("()")
;; 	   ("if" lhs "then" expr "else" expr)
;; 	   ("ifnull" id "then" expr "else" expr)
;; 	   (id ":=" lhs)
;; 	   ("alias" "(" id "=" aliaslhs ")")
;; 	   ("let" lhs "=" lhs "in" expr)
;; 	   ("assert" "(" lhs ")")
;; 	   (id "[" lhs "]" "<-" lhs)
;; 	   ("{" expr "}")
;; 	   ("$gamma" "{" tyenv "}")
;; 	   (expr ";" expr))

;; 	  (fundef
;; 	   (id "()" expr)
;; 	   (id "(" arglist ")" expr))
;; 	  (arglist
;; 	   (lhs "," lhs)
;; 	   (lhs))
;; 	  (lhs
;; 	   (id)
;; 	   ("*" lhs)
;; 	   ("(" arglist ")")
;; 	   (lhs "=" lhs) (lhs "<=>" lhs)
;; 	   ("(" lhs ")")
;; 	   (lhs "[" lhs "]"))
;; 	  (tyenv
;; 	   (tybind ";" tybind)
;; 	   (tybind))
;; 	  (aliaslhs
;; 	   ("(" lhs ")" "." id)
;; 	   (lhs))
;; 	  (tybind
;; 	   (id ":" typ))
;; 	  (typ
;; 	   (refine "int")
;; 	   (typ "ref" id)
;; 	   ("(" tuptype ")"))
;; 	  (refine
;; 	   ("T")
;; 	   (refine "/\\" refine)
;; 	   (id "<=>" id)
;; 	   (id "=" id))
;; 	  (tuptype
;; 	   (tybind "," tybind)
;; 	   (tybind))
;; 	  )
;; 	'((assoc ";"))
;; 	'((assoc ","))
;; 	'((assoc "="))
;; 	'((assoc "<=>")))))

(define-derived-mode imp-mode prog-mode "Imp Mode"
  :syntax-table imp-mode-syntax-table
  (progn
	(setq font-lock-defaults '(imp-highlights))
	;; (smie-setup imp-smie-grammar 
    ;;           :forward-token #'imp-smie-forward-token
    ;;           :backward-token #'imp-smie-backward-token)
	))
