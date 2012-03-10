;; (put 'func 'lisp-indent-function 1)
;; (put 'match 'lisp-indent-function 1)
;; (put 'if 'lisp-indent-function 0)
;; (put 'begin 'lisp-indent-function 0)

(defun lumgua-compile-file ()
  (interactive)
  (when (null lumgua-path)
    (error "You must set lumgua-path"))
  (let ((name (buffer-name)))
    (let ((end (string-match "\\.lisp" name)))
      (when (and (numberp end) (> end 0))
	(shell-command (concat "echo '(compilefile \""
			       (substring name 0 end)
			       "\")' | ./lispin"))))))

(defvar lumgua-path nil
  "The path of the directory containing `lispin'.")

(defun lumgua-lispin ()
  (if (null lumgua-path)
      (error "You must set lumgua-path")
    (concat lumgua-path "/lispin")))

(defun lumgua-eval-region (begin end)
  (shell-command-on-region begin end (lumgua-lispin)))

(defun lumgua-eval-defun ()
  (interactive)
  (save-excursion
    (end-of-defun)
    (let ((end (point)))
      (beginning-of-defun)
      (lumgua-eval-region (point) end))))

(defun lumgua-eval-last-sexp ()
  (interactive)
  (let ((end (point)))
    (save-excursion
      (backward-sexp)
      (lumgua-eval-region (point) end))))

(defun lumgua-indent-defun ()
  (interactive)
  (save-excursion
    (mark-defun)
    (indent-region (point) (mark))))
