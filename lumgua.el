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
