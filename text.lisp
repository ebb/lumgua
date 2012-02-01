(define strextend
  (func (cell . strs)
    (cellput cell (apply strcat (cons (cellget cell) strs)))))

(define streamnew
  (func (s)
    (let ((i (cellnew 0))
	  (n (strlength s)))
      (func (msg)
	(let ((j (cellget i)))
	  (cond
	   ((= msg 'peek)
	    (if (< j n)
		(strget s j)
	      nil))
	   ((= msg 'advance)
	    (cond
	     ((< j n)
	      (cellput i (+ 1 j)))))
	   (t
	    (throw "unknown stream message"))))))))

(define readall
  (func (s)
    (let ((stream (streamnew s)))
      (reverse (call/cc
		(func (esc)
		  (let ((exps (cellnew nil)))
		    (loop (func ()
			    (skipws stream)
			    (cond
			     ((stream 'peek)
			      (cellput exps (cons (read stream)
						  (cellget exps))))
			     (t (esc (cellget exps)))))))))))))

(define skipws
  (func (stream)
    (let ((c (stream 'peek)))
      (cond
       (c (cond
	   ((whitespacep c)
	    (stream 'advance)
	    (skipws stream))
	   ((= c ";")
	    (nextline stream)
	    (skipws stream))))))))

(define whitespacep
  (func (c)
    (substringp c " \t\n")))

(define nextline
  (func (stream)
    (let ((c (stream 'peek)))
      (cond
       ((and c (!= c "\n"))
	(stream 'advance)
	(nextline stream))))))

(define read
  (func (stream)
    (skipws stream)
    (let ((c (stream 'peek))
	  (table (list (list "`" readquasi)
		       (list "," readcomma)
		       (list "(" readlist)
		       (list "'" readquote)
		       (list "\"" readstring))))
      (cond
       ((nilp c)
	(throw "read: incomplete input")))
      (cond
       ((= c ")")
	(throw "read: unbalanced \")\"")))
      (let ((reader (lookup c table)))
	(if reader
	    (begin (stream 'advance)
		   (reader stream))
	  (readatom stream))))))

(define readquasi
  (func (stream)
    (list 'quasiquote (read stream))))

(define readcomma
  (func (stream)
    (let ((c (stream 'peek)))
      (cond
       ((nilp c)
	(throw "read: syntax error")))
      (cond
       ((= c "@")
	(stream 'advance)
	(list 'unquotesplicing (read stream)))
       (t (list 'unquote (read stream)))))))

(define readlist
  (func (stream)
    (call/cc
     (func (esc)
       (let ((exps (cellnew nil)))
	 (loop (func ()
		 (skipws stream)
		 (cond
		  ((not (stream 'peek))
		   (throw "read: unmatched \"(\"")))
		 (let ((c (stream 'peek)))
		   (cond
		    ((= c ")")
		     (stream 'advance)
		     (esc (reverse (cellget exps))))
		    ((= c ".")
		     (stream 'advance)
		     (cond
		      ((nilp (cellget exps))
		       (throw "read: ill-formed dotted list")))
		     (let ((finalform (read stream)))
		       (skipws stream)
		       (let ((c (stream 'peek)))
			 (cond
			  ((!= c ")")
			   (throw "read: ill-formed dotted list"))
			  (t
			   (stream 'advance)
			   (esc (append (reverse (cdr (cellget exps)))
					(cons (car (cellget exps))
					      finalform))))))))
		    (t (cellput exps
				(cons (read stream)
				      (cellget exps)))))))))))))

(define readquote
  (func (stream)
    (list 'quote (read stream))))

(define readstring
  (func (stream)
    (call/cc
     (func (esc)
       (let ((content (cellnew "")))
	 (let ((pushchar
		(func (c)
		  (stream 'advance)
		  (strextend content c))))
	   (loop (func ()
		   (let ((c (stream 'peek)))
		     (cond
		      ((nilp c)
		       (throw "read: unterminated string"))
		      ((= c "\"")
		       (stream 'advance)
		       (esc (cellget content)))
		      ((= c "\\")
		       (stream 'advance)
		       (let ((c (stream 'peek)))
			 (cond
			  ((nilp c) (throw "unterminated string"))
			  ((= c "t") (pushchar "\t"))
			  ((= c "n") (pushchar "\n"))
			  ((= c "\\") (pushchar "\\"))
			  ((= c "\"") (pushchar "\""))
			  (t (throw (strcat "read: unknown escape: \\" c))))))
		      (t (pushchar c))))))))))))

(define readatom
  (func (stream)
    (let ((terminators "()'\" \t\n"))
      (let ((str (call/cc
		  (func (esc)
		    (let ((buf (cellnew "")))
		      (loop (func ()
			      (let ((c (stream 'peek)))
				(cond
				 ((and c (not (substringp c terminators)))
				  (strextend buf c)
				  (stream 'advance))
				 (t (esc (cellget buf))))))))))))
	(cond
	 ((= str "nil") nil)
	 ((atoi str) (atoi str))
	 (t (intern str)))))))

(define escape
  (func (s)
    (let ((n (strlength s))
	  (se (cellnew "")))
      (for 0 n
	   (func (i)
	     (strextend
	      se (let ((c (strget s i)))
		   (cond
		    ((= c "\\") "\\\\")
		    ((= c "\"") "\\\"")
		    ((= c "\n") "\\n")
		    ((= c "\t") "\\t")
		    (t c))))))
      (cellget se))))

(define improperfoldl
  (func (f g z x)
    (jmp (cond
	  ((consp x)
	   (improperfoldl f g (f z (car x)) (cdr x)))
	  ((nilp x)
	   z)
	  (t
	   (g z x))))))

(define writecons
  (func (x)
    (let ((inards (improperfoldl
		   (func (z e)
		     (strcat z " " (write e)))
		   (func (z e)
		     (strcat z " . " (write e)))
		   (write (car x))
		   (cdr x))))
      (strcat "(" inards ")"))))

(define write
  (func (x)
    (cond
     ((numberp x) (itoa x))
     ((symbolp x) (symbolname x))
     ((nilp x) "nil")
     ((consp x) (writecons x))
     ((templatep x) "<template>")
     ((funcp x) "<func>")
     ((contp x) "<cont>")
     ((stringp x) (strcat "\"" (escape x) "\""))
     ((cellp x) "<cell>")
     ((arrayp x) "<array>")
     (t (throw "write: unknown type")))))

(define arrayfromlist
  (func (x)
    (cond
     ((nilp x)
      "[]")
     ((consp x)
      (let ((s (cellnew "[")))
	(strextend s (tojson (car x)))
	(foreach (func (elt)
		   (strextend s "," (tojson elt)))
		 (cdr x))
	(strextend s "]")
	(cellget s)))
     (t
      (throw "arrayfromlist: type error")))))

(define tojson
  (func (x)
    (cond
     ((or (nilp x) (consp x))
      (arrayfromlist x))
     ((numberp x)
      (write x))
     ((stringp x)
      (strcat "\"" (escape x) "\""))
     ((symbolp x)
      (strcat "\"" (symbolname x) "\""))
     (t
      (throw "tojson: unexpected type")))))
