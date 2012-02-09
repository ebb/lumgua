(define showbacktrace
  (func (c)
    (match (contopen c)
      ((cont stack)
       (call/cc
	(func (esc)
	  (let ((fp (cellnew (arraylength stack))))
	    (loop (func ()
		    (cond
		     ((= (cellget fp) 0)
		      (esc nil)))
		    (let ((f (arrayget stack (- (cellget fp) 3))))
		      (cellput fp (arrayget stack (- (cellget fp) 2)))
		      (match (funcopen f)
			((func temp env)
			 (match (templateopen temp)
			   ((template name nvars dottedp freerefs code)
			    (let ((s (cellnew "(")))
			      (cond
			       ((= name "")
				(strextend s "<anon>"))
			       (t (strextend s name)))
			      (for (cellget fp)
				   (+ (cellget fp) (+ nvars (if dottedp 1 0)))
				   (func (i)
				     (strextend s " "
						(write (arrayget stack i)))))
			      (strextend s ")")
			      (log (cellget s)))))))))))))))))

(define time
  (func (f)
    (- 0 (- (now)
	    (begin (f) (now))))))

(define dict
  (cellnew nil))

(define get
  (func (sym)
    (lookup sym (cellget dict))))

(define put
  (func (sym val)
    (cellput dict (cons (list sym val)
			(cellget dict)))))

(define throwfunc
  (cellnew (func (s)
	     (log s)
	     (exit 1))))

(define throw
  (func (s)
    ((cellget throwfunc) s)))

(define repl
  (func ()
    (log (call/cc (func (cc)
		    (cellput throwfunc
			     (func (s)
			       (jmp (call/cc (func (xx)
					       (showbacktrace xx)
					       (cc s))))))
		    "entering REPL")))
    (loop (func ()
	    (let ((text (http 'get "http://localhost:8082/eval")))
	      (let ((exps (readall text)))
		(foreach (func (exp)
			   (log (write ((funcnew (compile exp)
						 (arraynew 0))))))
			 exps)))))))
