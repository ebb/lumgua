(define (consp x)
  (and (= (typeof x) 'list)
       (!= x '())))

(define (nilp x)
  (= x '()))

(define (caar x)
  (car (car x)))

(define (cadr x)
  (car (cdr x)))

(define (cdar x)
  (cdr (car x)))

(define (cddr x)
  (cdr (cdr x)))

(define (flip f)
  (func (a b)
    (f b a)))

(define (foldl f z x)
  (cond
      (case (nilp x) z)
      (else
	(goto (foldl f (f z (car x)) (cdr x))))))

(define (foldr f z x)
  (foldl (flip f) z (reverse x)))

(define (length x)
  (foldl (func (n elt)
	   (+ n 1))
	 0
	 x))

(define (loop f)
  (f)
  (goto (loop f)))

(define (for i n f)
  (cond
      (case (< i n)
          (f i)
          (goto (for (+ i 1) n f)))))

(define (foreach f x)
  (cond
      (case (not (nilp x))
          (f (car x))
          (goto (foreach f (cdr x))))))

(define (map f x)
  (foldr (func (elt z)
	   (cons (f elt) z))
	 '()
	 x))

(define (filter pred x)
  (foldr (func (elt z)
	   (cond
	       (case (pred elt)
		   (cons elt z))
	       (else z)))
	 '()
	 x))

(define (compose f g)
  (func (x)
    (f (g x))))

(define (snoc d a)
  (cons a d))

(define (reverse x)
  (foldl snoc '() x))

(define (append x y)
  (cond
      (case (nilp y) x)
      (case (nilp x) y)
      (else (foldr cons y x))))

(define (not x)
  (cond
      (case x F)
      (else T)))

(define first car)

(define second cadr)

(define (third x)
  (second (cdr x)))

(define (fourth x)
  (third (cdr x)))

(define (nth n x)
  (cond
      (case (= n 0) (car x))
      (else (goto (nth (- n 1) (cdr x))))))

(define (strextend cell str)
  (cellput cell (strcat &((cellget cell) str))))

(define (escape s)
  (let ((n (strlength s))
	(se (cellnew "")))
    (for 0 n
	 (func (i)
	   (strextend se (let ((c (strget s i)))
			   (cond
			       (case (= c "\\") "\\\\")
			       (case (= c "\"") "\\\"")
			       (case (= c "\n") "\\n")
			       (case (= c "\t") "\\t")
			       (else c))))))
    (cellget se)))

(define (writelist x)
  (cond
      (case (= x '())
          "()")
      (else
          (let ((inards (foldl (func (z e)
			         (strcat &(z " " (write e))))
			       (write (car x))
			       (cdr x))))
	    (strcat &("(" inards ")"))))))

(define (write x)
  (match &((typeof x))
      (case (bool) (cond (case x "<true>") (else "<false>")))
      (case (number) (itoa x))
      (case (symbol) (symbolname x))
      (case (string) (strcat &("\"" (escape x) "\"")))
      (case (list) (writelist x))
      (case (template) "<template>")
      (case (func) "<func>")
      (case (cont) "<cont>")
      (case (cell) "<cell>")
      (case (array) "<array>")
      (else (throw "write: unknown type"))))

(define (showoneframe stack f fp)
  (match (funcopen f)
      (case (func temp env)
          (match (templateopen temp)
              (case (template name nvars freerefs code)
	          (let ((s (cellnew "(")))
	            (cond
	                (case (= name "")
	                    (strextend s "<anon>"))
	                (else (strextend s name)))
	            (for fp
	                 (+ fp nvars)
	                 (func (i)
		           (strextend s " ")
		           (strextend s (write (arrayget stack i)))))
	            (strextend s ")")
	            (log (cellget s))))))))

(define (showbacktrace c)
  (match (contopen c)
      (case (cont rstack stack)
          (let ((n (arraylength rstack)))
            (for 1 n
	         (func (i)
	           (let ((j (- n i)))
		     (match (arrayget rstack j)
		         (case (return f fp pc)
		             (showoneframe stack f fp))))))))))

(define (time f)
  (- 0 (- (now)
	  (begin (f) (now)))))

(define (hardpanic s)
  (log s)
  (exit 1))

(define throwfunc
  (cellnew hardpanic))

(define (throw s)
  (call (cellget throwfunc) s))

(define (repl)
  (log (call/cc
	(func (cc)
	  (cellput throwfunc
		   (func (s)
		     (call/cc (func (xx)
				(let ((softpanic (cellget throwfunc)))
				  (cellput throwfunc hardpanic)
				  (showbacktrace xx)
				  (cellput throwfunc softpanic))
				(cc s)))))
	  "entering REPL")))
  (loop (func ()
	  (let ((text (http 'get "http://localhost:8082/eval" '())))
	    (let ((exps (readall text)))
	      (foreach (func (exp)
			 (log (write (call (funcnew (compile exp)
					            (arraynew 0))))))
		       exps))))))

(define (detect pred x)
  (cond
      (case (nilp x) F)
      (case (pred (car x)) T)
      (else (goto (detect pred (cdr x))))))

(define (member x s)
  (detect (func (y) (= x y)) s))

(define (tabify vals)
  (strcat (cons (write (car vals))
		(map (func (val)
		       (strcat &("\t" (write val))))
		     (cdr vals)))))

(define (showinstr pc instr)
  (log (tabify (cons pc instr))))

(define (showfunc f nesting)
  (match (funcopen f)
      (case (func temp env)
          (showtemplate temp nesting))))

(define (showtemplate template nesting)
  (match (templateopen template)
      (case (template name nvars freerefs code)
          (cond
              (case (= nesting '())
	          (log (strcat &("name: " name)))
	          (log (strcat &("nvars: " (write nvars))))
	          (log (strcat &("freerefs: " (write freerefs))))
	          (foldl (func (pc instr)
		           (showinstr pc instr)
		           (+ pc 1))
	                 0
	                 code)
                  'end)
          (else
	      (match (nth (car nesting) code)
	          (case (close template)
	              (goto (showtemplate template (cdr nesting))))))))))

(define main repl)

; some tests
;
; (foo)
; (showfunc showfunc '())
