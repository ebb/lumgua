(func (consp x)
   (and
      (= (typeof x) 'list)
      (!= x '())))

(func (nilp x)
   (= x '()))

(func (caar x)
   (car (car x)))

(func (cadr x)
   (car (cdr x)))

(func (cdar x)
   (cdr (car x)))

(func (cddr x)
   (cdr (cdr x)))

(func (flip f)
   (func (a b)
      (f b a)))

(func (foldl f z x)
   (cond
      (case (nilp x) z)
      (else
         (goto (foldl f (f z (car x)) (cdr x))))))

(func (foldr f z x)
   (foldl (flip f) z (reverse x)))

(func (length x)
   (foldl
      (func (n elt)
         (+ n 1))
      0
      x))

(subr (loop f)
   (begin
      (f)
      (goto (loop f))))

(subr (for i n f)
   (cond
      (case (< i n)
         (begin
            (f i)
            (goto (for (+ i 1) n f))))))

(subr (foreach f x)
   (cond
      (case (not (nilp x))
         (begin
            (f (car x))
            (goto (foreach f (cdr x)))))))

(func (map f x)
   (foldr
      (func (elt z)
         (cons (f elt) z))
      '()
      x))

(func (filter pred x)
   (foldr
      (func (elt z)
         (cond
            (case (pred elt)
               (cons elt z))
            (else z)))
      '()
      x))

(func (compose f g)
   (func (x)
      (f (g x))))

(func (snoc d a)
   (cons a d))

(func (reverse x)
   (foldl snoc '() x))

(func (append x y)
   (cond
      (case (nilp y) x)
      (case (nilp x) y)
      (else (foldr cons y x))))

(func (not x)
   (cond
      (case x F)
      (else T)))

(let first car)

(let second cadr)

(func (third x)
   (second (cdr x)))

(func (fourth x)
   (third (cdr x)))

(func (nth n x)
   (cond
      (case (= n 0) (car x))
      (else (goto (nth (- n 1) (cdr x))))))

(subr (strextend cell str)
   (cellput cell (strcat &((cellget cell) str))))

(subr (escape s)
   (let n (strlength s))
   (let se (cellnew ""))
   (begin
      (for 0 n
         (subr (i)
            (strextend se
               ; TODO Fix this kludge.
               (cond
                  (else
                     (let c (strget s i))
                     (cond
                        (case (= c "\\") "\\\\")
                        (case (= c "\"") "\\\"")
                        (case (= c "\n") "\\n")
                        (case (= c "\t") "\\t")
                        (else c)))))))
      (cellget se)))

(subr (writelist x)
   (cond
      (case (= x '())
         "()")
      (else
         (let inards
            (foldl
               (func (z e)
                  (strcat &(z " " (write e))))
               (write (car x))
               (cdr x)))
         (strcat &("(" inards ")")))))

(func (write x)
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

(subr (showoneframe stack f fp)
   (match (funcopen f)
      (case (func temp env)
         (match (templateopen temp)
            (case (template name nvars freerefs code)
               (let s (cellnew "("))
               (begin
                  (cond
                     (case (= name "")
                        (strextend s "<anon>"))
                     (else
                        (strextend s name)))
                  (for fp (+ fp nvars)
                     (subr (i)
                        (begin
                           (strextend s " ")
                           (strextend s (write (arrayget stack i))))))
                  (strextend s ")")
                  (log (cellget s))))))))

(subr (showbacktrace c)
   (match (contopen c)
      (case (cont rstack stack)
         (let n (arraylength rstack))
         (for 1 n
            (subr (i)
               (let j (- n i))
               (match (arrayget rstack j)
                  (case (return f fp pc)
                     (showoneframe stack f fp))))))))

(subr (time f)
   (- 0
      (- (now)
         (begin (f) (now)))))

(subr (hardpanic s)
   (begin
      (log s)
      (exit 1)))

(let throwfunc
   (cellnew hardpanic))

(subr (throw s)
   (call (cellget throwfunc) s))

(subr (repl)
   (begin
      (log
         (call/cc
            (subr (cc)
               (begin
                  (cellput throwfunc
                     (subr (s)
                        (call/cc
                           (subr (xx)
                              (let softpanic (cellget throwfunc))
                              (begin
                                 (cellput throwfunc hardpanic)
                                 (showbacktrace xx)
                                 (cellput throwfunc softpanic)
                                 (cc s))))))
                  "entering REPL"))))
      (loop
         (subr ()
            (let text (http 'get "http://localhost:8082/eval" '()))
            ; TODO Fix this kludge.
            (cond
               (else
                  (let exps (readall text))
                  (foreach
                     (subr (exp)
                        (log (write (call (funcnew (compile exp) (arraynew 0))))))
                     exps)))))))

(func (detect pred x)
   (cond
      (case (nilp x) F)
      (case (pred (car x)) T)
      (else (goto (detect pred (cdr x))))))

(func (member x s)
   (detect (func (y) (= x y)) s))

(func (tabify vals)
   (strcat
      (cons (write (car vals))
         (map
            (func (val)
               (strcat &("\t" (write val))))
            (cdr vals)))))

(subr (showinstr pc instr)
   (log (tabify (cons pc instr))))

(subr (showfunc f nesting)
   (match (funcopen f)
      (case (func temp env)
         (showtemplate temp nesting))))

(subr (showtemplate template nesting)
   (match (templateopen template)
      (case (template name nvars freerefs code)
         (cond
            (case (= nesting '())
               (begin
                  (log (strcat &("name: " name)))
                  (log (strcat &("nvars: " (write nvars))))
                  (log (strcat &("freerefs: " (write freerefs))))
                  (foldl
                     (subr (pc instr)
                        (begin
                           (showinstr pc instr)
                           (+ pc 1)))
                     0
                     code)
                  'end))
            (else
               (match (nth (car nesting) code)
                  (case (close template)
                     (goto (showtemplate template (cdr nesting))))))))))

(let main repl)

; some tests
;
; (foo)
; (showfunc showfunc '())
