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
   (func (_ a b)
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
      (func (_ n elt)
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
      (func (_ elt z)
         (cons (f elt) z))
      '()
      x))

(func (filter pred x)
   (foldr
      (func (_ elt z)
         (if (pred elt) (cons elt z) z))
      '()
      x))

(func (compose f g)
   (func (_ x)
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
   (if x F T))

(let first car)

(let second cadr)

(func (third x)
   (second (cdr x)))

(func (fourth x)
   (third (cdr x)))

(func (nth n x)
   (if (= n 0)
      (car x)
      (goto (nth (- n 1) (cdr x)))))

(subr (strextend cell str)
   (cellput cell (strcat &((cellget cell) str))))

(subr (escape s)
   (let n (strlength s))
   (let se (cellnew ""))
   (begin
      (for 0 n
         (subr (_ i)
            (strextend se
               (let _
                  (let c (strget s i))
                  (cond
                     (case (= c "\\") "\\\\")
                     (case (= c "\"") "\\\"")
                     (case (= c "\n") "\\n")
                     (case (= c "\t") "\\t")
                     (else c))))))
      (cellget se)))

(func (writelist x)
   (cond
      (case (= x '())
         "()")
      (else
         (let inards
            (foldl
               (func (_ z e)
                  (strcat &(z " " (write e))))
               (write (car x))
               (cdr x)))
         (strcat &("(" inards ")")))))

(func (write x)
   (match &((typeof x))
      (case (bool) (if x "T" "F"))
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
                  (strextend s (if (= name "") "<anon>" name))
                  (for fp (+ fp nvars)
                     (subr (_ i)
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
            (subr (_ i)
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
            (subr (_ cc)
               (begin
                  (cellput throwfunc
                     (subr (_ s)
                        (call/cc
                           (subr (_ xx)
                              (let softpanic (cellget throwfunc))
                              (begin
                                 (cellput throwfunc hardpanic)
                                 (showbacktrace xx)
                                 (cellput throwfunc softpanic)
                                 (cc s))))))
                  "entering REPL"))))
      (loop
         (subr (_)
            (let text (http 'get "http://localhost:8082/eval" '()))
            (let _
               (let exps (readall text))
               (foreach
                  (subr (_ exp)
                     (log (write (call (funcnew (compile exp) (arraynew 0))))))
                  exps))))))

(func (detect pred x)
   (cond
      (case (nilp x) F)
      (case (pred (car x)) T)
      (else (goto (detect pred (cdr x))))))

(func (member x s)
   (detect (func (_ y) (= x y)) s))

(func (tabify vals)
   (strcat
      (cons (write (car vals))
         (map
            (func (_ val)
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
                     (subr (_ pc instr)
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
