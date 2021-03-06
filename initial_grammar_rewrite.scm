#lang eopl

(define print eopl:pretty-print)

(define-datatype program program?
 (a-program(expl1 expression?)))

(define-datatype expression expression?
 (const-exp(num number?))
  
 (binary-exp
       (exp1 expression?)
       (bin string?)
       (exp2 expression?))
  
 (if-exp
      (exp1 expression?) 
      (body1 (list-of expression?))
      (body2 (list-of expression?)))
  
 (var-exp(var symbol?))
  
 (let-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))
  
;  (begin-exp
;    (exp expression?)
;    (exps (list-of expression?)))
  (begin-exp
    (num-lit string?)
    (lits (list-of string?))
    (vars (list-of identifier?))
    (exps (list-of expression?))
    (ret expression?))
  
  (minus-exp(exp1 expression?))
  (plus-exp(exp1 expression?))

  ;(num-var-exp
  ; (num-lit string?)
  ; (var identifier?)
  ; (exps (list-of expression?)))
  
  (newref-exp
   (exp expression?))
  (deref-exp
   (var expression?))
  (setref-exp
   (var identifier?)
   (exp expression?))
  
  (emptylist-exp)
  
  (list-exp
   (exps (list-of expression?)))
  
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))
  
  (letproc-exp
   (name identifier?)
   (vars (list-of identifier?))
   (exp expression?)
   (body expression?))
  
  (letrec-exp
   (names (list-of identifier?))
   (varss (list-of (list-of identifier?)))
   (exps (list-of expression?))
   (body expression?))
  
  (call-exp
   (rator expression?)
   (rand (list-of expression?)))

  (while-exp
   (cond expression?)
   (body (list-of expression?)))
  (for-exp
   ;(num-lit string?)
   ;(var identifier?)
   (exp1 expression?)
   (cond expression?)
   (increment expression?)
   (body (list-of expression?)))
   
  (print-exp
   (exps (list-of expression?)))
  (endl-exp
   (nl string?))
  (space-exp
   (s string?))
  (tab-exp
   (t string?))
  (print-string-exp
   (ps string?))
  )

 (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?))
   (proc-val
    (proc proc?))
   (list-val
   (lst list?))
   (ref-val
    (ref reference?)))

  (define expval->num
    (lambda (v)
      (cases expval v
	(num-val (num) num)
	(else (expval-extractor-error 'num v)))))

  (define expval->bool
    (lambda (v)
      (cases expval v
	(bool-val (bool) bool)
	(else (expval-extractor-error 'bool v)))))

(define expval->ref
  (lambda (val)
    (cases expval val
      (ref-val (ref) ref)
      (else (expval-extractor-error 'ref val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc val)))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (expval-extractor-error 'list val)))))


  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

 (define-datatype proc proc?
   (procedure
    (vars (list-of identifier?))
    (body expression?)
    (saved-env environment?)))


(define-datatype environment environment?
  (empty-env)
  (extend-env
   (saved-var var?)
   (saved-val scheme-value?)
   (saved-env environment?))
  (extend-env-rec
   (names (list-of identifier?))
   (varss (list-of (list-of identifier?)))
   (exps (list-of expression?))
   (old-env environment?))
  (extend-env-ref
   (saved-var var?)
   (saved-val expval?)
   (saved-env environment?))
  )

(define var? symbol?)
(define scheme-value? (lambda (s) #t))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? search-var saved-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (names varss exps old-env)
                      (define (apply-rec names varss exps)
                        (if (null? names)
                            (apply-env old-env search-var)
                            (if (eqv? search-var (car names))
                                (proc-val (procedure (car varss) (car exps) env))
                                (apply-rec (cdr names) (cdr varss) (cdr exps)))))
                      (apply-rec names varss exps))
      (extend-env-ref (saved-var saved-ref saved-env)
                      (if (eqv? search-var saved-var)
                          (deref (expval->ref saved-ref))
                      (apply-env saved-env search-var)))
      )))

(define apply-ref
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (eqv? search-var saved-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (names varss exps old-env)
                      (define (apply-rec names varss exps)
                        (if (null? names)
                            (apply-env old-env search-var)
                            (if (eqv? search-var (car names))
                                (proc-val (procedure (car varss) (car exps) env))
                                (apply-rec (cdr names) (cdr varss) (cdr exps)))))
                      (apply-rec names varss exps))
      (extend-env-ref (saved-var saved-ref saved-env)
                      (if (eqv? search-var saved-var)
                          (expval->ref saved-ref)
                      (apply-ref saved-env search-var)))
      )))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define report-no-type-found
  (lambda (search-exp)
    (eopl:error 'apply-env "No type found ~s" search-exp)))

(define the-lexical-spec
    '((whitespace (whitespace) skip)
      (comment ("//" (arbno (not #\newline))) skip)
      (identifier
       (letter (arbno (or letter digit "_" "-" "?")))
       symbol)
      (number (digit (arbno digit)) number)
      (number ("-" digit (arbno digit)) number)
      (binary-op ((or "-" "+" "*" "/" "==" "!=" ">" "<" ">=" "<=")) string)
      (endl ("endl") string)
      (space ("space") string)
      (tab ("tab") string)
      (literal ((or "int" "double" "float" "long" "long long" "short"
                    "unsigned int" "signed int" "unsigned float" "signed float"
                    "unsigned double" "signed double" "unsigned long" "signed long"
                    "unsigned long long" "signed long long"
                    "unsigned short" "signed short"
                    "char" "unsigned char" "signed char"
                    "string" "bool"
                    )) string)
      (print-string ("'" (arbno letter) "'") string)
      ))
  
  (define the-grammar
    '((program (expression) a-program)

      (expression (number) const-exp)
      
      (expression 
       ("(" expression binary-op expression ")")
       binary-exp)
      
      (expression
       ("if" "(" expression ")" "{" (arbno expression) "}" "else" "{" (arbno expression) "}")
       if-exp)

      (expression (identifier) var-exp)

      (expression
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp) 

      ;(expression
      ; ("begin" expression (arbno ";" expression) "end")
      ; begin-exp)
      (expression
       (literal "main" "(" (arbno literal identifier) ")" "{" (arbno expression ";") "return" expression ";" "}")
       begin-exp)
      
      (expression
       ("--" expression)
       minus-exp)

      (expression
       ("++" expression)
       plus-exp)
      
      (expression
       ("newref" "(" expression ")")
       newref-exp)
      
      (expression
       ("deref" "(" expression ")")
       deref-exp)
      
      (expression
       ("set" identifier "=" expression)
       setref-exp)

      (expression
       ("emptylist")
       emptylist-exp)
      
      (expression
       ("list" "(" (separated-list expression ",") ")")
       list-exp)
      
      (expression
       ("proc" "(" (arbno identifier) ")" expression)
       proc-exp)
      
      (expression
       ("letproc" identifier "(" (arbno identifier) ")" expression "in" expression)
       letproc-exp)
      
      (expression
       ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression)
       letrec-exp)
      
      (expression
       ("[" expression (arbno expression) "]")
       call-exp)
      
      (expression
       ("while" "(" expression ")" "{" (arbno expression) "}" )
       while-exp)
      (expression
       ("for" "(" expression ";" expression ";" expression ")" "{" (arbno expression ";") "}")
       for-exp)

      (expression
       ("cout" (arbno "<<" expression) ";")
       print-exp)
      (expression
       (endl)
       endl-exp)
      (expression
       (space)
       space-exp)
      (expression
       (tab)
       tab-exp)
      (expression
       (print-string)
       print-string-exp)
      ))

(define scan&parse
     (sllgen:make-string-parser the-lexical-spec the-grammar))

(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

 (define value-of-program 
    (lambda (pgm)
      (initialize-store!)
      (cases program pgm
        (a-program (exp1)
          (value-of exp1 (init-env))))))
  
 
 (define help-if
    (lambda (exps env)
      (cond
        ((null? exps) '())
           (else (cons (value-of (car exps) env)(help-if (cdr exps) env))))))

;(define help-if
 ; (lambda (exps env)
  ;               (let ((last (value-of (car exps) env)))
   ;                (define (help-if-rec exps last)
    ;                 (if (null? exps)
     ;                    last
      ;                   (let ((last (value-of (car exps) env)))
       ;                    (help-if-rec (cdr exps) last))))
        ;           (help-if-rec exps last))))

(define help-print
  (lambda (exps env)
    (cond
      ((null? (cdr exps)) (let ((val (value-of (car exps) env)))
                            (display val)))
      (else
       (let ((val (value-of (car exps) env)))
       (display val) (help-print (cdr exps) env))))))

(define help-while-loop
  (lambda (cond body env)
    (begin
      (help-if body env)
        (let ((val (value-of cond env)))
          (if (equal? val (bool-val #t)) (help-while-loop cond body env)
            '())))))

(define help-for-loop
   (lambda (ref cond body increment env)
     (begin
       (help-if body env)
       (let ((new-val (value-of increment env)))
         ;(display "ref: ")(display ref)(display "\n")
         ;(display "new-val: ")(display new-val)(display " ")(display (find-expval new-val))
         (setref! ref (find-expval new-val))
         (let ((cond-val (value-of cond env)))
           (if (equal? cond-val (bool-val #t))
               (help-for-loop ref cond body increment env)
               '()))))))
         

(define declare-variables
  (lambda (vars env)
    (cond
      ((null? vars) env)
      (else (declare-variables (cdr vars) (extend-env-ref (car vars) (ref-val (newref 0)) env))
            )
      )
    ))

(define find-expval
  (lambda (val)
     ; (display "val: ")
     ; (display val)
     ; (display "\nexpval? ")
     ; (display (expval? val))
    (cond
     ((expval? val)
      ;(display "\nIn expval cond: ")(display val)(display"\n------\n")
      (cases expval val
	(num-val (num) (expval->num val))
        (bool-val (bool) (expval->bool val))
        (ref-val (ref) (expval->ref val))
	(else (report-no-type-found exp)))
      ); (expval? val)
     
    (else
     ;(display "\nIn else: ")(display val)
     val
       );else
    ) ;cond
    ))
  

  (define value-of
    (lambda (exp env)
      (cases expression exp
        (const-exp (num) (num-val num))
        (var-exp (var) (apply-env env var))
        (binary-exp (exp1 bin exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((num1 (if (expval? val1) (expval->num val1) val1))
                  (num2 (if (expval? val2) (expval->num val2) val2)))
              (cond
                ((equal? bin "-") (num-val(- num1 num2)))
                ((equal? bin "+") (num-val(+ num1 num2)))
                ((equal? bin "*") (num-val(* num1 num2)))
                ((equal? bin "/") (num-val(/ num1 num2)))
                ((equal? bin "==")(if (eqv? num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin "!=")(if (eqv? num1 num2) (bool-val #f)
                   (bool-val #t)))
                ((equal? bin "<")(if (< num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin ">")(if (> num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin "<=")(if (<= num1 num2) (bool-val #t)
                   (bool-val #f)))
                ((equal? bin ">=")(if (>= num1 num2) (bool-val #t)
                   (bool-val #f)))
                )
              )))

;        (begin-exp (exp exps)
;                 (let ((last (value-of exp env)))
;                   (define (begin-exp-rec exps last)
;                     (if (null? exps)
;                         last
;                         (let ((last (value-of (car exps) env)))
;                           (begin-exp-rec (cdr exps) last))))
;                   (begin-exp-rec exps last)))
        (begin-exp (num-lit lits vars exps ret)
                 (let ((new-env (declare-variables vars env)))
                   (display "Current environment: ")(display new-env)(display "\n")
                 (define (begin-exp-rec exps n-env)
                   (cond
                     ((null? (cdr exps)) (value-of (car exps) n-env))
                     (else
                      (value-of (car exps) n-env)
                      (begin-exp-rec (cdr exps) n-env))))
                 (begin-exp-rec exps new-env)
                 (value-of ret new-env)))                        
                       

        (newref-exp (exp1)
                  (let ((v1 (value-of exp1 env)))
                         (ref-val (newref v1))))
        (deref-exp (exp1)
                   (let ((v1 (value-of exp1 env)))
                     (let ((ref1 (expval->ref v1)))
                       (deref ref1))))
        (setref-exp (exp1 exp2)
                    (let ((ref (apply-ref env exp1)))
                      (let ((val2 (find-expval (value-of exp2 env))))
                        ;(display "\nIn setref-exp: ")(display val2)
                        ;(display "\n ref: ")(display ref)
                        (begin
                           (setref! ref val2)
                            (num-val ref)))))

        (if-exp (exp1 body1 body2)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (help-if body1 env)
              (help-if body2 env))))
        
        (let-exp (vars exps body)
               (let ((vals (map (lambda (exp) (value-of exp env)) exps)))
                 (define (add-env vars vals env)
                   (if (null? vars)
                       env
                       (add-env (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))
                 (value-of body (add-env vars vals env))))
        
        (minus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (- (if (expval? val1) (expval->num val1) val1) 1)))
             (num-val num1))))
        (plus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (+ (if (expval? val1) (expval->num val1) val1) 1)))
             (num-val num1))))

        (emptylist-exp () (list-val '()))
      
      (list-exp (exps)
                (list-val (map (lambda (exp) (value-of exp env)) exps)))
      
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      
      (letproc-exp (proc-name proc-args proc-body let-body)
                   (let ((proc (proc-val (procedure proc-args proc-body env))))
                     (value-of let-body
                               (extend-env proc-name proc env))))
      
      (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of letrec-body
                            (extend-env-rec p-name b-var p-body env)))
      
      (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (map (lambda (exp) (value-of exp env)) rand)))
                  (apply-procedure proc args)))

        

        (while-exp (cond body)
                   (let ((val (value-of cond env)))
                     (if (equal? val (bool-val #t)) (help-while-loop cond body env)
                       '()))
                   )

        (for-exp (exp1 cond increment body)
                 (let ((init-val (expval->num (value-of exp1 env))))
                   ;(display "exp1: ")(display exp1)(display " ")(display "init-val: ")(display init-val)(display "\n")
                 (let ((cond-val (value-of cond env)))
                   (if (equal? cond-val (bool-val #t)) (help-for-loop init-val cond body increment env)
                       '())))
                   )

        (print-exp (exps)
                   (help-print exps env))
        (endl-exp (nl)
                  "\n")
        (space-exp (nl)
                  " ")
        (tab-exp (nl)
                  "\t")
        (print-string-exp (ps)
                  (let ((len (string-length ps)))
                    (substring ps 1 (- len 1))))
        )))

(define init-env 
    (lambda ()
      (empty-env)))

(define (empty-store)
  (make-vector 0))

(define the-store 'uninitialized)

(define (get-val value-of-result)
  (car value-of-result))

(define (get-store)
  the-store)

(define (initialize-store!)
  (set! the-store (empty-store)))

(define (reference? v)
  (integer? v))

(define (identifier? x)
  (and (symbol? x)
       (not (eqv? x 'lambda))))

(define (newref val)
  (let* ((next-ref (vector-length the-store))
         (next-store (make-vector (+ next-ref 1) val)))
    (define (newref-rec idx)
      (if (equal? idx next-ref)
          0
          (begin (vector-set! next-store idx (vector-ref the-store idx))
                 (newref-rec (+ idx 1)))))
    (newref-rec 0)
    (set! the-store next-store)
    next-ref))

(define (deref ref)
  (vector-ref the-store ref))

(define (setref! ref val)
  (vector-set! the-store ref val)
  ref)

(define apply-procedure
  (lambda (proc1 args)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (define (apply-procedure-rec vars vals env)
                   (if (null? vars)
                       (if (null? vals)
                           (value-of body env)
                           (apply-procedure (expval->proc (value-of body env)) vals))
                       (if (null? vals)
                           (procedure vars body env)
                           (apply-procedure-rec (cdr vars) (cdr vals)
                                                (extend-env (car vars) (car vals) env)))))
                 (apply-procedure-rec vars args saved-env)))))

(define program-1
  "begin
 ++5;
   begin
(5 - 4);
end;
--5;
 end")

(define program-2
  "let x = newref(0)
   in begin
        setref(x, 11);
        setref(x ,(deref(x) - 5));
        setref(x, ++deref(x));
        --deref(x);
      end

")

(define program-3 "letrec sum(x y) = if ((x == 0)) {y} else{ [sum (x - 1) (y + 1)]} in [sum 3 2]")

(define program-4 "letrec
                             even(x) = if ((x == 0)) {1} else{ [odd (x - 1)]}
                             odd(x) = if ((x == 0)) {0} else{ [even (x - 1)]}
                           in [odd 13]")


(define program-5 "if( (5 == 6)) {(5 + 1) (1 + 2) } else{ (5 - 1) (1 + 1)} ")

(define program-6 "let x = newref(0) in begin
                              while ( (deref(x) <= 2) ){ setref(x, (deref(x) + 2)) } ; deref(x); end")

(define program-7 "let x = newref(3) in begin
                              if ( (deref(x) < 5) ) {1} else {0} ; deref(x); end")

(define program-8
  "int main() {
      cout << 6 << 5 << 7 << endl;;
      cout << (4 - 5) << 8 << 4;;
      return 0;
   }")

(define program-9
  "int main(int x int y int z) {
      for(int i = 0; (i < 3); ++i){
         setref(x, i);
         cout << x << endl;;
      };
      return 0;
   }")

(define program-10
  "int main(int x int y int z int a int i){
      set y = 11;
      set x = y;
      set z = ((x - 1) * 2);
      cout << z << endl;;
      for(set i = 0; (i < y); ++i){
         set a = i;
         cout << a << space;;
      };
      cout << endl;;
      return x;
  }")

(define program-11
  "int main(){
      cout << 'hello' << space << 'world' << endl;;
      return 0;
  }")

;(print (run program-1))
;(print (run program-2))


;(print (run program-3))

;(print (run program-4))

;(print (run program-5))

;(print (run program-6))
;(print (run program-7))

;(print (run program-8))

;(print (run program-9))
(print (run program-10))
(print (run program-11))