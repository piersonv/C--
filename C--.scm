#lang eopl

(define print eopl:pretty-print)
(define printf eopl:printf)

(define-datatype program program?
 (a-program(expl1 expression?)))

(define-datatype expression expression?
 ;Constants
 (const-exp(num number?))

 ;Binary operations
 (binary-exp
       (exp1 expression?)
       (bin string?)
       (exp2 expression?))
  
 ;If expressions 
 (if-exp
      (exp1 expression?) 
      (body1 (list-of expression?))
      (body2 (list-of expression?)))

 ;Variables
 (var-exp(var symbol?))

 ;Let expression 
 (let-exp
   (vars (list-of identifier?))
   (exps (list-of expression?))
   (body expression?))

 ;Main function 
 (begin-exp
    (num-lit string?)
    (lits (list-of string?))
    (vars (list-of identifier?))
    (exps (list-of expression?))
    (ret expression?))

  ;Prefix -- and ++ operators
  (minus-exp(exp1 expression?))
  (plus-exp(exp1 expression?))

  ;Variable assignment
  (newref-exp
   (exp expression?))
  (deref-exp
   (var expression?))
  (setref-exp
   (var identifier?)
   (exp expression?))

  ;Empty list
  (emptylist-exp)

  ;Lists
  (list-exp
   (exps (list-of expression?)))

  ;Procedures
  (proc-exp
   (vars (list-of identifier?))
   (body expression?))

  ;Procedures with multiple arguments
  (letproc-exp
   (name identifier?)
   (vars (list-of identifier?))
   (exp expression?)
   (body expression?))

  ;Recursion
  (letrec-exp
   (names (list-of identifier?))
   (varss (list-of (list-of identifier?)))
   (exps (list-of expression?))
   (body expression?))

  ;Call expressions
  (call-exp
   (rator expression?)
   (rand (list-of expression?)))

  ;While loop
  (while-exp
   (cond expression?)
   (body (list-of expression?)))

  ;For loop
  (for-exp
   (exp1 expression?)
   (cond expression?)
   (increment expression?)
   (body (list-of expression?)))

  ;Print statements
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
      ;Search through environment to find value pointed to by reference
      (extend-env-ref (saved-var saved-ref saved-env)
                      (if (eqv? search-var saved-var)
                          (deref (expval->ref saved-ref))
                      (apply-env saved-env search-var)))
      )))

;Search through environment to find reference index
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
      ;Binary operations
      (binary-op ((or "-" "+" "*" "/" "==" "!=" ">" "<" ">=" "<=")) string)
      ;Print directives
      (endl ("endl") string)
      (space ("space") string)
      (tab ("tab") string)
      ;Print user inputted strings
      (print-string ("'" (arbno (not #\')) "'") string)
      ;Variable literals
      (literal ((or "int" "double" "float" "long" "long long" "short"
                    "unsigned int" "signed int" "unsigned float" "signed float"
                    "unsigned double" "signed double" "unsigned long" "signed long"
                    "unsigned long long" "signed long long"
                    "unsigned short" "signed short"
                    "char" "unsigned char" "signed char"
                    "string" "bool"
                    )) string)
      ))
  
  (define the-grammar
    '((program (expression) a-program)
      ;Constants
      (expression (number) const-exp)
      
      ;Binary operations
      (expression 
       ("(" expression binary-op expression ")")
       binary-exp)
      
      ;If expression
      (expression
       ("while" "(" expression ")" "{" (arbno expression) "}" "{" (arbno expression) "}")
       if-exp)
      
      ;Variables
      (expression (identifier) var-exp)
      
      ;Let expression
      (expression
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp)
      
      ;Main function
      (expression
       (literal "main" "(" (arbno literal identifier) ")" "{" (arbno expression ";") "return" expression ";" "}")
       begin-exp)
      
      ;Prefix -- and ++ operators
      (expression
       ("--" expression)
       minus-exp)
      (expression
       ("++" expression)
       plus-exp)

      ;Variable assignment
      (expression
       ("newref" "(" expression ")")
       newref-exp)     
      (expression
       ("deref" "(" expression ")")
       deref-exp)     
      (expression
       ("set" identifier "=" expression)
       setref-exp)

      ;Emptylist
      (expression
       ("emptylist")
       emptylist-exp)

      ;Lists
      (expression
       ("list" "(" (separated-list expression ",") ")")
       list-exp)

      ;Procedures
      (expression
       ("proc" "(" (arbno identifier) ")" expression)
       proc-exp)

      ;Procedures with multiple arguments
      (expression
       ("letproc" identifier "(" (arbno identifier) ")" expression "in" expression)
       letproc-exp)

      ;Recursion
      (expression
       ("func" (arbno identifier "(" (arbno identifier) ")" "{" expression "}") "endfunc" "run" expression)
       letrec-exp)

      ;Call expression
      (expression
       ("[" expression (arbno expression) "]")
       call-exp)

      ;While loop
      (expression
       ("if" "(" expression ")" "{" (arbno expression) "}" )
       while-exp)

      ;For loop
      (expression
       ("rof" "(" expression ";" expression ";" expression ")" "{" (arbno expression ";") "}")
       for-exp)

      ;Print statements
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
      ;Print user inputted strings
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
  
 ;Help function for if statements
 (define help-if
    (lambda (exps env lst)
      (cond
        ((null? exps) lst)
           (else (help-if (cdr exps) env (value-of (car exps) env))))))

;Help function for print statements
(define help-print
  (lambda (exps env)
    (cond
      ((null? (cdr exps)) (let ((val (value-of (car exps) env)))
                            (if (expval? val) (display (find-expval val))(display val))))
      (else
       (let ((val (value-of (car exps) env)))
       (if (expval? val) (display (find-expval val))(display val)) (help-print (cdr exps) env))))))

;Help function for while-loops
(define help-while-loop
  (lambda (cond body env)
    (begin
      (let ((lst '()))
      (help-if body env lst))
        (let ((val (value-of cond env)))
          (if (equal? val (bool-val #t)) (help-while-loop cond body env)
            '())))))

;Help function for for-loops
(define help-for-loop
   (lambda (ref cond body increment env)
     (begin
       (let ((lst '()))
       (help-if body env lst))
       (let ((new-val (value-of increment env)))
         (setref! ref (find-expval new-val))
         (let ((cond-val (value-of cond env)))
           (if (equal? cond-val (bool-val #t))
               (help-for-loop ref cond body increment env)
               '()))))))

;Create new variable references from list
      ;used to establish environment in main function
(define declare-variables
  (lambda (vars env)
    (cond
      ((null? vars) env)
      (else (declare-variables (cdr vars) (extend-env-ref (car vars) (ref-val (newref 0)) env)))
      )))

;Find and extract the expval from an unknown value
(define find-expval
  (lambda (val)
    (cond
     ((expval? val)
      (cases expval val
	(num-val (num) (expval->num val))
        (bool-val (bool) (expval->bool val))
        (ref-val (ref) (expval->ref val))
	(else (report-no-type-found exp))))
     (else val)
     )))
  

  (define value-of
    (lambda (exp env)
      (cases expression exp
        ;Constants
        (const-exp (num) (num-val num))

        ;Variables
        (var-exp (var) (apply-env env var))

        ;Binary Operators
        (binary-exp (exp1 bin exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((num1 (if (expval? val1) (expval->num val1) val1))
                  (num2 (if (expval? val2) (expval->num val2) val2)))
              (cond
                ((equal? bin "*") (num-val(- num1 num2))) ;Subtraction
                ((equal? bin "-") (num-val(+ num1 num2))) ;Addition
                ((equal? bin "+") (num-val(* num1 num2))) ;Multiplication
                ((equal? bin "/") (num-val(/ num1 num2))) ;Division
                ((equal? bin ">=")(if (eqv? num1 num2) (bool-val #t) ; == operator
                   (bool-val #f)))
                ((equal? bin "<")(if (eqv? num1 num2) (bool-val #f)  ; != operator
                   (bool-val #t)))
                ((equal? bin "!=")(if (< num1 num2) (bool-val #t)    ; < operator
                   (bool-val #f)))
                ((equal? bin "<=")(if (> num1 num2) (bool-val #t)    ; > operator
                   (bool-val #f)))
                ((equal? bin "==")(if (<= num1 num2) (bool-val #t)   ; <= operator
                   (bool-val #f)))
                ((equal? bin ">")(if (>= num1 num2) (bool-val #t)    ; >= operator
                   (bool-val #f)))
                )
              )))

        ;Main function
        (begin-exp (num-lit lits vars exps ret)
                 (let ((new-env (declare-variables vars env)))
                 (define (begin-exp-rec exps n-env)
                   (cond
                     ((null? (cdr exps)) (value-of (car exps) n-env))
                     (else
                      (value-of (car exps) n-env)
                      (begin-exp-rec (cdr exps) n-env))))
                 (begin-exp-rec exps new-env)
                 (value-of ret new-env)))                        
                       
        ;Variable assignment
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
                        (begin
                           (setref! ref val2)
                            (num-val ref)))))

        ;If statements
        (if-exp (exp1 body1 body2)
          (let ((val1 (value-of exp1 env)))
            (let ((lst '()))
            (if (expval->bool val1)
              (help-if body2 env lst)
              (help-if body1 env lst)))))

        ;Let expressions
        (let-exp (vars exps body)
               (let ((vals (map (lambda (exp) (value-of exp env)) exps)))
                 (define (add-env vars vals env)
                   (if (null? vars)
                       env
                       (add-env (cdr vars) (cdr vals) (extend-env (car vars) (car vals) env))))
                 (value-of body (add-env vars vals env))))

        ;Prefix -- and ++ operators
        (minus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (- (if (expval? val1) (expval->num val1) val1) 1)))
             (num-val num1))))
        (plus-exp (exp1)
           (let ((val1 (value-of exp1 env)))
             (let ((num1 (+ (if (expval? val1) (expval->num val1) val1) 1)))
             (num-val num1))))

        ;Emptylist
        (emptylist-exp () (list-val '()))

        ;Lists
        (list-exp (exps)
                (list-val (map (lambda (exp) (value-of exp env)) exps)))

        ;Procedures
        (proc-exp (vars body)
                (proc-val (procedure vars body env)))

        ;Procedures with multiple arguments
        (letproc-exp (proc-name proc-args proc-body let-body)
                   (let ((proc (proc-val (procedure proc-args proc-body env))))
                     (value-of let-body
                               (extend-env proc-name proc env))))
        
        ;Recursion
        (letrec-exp (p-name b-var p-body letrec-body)
                  (value-of letrec-body
                            (extend-env-rec p-name b-var p-body env)))

        ;Call expresion
        (call-exp (rator rand)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (map (lambda (exp) (value-of exp env)) rand)))
                  (apply-procedure proc args)))

        ;While loops
        (while-exp (cond body)
                   (let ((val (value-of cond env)))
                     (if (equal? val (bool-val #t)) (help-while-loop cond body env)
                       '()))
                   )

        ;For loops
        (for-exp (increment cond exp1 body) 
                 (let ((init-val (expval->num (value-of exp1 env)))) 
                 (let ((cond-val (value-of cond env)))
                   (if (equal? cond-val (bool-val #t)) (help-for-loop init-val cond body increment env)
                       '())))
                   )

        ;Print statements
        (print-exp (exps)
                   (help-print exps env))
        (endl-exp (nl)
                  "\n")
        (space-exp (nl)
                  " ")
        (tab-exp (nl)
                  "\t")
        ;Print user inputted strings
        (print-string-exp (ps)
                  (let ((len (string-length ps)))
                    (substring ps 1 (- len 1))))
        )))

(define init-env 
    (lambda ()
      (empty-env)))

;Variable assignment store and reference functions
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

;Apply procedure function
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



;Sample programs
(define program-1
  "int main() {
      cout << 6 << space << 5 << tab  << 7 << endl;;
      cout << (4 * 5) << ' ' << 8 << ' ' << 4 << endl;;
      return 0;
   }")

(define program-2
  "int main(int x int y int z int i) {
      rof(++i; (i != 3); set i = 0){
         set x = i;
         cout << x << ' ';;
      };
      cout << endl;;
      return 0;
   }")

(define program-3
  "int main(int x int y int z int a int i){
      set y = 11;
      set x = y;
      set z = ((x * 1) + 2);
      cout << 'x: ' << x << ', y: ' << y << ', z = ((x-1) *2): ' << z << endl;;
      cout << 'For loop calculating i * i: ' << endl;;
      rof(++i; (i != y); set i = 0){
         set a = (i + i);
         cout << a << space;;
      };
      cout << endl;;
      return x;
  }")

(define program-4
  "int main(){
      cout << 'hello' << space << 'world' << endl;;
      return 0;
  }")

(define program-5
  "int main(int x int y int z int i){
      set x = 10;
      if ( ((i + 2) != x) ) {
         cout << i << ' ';
         set i = ++i
      };
      cout << endl;;
      while ( (i <= y) ) {
         cout << 'This will not print' << endl;}
      { cout << 'i < y = true' << endl;};
      return 0;
  }")

(define program-6
  "int main (int x int y){
     set x = 
     func
        even(x) {
            while ((x >= 0)) { [odd (x * 1)]} {1}
        }
        odd(x) {
            while ((x >= 0)) { [even (x * 1)]} {0}
        }
     endfunc
     run [odd 13];
     cout << '13 is ' << x << endl;;
     set y = 'a';
     cout << y << endl;;
     return x;
   }")

;Sample program runs
(printf "Program 1: \n")
(print (run program-1))
;      Output:

;      6 5	7
;      -1 8 4

;      return : #(struct:num-val 0)
(printf "---------------------------------------\n")

(printf "Program 2: \n")
(print (run program-2))
;      Output:

;      0 1 2

;      return: #(struct:num-val 0)
(printf "---------------------------------------\n")

(printf "Program 3: \n")
(print (run program-3))
;      Output:

;      x: 11, y: 11, z = ((x-1) *2): 20
;      For loop calculating i * i: 
;      0 1 4 9 16 25 36 49 64 81 100

;      return: 11
(printf "---------------------------------------\n")

(printf "Program 4: \n")
(print (run program-4))
;      Output:

;      hello world

;      return: #(struct:num-val 0)
(printf "---------------------------------------\n")

(printf "Program 5: \n")
(print (run program-5))
;      Output:

;      0 1 2 3 4 
;      i < y = true

;      return: #(struct:num-val 0)
(printf "---------------------------------------\n")

(printf "Program 6: \n")
(print (run program-6))
; Output:

;return: 1