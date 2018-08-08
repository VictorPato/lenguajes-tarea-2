#lang play

#|
<expr> ::= <num>
         | <bool>
         | <id>
         | <string>
         | {if <expr> <expr> <expr>}
         | {fun {<id>*}}  <expr>}
         | {<expr> <expr>*}
         | {local {<def>*} <expr>}
         | {match <expr> <case>+}

<case> ::= {'case <pattern> '=> <expr>}
<pattern> ::= <num>
         | <bool>
         | <string>
         | <id>
         | (<constr-id> <attr-id>*)

<def>  ::= {define <id> <expr>}
         | {datatype <typename> <type-constructor>*}}


<type-constructor> ::= {<id> <member>*}
<constr-id> :: = <id>
<attr-id> :: = <id>
<typename> :: = <id>
<member>   :: = <id>

|#
; expresiones
(deftype Expr
  (num n)
  (bool b)
  (str s)
  (ifc c t f)
  (id s)
  (app fun-expr arg-expr-list)
  (prim-app name args)   ; aplicación de primitivas
  (fun id body)
  (lcal defs body)
  (mtch val cases))

; definiciones
(deftype Def
  (dfine name val-expr) ; define
  (datatype name variants)) ; datatype

; variantes
(deftype Variant
  (variant name params))

; estructuras de datos
(deftype Struct
  (structV name variant values))

; caso en pattern matching
(deftype Case
  (cse pattern body))

; patrón
(deftype Pattern
  (idP id) ; identificador
  (litP l) ; valor literal 
  (constrP ctr patterns)) ; constructor y sub-patrones

;; parse :: s-expr -> Expr
(define(parse s-expr)
  (define (list-parser l)
    (match l
      [(list head values ...) (app (id 'Cons) (list (parse head) (list-parser values)))]
      [empty (app (id 'Empty) (list))]))
  (match s-expr
    [(list 'list values ...) (list-parser values)]
    [(? number?) (num s-expr)]
    [(? boolean?) (bool s-expr)]
    [(? string?) (str s-expr)]
    [(? symbol?) (id s-expr)]
    [(list 'if c t f) (ifc (parse c) (parse t) (parse f))]
    [(list 'fun xs b) (fun xs (parse b))]
    [(list 'with (list (list x e) ...) b)
     (app (fun x (parse b)) (map parse e))]
    [(list 'local defs body)
     (lcal (map parse-def defs) (parse body))]
    [(list 'match val-expr cases ...) ; note the elipsis to match n elements
     (mtch (parse val-expr) (map parse-case cases))] ; cases is a list
    [(list f args ...) ; same here
     (if (assq f *primitives*)
         (prim-app f (map parse args)) ; args is a list
         (app (parse f) (map parse args)))]))

; parse-def :: s-expr -> Def
(define(parse-def s-expr)  
  (match s-expr
    [(list 'define id val-expr) (dfine id (parse val-expr))]
    [(list 'datatype name variants ...) (datatype name (map parse-variant variants))]))

; parse-variant :: sexpr -> Variant
(define(parse-variant v)
  (match v
    [(list name params ...) (variant name params)]))

; parse-case :: sexpr -> Case
(define(parse-case c)
  (match c
    [(list 'case pattern => body) (cse (parse-pattern pattern) (parse body))]))

; parse-pattern :: sexpr -> Pattern      <---- editada para azucar sintactico de listas
(define(parse-pattern p)
  (define (list-parser l)
    (match l
      [(list head values ...) (constrP 'Cons (list (parse-pattern head) (list-parser values)))]
      [empty (constrP  'Empty (list))]))
  (match p
    [(list 'list values ...) (list-parser values)]
    [(? symbol?)  (idP p)]
    [(? number?)  (litP (num p))]
    [(? boolean?) (litP (bool p))]
    [(? string?)  (litP (str p))]
    [(list ctr patterns ...) (constrP (first p) (map parse-pattern patterns))])
  )

;; interp :: Expr Env -> number/boolean/procedure/Struct
(define(interp expr env)
  (match expr
    ; literals
    [(num n) n]
    [(bool b) b]
    [(str s) s]
    ; conditional
    [(ifc c t f)
     (if (interp c env)
         (interp t env)
         (interp f env))]
    ; identifier
    [(id x) (env-lookup x env)]
    ; function (notice the meta interpretation)
    [(fun ids body)
     (closureV ids (λ (arg-vals id)
                     (interp body (extend-env id arg-vals env))) env)]
    ; application                       <---- editada para lazyness
    [(app fun-expr arg-expr-list)
     (match (strict(interp fun-expr env))
       [(closureV fun-ids body cl-env)(body
                                   (map (λ (id a)
                                          (match id
                                            [(list 'lazy x) (exprV a env (box #f))]
                                            [ _ (strict(interp a env))])) fun-ids arg-expr-list)
                                   (map (λ (id)
                                          (match id
                                            [(list 'lazy x) x]
                                            [_ id])) fun-ids))]
       [_ (def (id i) fun-expr)
          ((interp fun-expr env)
           (match (env-lookup i env)
             [(list 'lazy x) (exprV arg-expr-list env (box #f))]
             [ _ (map (lambda(x) (interp x env)) arg-expr-list) ]))])]
    
    ; primitive application
    [(prim-app prim arg-expr-list)
     (apply (cadr (assq prim *primitives*))
            (map (λ (a) (interp a env)) arg-expr-list))]
    ; local definitions
    [(lcal defs body)
     (def new-env (extend-env '() '() env))            
     (for-each (λ (d) (interp-def d new-env)) defs) 
     (interp body new-env)]
    ; pattern matching
    [(mtch expr cases)
     (def value-matched (interp expr env))
     (def (cons alist body) (find-first-matching-case value-matched cases))
     (interp body (extend-env (map car alist) (map cdr alist) env))]))

; interp-def :: Def Env -> Void
(define(interp-def d env)
  (match d
    [(dfine id val-expr)
     (update-env! id (interp val-expr env) env)]
    [(datatype name variants)
     ;; extend environment with new definitions corresponding to the datatype
     (interp-datatype name env)
     (for-each (λ (v) (interp-variant name v env)) variants)]))

; interp-datatype :: String Env -> Void
(define(interp-datatype name env)
  ; datatype predicate, eg. Nat?
  (update-env! (string->symbol (string-append (symbol->string name) "?"))
               (λ (v) (symbol=? (structV-name (first v)) name))
               env))

; interp-variant :: String String Env -> Void
(define(interp-variant name var env)  
  ;; name of the variant or dataconstructor
  (def varname (variant-name var))  
  ;; variant data constructor, eg. Zero, Succ
  (update-env! varname
               (λ (args) (structV name varname args))
               env)
  ;; variant predicate, eg. Zero?, Succ?
  (update-env! (string->symbol (string-append (symbol->string varname) "?"))
               (λ (v) (symbol=? (structV-variant (first v)) varname))
               env))

;;;;
; pattern matcher
(define(find-first-matching-case value cases)
  (match cases
    [(list) #f]
    [(cons (cse pattern body) cs)
     (match (match-pattern-with-value pattern value)
       [#f (find-first-matching-case value cs)]
       [alist (cons alist body)])]))

(define(match-pattern-with-value pattern value)
  (match/values (values pattern value)
                [((idP i) v) (list (cons i v))]
                [((litP (bool v)) b)
                 (if (equal? v b) (list) #f)]
                [((litP (num v)) n)
                 (if (equal? v n) (list) #f)]
                [((constrP ctr patterns) (structV _ ctr-name str-values))
                 (if (symbol=? ctr ctr-name)
                     (apply append (map match-pattern-with-value
                                        patterns str-values))
                     #f)]
                [(x y) (error "Match failure")]))

;; run :: s-expr -> number/boolean/procedure/Strings    <---- editada para listas y pretty printing
(define(run prog)
  (define prog-with-lists (list 'local '{{datatype List 
                                                   {Empty} 
                                                   {Cons head tail}}
                                         {define length {fun {l} 
                                                             {match l
                                                               {case {Empty} => 0}
                                                               {case {Cons head tail} => (+ 1 (length tail))}}}}}
                                prog))
  (let ([result (interp (parse prog-with-lists) empty-env)])
    (if (Struct? result)
        (pretty-printing result)
        result)))


#|-----------------------------
Environment abstract data type
empty-env   :: Env
env-lookup  :: Sym Env -> Val 
extend-env  :: List[Sym] List[Val] Env -> Env
update-env! :: Sym Val Env -> Void
|#
(deftype Env
  (mtEnv)
  (aEnv bindings rest)) ; bindings is a list of pairs (id . val)

(def empty-env  (mtEnv))

(define(env-lookup id env)
  (match env
    [(mtEnv) (error 'env-lookup "no binding for identifier: ~a" id)]
    [(aEnv bindings rest)
     (def binding (assoc id bindings))
     (if binding
         (cdr binding)
         (env-lookup id rest))]))

(define (extend-env ids vals env)
  (aEnv (map cons ids vals) ; zip to get list of pairs (id . val)
        env))

;; imperative update of env, adding/overring the binding for id.
(define(update-env! id val env)
  (set-aEnv-bindings! env (cons (cons id val) (aEnv-bindings env))))

;;;;;;;

;;; primitives
; http://pleiad.cl/teaching/primitivas
(define *primitives*
  `((+       ,(lambda args (apply + args)))
    (-       ,(lambda args (apply - args)))
    (*       ,(lambda args (apply * args)))
    (%       ,(lambda args (apply modulo args)))             
    (odd?    ,(lambda args (apply odd? args)))
    (even?   ,(lambda args (apply even? args)))
    (/       ,(lambda args (apply / args)))
    (=       ,(lambda args (apply = args)))
    (<       ,(lambda args (apply < args)))
    (<=      ,(lambda args (apply <= args)))
    (>       ,(lambda args (apply > args)))
    (>=      ,(lambda args (apply >= args)))
    (zero?   ,(lambda args (apply zero? args)))
    (not     ,(lambda args (apply not args)))
    (and     ,(lambda args (apply (lambda (x y) (and x y)) args)))
    (or      ,(lambda args (apply (lambda (x y) (or x y)) args)))))

;;--------------------------------

;; pretty-printing :: Struct -> string
;; retorna una estructura en forma de string legible
(define (pretty-printing s)
  (define (pretty-printing-2 s)
    (define (print-list l)
      (match l
        [(list x (structV 'List _ vals)) (string-append (pretty-printing-2 x) (print-list vals))]
        [empty ""]))
    (match s
      [(? boolean?) (string-append " " (format "~a" s))]
      [(? number?) (string-append " " (number->string s))]
      [(structV 'List _ vals) (string-append " (list" (print-list vals) ")")]
      [(structV name variant values) (string-append " {"(symbol->string variant) (pretty-printing-2 values)"}")]
      [(cons h t) (string-append (pretty-printing-2 h) (pretty-printing-2 t))]
      [_ ""]))
  (substring (pretty-printing-2 s) 1))


;--------- Código para lazy estraido de clase 04/26 

(deftype Val
  (numV n)
  (closureV fun body env)
  (exprV expr env cache))

;; strict :: Val -> Val (only numV or closureV)
(define (strict v)
  (match v
    [(exprV expr env cache)
     (if (unbox cache)
         (unbox cache)
         (begin
           (let ([val (strict (interp expr env))])
             (set-box! cache val)
             val))
         )]
    [ _ v]))
