#lang play

(require "main.rkt")
;(print-only-errors #t)
;; Test sub-module.
;; See http://blog.racket-lang.org/2012/06/submodules.html

;this tests should never fail; these are tests for MiniScheme+ 
(module+ test
  (test (run '{+ 1 1}) 2)
  
  (test (run '{{fun {x y z} {+ x y z}} 1 2 3}) 6)  
  
  (test (run '{< 1 2}) #t)
  
  (test (run '{local {{define x 1}}
                x}) 1)
  
  (test (run '{local {{define x 2}
                      {define y {local {{define x 1}} x}}}
                {+ x x}}) 4)
  
  ;; datatypes  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {List? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Cons 1 2}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Cons 1 2}}})
        #f)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Empty? {Empty}}}) #t)
  
  (test (run '{local {{datatype List {Empty} {Cons a b}}} {Cons? {Empty}}})
        #f)      
  
  ;; match
  (test (run '{match 1 {case 1 => 2}}) 2)
  
  (test (run '{match 2
                {case 1 => 2}
                {case 2 => 3}})             
        3)
  
  (test (run '{match #t {case #t => 2}}) 2)
  
  (test (run '{match #f
                {case #t => 2}
                {case #f => 3}})             
        3)

  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}})
        #t)
  (test (run '{local {{datatype Nat
                                {Zero}
                                {Succ n}}
                      {define pred {fun {n} 
                                        {match n
                                          {case {Zero} => {Zero}}
                                          {case {Succ m} => m}}}}}
                {Succ? {pred {Succ {Succ {Zero}}}}}}) #t)
  )
; tests listas
(module+ test
  ;; pretty-printing
  (test (pretty-printing(structV 'Nat 'Succ (list (structV 'Nat 'Zero empty)))) "{Succ {Zero}}")
  (test (pretty-printing(structV 'Pair 'Left(list  1 (structV 'Pair 'Right (list 2))))) "{Left 1 {Right 2}}")
  (test (pretty-printing(structV 'Booleans 'Set (list #f (structV 'Booleans 'Empty empty) #t))) "{Set #f {Empty} #t}")
  ;; lists and length
  (test (run '{List? {Empty}}) #t)
  (test (run '{List? {Cons 1 {Empty}}}) #t)
  (test (run '{Cons? {Cons 1 2}}) #t)
  (test (run '{length {Empty}}) 0)
  (test (run '{length {Cons 1{ Cons 2{Empty}}}}) 2)
  ;; sintactic sugar for lists
  (test (run '{match {list {+ 1 1} 4 6}
                {case {Cons h r} => h}
                {case _ => 0}}) 2)
  (test (run '{length {list 1 2 3}}) 3)
  ;; pattern matching lists
  (test (run '{match {list 2 {list 4 5} 6}
                {case {list a {list b c} d} => c}}) 5)
  ;; pretty printing lists
  (test (run '{list 1 4 6}) "(list 1 4 6)")
  
  )

; tests lazyness
(module+ test
  (test (run '{{fun {x  {lazy y}} x} 1 {/ 1 0}}) 1)
  (test (run '{{fun {x  {lazy y}} x} 1 {/ 1 z}}) 1)
  (test/exn (run '{{fun {x y} x} 1 z}) "no binding for identifier: z") 

  )
;tests for extended MiniScheme+ 
#;(module+ sanity-tests
    (test (run '{local {{datatype Nat 
                                  {Zero} 
                                  {Succ n}}
                        {define pred {fun {n} 
                                          {match n
                                            {case {Zero} => {Zero}}
                                            {case {Succ m} => m}}}}}
                  {pred {Succ {Succ {Zero}}}}}) "{Succ {Zero}}")
  
    (test (run
           `{local ,stream-lib
              {local {,ones ,stream-take}
                {stream-take 11 ones}}}) "{list 1 1 1 1 1 1 1 1 1 1 1}")

    (test (run `{local ,stream-lib
                  {local {,stream-zipWith ,fibs}
                    {stream-take 10 fibs}}}) "{list 1 1 2 3 5 8 13 21 34 55}")

    (test (run `{local ,stream-lib
                  {local {,ones ,stream-zipWith}
                    {stream-take 10
                                 {stream-zipWith
                                  {fun {n m}
                                       {+ n m}}
                                  ones
                                  ones}}}})  "{list 2 2 2 2 2 2 2 2 2 2}")
    (test 
     (run `{local ,stream-lib
             {local {,stream-take ,merge-sort ,fibs ,stream-zipWith}
               {stream-take 10 {merge-sort fibs fibs}}}})   "{list 1 1 1 1 2 2 3 3 5 5}"))

