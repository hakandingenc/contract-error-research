#lang racket

; [*] indicates changes made as a result of property testing

; Racket namespace used for `eval`uating primitive operators
(define-namespace-anchor anchor)
(define racket-namespace (namespace-anchor->namespace anchor))

(require redex)
(require redex/tut-subst) ; For pre-defined substitution function

; Language definition
(define-language λe+c
  ; (p e e e ...) is needed to avoid contract errors for primitive functions
  ; as they all need at least 2 arguments. [*]
  [e  x v (e e) (if e e e) (p e e e ...) (mon c e)]
  [n  number]
  [b  boolean]
  [p  + * > <]
  [c  (flat v) (-> c c)]
  [v  b n (λ x e) error]
  [x  variable-not-otherwise-mentioned]
  [E  hole (p v ... E e ...) (if E e e) (E e) (v E) (mon c E)]
  #:binding-forms
  (λ x e #:refers-to x))

; Capture-avoiding substitution
(define-metafunction λe+c
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc (redex-match λe+c x)
                (list (term x)) (list (term v)) (term e))])

; Primitive function application
(define-metafunction λe+c
  [(δ (p n ...)) ,(apply (eval (term p) racket-namespace)
                         (term (n ...)))])

; Reduction relation
(define λe+c-red
  (reduction-relation
   λe+c
   #:domain e
   ; Small-step reductions
   (-->> (p n ...)
         (δ (p n ...))
         "p")
   (-->> (if #t e_1 e_2)
         e_1
         "if-t")
   (-->> (if #f e_1 e_2)
         e_2
         "if-f")
   (-->> ((λ x e) v)
         (subst x v e)
         "β")
   (-->> (mon (flat v_1) v_2)
         (if (v_1 v_2) v_2 error)
         "mon-first"
         ; Prevent reducing monitors with error [*]
         (side-condition (not (equal? (term v_2)
                                      (term error)))))
   (-->> (mon (-> c_1 c_2) v)
         (λ x (mon c_2 (v (mon c_1 x))))
         "mon-higher"
         ; Prevent reducing monitors with error [*]
         (side-condition (not (equal? (term v)
                                      (term error)))))
   ; Reduction relation for discarding a context with `error`
   (--> (in-hole E error)
        error
        "error"
        ; Prevent cycle in the trace graph
        (side-condition (not (equal? (term E)
                                     (term hole)))))
   with
   ; Standard reduction relation
   [(--> (in-hole E a1) (in-hole E a2))
    (-->> a1 a2)]))

; Reduction tests
(test-->> λe+c-red
          (term ((mon (-> (flat (λ x (> x 0)))
                          (flat (λ x (> x 0))))
                      (λ x (* 2 (+ x 5)))) 10))
          (term 30))
(test-->> λe+c-red
          (term ((mon (->
                       (-> (flat (λ x (> x 0)))
                           (flat (λ x (< x 0))))
                       (flat (λ x (> x 0))))
                      (λ f (f 10)))
                 (λ x (* -1 x))))
          (term error))
(test-->> λe+c-red
          (term (((mon (->
                        (-> (flat (λ x (> x 0)))
                            (flat (λ x (> x 0))))
                        (-> (flat (λ x (> x 0)))
                            (flat (λ x (> x 0)))))
                       (λ f f))
                  (λ x (* 2 x)))
                 10))
          20)

(redex-check λe+c
             e
             (= (length (apply-reduction-relation* λe+c-red (term e))) 1)
             #:attempts 100000)
