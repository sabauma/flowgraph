#lang racket/base

(require redex)
(require "flow.rkt")

(define fact
  (term
    (BL (n)
        ((y0 := (lt n 1)))
        y0
        ((#f (LINK fact-rec (n y0)))
         (#t (LINK fact-ret (n)))
         ))))

(define fact-rec
  (term
    (BL (n y0)
        ((y1 := (sub n 1))
         (y2 := (call fact y1))
         (y3 := (mult n y2)))
        y3
        ())))

(define fact-ret
  (term
    (BL (n)
        ((y4 := (add 1)))
        y4
        ())))
(redex-match FLOW block fact)
(redex-match FLOW block fact-rec)
(redex-match FLOW block fact-ret)

(define factorial-function
  (term ((fact ,fact) (fact-ret ,fact-ret) (fact-rec ,fact-rec))))

(define call-factorial
  (term
    (BL ()
        ((n := (call fact 5)))
        n
        ())))

(define fact-prog
  (term (,call-factorial () ε ,factorial-function)))

(redex-match FLOW+AS state fact-prog)

(apply-reduction-relation* reduce-flow fact-prog)
;; (traces reduce-flow fact-prog)
