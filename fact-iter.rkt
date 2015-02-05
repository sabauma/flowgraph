#lang racket/base

(require redex)
(require "flow.rkt")

(define fact
  (term
    (BL (n)
        ()
        #f
        ((#f (LINK fact-loop (n 1)))
         ))))

(define fact-loop
  (term
    (BL (n acc)
        ((jit-merge-point 1)
         (jit-can-enter 1)
         (st := (lt n 1)))
        st
        ((#t (LINK fact-done (acc)))
         (#f (LINK fact-body (n acc))))
        )))

(define fact-body
  (term
    (BL (n acc)
        ((n1   := (sub n 1))
         (acc1 := (mult acc n)))
        #f
        ((#f (LINK fact-loop (n1 acc1)))))))

(define fact-done
  (term (BL (acc) () acc ())))

(redex-match FLOW+JIT block fact)
(redex-match FLOW+JIT block fact-loop)
(redex-match FLOW+JIT block fact-body)
(redex-match FLOW+JIT block fact-done)

(define factorial-function
  (term ((fact ,fact) (fact-loop ,fact-loop) (fact-body ,fact-body) (fact-done ,fact-done))))

(define call-factorial
  (term
    (BL ()
        ((n := (call fact 5)))
        n
        ())))

(define fact-prog
  (term (,call-factorial () ε ,factorial-function)))

(redex-match FLOW+JIT state fact-prog)

;;(apply-reduction-relation* reduce-jit fact-prog)
(traces reduce-jit fact-prog)

(define ex
  (term
     ((PB
      ()
      st
      ((#t (LINK fact-done (acc)))
       (#f
        (LINK
         fact-body
         (n acc)))))
     ((n 5) (acc 1) (st #f))
     (FR () n (PB () n ()) ε)
     ((fact
       (BL
        (n)
        ()
        #f
        ((#f
          (LINK
           fact-loop
           (n 1))))))
      (fact-loop
       (BL
        (n acc)
        ((jit-merge-point 1)
         (jit-can-enter 1)
         (st := (lt n 1)))
        st
        ((#t
          (LINK fact-done (acc)))
         (#f
          (LINK
           fact-body
           (n acc))))))
      (fact-body
       (BL
        (n acc)
        ((n1 := (sub n 1))
         (acc1 := (mult acc n)))
        #f
        ((#f
          (LINK
           fact-loop
           (n1 acc1))))))
      (fact-done
       (BL (acc) () acc ())))
     1
     ((st := (lt n 1))))))
;;(redex-match FLOW+JIT trace-state ex)

