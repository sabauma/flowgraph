#lang racket

(require redex)

(define-language FLOW
  (block    (BL (arg ...) (op ...) x L))
  (op       (x := (opname arg ...)))
  (opname   primop call)
  (primop   add sub mult div equal lt)
  (arg      n x)
  (n        integer)
  (x        variable-not-otherwise-mentioned)
  (P        ((x F) ...))     ;; Program env    -- mapping from names to functions
  (E        ((x any) ...))   ;; Evaluation env -- mapping from names to values
  (F        ((x block) ...)) ;; Block env      -- mapping from names to blocks
  (L        ((n x) ...))     ;; Link env       -- mapping from values to names
  )

(define-metafunction FLOW
  δ : primop (arg ...) -> number
  [(δ add   (arg ...)) ,(apply + (term (arg ...)))]
  [(δ sub   (arg ...)) ,(apply - (term (arg ...)))]
  [(δ mult  (arg ...)) ,(apply * (term (arg ...)))]
  [(δ div   (arg ...)) ,(apply / (term (arg ...)))]
  [(δ equal (arg ...)) ,(if (apply = (term (arg ...))) 1 0)]
  [(δ lt    (arg ...)) ,(if (apply < (term (arg ...))) 1 0)]
  )

(define-extended-language FLOW+AS FLOW
  (S ε (FR E F x block S)) ;; Stack: environment and remainder of block
  ;; Interpreter state consissts of
  ;; * Current block being interpreted
  ;; * Environment
  ;; * Stack
  ;; * Current function (collection of blocks)
  ;; * Current program  (collection of functions)
  (state (DONE n) (block E S F P))
  )

;; Based off of https://github.com/esilkensen/cwc/blob/master/mates-silkensen.rkt
(define-metafunction FLOW+AS
  extend : ((x any) ...) (x ...) (any ...) -> ((x any) ...)
  [(extend ((x_1 any_1) ...) (x ..._n) (any ..._n))
   ((x_1 any_1) ... (x any) ...)]
  )

;; Looking up bindings in environments:
(define-metafunction FLOW+AS
  lookup-env : E x -> any
  [(lookup-env ((x_1 any_1) ... (x any) (x_2 any_2) ...) x)
    any
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup-env ((x_1 any_1) ...) x_2) #f]
  )

;; Looking up bindings in environments:
(define-metafunction FLOW+AS
  lookup-func : P x -> any
  [(lookup-func ((x_1 F_1) ... (x F) (x_2 F_2) ...) x)
    F
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup-func ((x_1 F_1) ...) x_2) #f]
  )

(define-metafunction FLOW+AS
  lookup-block : F x -> any
  [(lookup-block ((x_1 block_1) ... (x block) (x_2 block_2) ...) x)
    block
   (side-condition (not (member (term x) (term (x_2 ...)))))]
  [(lookup-block ((x_1 block_1) ...) x_2) #f]
  )

(define-metafunction FLOW+AS
  lookup-link : L n -> any
  [(lookup-link ((n_1 any_1) ... (n any) (n_2 any_2) ...) n)
    any
   (side-condition (not (member (term n) (term (n_2 ...)))))]
  [(lookup-link ((n_1 any_1) ...) n_2) #f]
  )

(define-metafunction FLOW+AS
  eval-arg : arg E -> any
  [(eval-arg n E) n]
  [(eval-arg x E) (lookup-env E x)]
  )

(define-metafunction FLOW
  eval-args : (arg ...) E -> (any ...)
  [(eval-args (arg ...) E) ((eval-arg arg E) ...)]
  )

(define-metafunction FLOW
  eval-primop : op E -> E
  [(eval-primop (x_2 := (primop arg ...)) E)
   (extend E (x_2) ((δ primop (eval-args (arg ...) E))))]
  )

(define-metafunction FLOW
  is-primop : op -> any
  [(is-primop (x := (primop arg ...))) #t]
  [(is-primop (x := (call arg ...)))   #f]
  )

(test-equal (term (extend ((d 1) (e 2)) (a b c) (1 2 3))) '((d 1) (e 2) (a 1) (b 2) (c 3)))
(test-equal (term (eval-args (a b c) ((a 1) (b 2)))) '(1 2 #f))
(test-equal (term (eval-arg c ((a 1) (b 2) (c 3)))) 3)
(test-equal (term (eval-arg 4 ((a 1) (b 2) (c 3)))) 4)
(test-equal (term (eval-primop (x := (add 1 2)) ())) '((x 3)))
(test-equal (term (eval-primop (x := (add y z)) ((y 1) (z 2)))) '((y 1) (z 2) (x 3)))

(define-metafunction FLOW
  entry-block : F -> block
  [(entry-block F) (lookup-block F entry)]
  )

(define-metafunction FLOW
  setup-env : block (n ...) -> E
  [(setup-env (BL (arg ..._0) (op ...) x L) (n ..._0)) (extend () (arg ...) (n ...))]
  )

(define test-block1
  (term
    (BL ()
        ((x1 := (add 1 2))
         (x2 := (add 4 x1))
         (x3 := (mult 2 4)))
        x3
        ((1 B1) (8 B2) (-1 B3))
        )))

(redex-match FLOW block test-block1)

(define test-block2
  (term
    (BL ()
        ((y1 := (add 4 2))
         (y2 := (add y1 2))
         (y3 := (sub y2 2)))
        y3
        ())))
(redex-match FLOW block test-block2)

(define test-function
  (term ((B1 ,test-block1) (B2 ,test-block2))))

(define test-program
  (term (,test-block1 () ε ,test-function ((test ,test-function)))))

(redex-match FLOW+AS state test-program)

(define fact-entry
  (term
    (BL (n)
        ((y0 := (lt n 1)))
        y0
        ((0 rec) (1 ret)))))

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
(redex-match FLOW block fact-entry)
(redex-match FLOW block fact-rec)
(redex-match FLOW block fact-ret)

(define factorial-function
  (term ((entry ,fact-entry) (ret ,fact-ret) (rec ,fact-rec))))

(define call-factorial
  (term
    (BL ()
        ((n := (call fact 10)))
        n
        ())))

(define fact-prog
  (term (,call-factorial () ε () ((fact ,factorial-function)))))

(redex-match FLOW+AS state fact-prog)

(define-metafunction FLOW+AS
  copy-env : (arg ...) E -> E
  [(copy-env (arg ...) E)
   (extend () (arg ...) (eval-args (arg ...) E))]
  )

(define reduce-flow
  (reduction-relation FLOW+AS
    ;; Execute current primop
    (--> ((BL (arg ...) (op_1 op ...) x L) E S F P)
         ((BL (arg ...) (op ...) x L) (eval-primop op_1 E) S F P)
         flow-primop
         (side-condition (term (is-primop op_1))))

    ;; Perform call operation
    (--> ((BL (arg_0 ...) ((x_1 := (call arg arg_1 ...)) op ...) x L) E S F P)
         (block
          (setup-env block (eval-args (arg_1 ...) E))
          (FR E F x_1 (BL (arg_0 ...) (op ...) x L) S)
          F_1
          P)
         flow-call
         (where F_1 (lookup-func P arg))
         (where block (entry-block F_1)))

    ;; Done with the block, see if we can find the associated link
    ;; For now, we just send along the whole environment
    (--> ((BL (arg ...) () x L) E S F P)
         ((BL (arg_1 ...) (op_1 ...) x_1 L_1)
          (copy-env (arg_1 ...) E) S F P)
         flow-finish-block-link
         (where x_3 (lookup-link L (lookup-env E x)))
         (where (BL (arg_1 ...) (op_1 ...) x_1 L_1)
                (lookup-block F x_3)))

    ;; If we can't find an associated link, try the default link (-1)
    (--> ((BL (arg ...) () x L) E S F P)
         ((BL (arg_1 ...) (op_1 ...) x_1 L_1)
          (copy-env (arg_1 ...) E) S F P)
         flow-finish-block-default
         (where x_1 (lookup-link L -1))
         (where (BL (arg_1 ...) (op_1 ...) x_1 L_1) (lookup-block F x_1))
         (side-condition
           (and (term (lookup-env E x))
                (not (term (lookup-link L (lookup-env E x)))))))

    ;; Empty set of links means we have a return block.
    ;; We return the value in the exitswitch variable.
    (--> ((BL (arg ...) () x ()) E (FR E_1 F_1 x_1 block_1 S_1) F P)
         (block_1 (extend E_1 (x_1) ((lookup-env E x))) S_1 F_1 P)
         flow-return
         (side-condition (and (term (lookup-env E x)))))

    ;; Empty links with and empty stack means we are done
    (--> ((BL (arg ...) () x ()) E ε F P)
         (DONE (lookup-env E x))
         flow-exit)
    )
  )

;;(apply-reduction-relation* reduce-flow fact-prog)
(traces reduce-flow fact-prog)

