; encodes the context 1 if alpha = l3?, 0 ow
(declare-fun ctxt () Int)
; value of b
(declare-fun flag () Int)
; f's return value
(declare-fun value () Int)
; value of n (irrelevant)
(declare-fun n-value () Int)

(assert (not (=>
  ; env constraints
  (and
    ; b's environment type 
    (and 
      (=> (= ctxt 1) (= flag 0)) (=> (not (= ctxt 1)) (= flag 1)) (= flag 0))
    ; n's environment type (this verifies even if this is commented out)
    (and
      (=> (= ctxt 1) (>= n-value 1)) (>= n-value 0)))
  (=> 
    ; result subtype
    (and (=> (= ctxt 1) (>= value 2)) (>= value 1))
    ; output type
    (> value 1)))))
(check-sat)
