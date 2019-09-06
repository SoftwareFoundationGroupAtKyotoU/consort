(declare-fun sorted-in-hd (Int Int Bool) Bool)
(declare-fun sorted-in-tl (Int Int Bool) Bool)

(declare-fun sorted-out-tl (Int Int Bool) Bool)
(declare-fun sorted-out-hd (Int Int Int Bool) Bool)

;; nu x hd !old
(declare-fun next-null-cond-hd (Int Int Int Int Bool) Bool)
(declare-fun next-null-cond-tl (Int Int Bool) Bool)

;; nu x hd !old
(declare-fun new-null-l-hd (Int Int Int Int Bool) Bool)
(declare-fun new-null-l-tl (Int Int Bool) Bool)

;; nu x hd !old
(declare-fun fold-lt-null-tail-hd (Int Int Int Int Bool) Bool)
(declare-fun fold-lt-null-tail-tail (Int Int Bool) Bool)

(declare-fun fold-lt-null-list-hd (Int Int Int Int Bool) Bool)
(declare-fun fold-lt-null-list-tail (Int Int Bool) Bool)

(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (next-null-cond-hd nu x !old hd false)))

(assert
 (forall ((nu Int) (outer Int))
		 (next-null-cond-tl nu outer false)))

(assert
 (forall ((nu Int) (hd Int) (!old Int) (x Int))
		 (new-null-l-hd nu x hd !old false)))

(assert
 (forall ((nu Int) (outer Int))
		 (new-null-l-tl nu outer false)))

;; fold up x and null
;; the hd of the tail is equal to x, and greater than hd (and old)
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (=> (and
			 (< hd x) (= hd !old) (= nu x))
			(fold-lt-null-tail-hd nu x hd !old true))))

;; the tail is all null
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer Int))
		 (=> (and
			 (new-null-l-hd nu x hd !old false))
			(fold-lt-null-tail-hd nu x hd !old false))))

;; the tail is all null
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer Int) (null?0 Bool) (null?1 Bool))
		 (=> (and
			 ;; the "outer" refinement is the refinement of x
			 (= outer x)
			 (< hd x)
			 (= hd !old)
			 (sorted-in-hd hd x true)
			 (new-null-l-hd outer x hd !old null?0)
			 (new-null-l-hd nu x hd !old null?1)
			 (new-null-l-tl nu outer null?1))
			(fold-lt-null-tail-tail nu outer null?1))))

;; fold up the output value, it is equal to the hd
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer Int))
		 (=> (and
			 (< hd x) (= hd !old) (= nu hd) (sorted-in-hd hd x true))
			(fold-lt-null-list-hd nu x hd !old true))))

;; at this point, we need to fold up the recursive type in the tail, it is
;; (x1: fold-lt-null-tail-hd (nu,x,hd,!old),
;;    M a.(x2: fold-lt-null-tail-hd (nu,x,hd, !old) /\ fold-lt-null-tail-tail (nu, x1)))

;; fold the HEAD of the tail list into position
(assert
 ;; assert local refinements
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (=>
		  (and
		   ;; constants
		   (< hd x)
		   (= hd !old)
		   (sorted-in-hd hd x true)
		   ;; now the refinement of x
		   (fold-lt-null-tail-hd nu x hd !old true))
		  ;; which must satisfy the local refinement
		  (fold-lt-null-list-hd nu x hd !old true))))

 (assert
  ;; we are folding x2 in the list (x1: hd, (x2: x, null)) into position
  ;; x2 is refined by the head refinement of the fold-lt-null-tail 
  ;; here outer refers to the refinement of hd,
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer Int))
		 (=>
		  (and
		   ;; constants
		   (< hd x)
		   (= hd !old)
		   (sorted-in-hd hd x true)
		   ;; now the refinement of hd, which is outer
		   (fold-lt-null-tail-hd nu x hd !old true)
		   (sorted-in-hd outer x true)
		   (= outer hd))
		  ;; now assert we must satisfy the recursive refinement
		  (fold-lt-null-list-tail nu outer true))))

(define-fun lt-ante
  ((x Int) (hd Int) (!old Int)) Bool
  (and
   (< hd x)
   (sorted-in-hd hd x true)
   (= hd !old)))

;; outer-x is the value in the immediate enclosing tuple, which is x
(define-fun tail-tail-fold-ante
  ((nu Int) (x Int) (hd Int) (!old Int) (outer-x Int)) Bool

  (and
   (lt-ante x hd !old)
   (fold-lt-null-list-hd nu x hd !old false)
   (fold-lt-null-tail-tail nu outer-x false)
   (= outer-x x)))

;; fold the tail of the tail list into position
(assert
 ;; assert local refinements
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer-x Int))
		 (=>
		  (and
		   (tail-tail-fold-ante nu x hd !old outer-x))
		  ;; which must satisfy the local refinement
		  (fold-lt-null-list-hd nu x hd !old false))))

;; satisfy the recursive refinement with respect to the x position
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer-x Int))
		 (=>
		  (tail-tail-fold-ante nu x hd !old outer-x)
		  (fold-lt-null-list-tail nu outer-x false))))

;; satisfy the recursive refinement with respect to the hd position
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (outer-x Int) (outer-hd Int))
		 (=>
		  (and
		   (tail-tail-fold-ante nu x hd !old outer-x)
		   (sorted-in-hd outer-hd x true)
		   (= outer-hd hd))
		  (fold-lt-null-list-tail nu outer-hd false))))

;; now output for this case, less than, null tail
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (=> (fold-lt-null-list-hd nu x hd !old true)
			(sorted-out-hd nu !old x true))))

;; for the tail, we have nondeterministic nullity, quantify as appropriate
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (null? Bool) (outer-x Int))
		 (=> (and
			 (lt-ante x hd !old)
			 (fold-lt-null-list-hd outer-x x hd !old true)
			 (fold-lt-null-list-tail nu outer-x null?)
			 (fold-lt-null-list-hd nu x hd !old null?))
			(sorted-out-hd nu !old x null?))))

(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (null? Bool) (outer-x Int))
		 (=> (and
			 (lt-ante x hd !old)
			 (fold-lt-null-list-hd outer-x x hd !old true)
			 (fold-lt-null-list-tail nu outer-x null?)
			 (fold-lt-null-list-hd nu x hd !old null?))
			(sorted-out-tl nu outer-x null?))))

;;; *** THIS COMPLETES THE LESS THAN/NXT NULL CASE ***

;;; *** THE RECURSIVE CASE *** !!! DANGER WILL ROBINSON

(define-fun nnull-outer-ante ((x Int) (hd Int) (outer-x Int)) Bool
  (and
   (sorted-in-hd outer-x x true)
   (sorted-in-tl outer-x hd true)))

;; assert subtyping for the arguments
;; the hd of the tail (refined by nnull-outer-ante) satisfies the sorted-in-hd
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (=>
		  (and
		   (lt-ante x hd !old)
		   (nnull-outer-ante x hd nu))
		  (sorted-in-hd nu x true))))

;; the tail of the tail (refined by the conjunction of tail w.r.t hd, and tail w.r.t hd)
;; satisfies the head...
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (null? Bool) (outer-x Int))
		 (=>
		  (and
		   (lt-ante x hd !old)
		   ;; refine the cddr
		   (sorted-in-hd nu x null?)
		   (sorted-in-tl nu hd null?)
		   (sorted-in-tl nu outer-x null?)
		   (nnull-outer-ante x hd outer-x))
		  (sorted-in-hd nu x null?))))

;; ... and tail refinements
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (null? Bool) (outer-x Int))
		 (=>
		  (and
		   ;; refine the cddr
		   (lt-ante x hd !old)
		   (sorted-in-hd nu x null?)
		   (sorted-in-tl nu hd null?)
		   (sorted-in-tl nu outer-x null?)
		   (nnull-outer-ante x hd outer-x))
		  (sorted-in-tl nu outer-x null?))))

;; now, fold up the result into the output

;; the head is easy
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (=>
		  (and
		   (lt-ante x hd !old)
		   (= nu hd))
		  (sorted-out-hd nu !old x true))))

;; the tail is a LITTLE harder
;; the cdar (the argument, or "head" to the recursive call...

;; .. assert the local refinement of the output
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (pre!old Int))
		 (=>
		  (and
		   (lt-ante x hd !old)
		   ;; the previous type is refined by the type of the cdar
		   (nnull-outer-ante x hd pre!old)
		   ;; XXX: Should this be true? Or nondeterministic??
		   (sorted-out-hd nu pre!old x true))
		  (sorted-out-hd nu !old x true))))

;; .. assert the recursive refinement w.r.t to the car of the return, aka hd
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (pre!old Int))
		 (=>
		  (and
		   (lt-ante x hd !old)
		   ;; the previous type is refined by the type of the cdar
		   (nnull-outer-ante x hd pre!old)
		   ;; XXX: Should this be true? Or nondeterministic??
		   (sorted-out-hd nu pre!old x true))
		  (sorted-out-tl nu hd true))))

;; now, for the cdar of the input (or cdr of the recursive call),
;; assert the three assignments

;; refactor the antecedent into this function
(define-fun lt-nnull-cddr-ante ((x Int) (hd Int) (!old Int) (pre!old Int) (outer-x Int) (nu Int) (null? Bool)) Bool
  (and
   (lt-ante x hd !old)
   (nnull-outer-ante x hd pre!old)
   (sorted-out-hd outer-x pre!old x true)
   (sorted-out-hd nu pre!old x null?)
   (sorted-out-tl nu outer-x null?)))

(assert
 (forall ((x Int) (hd Int) (!old Int) (pre!old Int) (outer-x Int) (nu Int) (null? Bool))
		 (=>
		  (lt-nnull-cddr-ante x hd !old pre!old outer-x nu null?)
		  (and
		   (< hd x)
		   (sorted-in-hd hd x true)
		   (sorted-in-hd pre!old x true)
		   (sorted-in-tl pre!old hd true)
		   (sorted-out-hd outer-x pre!old x true)
		   (sorted-out-hd nu pre!old x null?)
		   (sorted-out-tl nu outer-x null?)))))

(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (pre!old Int) (outer-x Int) (null? Bool))
		 (=>
		  (lt-nnull-cddr-ante x hd !old pre!old outer-x nu null?)
		  (sorted-out-hd nu !old x null?))))

(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (pre!old Int) (outer-x Int) (null? Bool))
		 (=>
		  (lt-nnull-cddr-ante x hd !old pre!old outer-x nu null?)
		  (sorted-out-tl nu outer-x null?))))

(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int) (pre!old Int) (outer-x Int) (null? Bool))
		 (=>
		  (lt-nnull-cddr-ante x hd !old pre!old outer-x nu null?)
		  (sorted-out-tl nu hd null?))))

;; THIS ENDS THE RECURSIVE CASE

;; The less than case (relatively easy)

(define-fun ge-ante ((x Int) (hd Int) (!old Int)) Bool
  (and
   (>= hd x)
   (sorted-in-hd hd x true)
   (= hd !old)))

(assert
 (forall ((nu Int) (hd Int) (!old Int))
		 (=> (ge-ante nu hd !old)
			(sorted-out-hd nu !old nu true))))

;; fold the cdar (aka, hd) into the tail position of the return
;; here nu is hd
(assert
 (forall ((nu Int) (x Int) (!old Int))
		 (=>
		  (and
		   (ge-ante x nu !old))
		  (sorted-out-hd nu !old x true))))

;; here nu is hd
(assert
 (forall ((nu Int) (x Int) (!old Int))
		 (=>
		   (ge-ante x nu !old)
		   (sorted-out-tl nu x true))))

(define-fun ge-cddr-ante ((nu Int) (x Int) (hd Int) (!old Int) (null? Bool)) Bool
  (and
   (ge-ante x hd !old)
   (sorted-in-hd nu x null?)
   (sorted-in-tl nu hd null?)))

(assert
 (forall ((nu Int) (x Int) (hd Int) (!old Int) (null? Bool))
		 (=>
		  (ge-cddr-ante nu x hd !old null?)
		  (sorted-out-hd nu !old x null?))))

(assert
 (forall ((nu Int) (x Int) (hd Int) (!old Int) (null? Bool))
		 (=>
		  (ge-cddr-ante nu x hd !old null?)
		  (sorted-out-tl nu x null?))))

(assert
 (forall ((nu Int) (x Int) (hd Int) (!old Int) (null? Bool))
		 (=>
		  (ge-cddr-ante nu x hd !old null?)
		  (sorted-out-tl nu hd null?))))

;; grounding
(assert
 (forall ((nu Int) (hd Int))
		 (sorted-in-tl nu hd false)))

;; canaries (have I broken something)
(assert
 (forall ((x Int) (hd Int) (!old Int) (nu Int))
		 (=> (fold-lt-null-tail-hd nu x hd !old true)
			(< hd nu))))

(assert
 (forall ((outer Int) (nu Int))
		 (=> (fold-lt-null-tail-tail nu outer false) true)))

(assert
 (forall ((nu Int) (x Int) (hd Int) (!old Int))
		 (=> (fold-lt-null-tail-hd nu x hd !old true)
			(<= hd nu))))

(assert
 (forall ((hd Int) (tl Int))
		 (=> (sorted-out-tl tl hd true) (<= hd tl))))

(assert
 (forall ((nu Int) (x Int))
		 (sorted-in-hd nu x true)))


;; finally, the DRIVER constraints
;; that sort preserves recursive lists

(assert
 (forall ((nu Int) (!pre Int) (x Int) (y Int) (flag? Bool))
		 (=> (sorted-out-hd nu !pre x flag?)
			(sorted-in-hd nu y flag?))))

;; and that the tail of a sorted list remains sorted w.r.t the head
(assert
 (forall ((nu Int) (!pre Int) (x Int) (outer-x Int) (outer-flag? Bool) (inner-flag? Bool))
		 (=>
		  (and
		   (sorted-out-hd outer-x !pre x outer-flag?)
		   (sorted-out-tl nu outer-x inner-flag?))
		  (sorted-in-tl nu outer-x inner-flag?))))

;; This is the CRUCIAL sorted list invariant
(assert
 (forall ((nu Int) (x Int) (!pre Int))
		 (=> (sorted-out-hd nu !pre x true)
			(or
			 (<= !pre nu)
			 (<= x nu)))))

;; the sorted list invariant in action
(assert
 (forall ((nu Int) (x Int) (cdar-hd Int) (hd Int))
		 (=>
		  (and
		   (<= hd cdar-hd)
		   (< hd x)
		   (sorted-out-hd nu cdar-hd x true))
		  (<= hd nu))))

(check-sat-using horn)
(get-model)
