;; (define-fun f-out-refinement ((out Int) (a1 Int) (a2 Int)) Bool
;;   (> out 1))

(declare-fun f-out-refinement (Int Int Int) Bool)

;; (define-fun fx-in-refinement ((in Int) (a1 Int) (a2 Int)) Bool
;;   (and
;;    (=> (= a1 3) (>= in 1)) (>= in 0)))

(declare-fun fx-in-refinement (Int Int Int) Bool)

;; (define-fun fb-in-refinement ((inFlag Int) (a1 Int) (a2 Int)) Bool
;;   (and
;;    (=> (= a1 3) (= inFlag 0))
;;     (=> (not (= a1 3)) (= inFlag 1))))

(declare-fun fb-in-refinement (Int Int Int) Bool)

;; (define-fun gx-in-refinement ((in Int) (a1 Int) (a2 Int)) Bool
;;   (and
;;    (=> (and (= a1 4) (= a2 3)) (>= in 1))
;;    (>= in 0)))

(declare-fun gx-in-refinement (Int Int Int) Bool)

;; (define-fun g-out-refinement ((in Int) (a1 Int) (a2 Int)) Bool
;;   (and
;;    (=> (and (= a1 4) (= a2 3)) (>= in 2))
;;    (>= in 1)))

(declare-fun g-out-refinement (Int Int Int) Bool)

(assert (forall ((bFlag Int) (n Int) (t Int) (a1 Int) (a2 Int))
				(=>
				 (and
				  (fx-in-refinement n a1 a2)
				  (fb-in-refinement bFlag a1 a2)
				  (= bFlag 1))
				 (=>
				  (= t (+ n 1))
				  (fx-in-refinement t 3 a1)))))

(assert (forall ((inFlag Int) (argFlag Int) (a1 Int) (a2 Int))
				(=>
				 (and
				  (fb-in-refinement inFlag a1 a2)
				  (= inFlag 1))
				 (=> (= argFlag 0)
					(fb-in-refinement argFlag 3 a1)))))
				  

(assert (forall ((n Int) (inFlag Int) (a1 Int) (a2 Int))
				(=>
				 (and
				  (fb-in-refinement inFlag a1 a2)
				  (= inFlag 1))
				 (=> (f-out-refinement n 3 a1) (f-out-refinement n a1 a2)))))

(assert (forall ((n Int) (argVal Int) (bFlag Int) (a1 Int) (a2 Int))
				(=> (and (fb-in-refinement bFlag a1 a2) (= bFlag 0) (fx-in-refinement argVal a1 a2))
				   (=> (g-out-refinement n 4 a1) (f-out-refinement n a1 a2)))))

(assert (forall ((n Int) (bFlag Int) (a1 Int) (a2 Int))
				(=> (and (fx-in-refinement n a1 a2) (fb-in-refinement bFlag a1 a2) (= bFlag 0))
				   (gx-in-refinement n 4 a1))))

(assert (forall ((n Int) (t Int) (a1 Int) (a2 Int))
				(=> (and (gx-in-refinement n a1 a2) (= t (+ n 1))) (g-out-refinement t a1 a2))))

(assert (fx-in-refinement 0 1 0))

(assert (fb-in-refinement 1 1 0))

(assert (gx-in-refinement 0 2 0))

(assert (forall ((r1 Int) (r2 Int))
				(=>
				 (and (f-out-refinement r1 1 0)
					  (g-out-refinement r2 2 0))
				 (> (+ r1 r2) 2))))

(check-sat)
(get-model)
