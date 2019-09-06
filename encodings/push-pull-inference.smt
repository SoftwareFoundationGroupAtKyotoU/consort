(declare-fun push-p-in (Int Int) Bool)
(declare-fun push-y-in (Int Int) Bool)
(declare-fun push-p-out (Int Int) Bool)

(declare-fun pull-p-in (Int Int) Bool)
(declare-fun pull-ret (Int Int) Bool)
(declare-fun merged-p (Int) Bool)

(define-fun l1 () Int 1)
(define-fun l2 () Int 2)
(define-fun l3 () Int 3)
(define-fun l4 () Int 4)
(define-fun l5 () Int 5)
(define-fun l6 () Int 6)

(assert (forall ((n Int) (y Int) (alpha Int))
				(=>
				 (and (push-y-in y alpha) (= n y))
				 (push-p-out n alpha))))

(assert (forall ((n Int) (alpha Int))
				(=> (pull-p-in n alpha) (pull-ret n alpha))))

(assert (forall ((n Int))
				(=> (= n 0) (push-y-in n l1))))
(assert (forall ((n Int))
				(=> (push-p-out n l1) (pull-p-in n l2))))
(assert (forall ((n Int))
				(=> (push-p-out n l1) (push-p-in n l3))))

(declare-fun constr1 (Int) Bool)
(assert (forall ((n Int)) (=> (> n 0) (constr1 n))))

(declare-fun constr2 (Int) Bool)
(assert (forall ((n Int)) (=> (> n 0) (constr2 n))))

(assert (forall ((n Int) (t Int) (incBy Int))
				(=> (and (constr1 incBy) (pull-ret n l2) (= t (+ n incBy))) (push-y-in t l3))))

(assert (forall ((n Int))
				(=> (push-p-out n l1) (push-p-in n l5))))

(assert (forall ((n Int) (t Int) (incBy Int))
				(=> (and (constr2 incBy) (pull-ret n l4) (= t (+ n incBy))) (push-y-in t l5))))

(assert (forall ((n Int))
				(=> (push-p-out n l1) (pull-p-in n l4))))

(assert (forall ((n Int))
				(=> (push-p-out n l5) (merged-p n))))

(assert (forall ((n Int))
				(=> (push-p-out n l3) (merged-p n))))

(assert (forall ((n Int))
				(=> (merged-p n) (>= n 1))))

(check-sat)
(get-model)
