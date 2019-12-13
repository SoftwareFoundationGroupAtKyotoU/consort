(declare-fun push-in-curr (Int Int) Bool)
(declare-fun push-in-len (Int Int) Bool)

(declare-fun after-check-curr (Int Int) Bool)
(declare-fun after-check-len (Int Int) Bool)

(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-in-curr curr len)
				  (push-in-len len curr)
				  (< curr len))
				 (after-check-curr curr len))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-in-curr curr len)
				  (push-in-len len curr)
				  (< curr len))
				 (after-check-len len curr))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-in-curr curr len)
				  (push-in-len len curr)
				  (not (< curr len)))
				 (after-check-curr curr (+ (* 2 len) 1)))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-in-curr curr len)
				  (push-in-len len curr)
				  (not (< curr len)))
				 (after-check-len (+ (* 2 len) 1) curr))))



(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (after-check-len len curr)
				  (after-check-curr curr len))
				 (< curr len))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (after-check-len len curr)
				  (after-check-curr curr len))
				 (push-in-curr (+ 1 curr) len))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (after-check-len len curr)
				  (after-check-curr curr len))
				 (push-in-len len (+ 1 curr)))))

(assert (push-in-curr 0 0))
(assert (push-in-len 0 0))

(check-sat-using horn)
(get-model)
