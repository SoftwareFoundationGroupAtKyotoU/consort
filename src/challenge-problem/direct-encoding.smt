(declare-fun push-curr-in (Int Int) Bool)
(declare-fun push-len-in (Int Int) Bool)
(declare-fun push-len-join (Int Int) Bool)
(declare-fun push-curr-join (Int Int) Bool)
(declare-fun update-curr-in (Int Int) Bool)
(declare-fun update-len-in (Int Int) Bool)

(declare-fun update-curr-out (Int Int) Bool)
(declare-fun update-len-out (Int Int) Bool)


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-curr-in curr len)
				  (push-len-in len curr)
				  (= curr len))
				 (push-curr-join curr (+ (* 2 len) 1)))))
				  
(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-curr-in curr len)
				  (push-len-in len curr)
				  (= curr len))
				 (push-len-join (+ (* 2 len) 1) curr))))

(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-curr-in curr len)
				  (push-len-in len curr)
				  (not (= curr len)))
				 (push-len-join len curr))))

(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-curr-in curr len)
				  (push-len-in len curr)
				  (not (= curr len)))
				 (push-curr-join curr len))))



(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-curr-join curr len)
				  (push-len-join len curr))
				 (update-curr-in curr len))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (push-curr-join curr len)
				  (push-len-join len curr))
				 (update-len-in len curr))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (update-curr-in curr len)
				  (update-len-in len curr))
				 (< curr len))))

(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (update-curr-in curr len)
				  (update-len-in len curr))
				 (update-len-out len (+ curr 1)))))

(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (update-curr-in curr len)
				  (update-len-in len curr))
				 (update-curr-out (+ curr 1) len))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (update-curr-out curr len)
				  (update-len-out len curr))
				 (push-curr-in curr len))))


(assert (forall ((curr Int) (len Int))
				(=>
				 (and
				  (update-curr-out curr len)
				  (update-len-out len curr))
				 (push-len-in len curr))))

;; (assert (push-curr-in 0 0))
;; (assert (push-len-in 0 0))

(assert (forall ((i-curr Int) (i-len Int))
				(=>
				 (and
				  (<= i-curr i-len)
				  (<= 0 i-len))
				 (push-curr-in i-curr i-len))))


(assert (forall ((i-curr Int) (i-len Int))
				(=>
				 (and
				  (<= i-curr i-len)
				  (<= 0 i-len))
				 (push-len-in i-len i-curr))))

(check-sat-using horn)
(get-model)
