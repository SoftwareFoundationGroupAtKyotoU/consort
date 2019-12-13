(declare-fun addition-in-m (Int Int) Bool)
(declare-fun addition-in-n (Int Int) Bool)

(declare-fun addition-out-m (Int Int) Bool)
(declare-fun addition-out-n (Int Int) Bool)

(declare-fun addition-out (Int Int Int) Bool)

(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (= n 0))
		  (addition-out m n m))))


(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (= n 0))
		  (addition-out-m m n))))

(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (= n 0))
		  (addition-out-n n m))))

(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (> n 0))
		  (addition-in-m (+ m 1) (- n 1)))))


(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (> n 0))
		  (addition-in-n (- n 1) (+ m 1)))))


(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (< n 0))
		  (addition-in-n (+ n 1) (- m 1)))))


(assert
 (forall ((m Int) (n Int))
		 (=>
		  (and
		   (addition-in-m m n)
		   (addition-in-n n m)
		   (< n 0))
		  (addition-in-m (- m 1) (+ n 1)))))

(assert
 (forall ((m Int) (n Int) (ret Int))
		 (=>
		  (and (> m 0)
			   (> n 0)
			   (addition-in-m m n)
			   (addition-in-n n m)
			   (addition-out m n ret))
		  (= ret (+ m n)))))

(check-sat-using horn)
