(declare-fun fib-in-n (Int) Bool)
(declare-fun fib-out-n (Int Int) Bool)

(assert
 (forall
  ((x Int))
  (=>
   (and
	(fib-in-n x)
	(< x 1))
   (fib-out-n 0 x))))


(assert
 (forall
  ((x Int))
  (=>
   (and
	(fib-in-n x)
	(= x 1))
   (fib-out-n 1 x))))

(assert
 (forall
  ((x Int))
  (=>
   (and
	(fib-in-n x)
	(> x 1))
   (fib-in-n (- x 1)))))


(assert
 (forall
  ((x Int))
  (=>
   (and
	(fib-in-n x)
	(> x 1))
   (fib-in-n (- x 2)))))

(assert
 (forall
  ((x Int) (r1 Int) (r2 Int))
  (=>
   (and
	(fib-in-n x)
	(fib-out-n r1 (- x 1))
	(fib-out-n r2 (- x 2)))
   (fib-out-n (+ r1 r2) x))))

(assert (fib-in-n 5))

(assert
 (forall
  ((ret Int))
  (=>
   (and
	(fib-in-n 5)
	(fib-out-n ret 5))
   (= ret 5))))

(check-sat-using horn)
(get-model)
