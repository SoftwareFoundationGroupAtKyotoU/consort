(define-fun plus-+-out ((out Int) (x1 Int) (x2 Int)) Bool
  (= out (+ x1 x2)))

(define-fun minus---out ((out Int) (x1 Int) (x2 Int)) Bool
  (= out (- x1 x2)))

(define-fun not-eq ((n1 Int) (n2 Int)) Bool
  (not (= n1 n2)))

(define-fun rel-<-out ((out Int) (x1 Int) (x2 Int)) Bool
 (ite (< x1 x2) (= out 0)
	   (= out 1)))
