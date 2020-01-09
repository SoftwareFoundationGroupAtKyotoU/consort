(declare-fun list-1-entry (Int) Bool)

(declare-fun entry-out (Int Int Int Bool) Bool)
(declare-fun entry-ret-unfold (Int Int) Bool)

(declare-fun p-unfold (Int Int) Bool)

(declare-fun post-call (Int Int Int Bool) Bool)

(assert
 (forall ((x Int) (nondet Int) (null1 Int) (null2 Int))
		 (=>
		  (and
		   (= nondet 0)
		   (list-1-entry x))
		  (entry-out x null1 null2 true))))


(assert
 (forall ((x Int) (nondet Int) (null1 Int) (null2 Int))
		 (=>
		  (and
		   (not (= nondet 0))
		   (list-1-entry x))
		  (list-1-entry (+ x 1)))))

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool))
		 (=>
		  (and
		   (not (= nondet 0))
		   (list-1-entry x)
		   (entry-out (+ x 1) hd tl null?))
		  (post-call x hd tl null?))))

(declare-fun post-fold (Int Int Int Bool Int Int Bool) Bool)

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int) (nondet2 Int))
		 (=>
		  (and
		   (list-1-entry x)
		   (post-call x hd tl true)
		   (not (= nondet 0)))
		  (post-fold x hd tl true x nondet2 false))))

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int))
		 (=>
		  (and
		   (post-call x hd tl false)
		   (not (= nondet 0)))
		  (post-fold x hd tl false x hd false))))

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int))
		 (=>
		  (and
		   (post-call x hd tl null?)
		   (not (= nondet 0)))
		  (post-fold x hd tl null? x tl false))))

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int))
		 (=>
		  (and
		   (post-call x hd tl false)
		   (not (= nondet 0)))
		  (p-unfold x hd))))

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int))
		 (=>
		  (entry-ret-unfold hd tl)
		  (p-unfold hd tl))))

(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int))
		 (=>
		  (and
		   (post-fold x hd tl null? p->hd p->tl false))
		  (entry-out x p->hd p->tl false))))


(assert
 (forall ((x Int) (nondet Int) (hd Int) (tl Int) (null? Bool) (p->hd Int) (p->tl Int))
		 (=>
		   (p-unfold hd tl)
		   (entry-ret-unfold hd tl))))

(assert
 (forall ((x Int) (y Int))
		 (=>
		  (entry-ret-unfold x y)
		  (< x y))))

(assert (forall ((h Int)) (list-1-entry 0)))

(check-sat-using horn)
(get-model)
