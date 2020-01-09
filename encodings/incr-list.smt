(declare-fun add-entry (Int) Bool)
(declare-fun add-exit (Int Int Bool Int Bool) Bool)

(declare-fun check-in (Int Bool Int Bool) Bool)

(assert
 (forall ((g Int) (hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool))
		 (=>
		  (add-entry g)
		  (add-exit g hd false tl false))))


(assert
 (forall ((g Int) (hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool))
		 (=>
		  (add-entry g)
		  (add-entry (+ g 1)))))


(assert
 (forall ((g Int) (hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool))
		 (=>
		  (and 
		   (add-entry g)
		   (add-exit (+ g 1) hd hd!null? tl tl!null?))
		  (add-exit g g true hd hd!null?))))


(assert
 (forall ((g Int) (hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool))
		 (=>
		  (and 
		   (add-entry g)
		   (add-exit (+ g 1) hd hd!null? tl tl!null?))
		  (add-exit g g true tl tl!null?))))

(assert (add-entry 0))

(assert
 (forall ((g Int) (hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool))
		 (=>
		  (add-exit g hd true tl true)
		  (< hd tl))))

(declare-fun check-unfold (Int Bool Int Bool Int Int Bool Int Bool) Bool)

(assert
 (forall ((hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool) (nxt Int) (nxt->tl Int) (nxt->tl!null? Bool))
		 (=>
		  (and
		   (check-in hd true tl tl!null?)
		   (check-in hd true nxt tl!null?)
		   (check-in nxt tl!null? nxt->tl nxt->tl!null?)
		   (check-in hd true nxt->tl nxt->tl!null?)
		   (=> (not tl!null?) (not nxt->tl!null?)))

		  (check-unfold
		   hd true tl tl!null?
		   hd nxt tl!null? nxt->tl nxt->tl!null?))))

(assert
 (forall ((hd Int) (hd!null? Bool) (tl Int) (g Int) (tl!null? Bool) (nxt Int) (nxt->tl Int) (nxt->tl!null? Bool))
		 (=>
		  (check-unfold hd true tl tl!null? g nxt true nxt->tl nxt->tl!null?)
		  (< g nxt))))

(assert
 (forall ((g Int) (hd Int) (hd!null? Bool) (tl Int) (tl!null? Bool))
		 (=>
		  (add-exit 0 hd true tl true)
		  (check-in hd hd!null? tl tl!null?))))


(check-sat-using horn)
(get-model)
