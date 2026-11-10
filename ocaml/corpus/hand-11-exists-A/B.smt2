(declare-fun c () Int)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(assert (forall ((X Int)) (=> (> X a) (distinct (f X) c))))
