(declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (forall ((X Int)) (>= (f X) b)))
