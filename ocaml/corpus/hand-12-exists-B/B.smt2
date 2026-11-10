(declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (exists ((X Int)) (< (f X) (- b 1))))
