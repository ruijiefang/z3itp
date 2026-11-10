(declare-fun c () Int)
(declare-fun f (Int) Int)
(declare-fun a () Int)
(assert (exists ((X Int)) (and (> X a) (= (f X) c))))
