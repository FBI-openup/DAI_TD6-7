(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun y0 () Real)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun l0 () Bool)
(declare-fun r0 () Bool)
(declare-fun u0 () Bool)
(declare-fun d0 () Bool)

; Initial state
(assert (= x0 0.0))
(assert (= y0 0.0))

; Target state
(assert (= x1 1.0))
(assert (= y1 1.0))

; Exactly one action
(assert (or l0 r0 u0 d0))
(assert (not (and l0 r0)))
(assert (not (and l0 u0)))
(assert (not (and l0 d0)))
(assert (not (and r0 u0)))
(assert (not (and r0 d0)))
(assert (not (and u0 d0)))

; Transitions
(assert (=> l0 (and (= x1 (- x0 1.0)) (= y1 y0))))
(assert (=> r0 (and (= x1 (+ x0 1.0)) (= y1 y0))))
(assert (=> u0 (and (= x1 x0) (= y1 (+ y0 1.0)))))
(assert (=> d0 (and (= x1 x0) (= y1 (- y0 1.0)))))

; Define avoid_obstacle function
(define-fun avoid_obstacle ((x Real) (y Real) (x_min Real) (x_max Real) (y_min Real) (y_max Real)) Bool
  (or (< x x_min) (> x x_max) (< y y_min) (> y y_max))
)

; Avoid obstacle at reasonable position e.g. [2.0, 3.0, 2.0, 3.0]
(assert (avoid_obstacle x1 y1 2.0 3.0 2.0 3.0))

(check-sat)
(get-model)
