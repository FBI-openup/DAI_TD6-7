(set-logic QF_LRA)
(declare-fun x0 () Real)
(declare-fun y0 () Real)
(declare-fun x1 () Real)
(declare-fun y1 () Real)
(declare-fun x2 () Real)
(declare-fun y2 () Real)
(declare-fun x3 () Real)
(declare-fun y3 () Real)

(declare-fun l0 () Bool) (declare-fun r0 () Bool) (declare-fun u0 () Bool) (declare-fun d0 () Bool)
(declare-fun l1 () Bool) (declare-fun r1 () Bool) (declare-fun u1 () Bool) (declare-fun d1 () Bool)
(declare-fun l2 () Bool) (declare-fun r2 () Bool) (declare-fun u2 () Bool) (declare-fun d2 () Bool)

; Initial state
(assert (= x0 0.0))
(assert (= y0 0.0))

; Target state (reachable in 3 steps e.g. (2,1) -> R, R, U)
(assert (= x3 2.0))
(assert (= y3 1.0))

; Exactly one action per step
(assert (or l0 r0 u0 d0)) (assert (not (and l0 r0))) (assert (not (and l0 u0))) (assert (not (and l0 d0))) (assert (not (and r0 u0))) (assert (not (and r0 d0))) (assert (not (and u0 d0)))
(assert (or l1 r1 u1 d1)) (assert (not (and l1 r1))) (assert (not (and l1 u1))) (assert (not (and l1 d1))) (assert (not (and r1 u1))) (assert (not (and r1 d1))) (assert (not (and u1 d1)))
(assert (or l2 r2 u2 d2)) (assert (not (and l2 r2))) (assert (not (and l2 u2))) (assert (not (and l2 d2))) (assert (not (and r2 u2))) (assert (not (and r2 d2))) (assert (not (and u2 d2)))

; Transitions
(assert (=> l0 (and (= x1 (- x0 1.0)) (= y1 y0)))) (assert (=> r0 (and (= x1 (+ x0 1.0)) (= y1 y0)))) (assert (=> u0 (and (= x1 x0) (= y1 (+ y0 1.0))))) (assert (=> d0 (and (= x1 x0) (= y1 (- y0 1.0)))))
(assert (=> l1 (and (= x2 (- x1 1.0)) (= y2 y1)))) (assert (=> r1 (and (= x2 (+ x1 1.0)) (= y2 y1)))) (assert (=> u1 (and (= x2 x1) (= y2 (+ y1 1.0))))) (assert (=> d1 (and (= x2 x1) (= y2 (- y1 1.0)))))
(assert (=> l2 (and (= x3 (- x2 1.0)) (= y3 y2)))) (assert (=> r2 (and (= x3 (+ x2 1.0)) (= y3 y2)))) (assert (=> u2 (and (= x3 x2) (= y3 (+ y2 1.0))))) (assert (=> d2 (and (= x3 x2) (= y3 (- y2 1.0)))))

; Define avoid_obstacle function
(define-fun avoid_obstacle ((x Real) (y Real) (x_min Real) (x_max Real) (y_min Real) (y_max Real)) Bool
  (or (< x x_min) (> x x_max) (< y y_min) (> y y_max))
)

; Obstacles at each step
(assert (avoid_obstacle x1 y1 4.0 5.0 4.0 5.0))
(assert (avoid_obstacle x2 y2 4.0 5.0 4.0 5.0))
(assert (avoid_obstacle x3 y3 4.0 5.0 4.0 5.0))

(check-sat)
(get-model)
