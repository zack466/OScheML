; calculates square roots using newton's method

; (define y 1.0) ; initial guess

; (define x 100.0) ; square of target

; (define dx 0.0001)

(define (abs x)
  (if (< x 0) (- x) x))

(define (sqrt x)
  (define (good-enough? y dx)
    (> dx (abs (- x (* y y)))))
  (define (improve guess)
    (* 0.5 (+ guess (/ x guess))))
  (define (rec guess)
    (if (good-enough? guess 0.0001) guess (rec (improve guess)))
   )
  (rec 1.0)
  )

(sqrt 1234)


