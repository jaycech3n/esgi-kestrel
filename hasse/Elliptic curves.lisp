(defun ec-curve (p a b)
(list p a b))
 
(defun ec-parameter-p (curve)
(first curve))
 
(defun ec-parameter-a (curve)
(second curve))
 
(defun ec-parameter-b (curve)
(third curve))

;multiply by natural number n
(defun f-nsmul (n x p) 
  (if (zp n)
      (f0)
    (f+ x
        (f-nsmul (- n 1) x p)
        p)))

;define elliptic curve
(defun ec-curve-p (curve)
  (and (true-listp curve)
       (equal (len curve) 3)

       (let ((p (ec-parameter-p curve))
             (a (ec-parameter-a curve))
             (b (ec-parameter-b curve)))

         (and (natp p)
              (< 3 p)

;define point on elliptic curve
(defun make-ec-point (x y)
  (cons x y))

(defun ec-point-x (point)
  (car point))

(defun ec-point-y (point)
  (cdr point))

(defun ec-infinity-p (point)
  (equal point :infinity))

(defun ec-affine-point-p (point curve)
  (and (consp point)
       (ec-curve-p curve)

       (let* ((x (ec-point-x point))
              (y (ec-point-y point))
              (p (ec-parameter-p curve))
              (a (ec-parameter-a curve))
              (b (ec-parameter-b curve)))

         (and
          (fp x p)
          (fp y p)
          (equal
           (f-square y p)
           (f+ (f+ (f-cube x p)
                   (f* a x p)
                   p)
               b
               p))))))
;either satisfy defining equation or point at infinity
(defun ec-point-p (point curve)
  (and (ec-curve-p curve)
       (or (ec-infinity-p point)
           (ec-affine-point-p point curve))))


(defun ec-add (p1 p2 curve)
  (cond
   ;; O + p2 = p2
   ((ec-infinity-p p1)
    p2)

   ;; p1 + O = p1
   ((ec-infinity-p p2)
    p1)

   (t
    (let* ((p  (ec-p curve))
           (a  (ec-a curve))
           (x1 (ec-point-x p1))
           (y1 (ec-point-y p1))
           (x2 (ec-point-x p2))
           (y2 (ec-point-y p2)))

      (cond
       ;; p2 = -p1, so p1 + p2 = O.
       ((and (equal x1 x2)
             (equal (f+ y1 y2 p) (f0)))
        :infinity)

       ;; Point doubling: p1 = p2.
       ((and (equal x1 x2)
             (equal y1 y2))
        (let* (;; lambda = (3*x1^2 + a) / (2*y1)
               (x1-squared (f* x1 x1 p))
               (three-x1-squared
                (f+ x1-squared
                    (f+ x1-squared x1-squared p)
                    p))
               (numerator
                (f+ three-x1-squared a p))
               (denominator
                (f+ y1 y1 p))
               (lambda
                (f* numerator
                    (f/ denominator p)
                    p))

               ;; x3 = lambda^2 - x1 - x2
               (x3
                (f+ (f+ (f* lambda lambda p)
                        (f- x1 p)
                        p)
                    (f- x2 p)
                    p))

               ;; y3 = lambda*(x1 - x3) - y1
               (y3
                (f+ (f* lambda
                        (f+ x1 (f- x3 p) p)
                        p)
                    (f- y1 p)
                    p)))
          (make-ec-point x3 y3)))

       ;; normal addition: p1 \neq p2.
       (t
        (let* (;; lambda = (y2 - y1) / (x2 - x1)
               (numerator
                (f+ y2 (f- y1 p) p))
               (denominator
                (f+ x2 (f- x1 p) p))
               (lambda
                (f* numerator
                    (f/ denominator p)
                    p))

               ;; x3 = lambda^2 - x1 - x2
               (x3
                (f+ (f+ (f* lambda lambda p)
                        (f- x1 p)
                        p)
                    (f- x2 p)
                    p))

               ;; y3 = lambda*(x1 - x3) - y1
               (y3
                (f+ (f* lambda
                        (f+ x1 (f- x3 p) p)
                        p)
                    (f- y1 p)
                    p)))
          (make-ec-point x3 y3))))))))
;; Definition of endomorphism of elliptic curves
(encapsulate
  (((ec-endo * *) => *))

  ;; Identity endomorphism as witness
  (local
   (defun ec-endo (point curve)
     point))

  ;; Closure
  (defthm ec-endo-closed
    (implies (and (ec-curve-p curve)
                  (ec-point-p point curve))
             (ec-point-p (ec-endo point curve)
                         curve)))

  ;; Preserves point at infinity.
  (defthm ec-endo-infinity
    (implies (ec-curve-p curve)
             (equal (ec-endo :infinity curve)
                    :infinity)))

  ;; Preserves elliptic curve addition.
  (defthm ec-endo-preserves-addition
    (implies (and (ec-curve-p curve)
                  (ec-point-p p1 curve)
                  (ec-point-p p2 curve))
             (equal
              (ec-endo (ec-add p1 p2 curve)
                       curve)
              (ec-add (ec-endo p1 curve)
                      (ec-endo p2 curve)
                      curve)))))
;;Torsion subgroups
(defun ec-n-torsion-point-p (point n curve)
  (and (natp n)
       (ec-curve-p curve)
       (ec-point-p point curve)
       (equal (ec-nsmul n point curve)
              :infinity)))

              
              
;;Exponentiation
(defun f-expt (x n p)
  (if (zp n)
      (f1)
    (f* x
        (f-expt x (- n 1) p)
        p)))
              
;; Frobenius endomorphism
(defun frobenius (point curve)
  (if (ec-infinity-p point)
      :infinity
    (let* ((p (ec-p curve))
           (x (ec-point-x point))
           (y (ec-point-y point)))
      (make-ec-point
       (f-expt x p p)
       (f-expt y p p)))))

;;Scalar multiplication of points on curve
(defun ec-nsmul (n point curve)
  (if (zp n)
      :infinity
    (ec-add point
            (ec-nsmul (- n 1) point curve)
            curve)))


              
;;Square Frobenius
(defun ec-frobenius-squared (point curve)
  (ec-frobenius
   (ec-frobenius point curve)
   curve))
              
              
;;Characteristic equation
(defun ec-frobenius-char-equation-p
       (point curve q trace)
  (equal
   (ec-add
    (ec-frobenius-squared point curve)
    (ec-nsmul q point curve)
    curve)
   (ec-nsmul trace
             (ec-frobenius point curve)
             curve)))
              
(defthm ec-frobenius-characteristic-equation
  (implies
   (and (ec-curve-p curve)
        (ec-point-p point curve)
        (natp q)
        (natp trace)
        (equal trace
               (- (+ q 1)
                  (ec-number-of-points curve))))
   (ec-frobenius-char-equation-p
    point curve q trace)))
