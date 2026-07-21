(defun eval-poly (coeffs x)
  (if (endp coeffs)
      0
    (+ (car coeffs)
       (* x (eval-poly (cdr coeffs) x)))))

(defun eval-ratfun (num1 num2 den x y)
  (/ (+ (eval-poly num1 x) (* y (eval-poly num2 x)))
     (eval-poly den x)))

(defun degree(p n)
  (if (endp p)
      -1
    (max (if (equal (car p) 0) -1 n)
         (degree (cdr p) (+ 1 n)))))

(defun degreerat(num1 num2 den)
  (max( (max(degree num1)
        (degree den))
      (+ (degree num2) 1) )

(defun eval-end(num1 num2 den1 den2 x y)
  (list (/ (eval-poly num1 x) (eval-poly den1 x))
            (* y (/ (eval-poly num2 x) (eval-poly den2 x)))))

(defun degree-end(num1 num2 den1 den2)
  (max(degree num1)
      (degree den1)))
      
;assume predicate separable exists 

(defun point-elliptic-curve(a b x y)
  (equal (* y y)
         (+ (* x x x)
            (* a x)
            b)))  
(defun power(x q)
  (if (zp q)
      1
    (* x (pow x (- q 1)))))

(defun eval-frobenius (x y q)
  (list (power(x q) power(y q))))



