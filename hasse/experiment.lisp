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
  (max(degree num1)
        (degree den)
      (+ (degree num2) 1) )



      
