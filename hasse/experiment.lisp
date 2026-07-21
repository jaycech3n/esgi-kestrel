(defun eval-poly (coeffs x)
  (if (endp coeffs)
      0
    (+ (car coeffs)
       (* x (eval-poly (cdr coeffs) x)))))

(defun eval-ratfun (num den x)
  (/ (eval-poly num x)
     (eval-poly den x)))

(defun degree(p n)
  (if (endp p)
      -1
    (max (if (equal (car p) 0) -1 n)
         (degree-aux (cdr p) (+ 1 n)))))
