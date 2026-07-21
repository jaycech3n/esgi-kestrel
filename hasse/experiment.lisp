;; evaluate polynomial (a_0,a_1, \dots, a_n) at x where a_i are coefficients
(defun eval-poly (coeffs x)
  (if (endp coeffs)
      0
    (+ (car coeffs)
       (* x (eval-poly (cdr coeffs) x)))))
;; evaluate a rational function of the form (p_1(x)+y*p_2(x))/q(x)
(defun eval-ratfun (num1 num2 den x y)
  (/ (+ (eval-poly num1 x) (* y (eval-poly num2 x)))
     (eval-poly den x)))

;; degree of a polynomial 
(defun degree(p n)
  (if (endp p)
      -1
    (max (if (equal (car p) 0) -1 n)
         (degree (cdr p) (+ 1 n)))))
;; degree of rational function of the form (p_1(x)+y*p_2(x))/q(x)
(defun degreerat(num1 num2 den)
  (max( (max(degree num1)
        (degree den))
      (+ (degree num2) 1) )
;; evaluate an endomorphism of the form (x,y) \mapsto (p_1(x)/q_1(x), p_2(x)/q_2(x)*y)
(defun eval-end(num1 num2 den1 den2 x y)
  (list (/ (eval-poly num1 x) (eval-poly den1 x))
            (* y (/ (eval-poly num2 x) (eval-poly den2 x)))))
;; definition of degree of endomorphism = degree of first component funciton
(defun degree-end(num1 num2 den1 den2)
  (max(degree num1)
      (degree den1)))
      
;;assume predicate separable exists 

;; check whether point (x,y) lies on the elliptic curve y^2=x^3+ax+b
(defun point-elliptic-curve(a b x y)
  (equal (* y y)
         (+ (* x x x)
            (* a x)
            b)))  
;; take x to the power of q     
(defun power(x q)
  (if (zp q)
      1
    (* x (pow x (- q 1)))))
;; evaluate the Frobenius map (x,y) \mapsto (x^q,y^q)
(defun eval-frobenius (x y q)
  (list (power(x q) power(y q))))

;; definition of field from acl2/books/projects/linear/field.lisp

(encapsulate (((fp *) => *)                   ;field element recognizer
              ((f+ * *) => *) ((f* * *) => *) ;addition and multiplication
	      ((f0) => *) ((f1) => *)         ;identities
	      ((f- *) => *) ((f/ *) => *))    ;inverses 
;; define finitefield: x is element of a list of field elements			 
(local (defun fp (x finitefield)
			 (if (endp finitefield)
				 nil
			 	(if (equal x (car finitefield))
						t
				 fp x (cdr finitefield)))))
;; addition mod p
  (local (defun f+mod-p (x y p) (mod (+ x y) p))

;; addition mod p^n (polynomials with coefficients in F_p)
(local (defun f+mod-pn (x y p n) 
		 
  (local (defun f* (x y) (* x y)))
  (local (defun f0 () 0))
  (local (defun f1 () 1))
  (local (defun f- (x) (- x)))
  (local (defun f/ (x) (/ x)))
  ;; Closure:
  (defthm f+closed (implies (and (fp x) (fp y)) (fp (f+ x y))))
  (defthm f*closed (implies (and (fp x) (fp y)) (fp (f* x y))))
  ;; Commutativity
  (defthmd f+comm (implies (and (fp x) (fp y)) (equal (f+ x y) (f+ y x))))
  (defthmd f*comm (implies (and (fp x) (fp y)) (equal (f* x y) (f* y x))))
  ;; Associativity:
  (defthmd f+assoc (implies (and (fp x) (fp y) (fp z)) (equal (f+ x (f+ y z)) (f+ (f+ x y) z))))
  (defthmd f*assoc (implies (and (fp x) (fp y) (fp z)) (equal (f* x (f* y z)) (f* (f* x y) z))))
  ;; Identity:
  (defthm fpf0 (fp (f0)))
  (defthm fpf1 (fp (f1)))
  (defthm f1f0 (not (equal (f1) (f0))))
  (defthm f0id (implies (fp x) (equal (f+ x (f0)) x)))
  (defthm f1id (implies (fp x) (equal (f* x (f1)) x)))
  ;; Inverse:
  (defthm fpf- (implies (fp x) (fp (f- x))))
  (defthm fpf/ (implies (and (fp x) (not (equal x (f0)))) (fp (f/ x))))
  (defthm f+inv (implies (fp x) (equal (f+ x (f- x)) (f0))))
  (defthm f*inv (implies (and (fp x) (not (equal x (f0)))) (equal (f* x (f/ x)) (f1))))
  ;; Distributivity:
  (defthm fdist (implies (and (fp x) (fp y) (fp z)) (equal (f* x (f+ y z)) (f+ (f* x y) (f* x z))))))

      


