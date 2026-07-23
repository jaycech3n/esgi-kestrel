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
(defun degree-aux (p n)
  (if (endp p)
      -1
      (max (if (equal (car p) 0) -1 n)
           (degree-aux (cdr p) (+ 1 n)))))

(defun degree (p)
  (degree-aux p 0))


;; degree of rational function of the form (p_1(x)+y*p_2(x))/q(x)
(defun degreerat(num1 num2 den)
  (max (max(degree num1)
           (degree den))
       (+ (degree num2) 1) ))
;; evaluate an endomorphism of the form (x,y) \mapsto (p_1(x)/q_1(x), p_2(x)/q_2(x)*y)
(defun eval-end(num1 num2 den1 den2 x y)
  (list (/ (eval-poly num1 x) (eval-poly den1 x))
        (* y (/ (eval-poly num2 x) (eval-poly den2 x)))))
;; definition of degree of endomorphism = degree of first component function
(defun degree-end(num1 num2 den1 den2)
  (declare (ignore num2 den2))
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
      (* x (power x (- q 1)))))
;; evaluate the Frobenius map (x,y) \mapsto (x^q,y^q)
(defun eval-frobenius (x y q)
  (list (power x q) (power y q)))

;;; (defthm eucl-alg-fin (implies (< 0 b) (< (mod  a b) b)))

(skip-proofs
 (defun eucl-alg (a b)
    (if (equal b 0)
        (list a 1 0)
        (let* ((rec (eucl-alg b (mod a b)))
               (g (car rec))
               (s (cadr rec))
               (u (caddr rec)))
          (list g
                u
                (- s (* (floor a b) u))))))
)

;; definition of field from acl2/books/projects/linear/field.lisp

(encapsulate (((fp *) => *)                   ;field element recognizer
              ((f+ * *) => *) ((f* * *) => *) ;addition and multiplication
	      ((f0) => *) ((f1) => *)         ;identities
	      ((f- *) => *) ((f/ *) => *))    ;inverses 
    ;; define finitefield: x is element of a list of field elements			 
    (local (defun fp (x p)
             (and (integerp x)
                  (<= 0 x)
                  (< x p))))
     ;; addition mod p
  (local (defun f+ (x y p) (mod (+ x y) p)))
  (local (defun f* (x y p) (mod (* x y) p)))
  (local (defun f0 () 0))
  (local (defun f1 () 1))
  (local (defun f- (x p) (mod(- x) p)))
  
  
  (local (defun f/ (x p) 
           (if (equal (mod x  p) 0)
               nil
               (let* ((res (eucl-alg x p))
                      (x   (cadr res)))
                 (mod x p)))))
                                 ;; Closure:
     (defthm f+closed (implies (and (fp x p) (fp y p)) (fp (f+ x y p))))
     (defthm f*closed (implies (and (fp x p) (fp y p)) (fp (f* x y p))))
                                 ;; Commutativity
     (defthmd f+comm (implies (and (fp x p) (fp y p)) (equal (f+ x y p ) (f+ y
           x p))))
     (defthmd f*comm (implies (and (fp x p) (fp y p)) (equal (f* x y p) (f* y x
           p))))
                                 ;; Associativity:
     (defthmd f+assoc (implies (and (fp x p) (fp y p) (fp z p)) (equal (f+ x
           (f+ y z p) p) (f+ (f+ x y p) z p ))))
     (defthmd f*assoc (implies (and (fp x p) (fp y p) (fp z p)) (equal (f* x
           (f* y z p ) p) (f* (f* x y p) z p))))
                                 ;; Identity:
     (defthm fpf0 (fp (f0)))
     (defthm fpf1 (fp (f1)))
     (defthm f1f0 (not (equal (f1) (f0))))
     (defthm f0id (implies (fp x p) (equal (f+ x (f0) p) x)))
     (defthm f1id (implies (fp x p) (equal (f* x (f1) p) x)))
                                 ;; Inverse:
     (defthm fpf- (implies (fp x p) (fp (f- x p) p)))
     (defthm fpf/ (implies (and (fp x p) (not (equal x (f0)))) (fp (f/ x p) p)))
     (defthm f+inv (implies (fp x p) (equal (f+ x (f- x p) p) (f0))))
     (defthm f*inv (implies (and (fp x p) (not (equal x (f0)))) (equal (f* x
           (f/ x p ) p) (f1))))
                                 ;; Distributivity:
     (defthm fdist (implies (and (fp x p) (fp y p ) (fp z p)) (equal (f* x (f+
           y z p)) (f+ (f* x y p) (f* x z p) p))))
                          ;; Characteristic p:
     (defthm characteristic-p
         (equal (n*f1 p)
                (f0)))
     (defthm characteristic-p-minimal
         (implies (and (natp n)
                       (< 0 n)
                       (< n p))
                  (not (equal (n*f1 n)
                              (f0)))))
     )

