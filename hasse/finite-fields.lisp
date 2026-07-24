; Executable prime fields and simple polynomial quotient extensions.

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/mod" :dir :system)

(defun pf-normalize (x p)
  (mod (ifix x) (if (and (integerp p) (< 1 p)) p 2)))

(defun pf-element-p (x p)
  (and (natp x) (natp p) (< 1 p) (< x p)))

(defthm pf-element-p-of-pf-normalize
  (implies (and (natp p) (< 1 p))
           (pf-element-p (pf-normalize x p) p))
  :hints (("Goal"
           :in-theory (enable pf-element-p pf-normalize))))

(defun no-divisor-at-or-below-p (p d)
  (if (or (not (natp d)) (< d 2))
      t
    (and (not (equal (mod p d) 0))
         (no-divisor-at-or-below-p p (1- d)))))

(defun prime-number-p (p)
  (and (natp p) (< 1 p)
       (no-divisor-at-or-below-p p (floor p 2))))

(defun pf-poly-trim (poly)
  (if (endp poly)
      nil
    (let ((rest (pf-poly-trim (cdr poly))))
      (if (and (endp rest) (equal (car poly) 0))
          nil
        (cons (car poly) rest)))))

(defun pf-poly-coefficients-p (poly p)
  (if (endp poly)
      (equal poly nil)
    (and (pf-element-p (car poly) p)
         (pf-poly-coefficients-p (cdr poly) p))))

(defun pf-polynomial-p (poly p)
  (and (true-listp poly)
       (pf-poly-coefficients-p poly p)
       (equal (pf-poly-trim poly) poly)))

(defun pf-poly-normalize (poly p)
  (if (endp poly)
      nil
    (pf-poly-trim
     (cons (pf-normalize (car poly) p)
           (pf-poly-normalize (cdr poly) p)))))

(defun pf-poly-degree (poly)
  (let ((poly (pf-poly-trim poly)))
    (if (endp poly) 0 (1- (len poly)))))

(defun pf-poly-add (x y p)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (endp x) (endp y))
      nil
    (pf-poly-trim
     (cons (pf-normalize (+ (if (consp x) (car x) 0)
                              (if (consp y) (car y) 0)) p)
           (pf-poly-add (if (consp x) (cdr x) nil)
                        (if (consp y) (cdr y) nil) p)))))

(defthm pf-poly-coefficients-p-of-pf-poly-trim
  (implies (pf-poly-coefficients-p x p)
           (pf-poly-coefficients-p (pf-poly-trim x) p))
  :hints (("Goal" :induct (pf-poly-trim x))))

(defthm pf-poly-trim-idempotent
  (equal (pf-poly-trim (pf-poly-trim x))
         (pf-poly-trim x))
  :hints (("Goal" :induct (pf-poly-trim x))))

(defthm pf-poly-coefficients-p-of-pf-poly-add
  (implies (and (natp p) (< 1 p))
           (pf-poly-coefficients-p (pf-poly-add x y p) p))
  :hints (("Goal" :induct (pf-poly-add x y p))))

(defthm pf-polynomial-p-of-pf-poly-add
  (implies (and (natp p) (< 1 p))
           (pf-polynomial-p (pf-poly-add x y p) p))
  :hints (("Goal"
           :in-theory (enable pf-polynomial-p))))

(defthm len-of-pf-poly-trim-upper-bound
  (<= (len (pf-poly-trim x)) (len x))
  :rule-classes :linear
  :hints (("Goal" :induct (pf-poly-trim x))))

(defthm len-of-pf-poly-add-upper-bound
  (<= (len (pf-poly-add x y p))
      (max (len x) (len y)))
  :rule-classes :linear
  :hints (("Goal" :induct (pf-poly-add x y p))))

(defthm len-of-pf-poly-add-when-inputs-bounded
  (implies (and (< (len x) n)
                (< (len y) n))
           (< (len (pf-poly-add x y p)) n))
  :hints (("Goal"
           :use len-of-pf-poly-add-upper-bound
           :cases ((<= (len x) (len y))))))

(defun pf-poly-neg (x p)
  (if (endp x)
      nil
    (pf-poly-trim
     (cons (pf-normalize (- (car x)) p)
           (pf-poly-neg (cdr x) p)))))

(defun pf-poly-sub (x y p)
  (pf-poly-add x (pf-poly-neg y p) p))

(defun pf-poly-scale (c x p)
  (if (endp x)
      nil
    (pf-poly-trim
     (cons (pf-normalize (* c (car x)) p)
           (pf-poly-scale c (cdr x) p)))))

(defun pf-poly-mul (x y p)
  (if (or (endp x) (endp y))
      nil
    (pf-poly-add (pf-poly-scale (car x) y p)
                 (cons 0 (pf-poly-mul (cdr x) y p)) p)))

(defun zeros (n)
  (if (zp n) nil (cons 0 (zeros (1- n)))))

(defun pf-poly-reduce-once (x modulus p)
  (let* ((x (pf-poly-trim x))
         (modulus (pf-poly-trim modulus))
         (shift (nfix (- (len x) (len modulus))))
         (lead (if (endp x) 0 (car (last x)))))
    (pf-poly-sub x
                 (append (zeros shift)
                         (pf-poly-scale lead modulus p))
                 p)))

(defun pf-poly-mod-aux (x modulus p fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((x (pf-poly-trim x))
        (modulus (pf-poly-trim modulus)))
    (if (or (zp fuel) (endp modulus) (< (len x) (len modulus)))
        x
      (pf-poly-mod-aux (pf-poly-reduce-once x modulus p)
                       modulus p (1- fuel)))))

(defun pf-poly-mod (x modulus p)
  (pf-poly-mod-aux (pf-poly-normalize x p)
                   (pf-poly-normalize modulus p)
                   p (len x)))

(defun pf-poly-eval-horner (poly x p)
  (if (endp poly)
      0
    (pf-normalize (+ (car poly)
                     (* x (pf-poly-eval-horner (cdr poly) x p))) p)))

(defun pf-poly-has-no-root-below-p (poly p x)
  (if (zp x)
      t
    (and (not (equal (pf-poly-eval-horner poly (1- x) p) 0))
         (pf-poly-has-no-root-below-p poly p (1- x)))))

(defun pf-irreducible-p (poly p)
  (let* ((poly (pf-poly-normalize poly p))
         (degree (pf-poly-degree poly)))
    (and (prime-number-p p)
         (equal (car (last poly)) 1)
         (or (equal degree 1)
             (and (or (equal degree 2) (equal degree 3))
                  (pf-poly-has-no-root-below-p poly p p))))))

(defthm degree-one-polynomial-is-irreducible
  (implies (and (prime-number-p p)
                (equal (pf-poly-degree (pf-poly-normalize poly p)) 1)
                (equal (car (last (pf-poly-normalize poly p))) 1))
           (pf-irreducible-p poly p)))

(defun ff-prime (p) (list :prime p))
(defun ff-extension (p modulus) (list :extension p (pf-poly-normalize modulus p)))
(defun ff-kind (field) (car field))
(defun ff-characteristic (field) (cadr field))
(defun ff-modulus (field) (caddr field))

(defun ff-field-p (field)
  (let ((p (ff-characteristic field)))
    (and (prime-number-p p)
         (or (and (equal (ff-kind field) :prime)
                  (equal (len field) 2))
             (and (equal (ff-kind field) :extension)
                  (equal (len field) 3)
                  (equal (car (last (ff-modulus field))) 1)
                  (pf-irreducible-p (ff-modulus field) p))))))

(defun ff-degree (field)
  (if (equal (ff-kind field) :extension)
      (pf-poly-degree (ff-modulus field))
    1))

(defun ff-cardinality (field)
  (expt (ff-characteristic field) (ff-degree field)))

(defun ff-normalize (x field)
  (if (equal (ff-kind field) :extension)
      (pf-poly-mod x (ff-modulus field) (ff-characteristic field))
    (pf-normalize x (ff-characteristic field))))

(defun ff-element-p (x field)
  (if (equal (ff-kind field) :extension)
      (and (pf-polynomial-p x (ff-characteristic field))
           (< (len x)
              (len (pf-poly-normalize (ff-modulus field)
                                      (ff-characteristic field)))))
    (pf-element-p x (ff-characteristic field))))

(defun ff-zero (field) (if (equal (ff-kind field) :extension) nil 0))
(defun ff-one (field) (if (equal (ff-kind field) :extension) '(1) 1))

(defun ff-add (x y field)
  (if (equal (ff-kind field) :extension)
      ;; Reduced representatives are closed under coefficientwise addition:
      ;; addition cannot increase their degree, so no polynomial division is
      ;; needed here.
      (pf-poly-add x y (ff-characteristic field))
    (pf-normalize (+ (ifix x) (ifix y)) (ff-characteristic field))))

(defthm ff-add-closed
  (implies (and (ff-field-p field)
                (ff-element-p x field)
                (ff-element-p y field))
           (ff-element-p (ff-add x y field) field)))

(defun ff-neg (x field)
  (if (equal (ff-kind field) :extension)
      (pf-poly-neg x (ff-characteristic field))
    (pf-normalize (- (ifix x)) (ff-characteristic field))))

(defun ff-mul (x y field)
  (if (equal (ff-kind field) :extension)
      (pf-poly-mod (pf-poly-mul x y (ff-characteristic field))
                   (ff-modulus field) (ff-characteristic field))
    (pf-normalize (* (ifix x) (ifix y)) (ff-characteristic field))))

(defun ff-pow (x n field)
  (if (zp n)
      (ff-one field)
    (ff-mul x (ff-pow x (1- n) field) field)))

(defun ff-inv (x field)
  (if (equal (ff-normalize x field) (ff-zero field))
      (ff-zero field)
    (ff-pow x (- (ff-cardinality field) 2) field)))

(defun ff-div (x y field) (ff-mul x (ff-inv y field) field))

(defun naturals-below (n)
  (if (zp n) nil (append (naturals-below (1- n)) (list (1- n)))))

(defun prepend-each (x lists)
  (if (endp lists) nil
    (cons (cons x (car lists)) (prepend-each x (cdr lists)))))

(defun prepend-all (xs lists)
  (if (endp xs) nil
    (append (prepend-each (car xs) lists)
            (prepend-all (cdr xs) lists))))

(defun coefficient-vectors (p n)
  (if (zp n)
      (list nil)
    (prepend-all (naturals-below p) (coefficient-vectors p (1- n)))))

(defun ff-normalize-list (xs field)
  (if (endp xs)
      nil
    (cons (ff-normalize (car xs) field)
          (ff-normalize-list (cdr xs) field))))

(defun ff-elements (field)
  (if (equal (ff-kind field) :extension)
      (remove-duplicates-equal
       (ff-normalize-list
        (coefficient-vectors (ff-characteristic field) (ff-degree field))
        field))
    (naturals-below (ff-characteristic field))))

(defun ff-frobenius (x field)
  (ff-pow x (ff-cardinality field) field))

; Small executable witnesses used to guard the representation against vacuity.
(defconst *ff2* (ff-prime 2))
(defconst *ff4* (ff-extension 2 '(1 1 1)))

(defthm ff2-is-a-field
  (ff-field-p *ff2*))

(defthm ff4-is-a-field
  (ff-field-p *ff4*))

(defthm ff4-has-four-enumerated-elements
  (equal (len (ff-elements *ff4*)) 4))
