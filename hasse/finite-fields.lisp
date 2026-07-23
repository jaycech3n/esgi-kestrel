; Executable prime fields and simple polynomial quotient extensions.

(in-package "ACL2")

(defun pf-normalize (x p)
  (mod (ifix x) (if (and (integerp p) (< 1 p)) p 2)))

(defun pf-element-p (x p)
  (and (natp x) (natp p) (< 1 p) (< x p)))

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
      (and (true-listp x)
           (equal x (ff-normalize x field)))
    (pf-element-p x (ff-characteristic field))))

(defun ff-zero (field) (if (equal (ff-kind field) :extension) nil 0))
(defun ff-one (field) (if (equal (ff-kind field) :extension) '(1) 1))

(defun ff-add (x y field)
  (if (equal (ff-kind field) :extension)
      (pf-poly-mod (pf-poly-add x y (ff-characteristic field))
                   (ff-modulus field) (ff-characteristic field))
    (pf-normalize (+ (ifix x) (ifix y)) (ff-characteristic field))))

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
