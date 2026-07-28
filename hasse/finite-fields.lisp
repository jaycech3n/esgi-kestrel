; Executable prime fields and simple polynomial quotient extensions.

; We start with primitive functions for working over prime fields and
; with polynomials over prime fields. These functions and theorems are denoted
; with a pf prefix. 


; This book defines functions for working with polynomials over prime 'fields'.
; We don't impose any structure on prime 
; The prefix pf is used to denote functions and theroems that relate to prime
; fields.

; In this book, we use
; A polynomial is merely a list of coefficients.

(in-package "ACL2")

(include-book "kestrel/arithmetic-light/mod" :dir :system)

;; ## Primitive functions for prime fields and polynomials over prime fields.
;;
;; In this section, we'll fix the field to be F_p for a prime p.



; Normalizes an element x modulo p, usually reduction of x mod p.
; Uses default 0 for x if x is not an integer.
; Uses default 2 for p if p is not an integer or p <= 1.
(defun pf-normalize (x p)
  (mod (ifix x) (if (and (integerp p) (< 1 p)) p 2)))

; pf-normalize is idempotent
(defthm pf-normalize-idempotent
 (equal (pf-normalize (pf-normalize x p) p) (pf-normalize x p)))2

; Is x an element of the prime field?
; Returns T if x if x and p are natural numbers with 1 < p and 0 <= x < p.
(defun pf-element-p (x p)
  (and (natp x) (natp p) (< 1 p) (< x p)))

; If p is a natural number and 1 < p then the the normalization of x mod p
; is an element of the prime field.
(defthm pf-element-p-of-pf-normalize
  (implies (and (natp p) (< 1 p))
           (pf-element-p (pf-normalize x p) p)))

; A brute force function that checks if p has no integer factors x
; in the range 1 < x <= d
; Returns T if d is not a natural number or if d < 2.
(defun no-divisor-at-or-below-p (p d)
  (if (or (not (natp d)) (< d 2))
      t
    (and (not (equal (mod p d) 0))
         (no-divisor-at-or-below-p p (1- d)))))

; Check if p is prime by testing if p is a natural number greater than 1 and
; testing if it has no integer factors x in the range  1 < x <= floor(p/2).
(defun prime-number-p (p)
  (and (natp p) (< 1 p)
       (no-divisor-at-or-below-p p (floor p 2))))

; Removes trailing zeros from polynomials. Here, a polynomial is treated simply
; as a list (possibly empty) of coefficients.
(defun pf-poly-trim (poly)
  (if (endp poly)
      nil
    (let ((rest (pf-poly-trim (cdr poly))))
      (if (and (endp rest) (equal (car poly) 0))
          nil
          (cons (car poly) rest)))))

; Do the cofficients of the polynomial poly belong to the prime field?
(defun pf-poly-coefficients-p (poly p)
  (if (endp poly)
      (equal poly nil)
    (and (pf-element-p (car poly) p)
         (pf-poly-coefficients-p (cdr poly) p))))

; If the coefficients of the polynomial poly belong to the prime field then so
; do the coefficients of the trimmed polynomial.
(defthm pf-poly-coefficients-p-of-pf-poly-trim
  (implies (pf-poly-coefficients-p x p)
           (pf-poly-coefficients-p (pf-poly-trim x) p))
  :hints (("Goal" :induct (pf-poly-trim x))))

; Is poly a pf-polynomial? For this to be the case,
; poly must be a list, with coefficients in the field and it must already
; be trimmed of trailing zeros.
(defun pf-polynomial-p (poly p)
  (and (true-listp poly)
       (pf-poly-coefficients-p poly p)
       (equal (pf-poly-trim poly) poly)))

; Trims the trailing zeros and normalises the coefficients of poly.
(defun pf-poly-normalize (poly p)
  (if (endp poly)
      nil
    (pf-poly-trim
     (cons (pf-normalize (car poly) p)
           (pf-poly-normalize (cdr poly) p)))))

(defthm pf-poly-coefficients-p-of-pf-poly-normalize
  (implies
   (and (natp p)
        (< 1 p))
   (pf-poly-coefficients-p
    (pf-poly-normalize x p)
p)))


; The degree of the polynomial poly. This is 0 for the 0 polynomial.
(defun pf-poly-degree (poly)
  (let ((poly (pf-poly-trim poly)))
    (if (endp poly) 0 (1- (len poly)))))

; Addition of polynomials.
(defun pf-poly-add (x y p)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (endp x) (endp y))
      nil
    (pf-poly-trim
     (cons (pf-normalize (+ (if (consp x) (car x) 0)
                              (if (consp y) (car y) 0)) p)
           (pf-poly-add (if (consp x) (cdr x) nil)
                        (if (consp y) (cdr y) nil) p)))))

; The pf-poly-trim function is idempotent.
(defthm pf-poly-trim-idempotent
  (equal (pf-poly-trim (pf-poly-trim x))
         (pf-poly-trim x))
  :hints (("Goal" :induct (pf-poly-trim x))))


; Trimming before normalization has no effect: normalization trims its result
; in any case.  This is the bridge between coefficient normalization and the
; canonical polynomial representation.
(defthm pf-poly-normalize-of-pf-poly-trim
  (equal (pf-poly-normalize (pf-poly-trim poly) p)
         (pf-poly-normalize poly p))
  :hints (("Goal" :induct (pf-poly-trim poly))))

; Polynomial normalization is idempotent.  The induction handles the
; coefficient list, PF-NORMALIZE-IDEMPOTENT handles each coefficient, and the
; preceding theorem removes the extra trim introduced at each recursive step.
(defthm pf-poly-normalize-idempotent
  (equal (pf-poly-normalize (pf-poly-normalize poly p) p)
         (pf-poly-normalize poly p))
  :hints (("Goal" :induct (pf-poly-normalize poly p))))

(defthm pf-poly-trim-of-pf-poly-normalize
  (equal (pf-poly-trim (pf-poly-normalize x p))
         (pf-poly-normalize x p))
  :hints (("Goal" :induct (pf-poly-normalize x p))))


; The sum (over the prime field) of two polynomials have coefficients in the
; prime field (assuming p is a natural number greater than 1)
(defthm pf-poly-coefficients-p-of-pf-poly-add
  (implies (and (natp p) (< 1 p))
           (pf-poly-coefficients-p (pf-poly-add x y p) p))
  :hints (("Goal" :induct (pf-poly-add x y p))))

; The sum (over the prime field) of two polynomials is a pf-polynomial.
(defthm pf-polynomial-p-of-pf-poly-add
  (implies (and (natp p) (< 1 p))
           (pf-polynomial-p (pf-poly-add x y p) p))
  :hints (("Goal"
           :in-theory (enable pf-polynomial-p))))

; The length of a trimmed polynomial x is no more than the length of x.
(defthm len-of-pf-poly-trim-upper-bound
  (<= (len (pf-poly-trim x)) (len x))
  :rule-classes :linear
  :hints (("Goal" :induct (pf-poly-trim x))))

; The length of the sum of two polynomials is at most the maximum of the
; lengths of the polynomials.
(defthm len-of-pf-poly-add-upper-bound
  (<= (len (pf-poly-add x y p))
      (max (len x) (len y)))
  :rule-classes :linear
  :hints (("Goal" :induct (pf-poly-add x y p))))

; If the x and y are polynomials of length less than n, then their sum has
; length less than n.
(defthm len-of-pf-poly-add-when-inputs-bounded
  (implies (and (< (len x) n)
                (< (len y) n))
           (< (len (pf-poly-add x y p)) n))
  :hints (("Goal"
           :use len-of-pf-poly-add-upper-bound
           :cases ((<= (len x) (len y))))))

; The (trimmed and normalized) negative of a polynomial x.
(defun pf-poly-neg (x p)
  (if (endp x)
      nil
    (pf-poly-trim
     (cons (pf-normalize (- (car x)) p)
           (pf-poly-neg (cdr x) p)))))

; Polynomial subtraction
(defun pf-poly-sub (x y p)
  (pf-poly-add x (pf-poly-neg y p) p))

; Scaling (and trimming and normalizing) a polynomial x by a constant c.
(defun pf-poly-scale (c x p)
  (if (endp x)
      nil
    (pf-poly-trim
     (cons (pf-normalize (* c (car x)) p)
           (pf-poly-scale c (cdr x) p)))))

; Multiplication of two polynomials
(defun pf-poly-mul (x y p)
  (if (or (endp x) (endp y))
      nil
    (pf-poly-add (pf-poly-scale (car x) y p)
                 (cons 0 (pf-poly-mul (cdr x) y p)) p)))

; The product (over the prime field) of two polynomials have coefficients in the
; prime field (assuming p is a natural number greater than 1)
(defthm pf-poly-coefficients-p-of-pf-poly-mul
  (implies (and (natp p) (< 1 p))
           (pf-poly-coefficients-p (pf-poly-mul x y p) p))
  :hints (("Goal" :induct (pf-poly-mul x y p))))

; The leading coefficient of a polynomial (or zero). Not sure if I need this.
(defun pf-poly-leading-coefficient (modulus p)
  (let ((modulus
         (pf-poly-trim
          (pf-poly-normalize modulus p))))
    (if (endp modulus)
        0
      (car (last modulus)))))


; A list of n zeros.
(defun zeros (n)
  (if (zp n) nil (cons 0 (zeros (1- n)))))

(defun pf-poly-butlast (x)
  (if (or (endp x) (endp (cdr x)))
      nil
    (cons (car x) (pf-poly-butlast (cdr x)))))

; Returns x - g * modulus, where g is chosen so that
; (if modulus is monic and if x and modulus are normalized),
; then the result has lower degree than x (or is zero).
; This is the first step in reduction modulo modulus.
;
; NOTE: this function returns the 'wrong' result if modulus isn't monic.
(defun pf-poly-reduce-once (x modulus p)
  (let* ((x (pf-poly-trim x))
         (modulus (pf-poly-trim modulus))
         (shift (nfix (- (len x) (len modulus))))
         (lead (if (endp x) 0 (car (last x)))))
    ;; The leading terms cancel because MODULUS is monic.  Construct the
    ;; remaining difference directly, omitting those two equal leading terms.
    (pf-poly-sub (pf-poly-butlast x)
                 (append (zeros shift)
                         (pf-poly-scale
                          lead (pf-poly-butlast modulus) p))
                 p)))

(defthm len-of-pf-poly-butlast
  (equal (len (pf-poly-butlast x))
         (if (consp x) (1- (len x)) 0))
  :hints (("Goal" :induct (pf-poly-butlast x))))

(defthm len-of-zeros
  (equal (len (zeros n)) (nfix n))
  :hints (("Goal" :induct (zeros n))))

(defthm len-of-pf-poly-scale-upper-bound
  (<= (len (pf-poly-scale c x p)) (len x))
  :rule-classes :linear
  :hints (("Goal" :induct (pf-poly-scale c x p))))

(defthm len-of-pf-poly-neg-upper-bound
  (<= (len (pf-poly-neg x p)) (len x))
  :rule-classes :linear
  :hints (("Goal" :induct (pf-poly-neg x p))))

(defthm len-of-shifted-scaled-pf-poly-butlast
  (implies
   (and (consp x)
        (consp modulus)
        (<= (len modulus) (len x)))
   (< (len
       (append
        (zeros (nfix (- (len x) (len modulus))))
        (pf-poly-scale c (pf-poly-butlast modulus) p)))
      (len x)))
  :hints
  (("Goal"
    :in-theory (enable nfix))))

(defthm pf-poly-coefficients-p-of-pf-poly-reduce-once
  (implies
   (and (natp p)
        (< 1 p))
   (pf-poly-coefficients-p
    (pf-poly-reduce-once x modulus p)
    p))
  :hints
  (("Goal"
    :in-theory
    (e/d (pf-poly-reduce-once
          pf-poly-sub)
         (pf-poly-add
          pf-poly-neg
          pf-poly-scale
          pf-poly-trim
          zeros
          binary-append)))))

(defthm len-of-pf-poly-reduce-once-decreases-raw
  (implies
   (and (consp (pf-poly-trim x))
        (consp (pf-poly-trim modulus))
        (<= (len (pf-poly-trim modulus))
            (len (pf-poly-trim x))))
   (< (len (pf-poly-reduce-once x modulus p))
      (len (pf-poly-trim x))))
  :hints
  (("Goal"
    :use
    ((:instance len-of-pf-poly-add-when-inputs-bounded
                (x (pf-poly-butlast (pf-poly-trim x)))
                (y (pf-poly-neg
                    (append
                     (zeros
                      (nfix (- (len (pf-poly-trim x))
                               (len (pf-poly-trim modulus)))))
                     (pf-poly-scale
                      (car (last (pf-poly-trim x)))
                      (pf-poly-butlast (pf-poly-trim modulus))
                      p))
                    p))
                (n (len (pf-poly-trim x))))
     (:instance len-of-shifted-scaled-pf-poly-butlast
                (x (pf-poly-trim x))
                (modulus (pf-poly-trim modulus))
                (c (car (last (pf-poly-trim x)))))
     (:instance len-of-pf-poly-neg-upper-bound
                (x (append
                    (zeros
                     (nfix (- (len (pf-poly-trim x))
                              (len (pf-poly-trim modulus)))))
                    (pf-poly-scale
                     (car (last (pf-poly-trim x)))
                     (pf-poly-butlast (pf-poly-trim modulus))
                     p)))))
    :in-theory
    (e/d (pf-poly-reduce-once
          pf-poly-sub)
         (pf-poly-add
          pf-poly-neg
          pf-poly-scale
          pf-poly-trim
          pf-poly-butlast
          zeros
          binary-append
          nfix
          len-of-pf-poly-add-when-inputs-bounded)))))

; If x has degree at least one and if modulus
; is a monic polynomial of degree at least one, then
; pf-poly-reduce-once x modulus p
; has degree less than the degree of x
(defthm len-of-pf-poly-reduce-once-decreases
  (let ((x (pf-poly-normalize x p))
        (modulus (pf-poly-normalize modulus p)))
    (implies
     (and (natp p)
          (< 1 p)
          (consp x)
          (consp modulus)
          (equal (car (last modulus)) 1)
          (<= (len modulus) (len x)))
     (< (len (pf-poly-reduce-once x modulus p))
        (len x))))
  :hints
  (("Goal"
    :use
    ((:instance len-of-pf-poly-reduce-once-decreases-raw
                (x (pf-poly-normalize x p))
                (modulus (pf-poly-normalize modulus p))))
    :in-theory
    (disable pf-poly-reduce-once
             pf-poly-normalize
             pf-poly-trim
             len-of-pf-poly-reduce-once-decreases-raw))))


; An auxiliary function used in computing the reduction of x modulo modulus.
; (assuming modulus is monic)
(defun pf-poly-mod-aux (x modulus p fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((x (pf-poly-trim x))
        (modulus (pf-poly-trim modulus)))
    (if (or (zp fuel) (endp modulus) (< (len x) (len modulus)))
        x
      (pf-poly-mod-aux (pf-poly-reduce-once x modulus p)
                       modulus p (1- fuel)))))
  

; The reduction of x modulo the monic polynonial modulus.
(defun pf-poly-mod (x modulus p)
  (pf-poly-mod-aux (pf-poly-normalize x p)
                   (pf-poly-normalize modulus p)
                   p (len x)))

(defthm pf-poly-coefficients-p-of-pf-poly-mod-aux
  (implies
   (and (natp p)
        (< 1 p)
        (pf-poly-coefficients-p x p)
        (pf-poly-coefficients-p modulus p))
   (pf-poly-coefficients-p
    (pf-poly-mod-aux x modulus p n)
    p))
  :hints
  (("Goal"
    :induct (pf-poly-mod-aux x modulus p n)
    :in-theory
    (e/d (pf-poly-mod-aux)
         (pf-poly-reduce-once
          pf-poly-sub
          pf-poly-add)))))

(defthm pf-poly-trim-of-pf-poly-mod-aux
  (equal
   (pf-poly-trim (pf-poly-mod-aux x modulus p n))
   (pf-poly-mod-aux x modulus p n))
  :hints
  (("Goal"
    :induct (pf-poly-mod-aux x modulus p n)
    :in-theory
    (e/d (pf-poly-mod-aux)
         (pf-poly-reduce-once)))))

(defthm pf-poly-coefficients-p-of-pf-poly-mod
  (implies
   (and (natp p)
        (< 1 p))
   (pf-poly-coefficients-p
    (pf-poly-mod polynomial modulus p)
    p))
  :hints
  (("Goal"
    :expand
    ((pf-poly-mod polynomial modulus p))
    :in-theory
    (e/d
     (pf-poly-coefficients-p-of-pf-poly-mod-aux)
     (pf-poly-mod-aux
      pf-poly-normalize)))))

(defthm pf-poly-trim-of-pf-poly-mod
  (equal
   (pf-poly-trim (pf-poly-mod x modulus p))
   (pf-poly-mod x modulus p))
  :hints
  (("Goal"
    :expand ((pf-poly-mod x modulus p))
    :in-theory (disable pf-poly-mod-aux))))

(defthm pf-polynomial-p-of-pf-poly-mod
  (implies
   (and (natp p)
        (< 1 p))
   (pf-polynomial-p
    (pf-poly-mod x modulus p)
    p))
  :hints
  (("Goal"
    :in-theory
    (e/d (pf-polynomial-p)
         (pf-poly-mod
          pf-poly-mod-aux
          pf-poly-coefficients-p
          pf-poly-trim)))))

; Evaluate the polynomial poly at value x using Horner's rule.
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

(defthm natp-of-ff-characteristic
  (implies
   (ff-field-p field)
   (natp (ff-characteristic field)))
  :hints
  (("Goal"
    :in-theory
    (enable ff-field-p prime-number-p))))

(defthm ff-characteristic-greater-than-one
  (implies
   (ff-field-p field)
   (< 1 (ff-characteristic field)))
  :hints
  (("Goal"
    :in-theory
    (enable ff-field-p prime-number-p))))

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

; For x to be an element of the given field means either
; (1) the field is an extension field, x is a pf-polynomial for that field and
;     the length of x is less than the length of the modulus that defines the
;     field or
; (2) the field is a prime field and x is an element of the prime field.
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


;;
;;
;;
;;
;;




#|

(thm
 (let ((x (pf-poly-normalize x p))
       (modulus (pf-poly-normalize modulus p)))
 (implies (consp modulus)
          (< (len (pf-poly-mod x modulus p)) (len modulus))))

)


(thm
 (implies (consp (pf-poly-normalize modulus p))
          (< (len (pf-poly-mod (pf-poly-normalize x p)
                               (pf-poly-normalize modulus p) p))
             (len (pf-poly-normalize modulus p))))
 )


; pf-poly-mod is idempotent
(defthm pf-poly-mod-idempotent
    (let* ((x (pf-poly-normalize x p))
           (modulus (pf-poly-normalize modulus p)))
      (implies
     (and (natp p)
          (< 1 p)
          (consp x)
          (consp modulus)
          (equal (car (last modulus)) 1)
          (<= (len modulus) (len x)))
       (equal
        (pf-poly-mod (pf-poly-mod x modulus p) modulus p)
        (pf-poly-mod x modulus p)) )))


; The degree of x modulo modulus is less than the degree of modulus.
(defthm len-of-pf-poly-mod-upper-bound
  (implies
   (and (natp p)
        (< 1 p)
        (consp (pf-poly-normalize modulus p))
        (equal (car (last (pf-poly-normalize modulus p))) 1))
   (< (len (pf-poly-mod x modulus p))
      (len (pf-poly-normalize modulus p)))))


(defthm degree-of-pf-poly-mod-upper-bound
  (let* ((x (pf-poly-trim (pf-normalize x p)))
         (modulus (pf-poly-trim (pf-normalize modulus p))))
  (implies
   (< 1 (pf-poly-degree modulus))
   
   (< (pf-poly-degree (pf-poly-mod x modulus p))
(pf-poly-degree modulus)))))



(defthm ff-mul-when-extension
  (implies
   (equal (ff-kind field) :extension)
   (equal
    (ff-mul x y field)
    (pf-poly-mod
     (pf-poly-mul x y (ff-characteristic field))
     (ff-modulus field)
     (ff-characteristic field))))
  :hints (("Goal" :in-theory (enable ff-mul))))



(thm
    (implies
     (and (ff-field-p field)
          (ff-element-p x field)
          (ff-element-p y field))
     
     (if (equal (ff-kind field) :extension)
         (let ((p (ff-characteristic field))
               (modulus (ff-modulus field)))
         (implies
          (and 
           (< 1 (pf-poly-degree modulus))
           (pf-polynomial-p x p)
           (pf-polynomial-p y p)
           )
          
          (ff-element-p (ff-mul x y field) field)          

          )
         )
         
         (ff-element-p (ff-mul x y field) field) ))
)



(thm
 (implies
  (and (ff-field-p field)
       (ff-element-p x field)
       (ff-element-p y field)
       (equal (ff-kind field) :extension)
       (< 1 (pf-poly-degree (ff-modulus field)))
       (pf-polynomial-p x (ff-characteristic field))
       (pf-polynomial-p y (ff-characteristic field))

       )
  (ff-element-p (ff-mul x y field) field)
  )
)
|#
