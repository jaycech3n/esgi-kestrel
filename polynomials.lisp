;;; Univariate polynomials over prime fields ℤ_p := ℤ/pℤ.
;   A polynomial cs ∈ ℤ_p[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

(ld "prelude.lisp")
(ld "prime-fields.lisp")

(defun polyp (cs p)
  (declare (xargs :guard (posp p)))
  (pfield::all-fep cs p))
  ; all-fep ensures that cs is a true list.

(defun monomialp (cs p)
  (and (polyp cs p) (singleton cs)))

(defconst *zeropoly* nil)
(defconst *onepoly* '(1))

; Removes trailing zeros.
(defun poly-nf (cs)
  (drop-vals-from-end 0 cs))

; Recognizes *any* list of zeroes
(defun zeropolyp (cs p)
  (and (polyp cs p) (all-equalp 0 cs)))

(defun nonzeropolyp (cs p)
  (and (polyp cs p) (not (all-equalp 0 cs))))

(defun poly-deg (cs)
  (let ((nf (poly-nf cs)))
    (if (nilp nf) :neginf (1- (len nf)))))

(defun raise-deg (n cs)
  (declare (xargs :guard (natp n)))
  (append (repeat n 0) cs))

(defun scale-poly (c cs p)
  (declare (xargs :guard
    (and (posp p)
         (pfield::fep c p)
         (polyp cs p)))
  )
  (pfield::mapmul c cs p))

; Doesn't trim trailing zeros
(defun poly+ (as bs p)
  (declare (xargs
    :guard (and (posp p)
                (polyp as p)
                (polyp bs p)))
           )
  (if (and (polyp as p) (polyp bs p))
      (cond ((atom as) bs)
            ((atom bs) as)
            ((and (consp as) (consp bs))
              (cons (pfield::add (first as) (first bs) p)
                    (poly+ (rest as) (rest bs) p))))
      :[poly+]-bad-inputs))

; Need the following to prove the guard condition for poly*.

(defthm all-fep-poly+
  (implies (and (posp p)
                (pfield::all-fep as p)
                (pfield::all-fep bs p))
           (pfield::all-fep (poly+ as bs p) p)))

(defun poly*-ind (as bs)
  (declare (xargs :measure (+ (len as) (len bs))))
  (cond ((and (consp as) (consp bs))
         (and (poly*-ind (rest as) (rest bs))
              (poly*-ind (rest as) bs)
              (poly*-ind as (rest bs))))
        (t t)))

(defun poly* (as bs p)
  (declare (xargs
    :guard
      (and (posp p)
           (polyp as p)
           (polyp bs p))
    :guard-hints
      (("Goal" :induct (poly*-ind as bs))))
  )
  (if (and (polyp as p) (polyp bs p))
      (cond ((or (atom as) (atom bs)) nil)
            ((and (consp as) (consp bs))
              (poly+ (scale-poly (first as) bs p)
                     (raise-deg 1 (poly* (rest as) bs p))
                     p)))
      :[poly*]-bad-inputs))

(defun poly-neg (cs p)
  (pfield::mapneg cs p))

(defun poly- (as bs p)
  (poly+ as (poly-neg bs p) p))
