;;; Univariate polynomials over prime fields ℤ_p := ℤ/pℤ.
;   A polynomial cs ∈ ℤ_p[x] is simply a list of coefficients.
;   The entry at index k is the coefficient of x^k.

(ld "prelude.lisp")
(ld "prime-fields.lisp")

(defun polyp (cs p)
  (declare (xargs :guard (posp p)))
  (all-fep cs p))

(defun zeropoly () nil)
(defun onepoly () '(1))

; Removes trailing zeros.
(defun poly-trim (cs)
  (drop-vals-from-end 0 cs))

; Recognizes *any* list of zeroes
(defun zeropolyp (cs p)
  (and (polyp cs p) (all-equalp 0 cs)))

(defun nonzeropolyp (cs p)
  (and (polyp cs p) (not (all-equalp 0 cs))))

(defun poly-deg (cs)
  (let ((ds (poly-trim cs)))
    (if (endp ds) :neginf (1- (len ds)))))

; TODO: should this be made abstract (i.e. definition disabled)?
(defun raise-deg (n cs)
  (declare (xargs :guard (natp n)))
  (append (repeat n 0) cs))

(defun scale-poly (c cs p)
  (declare (xargs
    :guard (and (posp p)
                (pfield::fep c p)
                (polyp cs p))))
  (mapmul c cs p))

; Doesn't trim trailing zeros
(defun poly+ (as bs p)
  (declare (xargs
    :guard (and (posp p)
                (polyp as p)
                (polyp bs p))
  ))
  (cond ((atom as) (true-list-fix bs))
        ((atom bs) (true-list-fix as))
        ((and (consp as) (consp bs))
          (cons (pfield::add (first as) (first bs) p)
                (poly+ (rest as) (rest bs) p))
        )))

; Needed for the guard condition for poly*
(defthm all-fep-poly+
  (implies (and (posp p) (all-fep as p) (all-fep bs p))
           (all-fep (poly+ as bs p) p)))

(defun poly* (as bs p)
  (declare (xargs
    :guard (and (posp p)
                (polyp as p)
                (polyp bs p))
  ))
  (cond ((atom as) nil)
        ((atom bs) nil)
        ((and (consp as) (consp bs))
          (poly+ (scale-poly (first as) bs p)
                 (raise-deg 1 (poly* (rest as) bs p))
                 p))))

; (defun poly*-alt-comm (as bs p)
;   (declare (xargs
;     :guard (and (posp p)
;                 (polyp as p)
;                 (polyp bs p))
;   ))
;   (cond ((or (atom as) (atom bs)) nil)
;         ((and (consp as) (consp bs))
;           (let ((a0 (first as)) (aas (rest as))
;                 (b0 (first bs)) (bbs (rest bs)))
;             (cons (pfield::mul a0 b0 p)
;                   (poly+ (poly+ (scale-poly a0 bbs p)
;                                 (scale-poly b0 aas p)
;                                 p)
;                          (raise-deg 1 (poly*-alt-comm aas bbs p))
;                          p)))
;         )))

(defun poly-neg (cs p)
  (declare (xargs
    :guard (and (posp p)
                (polyp cs p))
  ))
  (mapneg cs p))

(defun poly- (as bs p)
  (declare (xargs
    :guard (and (posp p)
                (polyp as p)
                (polyp bs p))
  ))
  (poly+ as (poly-neg bs p) p))
