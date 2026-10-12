(ld "polynomials.lisp")

;; ==== Algebraic properties ====

; --- ... of basic operations ---
; i.e. shifting and scaling.

(defthm poly-shift+
  (implies (and (natp m) (natp n))
           (equal (poly-shift m (poly-shift n cs))
                  (poly-shift (+ m n) cs))))

(defthm poly-scale-monomial
  (implies (and (posp p)
                (pfield::fep c p)
                (monomialp cs p))
           (equal (poly-scale c cs p)
                  (list (pfield::mul c (first cs) p)))))


; --- Addition ---

; The unit for addition is the zero polynomial
; *in its representation via the nil list*:
; it is *not* the case that zs + cs = cs or cs + zs = cs
; for an arbitrary representation zs of the zero polynomial!
; However, we have the following two useful equalities:

(defthm poly+-lunit-len-1
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (equal (poly+ '(0) cs p) cs))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm poly+-runit-len-1
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (equal (poly+ cs '(0) p) cs))
  :hints (("Goal" :in-theory (enable polyp))))

(defthm poly+-comm
  (implies (and (polyp as p) (polyp bs p))
           (equal (poly+ bs as p) (poly+ as bs p))))

(defthm poly+-assoc
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly+ (poly+ as bs p) cs p)
                  (poly+ as (poly+ bs cs p) p)))
  :hints (("Goal" :in-theory (enable polyp))))


; --- Multiplication ---

(defthm poly*-comm
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* bs as p) (poly* as bs p)))
  :hints (("Goal"
    :induct (poly*-ind as bs)
    :do-not '(eliminate-destructors generalize))))
