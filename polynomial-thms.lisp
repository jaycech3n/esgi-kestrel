(ld "polynomials.lisp")

;; ==== Algebraic properties ====

; --- ... of basic operations ---
; i.e. shifting and scaling.

(defthm poly-scale-monomial
  (implies (and (posp p)
                (pfield::fep c p)
                (monomialp cs p))
           (equal (poly-scale c cs p)
                  (list (pfield::mul c (first cs) p)))))

(defthm poly-shift+
  (implies (and (natp m) (natp n))
           (equal (poly-shift m (poly-shift n cs))
                  (poly-shift (+ m n) cs))))


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

(defthm poly-scale-dist-poly+
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly-scale c (poly+ as bs p) p)
                  (poly+ (poly-scale c as p)
                         (poly-scale c bs p) p))))

(defthm poly-shift-dist-poly+
  (implies (and (natp n)
                (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly-shift n (poly+ as bs p))
                  (poly+ (poly-shift n as)
                         (poly-shift n bs) p)))
  :hints (("Goal" :induct (nat-ind n))))

; Will this cause problems if left enabled?
(defthm swap-start-of-poly+-poly+
  (implies (and (posp p)
                (polyp as p) (polyp bs p) (polyp cs p))
           (equal (poly+ bs (poly+ as cs p) p)
                  (poly+ as (poly+ bs cs p) p))))


; --- Multiplication ---

(defthm poly*-comm
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* bs as p) (poly* as bs p)))
  :hints (("Goal"
    :induct (poly*-ind as bs)
    :do-not '(eliminate-destructors generalize))))

(defthm poly*-dist-poly+-l
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* as (poly+ bs cs p) p)
                  (poly+ (poly* as bs p)
                         (poly* as cs p) p)))
  :hints (("Goal"
    :in-theory (disable poly-scale poly-shift)
    :induct (len as)
    :do-not '(eliminate-destructors))))

(defthm poly*-assoc
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* (poly* as bs p) cs p)
                  (poly* as (poly* bs cs p) p)))
  :hints (("Goal"
    :in-theory (disable poly-scale poly-shift)
    :do-not '(eliminate-destructors)
  )))


#|

Induction on as?

LHS:

(poly+
  (poly-scale a0 bs)
  (poly-shift 1 (poly* ar bs)))

|#
