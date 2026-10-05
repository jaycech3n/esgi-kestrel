(ld "polynomials.lisp")

; --- Closure properties ---

; `rest` drops the constant term of a polynomial
(defthm poly-rest-closed
  (implies (polyp cs p) (polyp (rest cs) p))
  :rule-classes :type-prescription)

(defthm poly-nf-closed
  (implies (polyp cs p) (polyp (poly-nf cs) p))
  :rule-classes :type-prescription)

(defthm raise-deg-closed
  (implies (and (natp n) (posp p) (polyp cs p))
           (polyp (raise-deg n cs) p))
  :rule-classes :type-prescription)

(defthm scale-poly-closed
  (implies (and (posp p) (polyp cs p) (pfield::fep c p))
           (polyp (scale-poly c cs p) p))
  :rule-classes :type-prescription)

(defthm poly+-closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly+ as bs p) p))
  :rule-classes :type-prescription)

(defthm poly*-closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly* as bs p) p))
  :rule-classes :type-prescription)

(defthm poly-neg-closed
  (implies (and (posp p) (polyp cs p))
           (polyp (poly-neg cs p) p))
  :rule-classes :type-prescription)

(defthm poly--closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly- as bs p) p))
  :hints (("Goal" :in-theory (disable polyp poly-neg)))
  :rule-classes :type-prescription)


; --- Algebraic properties ---

(defthm raise-deg+
  (implies (and (natp m) (natp n))
           (equal (raise-deg m (raise-deg n cs))
                  (raise-deg (+ m n) cs))))

; (defthm scale-poly-monomial
;   (implies (and (pfield::fep c p)
;                 (monomialp cs p))
;            (equal (scale-poly c cs p)
;                   (list (pfield::mul c (first cs) p)))))

(defthm poly+-comm
  (implies (and (polyp as p) (polyp bs p))
           (equal (poly+ bs as p) (poly+ as bs p))))

(defthm poly+-assoc
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly+ (poly+ as bs p) cs p)
                  (poly+ as (poly+ bs cs p) p))))

; (defthmd raise-deg-dist-poly+
;   (implies (and (natp n)
;                 (posp p)
;                 (polyp as p)
;                 (polyp bs p))
;            (equal (raise-deg n (poly+ as bs p))
;                   (poly+ (raise-deg n as) (raise-deg n bs) p)))
;   :hints (("Goal" :induct (nat-ind n)
;                   :in-theory (enable repeat))))

; (defthmd scale-poly-decomp-as-poly+
;   (implies (and (posp p)
;                 (pfield::fep c p)
;                 (polyp cs p)
;                 (consp cs)) ; Mathematically, this should be `nonzeropolyp cs`
;                            ; but `consp cs` is more general.
;            (equal (scale-poly c cs p)
;                   (poly+ (list (pfield::mul c (first cs) p))
;                          (raise-deg 1 (scale-poly c (rest cs) p))
;                          p))))

(defthm poly*-comm
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* bs as p) (poly* as bs p)))
  :hints (
    ("Goal"
      :in-theory (disable scale-poly raise-deg)
      :induct (poly*-ind as bs)
      :do-not '(eliminate-destructors))
  )
)
