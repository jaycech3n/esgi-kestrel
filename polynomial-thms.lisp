(ld "polynomials.lisp")

; --- Sanity checks for zeropolyp ---

(defthmd zeropolyp-characterization
  (implies (and (dm::primep p) (polyp cs p))
    (iff (zeropolyp cs p)
         (or (nilp cs)
             (and (consp cs)
                  (zerop (first cs))
                  (zeropolyp (rest cs) p)))))
  :hints (("Goal" :in-theory (enable repeat)))
  )

(defthmd nonzeropolyp-iff-not-zeropolyp
  (implies (polyp cs p)
    (iff (nonzeropolyp cs p) (not (zeropolyp cs p)))))

(defthm poly-trim-zeropoly
  (implies (zeropolyp cs p) (nilp (poly-trim cs))))


; --- Closure properties ---

(defthm poly-trim-closed
  (implies (polyp cs p) (polyp (poly-trim cs) p))
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

(defthm poly+-comm
  (implies (and (polyp as p) (polyp bs p))
           (equal (poly+ bs as p) (poly+ as bs p))))

(defthm poly+-assoc
  (equal (poly+ (poly+ as bs p) cs p)
         (poly+ as (poly+ bs cs p) p)))

(defthmd poly+-unassoc
  (equal (poly+ as (poly+ bs cs p) p)
         (poly+ (poly+ as bs p) cs p)))

(defthmd raise-deg-dist-poly+
  (implies (and (natp n)
                (polyp as p)
                (polyp bs p))
           (equal (raise-deg n (poly+ as bs p))
                  (poly+ (raise-deg n as) (raise-deg n bs) p)))
  :hints (("Goal" :induct (induct-nat n)
                  :in-theory (enable repeat))))

(defthmd scale-poly-decomp-as-poly+
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p)
                (consp cs)) ; Mathematically, this should be `nonzeropolyp cs`
                           ; but `consp cs` is more general.
           (equal (scale-poly c cs p)
                  (poly+ (list (pfield::mul c (first cs) p))
                         (raise-deg 1 (scale-poly c (rest cs) p))
                         p))))

; (defthm poly*-comm
;   (implies (and (posp p)
;                 (polyp as p)
;                 (polyp bs p))
;            (equal (poly* as bs p) (poly* bs as p)))
;   ; :hints
;   ;   (("Goal"
;   ;     :use ((:instance poly+-unassoc
;   ;                      ())
;   ;           (:instance ?))))
; )