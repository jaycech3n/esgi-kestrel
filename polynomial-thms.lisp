(ld "polynomials.lisp")

;; ==== Closure properties ====

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

(defthm poly-scale-closed
  (implies (and (posp p) (polyp cs p) (pfield::fep c p))
           (polyp (poly-scale c cs p) p))
  :rule-classes :type-prescription)

; (posp p) (polyp bs p)
; ./ (pfield::fep (first as) p)
;    
; ----
; (polyp (poly-scale (first as) bs p) p)

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
  :rule-classes :type-prescription)


;; ==== Operational properties ====

; (defthm poly-scale-nonnil
;   (implies (and (polyp cs p) (consp cs))
;            (poly-scale c cs p)))

; (defthm poly+-nonnil
;   (implies as
;            (poly+ as bs p)))


;; ==== Algebraic properties ====

(defthm raise-deg+
  (implies (and (natp m) (natp n))
           (equal (raise-deg m (raise-deg n cs))
                  (raise-deg (+ m n) cs))))

; Unsure if this should be disabled by default.
(defthm poly-scale-monomials-comm
  (implies (and (monomialp as p) (monomialp bs p))
           (equal (poly-scale (first bs) as p)
                  (poly-scale (first as) bs p))))

; --- Addition ---

; The unit for addition is the zero polynomial
; *in its representation via the nil list*:
; it is *not* the case that zs + cs = cs or cs + zs = cs
; for an arbitrary representation zs of the zero polynomial!
; However, we have the following useful equalities:

(defthm poly+-lunit-zeropoly
  (implies (and (posp p)
                (polyp cs p)
                (zeropolyp zs p)
                (<= (len zs) (len cs)))
           (equal (poly+ zs cs p) cs))
  :hints (("Goal" :in-theory (enable repeat)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))
  ; Do not backchain by default: computing `len zs` and
  ; `len cs` may involve arbitrary reasoning.

(defthm poly+-runit-zeropoly
  (implies (and (posp p)
                (polyp cs p)
                (zeropolyp zs p)
                (<= (len zs) (len cs)))
           (equal (poly+ cs zs p) cs))
  :hints (("Goal" :in-theory (enable repeat)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm poly+-lunit-len-1
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (equal (poly+ '(0) cs p) cs)))

(defthm poly+-runit-len-1
  (implies (and (posp p)
                (polyp (poly-scale (first as) bs p) p)
                ; (polyp bs p) (pfield::fep (first as) p)
                ; (consp (poly-scale (first as) bs p))
                (consp bs)
                )
           ; (equal (poly+ cs '(0) p) cs)
           (equal (poly+ (poly-scale (first as) bs p) '(0) p)
                  (poly-scale (first as) bs p))
           )
  :hints (("Goal" :do-not '(eliminate-destructors)))
  )
; cs := (poly-scale (first as) bs p)
; need: polyp (poly-scale (first as) bs p)
; and   consp (poly-scale (first as) bs p)
; TODO: check that the above conditions are inferrable by acl2

; TEST

; (defstub wrap (xs) xs)

; (defaxiom testrule
;   (implies (and (posp p)
;                 (polyp cs p)
;                 cs)
;            (equal (poly+ cs (list 0) p) cs))
;   )

; (defthm test
;   (implies (and (posp p)
;                 (polyp cs p)
;                 cs)
;            (wrap (poly+ cs (list 0) p)))
;   :hints (("Goal" :do-not-induct t :in-theory (disable polyp))))

; (defthm test1
;   (implies (and (posp p)
;                 (polyp cs p)
;                 cs)
;            (wrap (poly+ (poly+ cs '(0) p) '(0) p)))
;   :hints (("Goal" :in-theory (disable poly+-runit-len-1))))

; (defthm test
;   (implies (and (posp p)
;                 (pfield::fep c p)
;                 (consp cs)
;                 (polyp cs p)
;                 )
;            (wrap (poly+ (poly-scale c cs p) '(0) p))
;            )
;   :hints (("Goal" :in-theory (disable poly-scale raise-deg poly+)
;                   :do-not-induct t))
;   )

; END TEST

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

; --- Multiplication ---

(defthm poly*-comm
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* bs as p) (poly* as bs p)))
  :hints (
    ("Goal"
      :in-theory (e/d ()
                      (polyp poly-scale raise-deg))
      :induct (poly*-ind as bs)
      :do-not '(eliminate-destructors))
  )
)
