(ld "polynomials.lisp")

(section

(local (in-theory (enable polyp)))

;; === Closure under operations ===

(defthm polyp-nf
  (implies (polyp cs p) (polyp (poly-nf cs) p))
  :rule-classes (:rewrite :type-prescription))

(defthm polyp-shift
  (implies (and (natp n) (posp p) (polyp cs p))
           (polyp (poly-shift n cs) p))
  :rule-classes (:rewrite :type-prescription))

(defthm poly-scale-closed
  (implies (and (posp p) (pfield::fep c p) (polyp cs p))
           (polyp (poly-scale c cs p) p))
  :rule-classes (:rewrite :type-prescription))

(defthm poly+-closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly+ as bs p) p))
  :rule-classes (:rewrite :type-prescription))

(defthm poly*-closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly* as bs p) p))
  :rule-classes (:rewrite :type-prescription))

(defthm poly-neg-closed
  (implies (and (posp p) (polyp cs p))
           (polyp (poly-neg cs p) p))
  :rule-classes (:rewrite :type-prescription))

(defthm poly--closed
  (implies (and (posp p) (polyp as p) (polyp bs p))
           (polyp (poly- as bs p) p))
  :rule-classes (:rewrite :type-prescription))


;; ==== Reasoning about polynomials ====

; The definition of `polyp` is disabled by default in lieu of more
; abstract "type" reasoning (by the closure rules above). This is not
; always enough, and we sometimes still require certain "lower-level"
; properties of the definition.

; We record these rules here. Some of them are mathematical, and some
; are more "operational" and abstraction-breaking, i.e. have to do
; with properties of the list representation.

; More type reasoning: `rest` "downshifts" a polynomial.
(defthm polyp-rest
  (implies (polyp cs p) (polyp (rest cs) p))
  :rule-classes (:rewrite :type-prescription))

; This one is only a rewrite rule and not a type prescription rule
; because we do not want "type" reasoning to prove `polyp` for low-
; level properties of the list representations.
(defthm polyp-cons
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p))
           (polyp (cons c cs) p)))

; all-fep ensures that cs is a true list.
(defthm polyp-true-listp
  (implies (polyp cs p) (true-listp cs))
  :rule-classes :forward-chaining)

(defthm polyp-first
  (implies (and (polyp cs p) (consp cs))
           (pfield::fep (first cs) p))
  :rule-classes :forward-chaining)

(defthm polyp-not-consp-is-nil
  (implies (and (polyp cs p) (not (consp cs)))
           (equal cs nil))
  :rule-classes :forward-chaining)

; "Fallback":
(defthm polyp-intro
  (implies (and (posp p) (pfield::all-fep cs p))
           (polyp cs p)))

)

;; ==== Operational properties ====

; i.e., abstraction-breaking.
; Annoying but they do occasionally appear in proofs,
; which likely means we could...
; TODO: engineer some better abstraction boundaries.

(defthm consp-poly-shift-consp
  (implies (and (natp n)
                (consp cs))
           (consp (poly-shift n cs))))

(defrule consp-poly-shift-pos
  (implies (posp n)
           (consp (poly-shift n cs)))
  :induct (nat-ind n))

(defthm consp-poly-scale
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (consp (poly-scale c cs p))))

(defrule consp-poly+
  (implies (and (posp p)
                (polyp as p) (polyp bs p)
                (consp as) (consp bs))
           (consp (poly+ as bs p)))
  :enable poly+)

(defthm consp-poly*
  (implies (and (posp p)
                (polyp as p) (polyp bs p)
                (consp as) (consp bs))
           (consp (poly* as bs p)))
  :hints (("Goal" :use consp-poly+)))

(defthm poly-shift-len
  (implies (natp n)
           (equal (len (poly-shift n cs))
                  (+ n (len cs)))))

; --- Properties involving rev ---

; If (polyp as p) holds, (rev as) may be seen
; as the *big endian* representation of as. We
; collect some required properties of (rev as)
; here; though what we really should do in the
; future is to...
; TODO: have separate type membership predicates
; for little and big endian polynomials, and
; hide `rev` behind an abstraction that converts
; endianness.

(defrule rev-poly-scale
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p))
           (equal (rev (poly-scale c cs p))
                  (poly-scale c (rev cs) p)))
  :enable pfield::rev-mapmul-eq-mapmul-rev)


;; ==== Algebraic properties ====

; --- ... of basic operations ---
; i.e. shifting and scaling.

; Apparently this is not always easily derived
; in the middle of other proofs.
(defthm poly-scale-nil (equal (poly-scale c nil p) nil))

(defthm poly-scale-constant
  (implies (and (posp p)
                (pfield::fep c p)
                (constpolyp cs p))
           (equal (poly-scale c cs p)
                  (list (pfield::mul c (first cs) p)))))

(defthm first-of-poly-scale
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p)
                (consp cs))
           (equal (first (poly-scale c cs p))
                  (pfield::mul c (first cs) p))))

; Candidate for disabling?
; I think not; let's say that a normal form for polynomials
; should have the primitive list functions `first` and `rest`
; in innermost positions.
(defthm rest-of-poly-scale
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p)
                (consp cs))
           (equal (rest (poly-scale c cs p))
                  (poly-scale c (rest cs) p))))

(defthm poly-scale-of-poly-scale
  (implies (and (posp p)
                (pfield::fep c p)
                (pfield::fep d p)
                (polyp cs p))
           (equal (poly-scale c (poly-scale d cs p) p)
                  (poly-scale (pfield::mul c d p) cs p))))

(defthm poly-shift+
  (implies (and (natp m) (natp n))
           (equal (poly-shift m (poly-shift n cs))
                  (poly-shift (+ m n) cs))))

(defthm poly-scale-of-poly-shift
  (implies (and (posp p)
                (natp n)
                (pfield::fep c p)
                (polyp cs p))
           (equal (poly-scale c (poly-shift n cs) p)
                  (poly-shift n (poly-scale c cs p)))))


; --- Addition ---

(section

(local (in-theory (enable poly+)))

(defthm poly+-comm
  (implies (and (polyp as p) (polyp bs p))
           (equal (poly+ bs as p) (poly+ as bs p))))

(defrule poly+-assoc
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly+ (poly+ as bs p) cs p)
                  (poly+ as (poly+ bs cs p) p)))
  :enable polyp)

(defthm poly-scale-dist-poly+
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly-scale c (poly+ as bs p) p)
                  (poly+ (poly-scale c as p)
                         (poly-scale c bs p) p))))

(defrule poly-shift-dist-poly+
  (implies (and (natp n)
                (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly-shift n (poly+ as bs p))
                  (poly+ (poly-shift n as)
                         (poly-shift n bs) p)))
  :induct (nat-ind n))

; Will this cause problems if left enabled?
(defthm swap-start-of-poly+-poly+
  (implies (and (posp p)
                (polyp as p) (polyp bs p) (polyp cs p))
           (equal (poly+ bs (poly+ as cs p) p)
                  (poly+ as (poly+ bs cs p) p))))

(defthm first-of-poly+
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (consp as)
                (consp bs))
           (equal (first (poly+ as bs p))
                  (pfield::add (first as) (first bs) p))))

(defthm rest-of-poly+
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (consp as)
                (consp bs))
           (equal (rest (poly+ as bs p))
                  (poly+ (rest as) (rest bs) p))))

(defthm first-of-poly+-poly-shift
  (implies (and (posp p)
                (posp n)
                (polyp as p)
                (polyp bs p)
                (consp as))
           (equal (first (poly+ as (poly-shift n bs) p))
                  (first as))))

(defthm rest-of-poly+-poly-shift-1
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (consp as))
           (equal (rest (poly+ as (poly-shift 1 bs) p))
                  (poly+ (rest as) bs p))))

; The unit for addition is the zero polynomial
; *in its representation via the nil list*:
; it is *not* the case that zs + cs = cs or cs + zs = cs
; for an arbitrary representation zs of the zero polynomial!
; However, we have the following two useful equalities:

(defrule poly+-lunit-len-1
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (equal (poly+ '(0) cs p) cs))
  :enable polyp)

(defrule poly+-runit-len-1
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (equal (poly+ cs '(0) p) cs))
  :enable polyp)

; The above are special cases of the following more general results:

(defruled poly+-lunit
  (implies (and (posp p)
                (zeropolyp zs p)
                (polyp cs p)
                (<= (len zs) (len cs)))
           (equal (poly+ zs cs p) cs))
  :enable (polyp repeat))

)

(defruled poly+-runit
  (implies (and (posp p)
                (zeropolyp zs p)
                (polyp cs p)
                (<= (len zs) (len cs)))
           (equal (poly+ cs zs p) cs))
  :enable poly+-lunit)


; --- Multiplication ---

(defthm poly*-nil-l
  (implies (and (posp p) (polyp cs p))
           (equal (poly* nil cs p) nil)))

(defthm poly*-nil-r
  (implies (and (posp p) (polyp cs p))
           (equal (poly* cs nil p) nil)))

; I think this is indeed the usual direction
; we want to normalize in.
(defrule poly*-poly-scale-l
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* (poly-scale c as p) bs p)
                  (poly-scale c (poly* as bs p) p)))
  :disable (poly-scale poly-shift))

(defrule poly*-dist-poly+-l
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* as (poly+ bs cs p) p)
                  (poly+ (poly* as bs p)
                         (poly* as cs p) p)))
  :enable poly+
  :disable (poly-scale poly-shift)
  :induct (len as)
  :do-not '(eliminate-destructors))

(defrule poly*-comm
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* bs as p) (poly* as bs p)))
  :enable poly+
  :induct (poly*-ind as bs)
  :do-not '(eliminate-destructors generalize))

(defrule poly*-poly-scale-r
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* as (poly-scale c bs p) p)
                  (poly-scale c (poly* as bs p) p)))
  :disable (poly-scale poly-shift)
  :use ((:instance poly*-comm
                   (as (poly-scale c bs p))
                   (bs as))))

(defthm poly*-dist-poly+-r
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* (poly+ as bs p) cs p)
                  (poly+ (poly* as cs p)
                         (poly* bs cs p) p))))

(defrule poly*-assoc
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* (poly* as bs p) cs p)
                  (poly* as (poly* bs cs p) p)))
  :prep-lemmas
    ((defruled rew
       (implies (and (posp p)
                     (polyp as p)
                     (polyp bs p)
                     (polyp cs p))
                (equal (poly+ as (poly+ bs cs p) p)
                       (poly+ (poly+ as cs p) bs p)))))
  :enable poly+
  :disable (poly-scale poly-shift poly* poly*-comm)
  :expand ((poly* (poly* as bs p) cs p)
           (poly* as (poly* bs cs p) p))
  :induct (poly*-ind as bs)
  :do-not '(eliminate-destructors generalize)
  :hints
    (("Subgoal *1/1.3"
       :expand ((poly* as bs p)
                (poly* bs cs p))
       :use (:instance rew
              (as (poly-scale (pfield::mul (first as) (first bs) p) cs p))
              (bs (poly-shift 1 (poly* (poly* (rest as) bs p) cs p)))
              (cs (poly-shift 1 (poly-scale (first as)
                                            (poly* (rest bs) cs p)
                                            p)))))))

; Multiplying by monomials
(defrule poly*-by-constpoly-l
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p))
           (equal (poly* (list c) cs p)
                  (poly-scale c cs p)))
  :enable poly+)

(defrule poly*-by-constpoly-r
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp cs p))
           (equal (poly* cs (list c) p)
                  (poly-scale c cs p)))
  :disable poly*)

(defrule poly*-by-monomial
  (implies (and (natp n)
                (posp p)
                (pfield::fep c p)
                (polyp cs p)
                (consp cs))
           (equal (poly* (monomial n c) cs p)
                  (poly-shift n (poly-scale c cs p))))
  :induct (nat-ind n)
  :hints
    (("Subgoal *1/1'"
       :do-not-induct t
       :expand (poly-shift n (list c))
       :in-theory (disable poly*-comm))
     ("Subgoal *1/1''"
       :use (:instance poly+-lunit
              (zs (pfield::mapmul 0 cs p))
              (cs (cons 0 (poly-shift (1- n) (pfield::mapmul c cs p))))))))