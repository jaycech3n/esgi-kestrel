(ld "polynomials.lisp")

;; ==== Operational properties ====

; i.e., abstraction-breaking.
; Annoying but they do occasionally appear in proofs,
; which probably means we could engineer some better
; abstraction boundaries. But at this stage the payoff
; doesn't seem worth it.

(defthm consp-poly-scale
  (implies (and (posp p)
                (polyp cs p)
                (consp cs))
           (consp (poly-scale c cs p))))

(defthm consp-poly+
  (implies (and (posp p)
                (polyp as p) (polyp bs p)
                (consp as) (consp bs))
           (consp (poly+ as bs p))))

(defthm consp-poly*
  (implies (and (posp p)
                (polyp as p) (polyp bs p)
                (consp as) (consp bs))
           (consp (poly* as bs p)))
  :hints (("Goal" :use consp-poly+)))


;; ==== Algebraic properties ====

; --- ... of basic operations ---
; i.e. shifting and scaling.

; Apparently this is not always easily derived
; in the middle of other proofs.
(defthm poly-scale-nil (equal (poly-scale c nil p) nil))

(defthm poly-scale-monomial
  (implies (and (posp p)
                (pfield::fep c p)
                (monomialp cs p))
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


; --- Multiplication ---

(defthm poly*-nil-l
  (implies (and (posp p) (polyp cs p))
           (equal (poly* nil cs p) nil)))

(defthm poly*-nil-r
  (implies (and (posp p) (polyp cs p))
           (equal (poly* cs nil p) nil)))

; I think this is indeed the usual direction
; we want to normalize in.
(defthm poly*-poly-scale-l
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* (poly-scale c as p) bs p)
                  (poly-scale c (poly* as bs p) p)))
  :hints (("Goal" :in-theory (disable poly-scale poly-shift))))

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
    :do-not '(eliminate-destructors)))
  )

(defthm poly*-comm
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* bs as p) (poly* as bs p)))
  :hints (("Goal"
    :induct (poly*-ind as bs)
    :do-not '(eliminate-destructors generalize))))

(defthm poly*-poly-scale-r
  (implies (and (posp p)
                (pfield::fep c p)
                (polyp as p)
                (polyp bs p))
           (equal (poly* as (poly-scale c bs p) p)
                  (poly-scale c (poly* as bs p) p)))
  :hints (("Goal"
    :in-theory (disable poly-scale poly-shift)
    :use ((:instance poly*-comm
                    (as (poly-scale c bs p))
                    (bs as))))))

(defthm poly*-dist-poly+-r
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* (poly+ as bs p) cs p)
                  (poly+ (poly* as cs p)
                         (poly* bs cs p) p))))

(section

(local (defthmd rew
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly+ as (poly+ bs cs p) p)
                  (poly+ (poly+ as cs p) bs p)))))

(defthm poly*-assoc
  (implies (and (posp p)
                (polyp as p)
                (polyp bs p)
                (polyp cs p))
           (equal (poly* (poly* as bs p) cs p)
                  (poly* as (poly* bs cs p) p)))
  :hints
    (("Goal"
       :in-theory (disable poly-scale poly-shift poly*
                           poly*-comm)
       :expand ((poly* (poly* as bs p) cs p)
                (poly* as (poly* bs cs p) p))
       :induct (poly*-ind as bs)
       :do-not '(eliminate-destructors generalize)
     )
     ("Subgoal *1/1.3"
       :expand ((poly* as bs p)
                (poly* bs cs p))
       :use (:instance rew
              (as (poly-scale (pfield::mul (first as) (first bs) p) cs p))
              (bs (poly-shift 1 (poly* (poly* (rest as) bs p) cs p)))
              (cs (poly-shift 1 (poly-scale (first as)
                                            (poly* (rest bs) cs p)
                                            p))))
     )))

)