(ld "arithmetic.lisp")
(ld "polynomials.lisp")

;; General
;  Theorems that would work on polynomials over
; general acl2-numbers, not just integers.

(defthmd zeropolyp-iff
  (implies (polyp p)
    (iff (zeropolyp p)
         (or (not p)
             (and (consp p)
                  (zerop (first p))
                  (zeropolyp (rest p)))))))

(defthmd not-zeropolyp-iff-nonzeropolyp
  (implies (polyp p)
    (iff (nonzeropolyp p) (not (zeropolyp p)))))

(defthm poly-trim-closed
  (iff (polyp (poly-trim p)) (polyp p)))

(defthm raise-deg-closed
  (implies (and (natp n) (polyp p))
           (polyp (raise-deg n p))))

(defthm scale-polynomial-closed
  (implies (and (polyp p) (integerp c)) (polyp (scale-polynomial p c))))

(defthm polynomial-+-closed
  (implies (and (polyp p) (polyp q)) (polyp (polynomial-+ p q))))

(defthm polynomial-*-closed
  (implies (and (polyp p) (polyp q)) (polyp (polynomial-* p q))))

(defthmd polynomial-+-comm
  (implies (and (polyp p) (polyp q))
           (equal (polynomial-+ p q) (polynomial-+ q p))))

(defthmd polynomial-+-unassoc
  (equal (polynomial-+ p (polynomial-+ q r))
         (polynomial-+ (polynomial-+ p q) r)))

(defthm poly-trim-zeropoly
  (implies (zeropolyp p) (not (poly-trim p))))

(defthm polynomial-*-2ndarg-nil
  (implies (polyp p) (zeropolyp (polynomial-* p nil))))

; poly* nil q evaluates definitionally to nil.
; The following is for nil in the second arg.
(defthm poly*-2ndarg-nil
  (implies (polyp p) (equal (poly* p nil) nil)))


;; ℤ[x]

(defthm poly+-closed
  (implies (and (polyp p) (polyp q)) (polyp (poly+ p q))))

(defthm poly*-closed
  (implies (and (polyp p) (polyp q)) (polyp (poly* p q))))

(defthm poly-neg-closed
  (implies (polyp p) (polyp (poly-neg p))))

(defthmd poly+-comm
  (implies (and (polyp p) (polyp q)) (equal (poly+ p q) (poly+ q p))))

(encapsulate ()
  (defun obv-comm-poly* (p q)
    (cond ((not (and (polyp p) (polyp q)))
            :error[obv-comm-poly*][p-or-q-not-poly])
          ((not p) nil)
          ((not q) nil)
          (t
            (poly-trim
              (poly+ (list (* (first p) (first q)))
              (poly+ (raise-deg 1 (scale-polynomial (rest q) (first p)))
              (poly+ (raise-deg 1 (scale-polynomial (rest p) (first q)))
                     (raise-deg 2 (obv-comm-poly* (rest p) (rest q))))))))))

  (local (defthm obv-comm-poly*-comm
    (implies (and (polyp p) (polyp q))
             (equal (obv-comm-poly* p q) (obv-comm-poly* q p)))
    :hints (("Goal"
      :in-theory (enable poly+-comm
                         polynomial-+-unassoc
                         polynomial-+-comm)))))

  ; (local (defthm poly*-eq-obv-comm-poly*
  ;   (implies (and (polyp p) (polyp q))
  ;            (equal (poly* p q) (obv-comm-poly* p q)))
  ;   :hints (("Goal"
  ;     :cases ((not p)
  ;             (not q)
  ;             (and (consp p) (consp q)))))
  ;   ))
)

; (defthmd poly*-comm-lem-1
;   (all-equalp 0 (rev (polynomial-* q nil))))

; (defthmd poly*-comm
;   (implies (and (polyp p) (polyp q)) (equal (poly* p q) (poly* q p))))



(defthm poly+-poly-neg
  (equal (poly+ p (poly-neg q)) (poly- p q)))

(defthm mapmod-poly+-mapmod-snd
  (implies (and (polyp p) (polyp q))
           (equal (mapmod (poly+ p (mapmod q n)) n)
                  (mapmod (poly+ p q) n))))


;; (ℤ/nℤ)[x]

(defthm polymod+-closed
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (polyp (polymod+ p q n))))

(defthm polymod*-closed
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (polyp (polymod* p q n)))
  :hints (("Goal" :in-theory (disable poly*))))

(defthmd polymod+-comm
  (implies (and (polyp p) (polyp q))
           (equal (polymod+ p q n) (polymod+ q p n))))

; (defthmd polymod*-comm
;   (implies (and (polyp p) (polyp q))
;            (equal (polymod* p q n) (polymod* q p n))))

; This should hold
(defthm polymod--equal
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (equal (polymod+ p (polymod-neg q n) n)
                  (polymod- p q n)))
  :hints
    (("Goal"
       :use ((:instance mapmod-poly+-mapmod-snd (q (map- q)))
             (:instance poly-neg-closed (p q))))
    ))

