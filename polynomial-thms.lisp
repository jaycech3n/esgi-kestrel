(ld "arithmetic.lisp")
(ld "polynomials.lisp")

;; ==== ℤ[x] ====

; A lot of these theorems would also work for
; polynomials over arbitrary acl2-numbers.


; --- Zero polynomials ---

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

(defthm poly-trim-zeropoly
  (implies (zeropolyp p) (nilp (poly-trim p))))


; --- Closure properties ---

(defthm poly-trim-closed
  (iff (polyp (poly-trim p)) (polyp p)))

(defthm raise-deg-closed
  (implies (and (natp n) (polyp p))
           (polyp (raise-deg n p)))
  :rule-classes :type-prescription)

(defthm scale-poly-closed
  (implies (and (polyp p) (integerp c))
           (polyp (scale-poly c p)))
  :rule-classes :type-prescription)

(defthm poly+-closed
  (implies (and (polyp p) (polyp q))
           (polyp (poly+ p q)))
  :rule-classes :type-prescription)

(defthm poly*-closed
  (implies (and (polyp p) (polyp q))
           (polyp (poly* p q)))
  :rule-classes :type-prescription)

(defthm poly-neg-closed
  (implies (polyp p) (polyp (poly-neg p))))


; --- Algebraic properties ---

(defthmd poly+-unassoc
  (equal (poly+ p (poly+ q r))
         (poly+ (poly+ p q) r)))

(defthmd poly+-comm
  (implies (and (polyp p) (polyp q))
           (equal (poly+ p q) (poly+ q p))))

(defthmd poly*-comm
  (implies (and (polyp p) (polyp q))
           (equal (poly* p q) (poly* q p)))
  :hints
    (("Subgoal *1/6''"
      :use (:instance poly+-comm
                      (p (scale-poly (first p) q))
                      (q (scale-poly (first q) p))))))

(defthm poly+-poly-neg
  (equal (poly+ p (poly-neg q)) (poly- p q)))

(defthm mapmod-poly+-mapmod-snd
  (implies (and (integerp n) (polyp p) (polyp q))
           (equal (mapmod (poly+ p (mapmod q n)) n)
                  (mapmod (poly+ p q) n))))



;; ==== (ℤ/nℤ)[x] ====

; --- Closure ---

(defthm polymod+-closed
  (implies (and (integerp n) (polyp p) (polyp q))
           (polyp (polymod+ p q n))))

(defthm polymod*-closed
  (implies (and (integerp n) (polyp p) (polyp q))
           (polyp (polymod* p q n)))
  :hints (("Goal" :in-theory (disable poly*))))

; --- Algebraic properties ---

(defthmd polymod+-comm
  (implies (and (polyp p) (polyp q))
           (equal (polymod+ p q n) (polymod+ q p n)))
  :hints (("Goal" :in-theory (disable poly+)
                  :use poly+-comm)))

(defthmd polymod*-comm
  (implies (and (polyp p) (polyp q))
           (equal (polymod* p q n) (polymod* q p n)))
  :hints (("Goal" :in-theory (disable poly*)
                  :use poly*-comm)))

(defthm polymod--equal
  (implies (and (integerp n) (polyp p) (polyp q))
           (equal (polymod+ p (polymod-neg q n) n)
                  (polymod- p q n)))
  :hints
    (("Goal"
      :use ((:instance mapmod-poly+-mapmod-snd (q (map- q)))
            (:instance poly-neg-closed (p q))))
    ))
