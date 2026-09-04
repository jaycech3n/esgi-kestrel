(ld "polynomials.lisp")

;; General

(defthmd zeropolyp-iff
  (iff (zeropolyp p)
       (or (nilp p)
           (and (consp p)
                (zerop (first p))
                (zeropolyp (rest p))))))

(defthmd not-zeropolyp-iff-nonzeropolyp
  (implies (polyp p)
           (iff (nonzeropolyp p) (not (zeropolyp p)))))

(defthm poly*x-closed
  (implies (polyp p) (polyp (poly*x p))))

(defthm scale-polynomial-closed
  (implies (and (polyp p) (integerp c)) (polyp (scale-polynomial p c))))


;; ℤ[x]

(defthm poly+-closed
  (implies (and (polyp p) (polyp q)) (polyp (poly+ p q))))

(defthm poly*-closed
  (implies (and (polyp p) (polyp q)) (polyp (poly* p q)))
  :hints
    (("Goal" :induct (len p))
     ("Subgoal *1/1''"
       :use
         ((:instance poly+-closed
                     (p (scale-polynomial q (car p)))
                     (q (cons 0 (polynomial-* (cdr p) q))))
          (:instance scale-polynomial-closed
                     (p q)
                     (c (car p)))
         ))
    ))

(defthmd poly+-comm
  (implies (and (polyp p) (polyp q)) (equal (poly+ p q) (poly+ q p))))

; [WIP]
; poly* nil q evaluates definitionally to nil.
; This is for nil in the second arg.
; (defthm poly*-nil (equal (poly* p nil) nil)
;   :hints (("Goal" :induct (len p))))

; (defthmd poly*-comm
;   (implies (and (polyp p) (polyp q)) (equal (poly* p q) (poly* q p))))


;; (ℤ/nℤ)[x]

(defthm polymod+-closed
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (polyp (polymod+ n p q))))

(defthm polymod*-closed
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (polyp (polymod* n p q)))
  :hints
    (("Goal"
       :do-not-induct t
       :use poly*-closed)))

(defthmd polymod+-comm
  (implies (and (integerp n)
                (polyp p)
                (polyp q))
           (equal (polymod+ n p q) (polymod+ n q p))))

; (defthmd polymod*-comm
;   (implies (and (integerp n)
;                 (polyp p)
;                 (polyp q))
;            (equal (polymod* n p q) (polymod* n q p))))

; This should hold
; (defthmd polymod--equal
;   (implies (and (integerp n)
;                 (polyp p)
;                 (polyp q))
;            (equal (polymod- n p q)
;                   (polymod+ n p (polymod-neg n q)))))