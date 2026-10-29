(ld "polynomial-thms.lisp")

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
              (cs (cons 0 (poly-shift (1- n) (pfield::mapmul c cs p)))))
       :in-theory (enable pfield::mapmul-0))))



#|
|#