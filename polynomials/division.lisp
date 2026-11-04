(ld "polynomial-thms.lisp")

; Core algorithm, tail recursive with accumulator for the quotient.
; Argument requirements:
; · `as` and `bs` in big endian,
; · `acc` in little endian representation of polynomials.
; · `bs` normalized, i.e. no leading zero.
(define poly-div-aux (as bs acc p)
  :enabled t
  :measure (+ (len as) (len bs))
  :guard (and (posp p)
              (pfield::all-fep as p)
              (pfield::all-fep bs p)
              (pfield::all-fep acc p)
              (consp bs)
              (not (equal (first bs) 0)))
  (cond ( (atom bs) :[poly-div-aux]-bad-inputs )
        ( (< (len as) (len bs)) (list acc as) )
        ( t
          (let* ((q  (pfield::div (first as) (first bs) p))
                 (cs (pfield::zipsub (rest as)
                                      (pfield::mapmul q (rest bs) p)
                                      p)))
            (poly-div-aux cs bs (cons q acc) p)))))

; Need this for the guard condition of poly-div.
(defthm poly-div-aux-consp
  (implies (and (posp p)
                (pfield::all-fep as p)
                (pfield::all-fep bs p)
                (pfield::all-fep acc p)
                (consp bs)
                (not (equal (first bs) 0)))
           (consp (poly-div-aux as bs acc p))))

; Returns a pair containing the quotient and remainder.
; Here `as` and `bs` are little endian.
(define poly-div (as bs p)
  :guard (and (posp p)
              (pfield::all-fep as p)
              (pfield::all-fep bs p))
  (let ((ds (drop-vals 0 (rev bs)))) ; Normalize divisor.
    (if (atom ds)
        :[poly-div]-bad-input
        (let* ((cs (rev as))
               (ret (poly-div-aux cs ds nil p)))
          (list (first ret)
                (rev (drop-vals 0 (second ret))))))))

; (defthm poly-div-correct
;   (implies (and (posp p)
;                 (polyp as p)
;                 (polyp bs p)
;                 (nonzeropolyp bs p))
;            (let*
;              ((res (poly-div as bs p))
;               (qs (first res))
;               (rs (second res)))
;              (equal (poly+ (poly* qs bs p) rs p)
;                     as)))
;   :hints (("Goal" :induct (len as))))