(ld "big-endian.lisp")

; Core algorithm, tail recursive with accumulator for the quotient.
; Argument requirements:
; · `ax` and `bx` in big endian,
; · `acc` in little endian representation of polynomials.
; · (coeffs bx) normalized, i.e. no leading zero.
(define poly-div-aux (ax bx acc p)
  :enabled t
  :measure (+ (len (coeffs ax)) (len (coeffs bx)))
  :guard (and (posp p)
              (bigpolyp ax p)
              (nonzero-normal-bigpolyp bx p)
              (polyp acc p))
  (let ((as (coeffs ax))
        (bs (coeffs bx)))
    (cond ( (atom bs) :[poly-div-aux]-bad-inputs )
          ( (< (len as) (len bs)) (list acc as) )
          ( t
            (let* ((q  (pfield::div (first as) (first bs) p))
                   (cs (pfieldlist::sub (rest as)
                                       (pfieldlist::scale q (rest bs) p)
                                       p)))
              (poly-div-aux cs bs (cons q acc) p))))))

#|

; Need this for the guard condition of poly-div.
(defthm poly-div-aux-consp
  (implies (and (posp p)
                (pfieldlist::all-fep as p)
                (pfieldlist::all-fep bs p)
                (pfieldlist::all-fep acc p)
                (consp bs)
                (not (equal (first bs) 0)))
           (consp (poly-div-aux as bs acc p))))

; Returns a pair containing the quotient and remainder.
; Here `as` and `bs` are little endian.
(define poly-div (as bs p)
  :guard (and (posp p)
              (pfieldlist::all-fep as p)
              (pfieldlist::all-fep bs p))
  (let ((ds (dropvals 0 (rev bs)))) ; Normalize divisor.
    (if (atom ds)
        :[poly-div]-bad-input
        (let* ((cs (rev as))
               (ret (poly-div-aux cs ds nil p)))
          (list (first ret)
                (rev (dropvals 0 (second ret))))))))

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

|#