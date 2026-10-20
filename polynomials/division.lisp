(ld "polynomial-thms.lisp")

(section

; Core algorithm, tail recursive with accumulator `qs` for the quotient.
; Argument requirements:
; · `as` and `bs` in big endian,
; · `qs` in little endian representation of polynomials.
; · `bs` normalized, i.e. no leading zero.
(defun poly-div-aux (as bs qs p)
  (declare (xargs
    :measure (+ (len as) (len bs))
    :guard
      (and (posp p)
           (pfield::all-fep as p)
           (pfield::all-fep bs p)
           (pfield::all-fep qs p)
           (consp bs)
           (not (equal (first bs) 0))))
  )
  (cond ((atom bs)
          :[poly-div-aux]-bad-inputs)
        ((< (len as) (len bs))
          (list qs as))
        (t
          (let*
            (( q (pfield::div (first as) (first bs) p))
             (ns (pfield::zipadd
                  (rest as)
                  (pfield::mapneg (pfield::mapmul q (rest bs) p) p)
                  p)))
            (poly-div-aux ns bs (cons q qs) p)))))

(defthm poly-div-aux-len
  (implies (and (posp p)
                (pfield::all-fep as p)
                (pfield::all-fep bs p)
                (pfield::all-fep qs p)
                (consp bs)
                (not (equal (first bs) 0)))
           (equal (len (poly-div-aux as bs qs p)) 2)))

(defthm poly-div-aux-consp
  (implies (and (posp p)
                (pfield::all-fep as p)
                (pfield::all-fep bs p)
                (pfield::all-fep qs p)
                (consp bs)
                (not (equal (first bs) 0)))
           (consp (poly-div-aux as bs qs p))))

; Assumes inputs are in big endian.
; Returns a pair containing the quotient and remainder.
(defun poly-div (as bs p)
  (declare (xargs :guard
    (and (posp p)
         (pfield::all-fep as p)
         (pfield::all-fep bs p)))
  )
  (let ; Convert little -> big endian, and normalize divisor.
    ((cs (rev as))
     (ds (drop-vals 0 (rev bs))))
    (if (atom ds)
        :[poly-div]-bad-input
        ; (poly-div-aux cs ds nil p)
        (let ((ret (poly-div-aux cs ds nil p)))
          (list (first ret)
                (rev (drop-vals 0 (second ret)))))
        )))

)