;;; Big endian coefficient list encoding of polynomials.

(ld "polynomial-thms.lisp")

; For certain algorithms (e.g. division) it is convenient to use an
; interim *big endian* coefficient list representation of polynomials.
; Here we collect functions and theorems to convert between encodings
; of different endianness.

; We encode the data of a big endian polynomial in a pair whose first
; entry is the symbol :big-endian.
(define bigpolyp (cx p)
  :guard (posp p)
  (and (pairp cx)
       (eql (first cx) :big-endian)
       (pfield::all-fep (second cx) p)))

; Should this be disabled?
; (defun )