;;; Big endian coefficient list encoding of polynomials.

(ld "polynomial-thms.lisp")

; For certain algorithms (e.g. division) it is convenient to use an
; interim *big endian* coefficient list representation of polynomials.
; Here we collect functions and theorems to convert between encodings
; of different endianness.

; We encode the data of a big endian polynomial in a pair whose first
; entry is the symbol :big-endian.
(define bigpolyp (cx p)
  :enabled t
  :guard (posp p)
  (and (pairp cx)
       (eql (first cx) :big-endian)
       (pfield::all-fep (second cx) p)))

(define coeffs (cx)
  :enabled t
  :guard (and (pairp cx)
              (eql (first cx) :big-endian))
  (second cx))

(define nonzero-normal-bigpolyp (cx p)
  :enabled t
  :guard (posp p)
  (and (bigpolyp cx p)
       (let ((cs (coeffs cx)))
         (and (consp cs)
              (not (equal (first cs) 0))))))


; ==== Operations ====

(define to-little (cx)
  (rev (coeffs cx)))

(defpkg "BIGEND"
  (union-eq *acl2-exports*
            *common-lisp-symbols-from-main-lisp-package*))

(in-package "BIGEND")

; This is "operational". Abstractly,
;   (padright- ax bx p)
; is the big endian representation of
;   (to-little ax)
;   - poly-shift (deg(to-little ax) - deg(to-little bx))
;                (to-little bx).
(defun padright-)