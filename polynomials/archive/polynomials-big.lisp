;;; Big endian polynomials

; Doable, but here the issue will be that operations e.g. multiplication
; will require lists to be extended at the end with zeroes.

(ld "../prelude.lisp")
(ld "../prime-fields.lisp")

(defun polyp (cs p)
  (declare (xargs :guard (posp p)))
  (pfieldlist::all-fep cs p))

(defun poly+ (as bs p)
  ; (declare (xargs :guard ?))
  (let ((args (pad-front 0 as bs)))
    (pfieldlist::add (first args) (second args) p)))

; (defun poly* (as bs p)
;   ?)
