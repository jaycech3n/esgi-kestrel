(in-package "HASSE-THM")
(ld "prelude.lisp")

;;; Univariate polynomials over an unspecified field.
;   A polynomial over a field K is simply a list of coefficients,
;   each of which is supposed to be an element of K.
;   The entry at index k is the coefficient of x^k.

(defun poly (coeffs) (reverse coeffs))
(defun zeropoly () nil)

; z is the zero of the field
(defun deg (p z) (pred (len (dropValsFromEnd z p))))

