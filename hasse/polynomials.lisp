;;; Polynomials over arbitrary fields.
;   A polynomial over a field K is simply a list of coefficients,
;   each of which is supposed to be an element of K.
;   The entry at index k is the coefficient of x^k.

(in-package "HASSE-THM")

(ld "prelude.lisp")
(ld "fields.lisp") ; pulls in the components dm::f0, dm::f+, ... of a generic field.

; "Constructors" for polynomials
(defun zeropoly () nil)
; This lets us write the coefficients in order of decreasing degree.
(defun poly (coeffs) (reverse coeffs))

; (Removes trailing zeros. f0 is the zero of the field.)
(defun norm-poly (p) (dropValsFromEnd (dm::f0) p))

(defun is-zeropoly (p) (endp (norm-poly p)))

(defun deg (p) (pred (len (norm-poly p))))

