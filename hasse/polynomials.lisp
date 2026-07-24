(in-package "HASSE-THM")

(ld "prelude.lisp")

;;; Univariate polynomials over an unspecified field.

;   A polynomial over a field K is simply a list of coefficients,
;   each of which is supposed to be an element of K.
;   The entry at index k is the coefficient of x^k.
;
;   Because the field is arbitrary, every function we write takes
;   the appropriate required field components as arguments.


; "Constructors" for polynomials
(defun zeropoly () nil)
; This lets us write the coefficients in order of decreasing degree.
(defun poly (coeffs) (reverse coeffs))

; (Removes trailing zeros. f0 is the zero of the field.)
(defun norm-poly (f0 p) (dropValsFromEnd f0 p))

(defun is-zeropoly (f0 p) (endp (norm-poly f0 p)))

(defun deg (f0 p) (pred (len (norm-poly f0 p))))
