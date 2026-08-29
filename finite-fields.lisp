(ld "arithmetic.lisp")
(ld "polynomials.lisp")
(ld "fields.lisp")

; Acknowledgement: portions of this are inspired by generated code in
; Gihan's branch. (TODO: ask about provenance---which parts were generated,
; and with which tool?)

; Representations of finite fields: either prime or an extension
(defun ff-prime (p)
  (declare (xargs :guard (dm::primep p)))
  (list :ff-prime p))

(defun ff-ext (p modulus)
  (declare (xargs :guard (dm::primep p)))
  (list :ff-ext p modulus))

(defun ff-kind    (F) (first  F))
(defun ff-char    (F) (second F))
(defun ff-modulus (F) (third  F))

(defun ff-normed (F x)
  (let ((char (ff-char F)))
    (case (ff-kind F)
      (:ff-prime (mod x char))
      (:ff-ext   (poly-normed (mapmod char x)))
      (otherwise :error))))

;; Field operations

; Recognizer for field elements; do not worry about normalizing mod p
(defun ff-p (F x)
  (case (ff-kind F)
    (:ff-prime (integerp x))
    (:ff-ext   (polyp x))
    (otherwise :error)))

(defun ff+ (F x y)
  (let ((char (ff-char F)))
    (case (ff-kind F)
      (:ff-prime (mod+ char x y))
      (:ff-ext   (polymod+ char x y))
      (otherwise :error))))

(defun ff* (F x y)
  (let ((char (ff-char F)))
    (case (ff-kind F)
      (:ff-prime (mod* char x y))
      (:ff-ext   (polymod* char x y))
      (otherwise :error))))

(defun ff0 (F)
  (case (ff-kind F)
    (:ff-prime 0)
    (:ff-ext   (zeropoly))
    (otherwise :error)))

(defun ff1 (F)
  (case (ff-kind F)
    (:ff-prime 1)
    (:ff-ext   (onepoly))
    (otherwise :error)))

(defun ff- (F x y)
  (let ((char (ff-char F)))
    (case (ff-kind F)
      (:ff-prime (mod- char x y))
      (:ff-ext   (polymod- char x y))
      (otherwise :error))))

; (defun ff/ (F x)
;   ...)
