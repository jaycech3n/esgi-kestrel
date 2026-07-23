(in-package "HASSE-THM")
(ld "prelude.lisp")
(ld "F2.lisp")

;;; Finite fields
(encapsulate (;; Field structure
              ((fp *) => *)
              ((f+ * *) => *) ((f0) => *) ((f- *) => *)
              ((f* * *) => *) ((f1) => *) ((f/ *) => *)
              ;; Finiteness structure
              ((base) => *)
              ((exponent) => *)
              ((code *) => *)
              ((decode *) => *))

  ; The witness is the smallest finite field, F2 = F_(2^1).
  (local (defun fp (x) (inF2 x)))
  (local (defun f+ (x y) (F2+ x y)))
  (local (defun f0 () (F2-0)))
  (local (defun f- (x) (F2- x)))
  (local (defun f* (x y) (F2* x y)))
  (local (defun f1 () (F2-1)))
  (local (defun f/ (x) (F2/ x)))
  (local (defun base () 2))
  (local (defun exponent () 1))
  (local (defun code (x) x))
  (local (defun decode (n) n))

  ; Finiteness axioms
  (defthm code-decode-bij
    (and (equal (decode (code x)) x) (equal (code (decode n)) n)))

  (defthm finiteness
    (iff (fp x) (in-rangep (expt (base) (exponent)) (code x)))
    :hints (("Goal" :use in-rangep-2-vals))))

