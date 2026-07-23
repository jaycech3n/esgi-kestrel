(in-package "HASSE-THM")

(ld "prelude.lisp")
(ld "F2.lisp")
(ld "primes.lisp")

;;; Finite fields

;; Structure and axioms of a finite field
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
  (local (defun fp (x) (F2.elt x)))
  (local (defun f+ (x y) (F2.+ x y)))
  (local (defun f0 () (F2.0)))
  (local (defun f- (x) (F2.- x)))
  (local (defun f* (x y) (F2.* x y)))
  (local (defun f1 () (F2.1)))
  (local (defun f/ (x) (F2./ x)))
  (local (defun base () 2))
  (local (defun exponent () 1))
  (local (defun code (x) x))
  (local (defun decode (n) n))

  ; Field axioms; copied from books/projects/linear/field.lisp
  (defthm  f+closed (implies (and (fp x) (fp y)) (fp (f+ x y))))
  (defthm  f*closed (implies (and (fp x) (fp y)) (fp (f* x y))))
  (defthm  fpf0     (fp (f0)))
  (defthm  fpf1     (fp (f1)))
  (defthm  f1f0     (not (equal (f1) (f0))))
  (defthm  f0id     (implies (fp x) (equal (f+ x (f0)) x)))
  (defthm  f1id     (implies (fp x) (equal (f* x (f1)) x)))
  (defthm  fpf-     (implies (fp x) (fp (f- x))))
  (defthm  fpf/     (implies (and (fp x) (not (equal x (f0)))) (fp (f/ x))))
  (defthm  f+inv    (implies (fp x) (equal (f+ x (f- x)) (f0))))
  (defthm  f*inv    (implies (and (fp x) (not (equal x (f0)))) (equal (f* x (f/ x)) (f1))))
  (defthm  fdist    (implies (and (fp x) (fp y) (fp z))
                             (equal (f* x (f+ y z)) (f+ (f* x y) (f* x z)))))
  (defthmd f+comm   (implies (and (fp x) (fp y)) (equal (f+ x y) (f+ y x))))
  (defthmd f*comm   (implies (and (fp x) (fp y)) (equal (f* x y) (f* y x))))
  (defthmd f+assoc  (implies (and (fp x) (fp y) (fp z)) (equal (f+ x (f+ y z)) (f+ (f+ x y) z))))
  (defthmd f*assoc  (implies (and (fp x) (fp y) (fp z)) (equal (f* x (f* y z)) (f* (f* x y) z))))

  ; Finiteness axioms
  (defthm base-is-prime (dm::primep (base))
    :hints (("Goal" :in-theory (enable dm::primep))))

  (defthm code-is-nat
    (implies (fp x) (natp (code x))))
  (defthm code-decode-bij
    (implies (and (fp x) (natp n))
             (and (equal (decode (code x)) x) (equal (code (decode n)) n))))
  (defthm finiteness1
    (implies (fp x) (finp (expt (base) (exponent)) (code x))))
  (defthm finiteness2
    (implies (finp (expt (base) (exponent)) n) (fp (decode n)))))


;; Theorems about finite fields
