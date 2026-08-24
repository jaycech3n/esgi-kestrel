(in-package "HASSE-THM")

;;; Structures in bijection with {0, ..., p^n - 1}

(ld "prelude.lisp")
(ld "primes.lisp")

(encapsulate (((eltp *) => *)
              ((base) => *)
              ((exponent) => *)
              ((code *) => *)
              ((decode *) => *))

  (local (defun eltp (x) (or (= 0 x) (= 1 x))))
  (local (defun base () 2))
  (local (defun exponent () 1))
  (local (defun code (x) x))
  (local (defun decode (x) x))

  (defthm base-is-prime (dm::primep (base))
    :hints (("Goal" :in-theory (enable dm::primep))))

  (defthm code-is-nat
    (implies (eltp x) (natp (code x))))
  (defthm code-decode-bij
    (implies (and (eltp x) (natp n))
             (and (equal (decode (code x)) x) (equal (code (decode n)) n))))
  (defthm finiteness1
    (implies (eltp x) (finp (expt (base) (exponent)) (code x))))
  (defthm finiteness2
    (implies (finp (expt (base) (exponent)) n) (eltp (decode n)))))
