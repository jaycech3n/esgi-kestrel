; Import basic definition of fields
(ld "projects/numbers/package.lsp" :dir :system)
(include-book "projects/linear/field" :dir :system)

(ld "prelude.lisp")

;; More definitions

(defun fsum (n x)
  (if (natp n)
      (if (zerop n)
          (dm::f0)
          (dm::f+ x (fsum (nat-pred n) x)))
      :error[fsum][n-not-nat))

; Field characteristic

(defun fchar-fin (n) ; note that this is not *the* characteristic
  (if (natp n)
      (equal (dm::f0) (fsum n (dm::f1)))
      :error[fchar-fin][n-not-nat]))

(defun fchar-0 (n)
  (if (natp n)
      (not (equal (dm::f0) (fsum n (dm::f1))))
      :error[fchar-0][n-not-nat]))