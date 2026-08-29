; Import basic definition of fields
(ld "projects/numbers/package.lsp" :dir :system)
(include-book "projects/linear/field" :dir :system)

(ld "prelude.lisp")

;; More definitions

(defun fsum (n x)
  (declare (type (satisfies natp) n))
  (if (mbt (natp n))
      (if (zerop n) (dm::f0)
          (dm::f+ x (fsum (nat-pred n) x)))
      (dm::f0)))

; Field characteristic

(defun fchar-fin (n) ; note that this is not *the* characteristic
  (declare (type (satisfies natp) n))
  (equal (dm::f0) (fsum n (dm::f1))))

(defun fchar-0 (n)
  (declare (type (satisfies natp) n))
  (not (equal (dm::f0) (fsum n (dm::f1)))))