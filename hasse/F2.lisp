(in-package "HASSE-THM")

;;; The finite field of order 2

;; Carrier of F2
(defun F2 () '(0 1))

;; Field structure of F2
(defun F2is0 (x) (= 0 x))
(defun F2is1 (x) (= 1 x))
(defun F2not0 (x) (F2is1 x))

(defun inF2 (x) (or (F2is0 x) (F2is1 x)))

(defun F2flip (x)
  ;; (declare (type (satisfies inF2) x))
  (if (F2is0 x) 1 0))

(defun F2+ (x y)
  ;; (declare (type (satisfies inF2) x y))
  (if (F2is0 x) y (F2flip y)))

(defun F2* (x y)
  ;; (declare (type (satisfies inF2) x y))
  (if (F2is0 x) 0 y))

(defun F2-0 () 0)
(defun F2-1 () 1)

(defun F2- (x)
  ;; (declare (type (satisfies inF2) x))
  x)

(defun F2/ (x)
  ;; (declare (type (satisfies inF2) x)
  ;;          (xargs :guard (F2not0 x)))
  x)

;; Field axioms

; Can I just import...
(ld "projects/numbers/package.lsp" :dir :system) ; defines the package for the next book
(include-book "projects/linear/field" :dir :system)

; ...instead of reproducing the following?

;; ; Closure:
;; (defthm F2+closed (implies (and (inF2 x) (inF2 y)) (inF2 (F2+ x y))))
;; (defthm F2*closed (implies (and (inF2 x) (inF2 y)) (inF2 (F2* x y))))
;; ; Commutativity
;; (defthmd F2+comm (implies (and (inF2 x) (inF2 y)) (equal (F2+ x y) (F2+ y x))))
;; (defthmd F2*comm (implies (and (inF2 x) (inF2 y)) (equal (F2* x y) (F2* y x))))
;; ; Associativity:
;; (defthmd F2+assoc (implies (and (inF2 x) (inF2 y) (inF2 z)) (equal (F2+ x (F2+ y z)) (F2+ (F2+ x y) z))))
;; (defthmd F2*assoc (implies (and (inF2 x) (inF2 y) (inF2 z)) (equal (F2* x (F2* y z)) (F2* (F2* x y) z))))
;; ; Identity:
;; (defthm 0inF2 (inF2 (F2-0)))
;; (defthm 1inF2 (inF2 (F2-1)))
;; (defthm F2-0-not-1 (not (equal (F2-1) (F2-0))))
;; (defthm F2-0-id (implies (inF2 x) (equal (F2+ x (F2-0)) x)))
;; (defthm F2-1-id (implies (inF2 x) (equal (F2* x (F2-1)) x)))
;; ; Inverse:
;; (defthm -inF2 (implies (inF2 x) (inF2 (F2- x))))
;; (defthm /inF2 (implies (and (inF2 x) (not (equal x (F2-0)))) (inF2 (F2/ x))))
;; (defthm F2+inv (implies (inF2 x) (equal (F2+ x (F2- x)) (F2-0))))
;; (defthm F2*inv (implies (and (inF2 x) (not (equal x (F2-0)))) (equal (F2* x (F2/ x)) (F2-1))))
;; ; Distributivity:
;; (defthm F2dist (implies (and (inF2 x) (inF2 y) (inF2 z)) (equal (F2* x (F2+ y z)) (F2+ (F2* x y) (F2* x z)))))
