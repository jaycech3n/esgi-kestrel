(in-package "HASSE-THM")

;;; The finite field of order 2

;; Carrier of F2
(defun F2 () '(0 1))

;; Field structure of F2
(defun F2.is0 (x) (= 0 x))
(defun F2.is1 (x) (= 1 x))

(defun F2.elt (x) (or (F2.is0 x) (F2.is1 x)))
(defun F2.flip (x) (if (F2.is0 x) 1 0))
(defun F2.+ (x y) (if (F2.is0 x) y (F2.flip y)))
(defun F2.0 () 0)
(defun F2.- (x) x)
(defun F2.* (x y) (if (F2.is0 x) 0 y))
(defun F2.1 () 1)
(defun F2./ (x) x)

; Closure:
(defthm F2.+closed (implies (and (F2.elt x) (F2.elt y)) (F2.elt (F2.+ x y))))
(defthm F2.*closed (implies (and (F2.elt x) (F2.elt y)) (F2.elt (F2.* x y))))
; Commutativity
(defthmd F2.+comm (implies (and (F2.elt x) (F2.elt y)) (equal (F2.+ x y) (F2.+ y x))))
(defthmd F2.*comm (implies (and (F2.elt x) (F2.elt y)) (equal (F2.* x y) (F2.* y x))))
; Associativity:
(defthmd F2.+assoc (implies (and (F2.elt x) (F2.elt y) (F2.elt z)) (equal (F2.+ x (F2.+ y z)) (F2.+ (F2.+ x y) z))))
(defthmd F2.*assoc (implies (and (F2.elt x) (F2.elt y) (F2.elt z)) (equal (F2.* x (F2.* y z)) (F2.* (F2.* x y) z))))
; Identity:
(defthm F2.elt-0 (F2.elt (F2.0)))
(defthm F2.elt-1 (F2.elt (F2.1)))
(defthm F2.0-not-1 (not (equal (F2.1) (F2.0))))
(defthm F2.0-id (implies (F2.elt x) (equal (F2.+ x (F2.0)) x)))
(defthm F2.1-id (implies (F2.elt x) (equal (F2.* x (F2.1)) x)))
; Inverse:
(defthm F2-closed-under- (implies (F2.elt x) (F2.elt (F2.- x))))
(defthm F2-closed-under/ (implies (and (F2.elt x) (not (equal x (F2.0)))) (F2.elt (F2./ x))))
(defthm F2.+inv (implies (F2.elt x) (equal (F2.+ x (F2.- x)) (F2.0))))
(defthm F2.*inv (implies (and (F2.elt x) (not (equal x (F2.0)))) (equal (F2.* x (F2./ x)) (F2.1))))
; Distributivity:
(defthm F2dist (implies (and (F2.elt x) (F2.elt y) (F2.elt z)) (equal (F2.* x (F2.+ y z)) (F2.+ (F2.* x y) (F2.* x z)))))
