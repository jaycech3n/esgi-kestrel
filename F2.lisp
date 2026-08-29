;;; The finite field of order 2

(in-package "HASSE-THM")

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
