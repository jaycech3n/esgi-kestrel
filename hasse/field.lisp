; Abstract ambient algebraic closure, its finite fixed field, and Frobenius.

(in-package "ACL2")

(encapsulate
 (((fe-p *) => *)
  ((fq-elt-p *) => *)
  ((fzero) => *)
  ((fadd * *) => *)
  ((fmul * *) => *)
  ((frob *) => *))

 (local (defun fe-p (x) (equal x nil)))
 (local (defun fq-elt-p (x) (equal x nil)))
 (local (defun fzero () nil))
 (local (defun fadd (x y) (declare (ignore x y)) nil))
 (local (defun fmul (x y) (declare (ignore x y)) nil))
 (local (defun frob (x) (declare (ignore x)) nil))

 (defthm fq-elements-are-ambient-elements
   (implies (fq-elt-p x) (fe-p x)))

 (defthm fzero-is-an-ambient-element
   (fe-p (fzero)))

 (defthm fadd-closed
   (implies (and (fe-p x) (fe-p y)) (fe-p (fadd x y))))

 (defthm fmul-closed
   (implies (and (fe-p x) (fe-p y)) (fe-p (fmul x y))))

 (defthm frob-closed
   (implies (fe-p x) (fe-p (frob x))))

 (defthm frob-of-add
   (implies (and (fe-p x) (fe-p y))
            (equal (frob (fadd x y))
                   (fadd (frob x) (frob y)))))

 (defthm frob-of-mul
   (implies (and (fe-p x) (fe-p y))
            (equal (frob (fmul x y))
                   (fmul (frob x) (frob y)))))

 (defthm frob-fixes-fq-elements
   (implies (fq-elt-p x) (equal (frob x) x)))

 (defthm frob-fixed-elements-are-fq-elements
   (implies (and (fe-p x) (equal (frob x) x))
            (fq-elt-p x))))

(defun fsquare (x) (fmul x x))
(defun fcube (x) (fmul (fmul x x) x))
