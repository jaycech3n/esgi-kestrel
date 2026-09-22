(ld "list-defuns.lisp")

; Should we use the prime field stuff instead?

(defun map- (xs)
  (if (consp xs)
      (cons (- (first xs)) (map- (rest xs)))
      xs))