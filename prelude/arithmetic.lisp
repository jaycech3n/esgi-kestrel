(include-book "arithmetic-5/top" :dir :system)

; I can't believe I have to define this to do natural number induction.
(defun induct-nat (n)
  (if (posp n) (induct-nat (1- n)) nil))