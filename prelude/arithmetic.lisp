(include-book "arithmetic-5/top" :dir :system)

; I can't believe I have to define this to do natural number induction.
(defun nat-ind (n)
  (if (posp n) (nat-ind (1- n)) nil))