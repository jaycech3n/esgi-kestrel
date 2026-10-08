(ld "prelude/arithmetic.lisp")
(ld "prelude/lists.lisp")
(ld "prelude/list-thms.lisp")

(defmacro section (&rest content)
  (cons 'encapsulate (cons 'nil content)))