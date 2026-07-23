; This is the base of the book.
(ld "package.lsp")

; Prelude is just utility stuff
(ld "prelude.lisp")

; Mathematical content
(in-package "HASSE-THM")
(ld "polynomials.lisp")
(ld "F2.lisp")
(ld "finite-fields.lisp")
