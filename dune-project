(lang dune 3.24)

(using menhir 3.0)

(name truss)

(generate_opam_files true)

(package
 (name truss)
 (synopsis "The stage0 compiler for the Truss programming language")
 (allow_empty)
 (depends
  (ocaml
   (>= 5.5))
  (dune
   (>= 3.24))
  (zarith
   (>= 1.14))
  (menhir
   (and
    :with-test
    (>= 20260209)))
  (ocamlformat
   (and
    :with-dev-setup
    (= 0.29.0)))))
