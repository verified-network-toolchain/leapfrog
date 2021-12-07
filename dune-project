(lang dune 2.7)
(using coq 0.2)
(name leapfrog)

(package
 (name leapfrog)
 (depends
  mirrorsolve
  bignum
  (coq :build)
  (coq-equations :build))
  (synopsis "Poulet4: Petr4 in Coq"))
