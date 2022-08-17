(lang dune 2.9)
(using coq 0.2)
(name leapfrog)

(generate_opam_files true)

(package
 (name leapfrog)
 (version 0.1.0)
 (synopsis     "Leapfrog: Certified Equivalence for Protocol Parsers")
 (maintainers  "me@ryandoeng.es" "tobias@kap.pe" "jsarracino@cs.cornell.edu")
 (authors      "Ryan Doenges" "Tobias Kappé" "John Sarracino")
 (homepage     "https://github.com/verified-network-toolchain/leapfrog")
 (bug_reports  "https://github.com/verified-network-toolchain/leapfrog")
 (license      "Apache 2.0")
 (depends
   mirrorsolve
   (coq (and :build (= "8.15.2")))
   (coq-equations (and :build (= "1.3+8.15"))))
)
