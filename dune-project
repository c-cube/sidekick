(lang dune 2.0)

(generate_opam_files true)

(license Apache)

(authors "Simon Cruanes" "Guillaume Bury")

(maintainers "simon.cruanes.2007@m4x.org")

(version dev)

(homepage "https://github.com/c-cube/sidekick")

(source
 (github c-cube/sidekick))

(bug_reports "https://github.com/c-cube/sidekick/issues/")

(using menhir 1.0)

(package
 (name sidekick)
 (synopsis "SMT solver based on msat and CDCL(T) (core library)")
 (depends
  (containers
   (and
    (>= 3.6)
    (< 4.0)))
  (iter
   (>= 1.0))
  (zarith :with-test)
  (alcotest :with-test)
  (odoc :with-doc))
 (depopts
  (mtime
   (>= 2.0)) ; for profiling stuff
  memtrace ; memory profiling
  zarith ; for arith
  )
 (tags
  ("sat" "smt"))
 (conflicts
  (zarith
   (< 1.8))
  ; need infix ops
  ))

(package
 (name sidekick-base)
 (synopsis "Concrete terms and theories for sidekick")
 (depends
  zarith
  (smtlib-utils
   (and
    (>= "0.1")
    (< "0.5")))
  (sidekick
   (= :version))
  (qcheck
   (and
    :with-test
    (>= 0.16)))
  (mdx :with-test)
  (odoc :with-doc)
  menhir))

(package
 (name sidekick-bin)
 (synopsis "SMT solver based on msat and CDCL(T) (standalone binary)")
 (depends
  zarith
  (sidekick
   (= :version))
  (sidekick-base
   (= :version))
  menhir))
