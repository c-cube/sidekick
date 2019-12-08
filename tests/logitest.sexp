
(prover
  (name sidekick-dev)
  (binary "./sidekick")
  (cmd "./sidekick --no-check --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(dir
  (path tests)
  (pattern ".*.(smt2|cnf)")
  (expect (run z3)))

(task
  (name sidekick-local-test)
  (action
    (run_provers
      (provers sidekick)
      (timeout 10)
      (dirs tests))))


