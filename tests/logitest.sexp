
(prover
  (name sidekick-dev)
  (cmd "${cur_dir}/../sidekick --no-check --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(dir
  (path $cur_dir)
  (pattern ".*.(smt2|cnf)")
  (expect (try (run smtlib-read-status) (run z3))))

(task
  (name sidekick-local-test)
  (action
    (run_provers
      (provers sidekick)
      (timeout 10)
      (dirs tests))))

