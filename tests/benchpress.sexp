
(prover
  (name sidekick-dev)
  (cmd "$cur_dir/../sidekick --no-check --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(dir
  (path $cur_dir)
  (pattern ".*.(smt2|cnf)$")
  (expect (try (run smtlib-read-status) (run z3) (const unknown))))

(task
  (name sidekick-smt-quick)
  (action
    (run_provers
      (provers sidekick-dev z3)
      (timeout 10)
      (dirs $cur_dir/sat $cur_dir/unsat $cur_dir/pigeon))))

(task
  (name sidekick-smt-local)
  (action
    (run_provers
      (provers sidekick-dev z3)
      (timeout 10)
      (dirs $cur_dir/))))

(task
  (name sidekick-smt-nodir)
  (action
    (run_provers
      (provers sidekick-dev z3)
      (timeout 10)
      (dirs))))

(task
  (name sidekick-smt-all)
  (action
    (run_provers
      (provers sidekick-dev z3)
      (timeout 10)
      (dirs $HOME/workspace/smtlib))))

(set-options (progress true))

