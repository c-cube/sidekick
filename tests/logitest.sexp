
(prover
  (name sidekick-dev)
  (cmd "$cur_dir/../sidekick --no-check --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(task
  (name sidekick-smt-all)
  (action
    (run_provers
      (provers sidekick-dev z3)
      (timeout 10)
      (dirs $HOME/workspace/smtlib))))

