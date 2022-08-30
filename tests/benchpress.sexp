
(prover
  (name sidekick-dev)
  (cmd "$cur_dir/../sidekick --no-check --time $timeout $file")
  (unsat "^unsat")
  (sat "^sat")
  (unknown "^(timeout|unknown)")
  (version "git:."))

(proof_checker
  (name quip)
  (cmd "quip check --color=false $proof_file --problem=$file")
  (valid "^OK$")
  (invalid "^FAIL$"))

(prover
  (name sidekick-dev-p)
  (inherits sidekick-dev)
  (cmd "$cur_dir/../sidekick --no-check --time $timeout $file -o $proof_file")
  (proof_ext ".quip.gz")
  (proof_checker quip)
  (produces_proof true))

(dir
  (path $cur_dir)
  (pattern ".*.(smt2|cnf)$")
  (expect (try (run smtlib-read-status) (run z3) (const unknown))))

(task
  (name sidekick-smt-quick)
  (action
    (run_provers
      (provers (sidekick-dev z3))
      (timeout 10)
      (dirs ($cur_dir/sat $cur_dir/unsat $cur_dir/pigeon)))))

; only unsat SMT problems
(task
  (name sidekick-smt-quick-proofs)
  (action
    (run_provers
      (provers (sidekick-dev sidekick-dev-p z3))
      (timeout 10)
      (pattern ".*.smt2$")
      (dirs ($cur_dir/unsat)))))

(task
  (name sidekick-smt-local)
  (action
    (run_provers
      (provers (sidekick-dev z3))
      (timeout 10)
      (dirs ($cur_dir/)))))

(task
  (name sidekick-smt-nodir)
  (action
    (run_provers
      (provers (sidekick-dev z3))
      (timeout 10)
      (dirs ()))))

(task
  (name sidekick-smt-all)
  (action
    (run_provers
      (provers (sidekick-dev z3))
      (timeout 10)
      (dirs ($HOME/workspace/smtlib)))))

(set-options (progress true))

