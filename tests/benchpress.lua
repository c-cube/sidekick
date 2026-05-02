-- benchpress configuration file
-- Type annotations for LuaLS / lua-language-server (EmmyLua format).
-- Delete this block if you do not use a Lua LSP.

---@class BP.ProverParams
---@field name string                    # prover identifier
---@field binary? string                 # binary path/name (default: same as name, looked up in $PATH)
---@field cmd string                     # command template, e.g. "$binary $file"
---@field sat? string                    # Perl regex matching SAT output
---@field unsat? string                  # Perl regex matching UNSAT output
---@field unknown? string                # Perl regex matching unknown output
---@field timeout? string                # Perl regex matching timeout output
---@field memory? string                 # Perl regex matching OOM output
---@field static_labels? string[]        # labels attached to every result
---@field parse? fun(stdout:string, stderr:string):{res:string,labels?:table<string,boolean>}|nil  # custom result parser
---@field produces_proof? boolean        # whether the prover emits proof files
---@field proof_ext? string              # file extension for proof files (e.g. "proof")
---@field proof_checker? string          # name of prover used to check proofs
---@field binary_deps? string[]          # extra required binaries

---@class BP.DirParams
---@field path string                    # directory path (supports $cur_dir)
---@field pattern? string                # Perl regex to match filenames
---@field expect? "comment"|"unknown"|"sat"|"unsat"|"error"|"timeout"  # default expected result
---@field name? string                   # logical name for this directory

---@class BP.RunProversParams
---@field provers string[]               # prover names to run
---@field dirs string[]                  # directory paths or names
---@field timeout? integer               # per-problem timeout in seconds
---@field memory? integer                # per-problem memory limit in MB
---@field j? integer                     # parallel jobs
---@field pattern? string                # override file-matching pattern

---@class BP.TaskParams
---@field name string                    # task identifier
---@field action any                     # result of run_provers / seq / run_cmd
---@field synopsis? string               # short description shown in listings

---@class BP
---@field prover fun(p:BP.ProverParams)             # register a prover definition
---@field dir fun(p:BP.DirParams)                   # register a problem directory
---@field run_provers fun(p:BP.RunProversParams):any # build a run-provers action
---@field seq fun(...):any                           # sequence several actions
---@field run_cmd fun(cmd:string):any               # build a shell-command action
---@field task fun(p:BP.TaskParams)                 # register a named task
---@field on fun(event:string, fn:function)         # register an event hook
---@field cur_dir string                            # directory of this config file (read-only)

---@type BP
benchpress = benchpress

-- ── Provers ───────────────────────────────────────────────────────────────────

benchpress.prover {
  name    = "my-prover",
  binary  = "my-prover", -- looked up in $PATH
  cmd     = "$binary $file",
  sat     = "^SAT",
  unsat   = "^UNSAT",
  unknown = "^UNKNOWN",
}

-- ── Problem directories ───────────────────────────────────────────────────────

benchpress.dir {
  path    = "$cur_dir/problems/",
  pattern = ".*\\.smt2",
}

-- ── Tasks ─────────────────────────────────────────────────────────────────────

benchpress.task {
  name   = "all",
  action = benchpress.run_provers {
    provers = { "my-prover" },
    dirs    = { "$cur_dir/problems/" },
    timeout = 30,
  },
}
benchpress.prover {
  name  = "z3",
  cmd   = "z3 $file",
  sat   = "^sat",
  unsat = "^unsat",
}

benchpress.prover {
  name    = "sidekick-dev",
  cmd     = "$cur_dir/../sidekick --no-check --time $timeout $file",
  unsat   = "^unsat",
  sat     = "^sat",
  unknown = "^(timeout|unknown)",
}

benchpress.prover {
  name           = "sidekick-dev-p",
  cmd            = "$cur_dir/../sidekick --no-check --time $timeout $file -o $proof_file",
  unsat          = "^unsat",
  sat            = "^sat",
  unknown        = "^(timeout|unknown)",
  produces_proof = true,
  proof_ext      = ".quip.gz",
  proof_checker  = "quip",
}

benchpress.prover {
  name  = "quip",
  cmd   = "quip check --color=false $proof_file --problem=$file",
  sat   = "^OK$",
  unsat = "^FAIL$",
}

benchpress.dir {
  path    = "$cur_dir/sat",
  pattern = ".*.(smt2|cnf)$",
  expect  = "sat",
}

benchpress.dir {
  path    = "$cur_dir/unsat",
  pattern = ".*.(smt2|cnf)$",
  expect  = "unsat",
}

benchpress.dir {
  path    = "$cur_dir/pigeon",
  pattern = ".*.(smt2|cnf)$",
  expect  = "unsat",
}

benchpress.task {
  name   = "sidekick-smt-quick",
  action = benchpress.run_provers {
    provers = { "sidekick-dev", "z3" },
    timeout = 10,
    dirs    = { "$cur_dir/sat", "$cur_dir/unsat", "$cur_dir/pigeon" },
  },
}

benchpress.task {
  name   = "sidekick-smt-quick-proofs",
  action = benchpress.run_provers {
    provers = { "sidekick-dev", "sidekick-dev-p", "z3" },
    timeout = 10,
    pattern = ".*.smt2$",
    dirs    = { "$cur_dir/unsat" },
  },
}

benchpress.task {
  name   = "sidekick-smt-local",
  action = benchpress.run_provers {
    provers = { "sidekick-dev", "z3" },
    timeout = 10,
    dirs    = { "$cur_dir/" },
  },
}

benchpress.task {
  name   = "sidekick-smt-nodir",
  action = benchpress.run_provers {
    provers = { "sidekick-dev", "z3" },
    timeout = 10,
    dirs    = {},
  },
}
