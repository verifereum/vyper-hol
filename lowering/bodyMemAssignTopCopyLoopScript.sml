(* Linear-memory checks for the actual memory-to-storage copy body. *)
Theory bodyMemAssignTopCopyLoop
Ancestors
  bodyMemAssignTopCopyFacts
  fragExecMem instMemFrontier context compileEnv emitHelper emitHelperProps
  fragExec exprLoweringProps venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem body_mem_storage_singleton_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME b /\
  w2n b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id MLOAD [src] [v];
     mk_inst (id+1) (if loc = LocStorage then SSTORE else TSTORE)
       [dst; Var v] []] s
Proof
  strip_tac >>
  simp[run_inst_seq_mem_ok_cons, below_frontier_MLOAD] >>
  Cases_on `step_inst_base (mk_inst id MLOAD [src] [v]) s` >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def] >>
  Cases_on `loc = LocStorage` >> simp[]
QED

Theorem body_mem_storage_iteration_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME b /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv; mv; sv; vv; dv; nv] /\
  (!x. src = Var x ==> ~MEM x [cv; mv; sv; vv; dv; nv]) /\
  w2n b + 32*(k+1) < dimword (:256) /\
  w2n b + 32*(k+1) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s
Proof
  strip_tac >>
  `!t. run_inst_seq_mem_ok
    [mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] t` by
    (gen_tac >> irule run_inst_seq_mem_ok_every >> simp[] >>
     rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >>
     simp[mk_inst_def]) >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s =
     OK (update_var mv (n2w k * 32w) s)` by
    (irule step_MUL >> simp[eval_operand_lit]) >>
  `inst_mem_below_frontier (mk_inst id MUL [Var cv; Lit 32w] [mv]) s` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s1` >>
  `eval_operand src s1 = SOME b /\
   eval_operand (Var mv) s1 = SOME (n2w k * 32w)` by
    (Cases_on `src` >>
     gvs[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (id+1) ADD [src; Var mv] [sv]) s1 =
     OK (update_var sv (b + n2w k * 32w) s1)` by
    (irule step_ADD >> simp[]) >>
  `inst_mem_below_frontier (mk_inst (id+1) ADD [src; Var mv] [sv]) s1` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s2` >>
  `w2n (b + n2w k * 32w) = w2n b + k*32` by
    (`b + n2w k * 32w = n2w (w2n b + k*32)` by
       simp[GSYM word_add_n2w, GSYM word_mul_n2w] >>
     asm_rewrite_tac[] >>
     `w2n b + k*32 < dimword (:256)` by decide_tac >>
     simp[w2n_n2w, LESS_MOD]) >>
  `inst_mem_below_frontier (mk_inst (id+2) MLOAD [Var sv] [vv]) s2` by
    (simp[below_frontier_MLOAD, Abbr `s2`, Abbr `s1`,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     decide_tac) >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  Cases_on `step_inst_base (mk_inst (id+2) MLOAD [Var sv] [vv]) s2` >>
  gvs[]
QED

Theorem body_mem_storage_iteration_mem_ok_modular:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand src s = SOME b /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv; mv; sv; vv; dv; nv] /\
  (!x. src = Var x ==> ~MEM x [cv; mv; sv; vv; dv; nv]) /\
  w2n b + 32*(k+1) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s
Proof
  strip_tac >>
  `!t. run_inst_seq_mem_ok
    [mk_inst (id+3) ADD [dst; Var cv] [dv];
     mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] t` by
    (gen_tac >> irule run_inst_seq_mem_ok_every >> simp[] >>
     rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >>
     simp[mk_inst_def]) >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) s =
     OK (update_var mv (n2w k * 32w) s)` by
    (irule step_MUL >> simp[eval_operand_lit]) >>
  `inst_mem_below_frontier (mk_inst id MUL [Var cv; Lit 32w] [mv]) s` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s1` >>
  `eval_operand src s1 = SOME b /\
   eval_operand (Var mv) s1 = SOME (n2w k * 32w)` by
    (Cases_on `src` >>
     gvs[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE]) >>
  `step_inst_base (mk_inst (id+1) ADD [src; Var mv] [sv]) s1 =
     OK (update_var sv (b + n2w k * 32w) s1)` by
    (irule step_ADD >> simp[]) >>
  `inst_mem_below_frontier (mk_inst (id+1) ADD [src; Var mv] [sv]) s1` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s2` >>
  `w2n (b + n2w k * 32w) + 32 <= s.vs_alloca_next` by
    (irule topcopy_index_bound >> qexists_tac `k+1` >> simp[]) >>
  `inst_mem_below_frontier (mk_inst (id+2) MLOAD [Var sv] [vv]) s2` by
    simp[below_frontier_MLOAD, Abbr `s2`, Abbr `s1`,
         eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  Cases_on `step_inst_base (mk_inst (id+2) MLOAD [Var sv] [vv]) s2` >>
  gvs[]
QED
