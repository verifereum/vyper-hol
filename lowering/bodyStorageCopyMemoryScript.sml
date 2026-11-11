(* Actual storage/transient copy prefixes and their linear-memory footprints. *)
Theory bodyStorageCopyMemory
Ancestors
  exprSimStorageCopy storageDecodeMemory fragExecMem instMemFrontier
  context compileEnv emitHelper emitHelperProps fragExec exprLoweringProps
  venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map
Libs
  monadsyntax

Theorem body_storage_singleton_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  (!x. dst = Var x ==> x <> v) /\
  b + 32 < dimword (:256) /\ b + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id (if loc = LocStorage then SLOAD else TLOAD) [src] [v];
     mk_inst (id+1) MSTORE [dst; Var v] []] s
Proof
  strip_tac >> (rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> gvs[mk_inst_def]) >>
  gvs[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def] >>
  Cases_on `eval_operand src s` >> simp[] >>
  simp[run_inst_seq_mem_ok_last, GSYM mk_inst_def, below_frontier_MSTORE] >>
  Cases_on `dst` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[])
QED

Theorem body_storage_iteration_mem_ok:
  (loc = LocStorage \/ loc = LocTransient) /\
  eval_operand dst s = SOME (n2w b : bytes32) /\
  eval_operand (Var cv) s = SOME (n2w k) /\
  ALL_DISTINCT [cv; sv; vv; mv; dv; nv] /\
  (!x. src = Var x \/ dst = Var x ==>
       ~MEM x [cv; sv; vv; mv; dv; nv]) /\
  b + 32*(k+1) < dimword (:256) /\
  b + 32*(k+1) <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok
    [mk_inst id ADD [src; Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+3) ADD [dst; Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv; Var vv] [];
     mk_inst (id+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]] s
Proof
  strip_tac >> (
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  Cases_on `eval_operand src s`
  >- simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  `step_inst_base (mk_inst id ADD [src; Var cv] [sv]) s =
     OK (update_var sv (x + n2w k) s)` by (irule step_ADD >> simp[]) >>
  simp[] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def,
       eval_operand_update_var] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok _ s2` >>
  `eval_operand dst s2 = SOME (n2w b) /\
   eval_operand (Var cv) s2 = SOME (n2w k) /\
   s2.vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `dst` >>
     gvs[Abbr `s2`, ALL_DISTINCT, eval_operand_def,
         lookup_var_update_var, update_var_def]) >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst (id+2) MUL [Var cv; Lit 32w] [mv]) s2 =
     OK (update_var mv (n2w k * 32w) s2)` by
    (irule step_MUL >> simp[eval_operand_lit]) >>
  simp[] >>
  `eval_operand dst (update_var mv (n2w k * 32w) s2) = SOME (n2w b)` by
    (Cases_on `dst` >> gvs[eval_operand_def, lookup_var_update_var]) >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst (id+3) ADD [dst; Var mv] [dv])
      (update_var mv (n2w k * 32w) s2) =
     OK (update_var dv (n2w b + n2w k * 32w)
           (update_var mv (n2w k * 32w) s2))` by
    (irule step_ADD >> simp[eval_operand_update_var]) >>
  simp[] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (simp[below_frontier_MSTORE, eval_operand_update_var, update_var_def] >>
      `b + k * 32 < dimword (:256)` by decide_tac >>
      simp[word_mul_n2w, word_add_n2w, w2n_n2w] >>
      decide_tac) >>
  Cases_on `step_inst_base (mk_inst (id+4) MSTORE [Var dv; Var vv] [])
    (update_var dv (n2w b + n2w k * 32w)
      (update_var mv (n2w k * 32w) s2))` >> simp[] >>
  pure_once_rewrite_tac[run_inst_seq_mem_ok_cons] >> conj_tac
  >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  Cases_on `step_inst_base (mk_inst (id+5) ADD [Var cv; Lit 1w] [nv]) v` >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def])
QED

(* Resolve the shared execution interface here, without duplicating it. *)
val () = (List.app (fn _ => ())
  [storage_copy_source_run_effect, storage_copy_destination_run_effect,
   storage_copy_increment_run_effect, storage_copy_body_run,
   storage_copy_body_run_effect];
  print "BODY_STORAGE_COPY_EXECUTION_EXPORTS OK\n");

