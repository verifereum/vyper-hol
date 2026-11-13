Theory lowerDloadPtrPhase
Ancestors
  lowerDloadPtrRel lowerDloadPtrTaint lowerDloadPtrBoundary lowerDloadDefs ptrDiscipline
  venomExecSemantics venomState list finite_map words

(* Replay records successful proper prefixes only.  The boundary core relates
   the source to t0, not to the partially modified t.  Consumers additionally
   require phase < LENGTH emitted.  A terminal/revert result is a separate
   exit case of reachability induction, never a positive active phase. *)
Definition dload_prefix_match_def:
  (dload_prefix_match fuel C PG emitted 0 t0 H0 un0 t H un <=>
    t = t0 /\ H = H0 /\ un = un0) /\
  (dload_prefix_match fuel C PG emitted (SUC k) t0 H0 un0 t H un <=>
    k < LENGTH emitted /\
    ?u J vn v.
      dload_prefix_match fuel C PG emitted k t0 H0 un0 u J vn /\
      step_inst fuel C (EL k emitted) u = OK v /\
      t = v with vs_inst_idx := SUC u.vs_inst_idx /\
      H = step_prov PG J (EL k emitted) v /\
      un = step_taint (EL k emitted) u v vn)
End

Theorem dload_prefix_zero:
  dload_prefix_match fuel C PG emitted 0 t0 H0 un0 t H un <=>
  t = t0 /\ H = H0 /\ un = un0
Proof
  simp[dload_prefix_match_def]
QED

Theorem dload_prefix_extend:
  dload_prefix_match fuel C PG emitted k t0 H0 un0 u J vn /\
  k < LENGTH emitted /\ step_inst fuel C (EL k emitted) u = OK v ==>
  dload_prefix_match fuel C PG emitted (SUC k) t0 H0 un0
    (v with vs_inst_idx := SUC u.vs_inst_idx)
    (step_prov PG J (EL k emitted) v)
    (step_taint (EL k emitted) u v vn)
Proof
  strip_tac >> simp[Once dload_prefix_match_def] >> metis_tac[]
QED

Theorem dload_prefix_first:
  dload_prefix_match fuel C PG (inst::rest) 1 t0 H0 un0 t H un <=>
  ?v. step_inst fuel C inst t0 = OK v /\
      t = v with vs_inst_idx := SUC t0.vs_inst_idx /\
      H = step_prov PG H0 inst v /\ un = step_taint inst t0 v un0
Proof
  pure_rewrite_tac[arithmeticTheory.ONE, dload_prefix_match_def] >> simp[]
QED

Theorem dload_prefix_alloca_lookup:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
  inst.inst_outputs = [out] /\
  FLOOKUP t0.vs_allocas inst.inst_id = NONE /\
  dload_prefix_match fuel C PG (inst::rest) 1 t0 H0 un0 t H un ==>
  FLOOKUP t.vs_allocas inst.inst_id = SOME (t0.vs_alloca_next,32)
Proof
  simp[dload_prefix_first] >> rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE, dimword_def]
QED

Theorem dload_prefix_codecopy_clears:
  k < LENGTH emitted /\ EL k emitted = inst /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; size_op] /\
  eval_operand dst u = SOME b /\ eval_operand src u = SOME a /\
  eval_operand size_op u = SOME n /\ w2n n = 32 /\
  dload_prefix_match fuel C PG emitted k t0 H0 un0 u J vn /\
  step_inst fuel C inst u = OK v ==>
  dload_prefix_match fuel C PG emitted (SUC k) t0 H0 un0
    (v with vs_inst_idx := SUC u.vs_inst_idx)
    (step_prov PG J inst v) (step_taint inst u v vn) /\
  mem_word_taint (step_taint inst u v vn).t_mem (w2n b) = {}
Proof
  strip_tac >> conj_tac
  >- (simp[Once dload_prefix_match_def] >>
      qexistsl [`u`,`J`,`vn`,`v`] >> simp[]) >>
  simp[step_taint_def] >> irule codecopy_scratch_step_untainted >>
  gvs[step_inst_non_invoke] >> metis_tac[]
QED

Theorem dload_supply_phase_shape:
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\
  i.inst_outputs = [out] /\ lower_dload_inst_supply supply i = (xs,next) ==>
  LENGTH xs = 4 /\ (EL 0 xs).inst_opcode = ALLOCA /\
  (EL 0 xs).inst_operands = [Lit 32w] /\
  (?tmp. (EL 0 xs).inst_outputs = [tmp]) /\
  (EL 2 xs).inst_opcode = CODECOPY /\
  (?dst src. (EL 2 xs).inst_operands = [dst;src;Lit 32w])
Proof
  simp[lower_dload_inst_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem dloadbytes_supply_phase_shape:
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;src;sz] /\
  lower_dload_inst_supply supply i = (xs,next) ==>
  LENGTH xs = 2 /\ (EL 0 xs).inst_opcode = ADD /\
  (EL 1 xs).inst_opcode = CODECOPY /\
  (?codeptr. (EL 1 xs).inst_operands = [dst;codeptr;sz])
Proof
  simp[lower_dload_inst_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem dload_prefix_successor:
  dload_prefix_match fuel C PG emitted (SUC k) t0 H0 un0 t H un ==>
  k < LENGTH emitted /\
  ?u J vn v.
    dload_prefix_match fuel C PG emitted k t0 H0 un0 u J vn /\
    step_inst fuel C (EL k emitted) u = OK v /\
    t = v with vs_inst_idx := SUC u.vs_inst_idx /\
    H = step_prov PG J (EL k emitted) v /\
    un = step_taint (EL k emitted) u v vn
Proof
  simp[Once dload_prefix_match_def]
QED
