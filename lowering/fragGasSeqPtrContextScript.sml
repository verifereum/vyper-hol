(* Restore the actual context for straight-line copies whose instructions
   preserve the allocation map and both free-memory bounds. *)
Theory fragGasSeqPtrContext
Ancestors
  fragGasSeqPtr ptrSafeRun ptrDiscipline venomInstProofs1 venomMemProps
  venomExecSemantics venomState venomInst context list exprLoweringProps

Theorem ordinary_step_allocas_below_fmp[local]:
  step_inst_base i s = OK u /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
  i.inst_opcode <> DALLOCA ==>
  (allocas_below_fmp u <=> allocas_below_fmp s)
Proof
  strip_tac >>
  `i.inst_opcode <> ALLOCA` by
    (Cases_on `i.inst_opcode` >> fs[is_alloca_op_def]) >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >>
  drule_all step_inst_base_preserves_all >>
  simp[allocas_below_fmp_def]
QED

Theorem ptr_inst_ok_restore_ctx:
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  i.inst_opcode <> INVOKE /\
  ptr_inst_ok D lo fuel (ctx with ctx_functions := []) fn G tn i s ==>
  ptr_inst_ok D lo fuel ctx fn G tn i s
Proof
  simp[ptr_inst_ok_def, step_inst_non_invoke, ctx_has_dalloca_def]
QED

Theorem inst_seq_ptr_restore_ctx:
  !code s G tn G' tn'.
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
      i.inst_opcode <> DALLOCA) code /\
    inst_seq_ptr D lo (ctx with ctx_functions := []) fn PG G tn code s G' tn' ==>
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn'
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[ptr_inst_ok_def, step_inst_non_invoke, ctx_has_dalloca_def]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >>
  drule_all ordinary_step_allocas_below_fmp >> strip_tac >>
  fs[allocas_below_fmp_def] >> metis_tac[]
QED

Theorem run_inst_seq_allocas_below_fmp:
  !code s t.
    allocas_below_fmp s /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
      i.inst_opcode <> DALLOCA) code /\
    run_inst_seq code s = OK t ==>
    allocas_below_fmp t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  first_x_assum irule >> simp[] >> qexists_tac `u` >> simp[] >>
  metis_tac[ordinary_step_allocas_below_fmp]
QED
