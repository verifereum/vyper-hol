Theory bodyPtrPrecompileBuiltinsPrefixFrames
Ancestors bodyPtrPrecompileBuiltinsCompletePrefixes decoderGhostFramePtr
          fragGasSeqPtr ptrDiscipline bodyPtrDefs pred_set list
          venomExecSemantics venomState exprLoweringProps

(* The second store footprint may be empty (ECAdd and ECMul), or the
   recovery output-zero range.  Keep allocation growth explicit. *)
Theorem prefix_taint_bound:
  final = (((initial UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 ==>
  final SUBSET (initial UNION alloc1 UNION alloc2)
Proof
  SET_TAC[]
QED

Theorem prefix_taint_exterior:
  final = (((initial UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 /\
  i NOTIN (alloc1 UNION alloc2 UNION writes1 UNION writes2) ==>
  (i IN final <=> i IN initial)
Proof
  SET_TAC[]
QED

Theorem prefix_taint_below_frontier:
  final = (((initial UNION alloc1) DIFF writes1) UNION alloc2) DIFF writes2 /\
  (!j. j IN (alloc1 UNION alloc2 UNION writes1 UNION writes2) ==> frontier <= j) /\
  i < frontier ==>
  (i IN final <=> i IN initial)
Proof
  strip_tac >> irule prefix_taint_exterior >>
  qexistsl [`alloc1`, `alloc2`, `writes1`, `writes2`] >>
  metis_tac[IN_UNION, arithmeticTheory.NOT_LESS_EQUAL]
QED

Theorem inst_seq_ptr_nonmemory_frame:
  !code s G tn G' tn'.
    EVERY (\i. i.inst_opcode <> CALL /\ i.inst_opcode <> SSTORE /\
      i.inst_opcode <> TSTORE /\ i.inst_opcode <> ISTORE) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' ==>
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[AllCaseEqs()] >>
  drule_all step_taint_nonmemory_frame >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem staging_step_runtime_fields:
  (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = ADD \/
   inst.inst_opcode = MLOAD \/ inst.inst_opcode = MSTORE) /\
  step_inst_base inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >> gvs[] >> gvs[step_inst_base_def] >>
  gvs[exec_alloca_def, exec_pure2_def, exec_read1_def, exec_write2_def,
    AllCaseEqs()] >>
  gvs[update_var_def, mstore_def]
QED

Theorem staging_sequence_runtime_fields:
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) code /\
  run_inst_seq code s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  strip_tac >>
  ` (t.vs_call_ctx,t.vs_accounts,t.vs_transient) =
    (s.vs_call_ctx,s.vs_accounts,s.vs_transient)` suffices_by simp[] >>
  irule (BETA_RULE (ISPEC ``\u:venom_state. (u.vs_call_ctx,u.vs_accounts,u.vs_transient)``
    run_inst_seq_preserves_field)) >> qexists_tac `code` >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
   i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE` by metis_tac[] >>
  metis_tac[staging_step_runtime_fields]
QED

Theorem staging_alloca_footprint_above_frontier:
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK t /\
  i IN new_site_bytes s t ==>
  s.vs_alloca_next <= i
Proof
  strip_tac >> gvs[step_inst_base_def] >>
  gvs[exec_alloca_def, AllCaseEqs()] >>
  gvs[new_site_bytes_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      finite_mapTheory.FLOOKUP_DEF] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[]
QED
