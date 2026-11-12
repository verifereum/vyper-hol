(* Endpoint framing for the ghosts of the actual checked BLOCKHASH prefix. *)
Theory bodyPtrEnvBuiltinsBlockHashFrame
Ancestors bodyPtrEnvBuiltinsBlockHashRun bodyPtrEnvBuiltinsSequenceFrame
  bodyPtrEnvBuiltinsEdges builtinProps emitHelperProps decoderGhostFramePtr
  ptrDiscipline ptrSafeRun fragGasSeqPtr venomExecSemantics venomInst venomState
  compileEnv codegenRel contextCodegenRel finite_map pred_set list

Theorem blockhash_step_state_frame[local]:
  MEM i.inst_opcode [SUB; SLT; LT; ISZERO; ASSERT; NUMBER; BLOCKHASH] /\
  step_inst_base i s = OK t ==>
  t = s with vs_vars := t.vs_vars
Proof
  strip_tac >> Cases_on `i.inst_opcode = NUMBER \/ i.inst_opcode = BLOCKHASH`
  >- (drule_all step_hash_read_frame >> simp[]) >>
  irule (cj 1 step_pure_opcode_frame) >> qexists_tac `i` >> simp[] >> gvs[]
QED

Theorem blockhash_step_taint_frame[local]:
  MEM i.inst_opcode [SUB; SLT; LT; ISZERO; ASSERT; NUMBER; BLOCKHASH] /\
  step_inst_base i s = OK t ==>
  (step_taint i s t tn).t_mem = tn.t_mem /\
  (step_taint i s t tn).t_stor = tn.t_stor /\
  (step_taint i s t tn).t_trans = tn.t_trans /\
  (step_taint i s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> drule_all blockhash_step_state_frame >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `t = _` (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_fmp)`) >>
     simp[]) >>
  conj_tac
  >- (irule step_taint_no_memory_effect >> simp[] >>
      gvs[MEM] >> simp[written_taint_def, source_memory_write_ranges_def] >>
      Cases_on `i.inst_operands` >> simp[] >>
      Cases_on `t'` >> simp[] >> Cases_on `t''` >> simp[] >>
      Cases_on `t'` >> simp[]) >>
  irule step_taint_nonmemory_frame >> gvs[MEM]
QED

Theorem blockhash_checked_taint_frame:
  compile_blockhash arg sa = (op,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> drule compile_blockhash_outputs >> strip_tac >>
  irule (BETA_RULE (Q.INST [`R` |-> `\H q. q.t_mem = tn.t_mem /\
    q.t_stor = tn.t_stor /\ q.t_trans = tn.t_trans /\ q.t_imm = tn.t_imm`]
    (SPEC_ALL inst_seq_ptr_invariant))) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `MEM i.inst_opcode [SUB; SLT; LT; ISZERO; ASSERT; NUMBER; BLOCKHASH]` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all blockhash_step_taint_frame >> simp[]
QED

Theorem blockhash_checked_register_frame:
  compile_blockhash arg sa = (op,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  not_fresh_at sa x ==>
  FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)
Proof
  strip_tac >> drule compile_blockhash_outputs >> strip_tac >>
  irule (BETA_RULE (Q.INST [`R` |-> `\H q. FLOOKUP H x = FLOOKUP G x /\
    op_taint q (Var x) = op_taint tn (Var x)`] (SPEC_ALL inst_seq_ptr_invariant))) >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `~MEM x i.inst_outputs` by (fs[EVERY_MEM] >> metis_tac[]) >>
  simp[step_prov_other_output, step_taint_other_output]
QED

Theorem blockhash_checked_ghost_frame:
  compile_blockhash arg sa = (op,sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' ==>
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> drule_all blockhash_checked_register_frame >> simp[]) >>
  drule_all blockhash_checked_taint_frame >> simp[]
QED
