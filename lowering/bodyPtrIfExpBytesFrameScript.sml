Theory bodyPtrIfExpBytesFrame
Ancestors bodyPtrDefs appendStorageGhostPtr exprSimDefs compileEnv
  valueEncoding venomState ptrDiscipline finite_map fragGasSeqPtr venomInst
  venomExecSemantics fragExec exprLoweringProps context compileEnv emitHelper

Theorem bytes_writer_stor_taint_ok:
  stor_taint_ok cx tn s /\
  sf.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm ==>
  stor_taint_ok cx tnf sf
Proof
  simp[stor_taint_ok_def]
QED

Theorem bytes_writer_ghost_kept:
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==>
      off+sz <= p \/ p+len <= off) ==> off+sz <= b \/ b+n <= off) /\
  (!name p len. local_region ce es.scopes s0 name p len ==>
    p+len <= b \/ b+n <= p) ==>
  ghost_kept ce es sa G0 tn0 s0 Gf tnf
Proof
  rewrite_tac[ghost_kept_def] >> strip_tac >> conj_tac
  >- metis_tac[] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  `~(b <= i /\ i < b+n)` by (res_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem bytes_writer_return_buf:
  return_buf_ptr d ce G tn s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x. not_fresh_at sc x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
    lookup_var x sf = lookup_var x s) ==>
  return_buf_ptr d ce Gf tnf sf
Proof
  strip_tac >> Cases_on `d` >> simp[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def] >>
  metis_tac[ptr_covers_old_transport]
QED

Theorem bytes_writer_ghost_inv:
  ghost_inv d ce cx es G tn s /\
  (!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x. not_fresh_at sc x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
    lookup_var x sf = lookup_var x s) /\
  (!name entry p sz w. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + type_memory_size entry.type <= b \/ b+n <= w2n w)) /\
  (!ft fv p. val_wf ft fv /\ (p+type_memory_size ft <= b \/ b+n <= p) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory ft fv p m) /\
  stor_taint_ok cx tnf sf ==>
  ghost_inv d ce cx es Gf tnf sf
Proof
  strip_tac >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sc p` by metis_tac[] >>
      `ptr_covers G tn p s sz /\
       !w m. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
         val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
      conj_tac
      >- (irule ptr_covers_old_transport >> goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >> simp[]) >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\
       (w2n w + type_memory_size entry.type <= b \/ b+n <= w2n w)` by metis_tac[] >>
      qpat_x_assum `!ft fv p. _` irule >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule bytes_writer_return_buf >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem inst_seq_ptr_immutable_frame:
  !insts D lo ctx fn PG G tn s Gf tnf.
  EVERY (\i. i.inst_opcode <> ISTORE) insts /\
  inst_seq_ptr D lo ctx fn PG G tn insts s Gf tnf ==>
  tnf.t_imm = tn.t_imm
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum drule >>
  simp[step_taint_def, imm_taint_def]
QED

Theorem bytes_writer_step_ambient:
  (i.inst_opcode = MLOAD \/ i.inst_opcode = ADD \/
   i.inst_opcode = AND \/ i.inst_opcode = MCOPY) /\
  step_inst_base i s = OK u ==>
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def] >>
  gvs[exec_read1_def, exec_pure2_def, AllCaseEqs(), update_var_def,
      mcopy_def, write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
  strip_tac >> gvs[]
QED

Theorem bytes_writer_seq_ambient:
  !insts s sf.
  EVERY (\i. i.inst_opcode = MLOAD \/ i.inst_opcode = ADD \/
    i.inst_opcode = AND \/ i.inst_opcode = MCOPY) insts /\
  run_inst_seq insts s = OK sf ==>
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient
Proof
  Induct >> simp[run_inst_seq_def] >> rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_at (Pat `step_inst_base _ _ = _`) bytes_writer_step_ambient >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem bytes_writer_ambient_effects:
  compile_store_bytestring src dst sa = ((),sb) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  run_inst_seq (emitted_insts sa sb) s = OK sf ==>
  tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
  sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode = MLOAD \/ i.inst_opcode = ADD \/
     i.inst_opcode = AND \/ i.inst_opcode = MCOPY) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
     simp[compile_store_bytestring_def, compile_bytestring_copy_len_def,
          comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, listTheory.DROP_APPEND1] >> simp[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sa sb)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[]) >>
  conj_tac >- (drule_all inst_seq_ptr_immutable_frame >> simp[]) >>
  drule_all bytes_writer_seq_ambient >> simp[]
QED
