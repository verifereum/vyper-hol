(* The runtime DLOAD stage of the actual immutable-copy compiler. *)
Theory bodyPtrMakeArrayImmutableOne
Ancestors
  bodyPtrMakeArrayOffsetFrame bodyPtrMakeArrayImmutableStep
  bodyPtrMakeArrayCopyStep bodyPtrMakeArrayEmission
  exprSimCopy immutableCopyExecution context compileEnv emitHelper emitHelperProps
  exprLoweringProps fragGasSeqPtr ptrDiscipline bodyPtrDefs venomState
  venomExecSemantics venomInst finite_map

Theorem immutable_runtime_load_raw_frame:
  compile_imm_load_word F imm op sa = (r,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ allocas_from 0 s /\ ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand r u = SOME (immutable_copy_read F a s) /\
    copy_old_operand sb r /\ op_taint tnf r = {} /\
    u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
    u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    (!p. not_fresh_at sa p ==>
      lookup_var p u = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all copy_runtime_load >> strip_tac >>
  gvs[compile_imm_load_word_def] >>
  drule emitted_insts_emit_op >> strip_tac >> rename1 `r = Var out` >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[] >> metis_tac[emit_op_old_var_separate, arithmeticTheory.LESS_EQ_REFL]) >>
  `s' = update_var out (immutable_copy_read F a s) s` by
    gvs[copy_runtime_frame_def, run_inst_seq_def, Once step_inst_base_def,
        mk_inst_def, exec_read1_def, immutable_copy_read_def] >>
  qexistsl_tac [`s'`,
    `step_prov PG G (mk_inst sa.cs_next_id DLOAD [op] [out]) s'`,
    `step_taint (mk_inst sa.cs_next_id DLOAD [op] [out]) s s' tn`] >>
  simp[] >>
  conj_tac
  >- (simp[inst_seq_ptr_def, ptr_inst_ok_external_load,
           Once step_inst_base_def, mk_inst_def, exec_read1_def,
           immutable_copy_read_def]) >>
  conj_tac
  >- (gvs[] >> simp[op_taint_def, step_taint_def, set_var_taint_def,
                    out_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
  gvs[] >>
  simp[external_load_ghost_frame, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt strip_tac >> Cases_on `out = p` >> gvs[] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem immutable_runtime_store_raw_frame:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  copy_old_operand sa (Var dst) /\ copy_old_operand sa value /\
  lookup_var dst s = SOME b /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn dst s 32 /\
  ~ctx_has_dalloca ctx ==>
  ?u Gf tnf.
    copy_runtime_frame sa s sb u /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    u = mstore (w2n b) w s /\ Gf = G /\ tnf.t_var = tn.t_var /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    u.vs_data_section = s.vs_data_section /\
    u.vs_immutables = s.vs_immutables /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
    tnf.t_imm = tn.t_imm /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient
Proof
  strip_tac >>
  `eval_operand (Var dst) s = SOME b` by simp[eval_operand_def] >>
  drule_all copy_runtime_store >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qexistsl_tac [`mstore (w2n b) w s`,
    `step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
      (mstore (w2n b) w s)`,
    `step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s
      (mstore (w2n b) w s) tn`] >>
  simp[] >>
  conj_tac
  >- simp[inst_seq_ptr_def, ptr_inst_ok_mstore_raw,
          Once step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def] >>
  simp[mstore_raw_ghost_frame] >>
  simp[mstore_def]
QED

Theorem immutable_destination_raw_window:
  compile_lit_byte_offset (Var root) off sa = (r,sb) /\
  copy_runtime_frame sa s sb u /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
  ptr_covers G tn root s m /\ lookup_var root s = SOME b /\
  FLOOKUP G root = SOME (blo,cap) /\ blo + cap <= dimword(:256) /\
  off + 32 * SUC n <= m ==>
  ?p. r = Var p /\ ptr_covers Gf tnf p u 32
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def,
           copy_runtime_frame_def, emitted_insts_def, run_inst_seq_def,
           inst_seq_ptr_def] >>
      irule immutable_offset_zero_window >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[compile_lit_byte_offset_def] >>
  drule emitted_insts_emit_op >> strip_tac >> rename1 `r = Var out` >>
  `u = update_var out (b+n2w off) s` by
    gvs[copy_runtime_frame_def, run_inst_seq_def, Once step_inst_base_def,
        mk_inst_def, exec_pure2_def, eval_operand_def] >>
  gvs[inst_seq_ptr_def, Once step_inst_base_def, mk_inst_def,
      exec_pure2_def, eval_operand_def] >>
  drule_all immutable_offset_destination_window >>
  simp[ptr_covers_def, mk_inst_def, lookup_var_def, update_var_def] >>
  metis_tac[]
QED
