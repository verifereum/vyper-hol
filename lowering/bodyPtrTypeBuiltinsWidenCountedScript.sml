Theory bodyPtrTypeBuiltinsWidenCounted
Ancestors
  bodyPtrTypeBuiltinsWidenCopy bodyPtrTypeBuiltinsWidenCopyShape
  bodyPtrTypeBuiltinsCopyCounted fragGasSeqPtr ghostPcTransportPtr
  bodyPtrDefs exprLoweringProps context emitHelperProps rich_list
  venomState venomInst loweringHalt exprSimPtrLiteralBuffer

Theorem widen_copy_straight_code:
  compile_bytestring_widen_copy capacity src n sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule_all widen_copy_code_split >> strip_tac >>
  qpat_x_assum `emitted_insts sa sb = _` (fn h => rewrite_tac[h]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule copy_memory_emitted_shape >> disch_tac >>
  Cases_on `n = 0` >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem widen_copy_counted_certificate:
  compile_bytestring_widen_copy capacity (Var src) n sa = (op,sb) /\
  fn_has_code sa sb fn /\ run_inst_seq (emitted_insts sa sb) s0 = OK t /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\ n <= capacity /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  expr_val_at cenv cx tsrc slo sa es v (Var src) s0 /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ ~is_word_type tsrc /\
  val_wf tv v /\ val_footprint tv v <= n /\ lookup_var src s0 = SOME a /\
  ptr_covers G0 tn0 src s0 n /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==> val_in_memory tv v (w2n a) m) /\
  ~s0.vs_halted /\ lookup_block s0.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s0.vs_inst_idx bb.bb_instructions) ==>
  ?dst b G th. op = Var dst /\
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G th
      (OK (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
    lookup_var dst (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) = SOME b /\
    ptr_covers G th dst (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) capacity /\
    ghost_inv d cenv cx es G th (t with vs_inst_idx := s0.vs_inst_idx + LENGTH (emitted_insts sa sb)) /\
    ghost_kept cenv es sa G0 tn0 s0 G th /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> drule_all widen_copy_checked_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all widen_copy_straight_code >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> strip_tac >>
  qexistsl_tac [`dst`,`b`,`G`,`th`] >> simp[lookup_var_def] >>
  conj_tac >- metis_tac[listTheory.LENGTH, arithmeticTheory.ADD_COMM] >>
  conj_tac >- fs[lookup_var_def] >>
  mp_tac (Q.INST [`tn` |-> `th`, `gs` |-> `es.gas_obs`,
    `s` |-> `t`, `idx` |-> `LENGTH (emitted_insts sa sb) + s0.vs_inst_idx`]
    literal_ptr_ghost_inv_normalize) >> simp[]
QED
