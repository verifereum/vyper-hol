(* Bounded straight-line runtime immutable-copy composition. *)
Theory exprPtrCodeCopyIteration
Ancestors
  exprPtrCodeCopyOffset exprPtrCodeCopyLoad exprPtrCodeCopyStore
  emittedSeqComposePtr exprSimCopy context compileEnv loweringStateRelDefs exprLoweringProps
  emitHelper emitHelperProps fragGasSeqPtr ptrDiscipline venomState venomInst
  finite_map list arithmetic bodyPtrDefs immutableCopyExecution

Theorem code_copy_offset_nonterminators[local]:
  compile_lit_byte_offset op off sa = (r,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule code_offset_insts >>
  simp[EVERY_MEM] >> metis_tac[is_terminator_def]
QED

Theorem code_copy_frame_uniform_compose[local]:
  copy_runtime_frame sa s sm t /\ copy_runtime_frame sm t sb u /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm) /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm)
    (s with vs_inst_idx := k) G1 tn1) /\
  (!k. inst_seq_ptr D lo ctx fn PG G1 tn1 (emitted_insts sm sb)
    (t with vs_inst_idx := k) G2 tn2) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) G2 tn2
Proof
  strip_tac >> irule emitted_inst_seq_ptr_uniform_compose >>
  qexistsl [`G1`, `sm`, `t`, `tn1`] >>
  fs[copy_runtime_frame_def, inst_extends_def]
QED

Theorem code_copy_read_nonterminators[local]:
  compile_lit_byte_offset src off sa = (arg,sm) /\
  compile_imm_load_word F imm arg sm = (op,sb) /\
  copy_runtime_frame sa s sm t /\ copy_runtime_frame sm t sb u ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[copy_runtime_frame_def]) >>
  simp[EVERY_APPEND] >> conj_tac
  >- metis_tac[code_copy_offset_nonterminators] >>
  fs[compile_imm_load_word_def] >>
  drule emitted_op_nonterminators >> simp[is_terminator_def]
QED

Theorem code_copy_read_prefix:
  compile_lit_byte_offset src off sa = (arg,sm) /\
  compile_imm_load_word F imm arg sm = (op,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  op_taint tn src = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    op_taint tnf op = {} /\ op_prov Gf op = NONE /\
    copy_old_operand sb op /\ (?v. eval_operand op t = SOME v) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >> drule_all code_copy_source_offset >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule_all code_copy_runtime_load >>
  disch_then (qspecl_then [`fn`, `PG`, `Gf`, `D`] strip_assume_tac) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >> simp[] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  rpt conj_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (irule code_copy_frame_uniform_compose >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[code_copy_offset_nonterminators])
  >- metis_tac[code_copy_read_nonterminators]
  >- metis_tac[]
  >> metis_tac[]
QED

Theorem code_copy_write_suffix:
  compile_lit_byte_offset (Var root) off sa = (dst,sm) /\
  emit_void MSTORE [dst;v] sm = ((),sb) /\
  not_fresh_at sa root /\ copy_old_operand sa v /\
  lookup_var root s = SOME b /\ eval_operand v s = SOME value /\
  op_taint tn v = {} /\ ptr_covers G tn root s capacity /\
  off < capacity /\ off + 32 <= capacity /\
  w2n b + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem = tn.t_mem DIFF
      {j | w2n (b + n2w off) <= j /\ j < w2n (b + n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  strip_tac >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  `copy_old_operand sa (Var root) /\ eval_operand (Var root) s = SOME b` by
    simp[copy_old_operand_def, eval_operand_def] >>
  drule_all code_copy_source_offset >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  drule_all code_copy_destination_coverage >> strip_tac >> gvs[] >>
  `copy_old_operand sm v` by
    metis_tac[copy_old_operand_mono, copy_runtime_frame_def] >>
  `eval_operand v t = SOME value` by metis_tac[copy_runtime_frame_operand] >>
  `op_taint tnf v = {}` by
    metis_tac[old_operand_taint_frame, copy_old_operand_def] >>
  drule_all code_copy_runtime_store >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >> simp[] >> rpt conj_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (irule code_copy_frame_uniform_compose >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[code_copy_offset_nonterminators])
  >> metis_tac[]
QED

Theorem code_copy_runtime_one_ptr:
  immutable_copy_one F imm src (Var root) off sa = ((),sb) /\
  copy_old_operand sa src /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s capacity /\
  off < capacity /\ off + 32 <= capacity /\
  w2n b + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    copy_runtime_frame sa s sb t /\
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) Gf tnf) /\
    tnf.t_mem = tn.t_mem DIFF
      {j | w2n (b + n2w off) <= j /\ j < w2n (b + n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p n. not_fresh_at sa p /\ ptr_covers G tn p s n ==>
      ptr_covers Gf tnf p t n)
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases] >> strip_tac >>
  drule_all code_copy_read_prefix >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `copy_runtime_frame sa s sm t` >>
  `not_fresh_at sm root` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `lookup_var root t = SOME b` by fs[copy_runtime_frame_def] >>
  `ptr_covers Gf tnf root t capacity` by metis_tac[] >>
  `w2n b + off < dimword(:256)` by decide_tac >>
  drule_all code_copy_write_suffix >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`Gf'`, `tnf'`, `t'`] >> simp[] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sm p` by
    (fs[copy_runtime_frame_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  rpt conj_tac
  >- metis_tac[copy_runtime_frame_trans]
  >- (irule code_copy_frame_uniform_compose >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[])
  >> metis_tac[]
QED

Theorem code_copy_one_insts:
  immutable_copy_one F imm src dst off sa = ((),sb) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; DLOAD; MSTORE]) (emitted_insts sa sb)
Proof
  strip_tac >>
  `compile_imm_copy_to_memory F imm src dst (SUC 0) off sa = ((),sb)` by
    simp[immutable_copy_suc, comp_ignore_bind_def,
         compile_imm_copy_to_memory_def, comp_return_def, comp_bind_def] >>
  drule code_copy_insts >> strip_tac >>
  fs[emitted_insts_def, DROP_APPEND]
QED

(* Generalized from the singleton conversion: arbitrary unrolled runtime copy. *)
Theorem code_copy_range_counted:
  compile_imm_copy_to_memory F imm src dst n off sa = ((),sb) /\
  copy_runtime_frame sa s sb t /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
    (s with vs_inst_idx := k) Gf tnf) ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 Gf tnf
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)))
Proof
  strip_tac >> drule code_copy_insts >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD; DLOAD; MSTORE]) (emitted_insts sa sb)` by
    fs[emitted_insts_def, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[is_terminator_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> strip_tac >> gvs[]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tnf` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  fs[copy_runtime_frame_def] >> drule_all run_inst_seq_gas_path_ptr >> simp[]
QED
