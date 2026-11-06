(* Checked byte offsets shared by runtime immutable-copy clients. *)
Theory reasonCodeOffsetPtr
Ancestors
  reasonTupleCopyPtr reasonEncoderTailPtr context compileEnv emitHelper
  contextCodegenRelProps exprLoweringProps bodyPtrDefs fragGasSeqPtr
  venomState venomInst finite_map words fragExec ptrDiscipline

Theorem code_offset_emit_shape:
  emit_op ADD [op; Lit (n2w off)] sa = (Var out,sb) ==>
  emit_inst ADD [op; Lit (n2w off)] [out]
    (sa with cs_next_var := sa.cs_next_var + 1) = ((),sb) /\
  (!p. not_fresh_at sa p ==> p <> out)
Proof
  simp[emit_op_def, fresh_var_def, comp_bind_def, comp_ignore_bind_def,
       emit_inst_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >> simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem code_offset_emit_var:
  emit_op ADD [op; Lit (n2w off)] sa = (r,sb) ==> ?out. r = Var out
Proof
  simp[emit_op_def, fresh_var_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> metis_tac[]
QED

Theorem code_offset_add_resources_ptr:
  emit_op ADD [op; Lit (n2w off)] sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand r sf = SOME (a + n2w off) /\ op_taint tnf r = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule code_offset_emit_var >> strip_tac >> gvs[] >>
  drule code_offset_emit_shape >> strip_tac >>
  `fn_has_code (sa with cs_next_var := sa.cs_next_var + 1) sb func` by
    gvs[fragExecTheory.fn_has_code_def, emitted_blocks_def] >>
  gvs[op_taint_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) reason_copy_binop_resources_ptr >>
  simp[eval_operand_def, op_taint_def] >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[eval_operand_def] >>
  gen_tac >> strip_tac >>
  `p <> out` by metis_tac[] >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[]
QED

Theorem compile_lit_byte_offset_path_ptr:
  compile_lit_byte_offset op off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand op s = SOME a /\ op_taint tn op = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand r sf = SOME (a + n2w off) /\ op_taint tnf r = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[WORD_ADD_0, venom_state_component_equality] >>
      irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >> simp[]) >>
  Cases_on `op`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[eval_operand_def, op_taint_def, venom_state_component_equality] >>
      irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >> simp[]) >>
  gvs[compile_lit_byte_offset_def] >>
  drule_all code_offset_add_resources_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> gvs[]
QED

Theorem code_offset_add_covers_ptr:
  emit_op ADD [Var root; Lit (n2w off)] sa = (Var out,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  off < dimword(:256) /\ off + needed <= capacity /\
  w2n a + off < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w off) /\ ptr_covers Gf tnf out sf needed /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule code_offset_emit_shape >> strip_tac >>
  `fn_has_code (sa with cs_next_var := sa.cs_next_var + 1) sb func` by
    gvs[fn_has_code_def, emitted_blocks_def] >>
  `needed + off <= capacity /\ off + w2n a < dimword(:256)` by decide_tac >>
  gvs[op_taint_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) reason_encoder_offset_path_ptr >>
  simp[eval_operand_def, op_taint_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  gen_tac >> strip_tac >> `p <> out` by metis_tac[] >>
  first_x_assum (qspec_then `p` mp_tac) >> simp[]
QED

Theorem compile_lit_byte_offset_covers_ptr:
  compile_lit_byte_offset (Var root) off sa = (r,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var root s = SOME a /\ ptr_covers G tn root s capacity /\
  off < dimword(:256) /\ off + needed <= capacity /\
  w2n a + off < dimword(:256) ==>
  ?out Gf tnf sf.
    r = Var out /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w off) /\ ptr_covers Gf tnf out sf needed /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[WORD_ADD_0] >> conj_tac
      >- (irule (cj 1 fragGasPathPtrTheory.gas_path_ptr_rules) >> simp[]) >>
      gvs[ptr_covers_def] >> decide_tac) >>
  gvs[compile_lit_byte_offset_def] >>
  drule code_offset_emit_var >> strip_tac >> gvs[] >>
  `off < dimword(:256) /\ off + needed <= capacity /\
   w2n a + off < dimword(:256)` by decide_tac >>
  drule_all code_offset_add_covers_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED
