(* One-word runtime immutable transfers, shared by reason consumers. *)
Theory reasonCodeTransferPtr
Ancestors
  reasonCodeLoadPtr reasonCodeOffsetPtr reasonEncoderTailPtr
  immutableCopyExecution emitHelperProps exprLoweringProps
  context compileEnv emitHelper fragExec bodyPtrDefs ptrDiscipline
  venomState venomInst finite_map words fragGasPathPtr

Theorem code_offset_compiler_frame:
  compile_lit_byte_offset op off sa = (r,sb) /\
  (!p. op = Var p ==> not_fresh_at sa p) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!p. not_fresh_at sa p ==> not_fresh_at sb p) /\
  (!p. r = Var p ==> not_fresh_at sb p)
Proof
  strip_tac >> drule immutable_byte_offset_extends >> strip_tac >>
  conj_tac >- simp[] >> conj_tac
  >- (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `off = 0` >- gvs[compile_lit_byte_offset_def, comp_return_def] >>
  Cases_on `op` >- gvs[compile_lit_byte_offset_def, comp_return_def] >>
  gvs[compile_lit_byte_offset_def, emit_op_def, fresh_var_def, comp_bind_def,
      comp_ignore_bind_def, emit_inst_def, fresh_id_def, emit_def,
      comp_return_def, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem code_load_compiler_frame:
  emit_op DLOAD [src] sa = (r,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (!p. not_fresh_at sa p ==> not_fresh_at sb p) /\
  (!p. r = Var p ==> not_fresh_at sb p)
Proof
  simp[emit_op_def, fresh_var_def, comp_bind_def, comp_ignore_bind_def,
       emit_inst_def, fresh_id_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >> simp[not_fresh_at_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS,
            arithmeticTheory.LESS_EQ_ADD]
QED

Theorem code_word_read_path_ptr:
  compile_lit_byte_offset src off sa = (src_op,c1) /\
  emit_op DLOAD [src_op] c1 = (value,sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  (!p. src = Var p ==> not_fresh_at sa p) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand value sf = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n (a + n2w off)) s.vs_data_section ++ REPLICATE 32 0w))) /\
    op_taint tnf value = {} /\ op_prov Gf value = NONE /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_memory = s.vs_memory /\
    sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all code_offset_compiler_frame >> strip_tac >>
  drule_at (Pat `compile_lit_byte_offset _ _ _ = _`)
    compile_lit_byte_offset_path_ptr >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
  `s1.vs_data_section = s.vs_data_section` by
    gvs[venom_state_component_equality] >>
  `allocas_from 0 s1` by simp[allocas_from_def] >>
  drule_at (Pat `emit_op DLOAD _ _ = _`) reason_code_load_path_ptr >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `G1`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  gvs[venom_state_component_equality]
QED

Theorem code_word_store_path_ptr:
  compile_lit_byte_offset (Var dst) off sa = (dst_op,c1) /\
  emit_void MSTORE [dst_op;value] c1 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s capacity /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  (!p. value = Var p ==> not_fresh_at sa p) /\
  off < dimword(:256) /\ off + 32 <= capacity /\
  w2n b + off < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore (w2n (b + n2w off)) w s).vs_memory /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem DIFF
      {i | w2n (b + n2w off) <= i /\ i < w2n (b + n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_at (Pat `compile_lit_byte_offset _ _ _ = _`)
    (Q.INST [`needed` |-> `32`] compile_lit_byte_offset_covers_ptr) >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
  `eval_operand value s1 = SOME w /\ op_taint tn1 value = {}` by
    (Cases_on `value` >> gvs[eval_operand_def, op_taint_def,
      venom_state_component_equality]) >>
  gvs[] >> drule_at (Pat `emit_void MSTORE _ _ = _`)
    reason_encoder_mstore_resources_ptr >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G1`, `tnf`, `sf`] >> simp[] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac >- (irule immutable_mstore_memory_cong >> simp[]) >>
  gvs[venom_state_component_equality] >>
  rpt strip_tac >> gvs[ptr_covers_def, op_taint_def] >> metis_tac[]
QED

Theorem code_word_transfer_path_ptr:
  compile_lit_byte_offset src off sa = (src_op,c1) /\
  emit_op DLOAD [src_op] c1 = (value,c2) /\
  compile_lit_byte_offset (Var dst) off c2 = (dst_op,c3) /\
  emit_void MSTORE [dst_op;value] c3 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s capacity /\
  (!p. src = Var p ==> not_fresh_at sa p) /\ not_fresh_at sa dst /\
  off < dimword(:256) /\ off + 32 <= capacity /\
  w2n b + off < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mstore (w2n (b + n2w off))
      (word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n (a + n2w off)) s.vs_data_section ++ REPLICATE 32 0w))) s).vs_memory /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem DIFF
      {i | w2n (b + n2w off) <= i /\ i < w2n (b + n2w off) + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. w2n (b + n2w off) <= i /\ i < w2n (b + n2w off) + 32 ==>
      i NOTIN tnf.t_mem) /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p sf k) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule code_load_compiler_frame >> strip_tac >>
  `sa.cs_next_var <= c1.cs_next_var` by
    metis_tac[immutable_byte_offset_extends] >>
  `!p. not_fresh_at sa p ==> not_fresh_at c2 p` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  drule_at (Pat `emit_op DLOAD _ _ = _`) code_word_read_path_ptr >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
  `lookup_var dst s1 = SOME b /\ ptr_covers G1 tn1 dst s1 capacity` by
    (gvs[ptr_covers_def, op_taint_def] >> metis_tac[]) >>
  drule_at (Pat `emit_void MSTORE _ _ = _`) code_word_store_path_ptr >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >> conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac >- (irule immutable_mstore_memory_cong >> simp[]) >>
  gvs[venom_state_component_equality] >>
  rpt strip_tac >> gvs[ptr_covers_def, op_taint_def] >> metis_tac[]
QED
