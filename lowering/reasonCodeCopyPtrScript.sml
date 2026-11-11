(* Counted runtime immutable copies, with exact checked transfer effects. *)
Theory reasonCodeCopyPtr
Ancestors
  reasonCodeTransferPtr reasonCodeLoadPtr reasonCodeOffsetPtr
  immutableCopyExecution compilerChainCode exprLoweringProps
  context compileEnv loweringStateRelDefs emitHelper fragExec bodyPtrDefs ptrDiscipline
  venomState venomInst finite_map words fragGasPathPtr

Theorem code_copy_suc_parts:
  compile_imm_copy_to_memory F imm src dst (SUC n) off sa = ((),sb) ==>
  ?src_op value dst_op c1 c2 c3 c4.
    compile_lit_byte_offset src off sa = (src_op,c1) /\
    emit_op DLOAD [src_op] c1 = (value,c2) /\
    compile_lit_byte_offset dst off c2 = (dst_op,c3) /\
    emit_void MSTORE [dst_op;value] c3 = ((),c4) /\
    compile_imm_copy_to_memory F imm src dst n (off+32) c4 = ((),sb)
Proof
  simp[Once compile_imm_copy_to_memory_def, compile_imm_load_word_def,
       comp_ignore_bind_def, immutable_comp_bind_cases] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem code_offset_extends:
  compile_lit_byte_offset op off sa = (r,sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule immutable_byte_offset_extends >>
  simp[cs_extends_def, same_blocks_def] >>
  strip_tac >> qexists_tac `[]` >> simp[]
QED

Theorem code_copy_suc_code:
  compile_lit_byte_offset src off sa = (src_op,c1) /\
  emit_op DLOAD [src_op] c1 = (value,c2) /\
  compile_lit_byte_offset dst off c2 = (dst_op,c3) /\
  emit_void MSTORE [dst_op;value] c3 = ((),c4) /\
  compile_imm_copy_to_memory F imm src dst n (off+32) c4 = ((),sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\
  fn_has_code c4 sb func
Proof
  strip_tac >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\
   cs_extends c3 c4 /\ cs_extends c4 sb` by
    (rpt conj_tac >- metis_tac[code_offset_extends]
     >- metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND]
     >- metis_tac[code_offset_extends]
     >- metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, ci_mono_def, pairTheory.SND]) >>
  qspecl_then [`[c1;c2;c3;c4;sb]`, `sa`, `func`] mp_tac compiler_chain_has_code >>
  simp[]
QED

Theorem code_word_compiler_mono:
  compile_lit_byte_offset src off sa = (src_op,c1) /\
  emit_op DLOAD [src_op] c1 = (value,c2) /\
  compile_lit_byte_offset (Var dst) off c2 = (dst_op,c3) /\
  emit_void MSTORE [dst_op;value] c3 = ((),c4) ==>
  sa.cs_next_var <= c4.cs_next_var
Proof
  strip_tac >>
  `sa.cs_next_var <= c1.cs_next_var /\
   c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= c3.cs_next_var /\
   c3.cs_next_var <= c4.cs_next_var` by
    (rpt conj_tac >- metis_tac[immutable_byte_offset_extends]
     >- metis_tac[code_load_compiler_frame]
     >- metis_tac[immutable_byte_offset_extends] >>
     metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND]) >>
  simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac
QED

Theorem code_copy_path_ptr:
  !n off sa sb s G tn.
  compile_imm_copy_to_memory F imm src (Var dst) n off sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME b /\ ptr_covers G tn dst s capacity /\
  (!p. src = Var p ==> not_fresh_at sa p) /\ not_fresh_at sa dst /\
  off + 32*n <= capacity /\ w2n b + off + 32*n < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (immutable_transfers F F a b n off s).vs_memory /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_data_section = s.vs_data_section /\
    tnf.t_mem = tn.t_mem DIFF
      {i | w2n b + off <= i /\ i < w2n b + off + 32*n} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
      ptr_covers Gf tnf p sf k) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  Induct >- (rpt gen_tac >> simp[compile_imm_copy_to_memory_def,
    comp_return_def, immutable_transfers_def] >> strip_tac >> gvs[] >>
    qexistsl_tac [`G`, `tn`, `s`] >> simp[gas_path_ptr_rules, venom_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  drule code_copy_suc_parts >> strip_tac >>
  drule_all code_copy_suc_code >> strip_tac >>
  `off < dimword(:256) /\ off + 32 <= capacity /\
   w2n b + off < dimword(:256)` by decide_tac >>
  drule_at (Pat `emit_op DLOAD _ _ = _`) code_word_transfer_path_ptr >>
  disch_then (drule_all_then strip_assume_tac) >>
  first_x_assum (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
  drule_all code_word_compiler_mono >> strip_tac >>
  `!p. not_fresh_at sa p ==> not_fresh_at c4 p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `eval_operand src s1 = SOME a /\ op_taint tn1 src = {} /\
   lookup_var dst s1 = SOME b /\ ptr_covers G1 tn1 dst s1 capacity` by
    (Cases_on `src` >> gvs[eval_operand_def, op_taint_def,
      venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `!off sa sb s G tn. _`
    (qspecl_then [`off+32`, `c4`, `sb`, `s1`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac >- suspend "memory" >>
  conj_tac >- gvs[venom_state_component_equality] >>
  suspend "taint"
QED

Resume code_copy_path_ptr[memory]:
  simp[immutable_transfers_def] >>
  irule (cj 1 immutable_transfers_cong) >>
  gvs[immutable_word_transfer_fields, immutable_transfer_data,
      immutable_copy_read_def, venom_state_component_equality]
QED

Resume code_copy_path_ptr[taint]:
  `w2n (b + n2w off) = w2n b + off` by
    (simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w] >> decide_tac) >>
  simp[] >>
  simp[pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF] >>
  gen_tac >> Cases_on `x IN tn.t_mem` >>
  simp[arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Finalise code_copy_path_ptr

