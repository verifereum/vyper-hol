(* Static fetch geometry of the request-ready external-call stage. *)
Theory entryCreateExtCallGeometry
Ancestors
  entryCreateFocusSpec exprLowering emitHelper compileEnv context
  fragExec abiEncoderProps venomInst venomState list rich_list arithmetic

Theorem stage_slot_geometry_from_blocks[local]:
  emitted_blocks sp sr =
    [<|bb_label := fail_lbl; bb_instructions := failure|>;
     <|bb_label := sp.cs_current_bb;
       bb_instructions := sp.cs_current_insts ++ prefix|>] /\
  LENGTH prefix = n /\ LENGTH failure = 4 /\
  EVERY (\i. i.inst_id IN frag_ids sp sr) (prefix ++ failure) /\
  fn_has_code sp sr func /\
  ALL_DISTINCT (sr.cs_current_bb ::
                MAP (\bb. bb.bb_label) (emitted_blocks sp sr)) ==>
  !s. ((s.vs_current_bb = sp.cs_current_bb /\
         ?j. j < n /\ s.vs_inst_idx = LENGTH sp.cs_current_insts + j) \/
        (s.vs_current_bb = fail_lbl /\ s.vs_inst_idx < 4)) ==>
      ~create_operand_at sr s /\
      !bb i. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
             get_instruction bb s.vs_inst_idx = SOME i ==>
             i.inst_id IN frag_ids sp sr
Proof
  strip_tac >>
  `lookup_block sp.cs_current_bb func.fn_blocks =
       SOME <|bb_label := sp.cs_current_bb;
              bb_instructions := sp.cs_current_insts ++ prefix|> /\
   lookup_block fail_lbl func.fn_blocks =
       SOME <|bb_label := fail_lbl; bb_instructions := failure|>` by
    (fs[fn_has_code_def] >>
     qpat_x_assum `!bb. MEM bb (emitted_blocks sp sr) ==> _` mp_tac >>
     simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[] >> strip_tac >> gen_tac >> strip_tac
  >- (simp[create_operand_at_def] >> rpt strip_tac >>
      gvs[get_instruction_def, EL_APPEND_EQN, EVERY_EL]) >>
  simp[create_operand_at_def] >> rpt strip_tac >>
  gvs[get_instruction_def, EVERY_EL]
QED

Theorem extcall_stage_slot_geometry:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
   else comp_return ()) sp = ((),s1) /\
  emit_op opc ops s1 = (success,s2) /\
  fresh_label "extcall_fail" s2 = (fail_lbl,s3) /\
  fresh_label "extcall_cont" s3 = (cont_lbl,s4) /\
  emit_inst JNZ [success; Label cont_lbl; Label fail_lbl] [] s4 = ((),s5) /\
  new_block fail_lbl s5 = (old_lbl,s6) /\
  emit_op RETURNDATASIZE [] s6 = (rds,s7) /\
  compile_alloc_buffer 0 s7 = (fail_buf,s8) /\
  emit_void RETURNDATACOPY [fail_buf.buf_operand; Lit 0w; rds] s8 = ((),s9) /\
  emit_inst REVERT [fail_buf.buf_operand; rds] [] s9 = ((),s10) /\
  new_block cont_lbl s10 = (u,sr) /\
  fn_has_code sp sr func /\
  ALL_DISTINCT (sr.cs_current_bb ::
                MAP (\bb. bb.bb_label) (emitted_blocks sp sr)) ==>
  (!s. create_operand_at sr s <=> s.vs_current_bb = cont_lbl /\ s.vs_inst_idx = 0) /\
  !s. ((s.vs_current_bb = sp.cs_current_bb /\
         ?j. j < (if ret_type = NoneT /\ ~skip then 2 else 0) + 2 /\
             s.vs_inst_idx = LENGTH sp.cs_current_insts + j) \/
        (s.vs_current_bb = fail_lbl /\ s.vs_inst_idx < 4)) ==>
      ~create_operand_at sr s /\
      !bb i. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
             get_instruction bb s.vs_inst_idx = SOME i ==>
             i.inst_id IN frag_ids sp sr
Proof
  strip_tac >> conj_tac
  >- (fs[new_block_def] >> gvs[create_operand_at_def]) >>
  match_mp_tac (GEN_ALL stage_slot_geometry_from_blocks) >> simp[] >>
  qexistsl_tac [`DROP (LENGTH sp.cs_current_insts) s5.cs_current_insts`, `s10.cs_current_insts`] >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  Cases_on `ret_type = NoneT /\ ~skip` >>
  qpat_x_assum `(if ret_type = NoneT /\ ~skip then _ else _) sp = _` mp_tac >>
  simp[compile_extcodesize_check_def, comp_return_def, comp_bind_def,
       comp_ignore_bind_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> disch_then (SUBST_ALL_TAC o SYM) >>
  gvs[fresh_label_def, emit_op_def, emit_inst_def, emit_void_def,
      compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[emitted_blocks_def, DROP_LENGTH_APPEND, frag_ids_def, mk_inst_def]
QED
