Theory bodyPtrTypeBuiltinsEmbeddingProbe
Ancestors
  bodyPtrTypeBuiltinsPathBoundary bodyPtrTypeBuiltinsScalarInput
  loweringSlice emitHelperProps emitHelper compileEnv
  fragGasPathPtr fragExec ptrSafeRun venomExecSemantics venomInstProofs
  venomState venomInst ptrDiscipline

Theorem mload_edge_control:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = MLOAD ==>
  t.vs_current_bb = s.vs_current_bb /\
  t.vs_inst_idx = SUC s.vs_inst_idx
Proof
  strip_tac >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, exit_result_def] >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
      exec_read1_def, update_var_def, exit_result_def]
QED

Theorem scalar_name_edge_continuation:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann name) sa = (op, sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path_ptr_edge D lo ctx fn PG G tn s n H ts (OK t) ==>
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ op_prov H op = NONE
Proof
  strip_tac >>
  `op_prov H op = NONE` by (irule scalar_name_edge_none >> metis_tac[]) >>
  drule_all lower_value_name_word >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id MLOAD [Var p]
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _`)
    mload_edge_control >> simp[] >>
  disch_then (qspec_then `mk_inst sa.cs_next_id MLOAD [Var p]
    [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
  gvs[mk_inst_def, arithmeticTheory.ADD1]
QED

Theorem first_arrival_after_one_edge:
  ptr_first_arrival D lo ctx fn PG hit G tn s n H ts t /\
  ~hit s /\
  (!k J us u. gas_path_ptr_edge D lo ctx fn PG G tn s k J us (OK u) ==>
     hit u /\ post J u) ==>
  post H t
Proof
  once_rewrite_tac[ptr_first_arrival_cases] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule_all ptr_first_arrival_initial_hit >> strip_tac >> gvs[]
QED

Theorem scalar_name_first_arrival_none:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  is_word_type ann /\
  lower_value compile_expr cenv ty (Name ann name) sa = (op, sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_first_arrival D lo ctx fn PG
    (\u. u.vs_current_bb = sb.cs_current_bb /\
         u.vs_inst_idx = LENGTH sb.cs_current_insts)
    G tn s n H ts t ==>
  op_prov H op = NONE
Proof
  strip_tac >>
  `s.vs_inst_idx <> LENGTH sb.cs_current_insts` by
    (drule_all scalar_name_emitted_load >> strip_tac >> simp[]) >>
  qpat_x_assum `ptr_first_arrival _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[ptr_first_arrival_cases] >> simp[] >> strip_tac >>
  `u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ op_prov H' op = NONE` by
    (irule scalar_name_edge_continuation >> metis_tac[]) >>
  drule ptr_first_arrival_initial_hit >> simp[] >> metis_tac[]
QED
