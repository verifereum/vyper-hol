Theory bodyPtrIfExpRuntimeCompiler
Ancestors immutableCopyExecution context compileEnv emitHelper
  fragExec rich_list

Theorem ifexp_runtime_offset_extends:
  compile_lit_byte_offset op off sa = (dst,sb) ==> cs_extends sa sb
Proof
  Cases_on `off = 0` >>
  simp[compile_lit_byte_offset_def, comp_return_def] >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, comp_return_def,
       emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[cs_extends_def] >> simp[IS_PREFIX_APPEND]
QED

Theorem ifexp_runtime_one_parts:
  immutable_copy_one F imm src dst off sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?sop ca value cb dop cc.
    compile_lit_byte_offset src off sa = (sop,ca) /\
    emit_op DLOAD [sop] ca = (value,cb) /\
    compile_lit_byte_offset dst off cb = (dop,cc) /\
    emit_void MSTORE [dop;value] cc = ((),sb) /\
    fn_has_code sa ca fn /\ fn_has_code ca cb fn /\
    fn_has_code cb cc fn /\ fn_has_code cc sb fn /\
    cs_extends sa ca /\ cs_extends ca cb /\ cs_extends cb cc /\ cs_extends cc sb
Proof
  simp[immutable_copy_one_def, immutable_comp_bind_cases,
       compile_imm_load_word_def] >> strip_tac >>
  `cs_extends sa st1 /\ cs_extends st1 st1' /\
   cs_extends st1' st1'' /\ cs_extends st1'' sb` by
    (conj_tac >- metis_tac[ifexp_runtime_offset_extends] >>
     conj_tac >-
       (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
        simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
        rpt strip_tac >> gvs[cs_extends_def] >> simp[IS_PREFIX_APPEND]) >>
     conj_tac >- metis_tac[ifexp_runtime_offset_extends] >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[cs_extends_def] >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends st1' sb /\ cs_extends st1 sb` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_at (Pat `fn_has_code st1 sb fn`) fn_has_code_split >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `fn_has_code st1' sb fn`) fn_has_code_split >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`src_op`, `st1`, `value`, `st1'`, `dst_op`, `st1''`] >> simp[]
QED
