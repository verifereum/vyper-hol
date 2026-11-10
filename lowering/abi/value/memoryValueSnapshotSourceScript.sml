(* TOP-LEVEL: checked Log argument snapshots preserve typed values without
   an assumed compiler/source footprint inequality. Word and pure-suffix
   cases retain their operand; other values use the actual materialization. *)
Theory memoryValueSnapshotSource
Ancestors
  memoryValueSnapshot memoryValueDefs memoryValueTyping typeLayoutProps
  bytesSnapshotProps bytesSnapshotCode abiBytestringCode
  valueLoadProps compileVyper compileEnv context exprLoweringProps stmtLowering
  typedCopyProducer vyperValue vyperTyping vyperTypeContract vyperContext vyperExprEffects
  fragBlockPath fragExec venomState list words

Theorem checked_materialize_aggregate_path:
  !tops in_deploy layouts addr art ctx func cenv ty tv v src cs op cs' ss src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    ~is_word_type ty /\ ~is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_size tv < dimword(:256) /\
    lowered_value_rel ty tv v src ss /\ eval_operand src ss = SOME src_addr /\
    src <> Var (STRING #"%" (toString cs.cs_next_var)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      (!arg_op. arg_op <> op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all type_memory_bytes_evaluated >> simp[]) >>
  `val_wf tv v` by
    (irule value_has_type_val_wf >> fs[lowered_value_rel_def]) >>
  `memory_value_rel tv v (w2n src_addr) ss.vs_memory` by gvs[lowered_value_rel_def] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `src`, `cs`, `op`, `cs'`,
    `ss`, `src_addr`] compile_materialize_aggregate_path) >> impl_tac >- simp[] >>
  strip_tac >> rename1 `fragment_path ctx func ss out` >> qexists_tac `out` >>
  gvs[lowered_value_rel_def]
QED

Theorem compile_log_save_arg_nonbytes_correct:
  !tops in_deploy layouts addr art ctx func cenv ty tv v src es cs op cs' ss.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\ ~is_bytestring_type ty /\
    compile_log_save_arg cenv ty src es cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\
    (~is_word_type ty /\ ~EVERY pure_expr es ==>
      type_memory_size tv < dimword(:256) /\
      src <> Var (STRING #"%" (toString cs.cs_next_var))) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      (!arg_op. arg_op <> op ==> eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> DISCH_TAC >>
  Cases_on `is_word_type ty \/ EVERY pure_expr es`
  >- (gvs[compile_log_save_arg_def, comp_return_def] >> qexists_tac `ss` >> simp[]) >>
  `~is_word_type ty /\ ~EVERY pure_expr es` by fs[] >>
  `?src_addr. eval_operand src ss = SOME src_addr` by fs[lowered_value_rel_def] >>
  gvs[compile_log_save_arg_def, EVERY_NOT_EXISTS] >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `ty`, `tv`, `v`, `src`, `cs`, `op`, `cs'`, `ss`, `src_addr`] checked_materialize_aggregate_path) >>
  impl_tac >- simp[] >> strip_tac >> goal_assum drule >> simp[]
QED

Theorem checked_materialize_bytes_path:
  !tops in_deploy layouts addr art ctx func cenv ty tv v src cs op cs' ss src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\ is_bytestring_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_size tv < dimword(:256) /\
    lowered_value_rel ty tv v src ss /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name) (compiler_var_names cs.cs_next_var 6) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names cs.cs_next_var 6) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (drule_all type_memory_bytes_evaluated >> simp[]) >>
  mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `src`,
    `cs`, `op`, `cs'`, `ss`, `src_addr`] compile_materialize_bytes_path) >>
  impl_tac >- simp[] >> strip_tac >> goal_assum drule >> simp[]
QED

Theorem checked_materialize_path:
  !tops in_deploy layouts addr art ctx func cenv ty tv v src cs op cs' ss src_addr.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\ ~is_word_type ty /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_size tv < dimword(:256) /\
    lowered_value_rel ty tv v src ss /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name)
      (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 6 else 1)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 6 else 1)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt strip_tac >> Cases_on `is_bytestring_type ty` >> fs[]
  >- (drule_all_then (qspec_then `ctx` strip_assume_tac) checked_materialize_bytes_path >>
      goal_assum drule >> simp[]) >>
  fs[compiler_var_names_def, GENLIST_1] >>
  drule_all compile_materialize_aggregate_code >> strip_tac >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) checked_materialize_aggregate_path >>
  goal_assum drule >> simp[]
QED

Theorem compile_log_save_arg_correct:
  !tops in_deploy layouts addr art ctx func cenv ty tv v src es cs op cs' ss.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    evaluate_type (type_env tops) ty = SOME tv /\
    compile_log_save_arg cenv ty src es cs = (op,cs') /\
    lowered_value_rel ty tv v src ss /\
    (~is_word_type ty /\ ~EVERY pure_expr es ==>
      type_memory_size tv < dimword(:256) /\
      EVERY (\name. src <> Var name)
        (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 6 else 1))) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 6 else 1)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_word_type ty \/ EVERY pure_expr es`
  >- (gvs[compile_log_save_arg_def, comp_return_def] >> qexists_tac `ss` >> simp[]) >>
  `~is_word_type ty /\ ~EVERY pure_expr es` by fs[] >>
  `type_memory_size tv < dimword(:256) /\
    EVERY (\name. src <> Var name)
      (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 6 else 1))` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `?src_addr. eval_operand src ss = SOME src_addr` by fs[lowered_value_rel_def] >>
  qpat_x_assum `compile_log_save_arg _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [compile_log_save_arg_def] >> strip_tac >>
  drule_all_then (qspec_then `ctx` strip_assume_tac) checked_materialize_path >>
  goal_assum drule >> simp[]
QED
