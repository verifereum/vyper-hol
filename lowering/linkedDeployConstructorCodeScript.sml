(* Code intervals in the packaged linked constructor entry. *)
Theory linkedDeployConstructorCode
Ancestors
  ctorDeployBodyShadow ctorDeployLoweringCode ctorDeployLoweringCodeShape
  ctorDeployEntryLabels ctorDeployMemoryRunMemEntryLabel
  compileUnitPackageShape bodyFullShadowInternalRun bodyFullShadowInternalCode
  compileVyper compileEnv moduleLowering loweringShapeDefs
  vyperCompiler venomInst context intCallLookup fragExec emitHelper list pair

Theorem deploy_constructor_value_guard_code:
  comp_bind (emit_op CALLVALUE []) (\cv.
    comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v]))
    (initial_compile_state "__deploy") = ((),st_pay) /\
  fn_has_code (initial_compile_state "__deploy") st_pay fn ==>
  ?bb tail.
    venomInst$lookup_block "__deploy" fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst 0 CALLVALUE [] ["%0"];
       mk_inst 1 ISZERO [Var "%0"] ["%1"];
       mk_inst 2 ASSERT [Var "%1"] []] ++ tail

Proof
  strip_tac >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [emit_op_def, emit_void_def, emit_inst_def,
    fresh_var_def, fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, initial_compile_state_def] >>
  strip_tac >>
  simp_tac bool_ss [fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >>
  qexistsl_tac [`bb`,`l`] >>
  gvs[] >> EVAL_TAC
QED

Theorem run_linked_deploy_constructor_code:
  ce0.ce_nonreentrant = (lnr,lkey,lut,F) /\
  run_deploy_lowering T rp runtime_bc cap args 0 ifns ce0 stmts
    pay nr key trans "__deploy" = SOME unit /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ifns) ==>
  ?st_pay imm st1 ce1 st2 st3 exit_lbl sa sb sj old_bb st_exit
   st_epilogue st_final fn.
    (if pay then comp_return () else
      comp_bind (emit_op CALLVALUE []) (\cv.
        comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v])))
      (initial_compile_state "__deploy") = ((),st_pay) /\
    (if cap > 0 then
       comp_bind (compile_fixed_region_with_id cap)
         (\r. comp_return (SND r).buf_operand)
     else comp_return (Lit 0w)) st_pay = (imm,st1) /\
    compile_register_constructor_args
      (ce0 with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
      args 0 0 st1 = (ce1,st2) /\
    (if nr then compile_nonreentrant_lock key trans F else comp_return ())
      st2 = ((),st3) /\
    fresh_label "ctor_exit" st3 = (exit_lbl,sa) /\
    compile_stmts (ce1 with ce_ctor_exit_label := SOME exit_lbl)
      NoLoop NoneT stmts sa = ((),sb) /\
    (if block_is_terminated sb then comp_return ()
     else emit_inst JMP [Label exit_lbl] []) sb = ((),sj) /\
    new_block exit_lbl sj = (old_bb,st_exit) /\
    (if nr then compile_nonreentrant_unlock key trans F else comp_return ())
      st_exit = ((),st_epilogue) /\
    compile_constructor_epilogue (LENGTH runtime_bc) cap imm st_epilogue =
      ((),st_final) /\
    venomInst$lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__deploy" /\
    fn_inst_ids_distinct fn /\
    fn_has_code (initial_compile_state "__deploy") st_pay fn /\
    fn_has_code (initial_compile_state "__deploy") sa fn /\
    fn_has_code sa sb fn /\ fn_has_code sb sj fn /\
    fn_has_code st_exit st_final fn

Proof
  strip_tac >>
  drule_all run_deploy_lowering_ctor_trace >> strip_tac >>
  drule deploy_internal_run_labels >> strip_tac >>
  `compile_generate_deploy T (LENGTH runtime_bc) cap args 0 [] ce0 stmts
    pay nr key trans (initial_compile_state "__deploy") = ((),st_final)` by
    (PURE_REWRITE_TAC [compile_generate_deploy_def, COND_CLAUSES,
       ctor_code_cond_not, ctor_lock_flag_select] >>
     simp_tac bool_ss [comp_ignore_bind_def, comp_bind_def, comp_get_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >>
     gvs[compile_internal_fn_bodies_def, comp_return_def]) >>
  `start = st_final` by fs[] >>
  pop_assum SUBST_ALL_TAC >>
  `final = post` by fs[] >>
  pop_assum SUBST_ALL_TAC >>
  `raw = ctx` by fs[] >>
  pop_assum SUBST_ALL_TAC >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ifns))` by
    (drule extract_context_internal_names >> strip_tac >>
     fs[lowering_context_ok_def, ctx_fn_names_def, install_immutable_reservation_def]) >>
  drule_all deploy_ctor_packaged_entry_by_labels >> strip_tac >>
  drule_all deploy_ctor_member_certificates >> strip_tac >>
  qabbrev_tac `fn = mk_raw_function "__deploy" (all_blocks st_final)` >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions)` by
    fs[lowering_context_ok_def, ctx_fn_names_def, install_immutable_reservation_def] >>
  `venomInst$lookup_function "__deploy" unit.cu_context.ctx_functions = SOME fn` by
    (mp_tac (Q.SPECL [`unit.cu_context.ctx_functions`,`fn`]
       lookup_function_distinct_mem) >>
     simp[install_immutable_reservation_def]) >>
  `~MEM "__deploy" (MAP FST (internal_fn_descriptors ifns))` by
    (`~internal_label_ok "__deploy"` by EVAL_TAC >>
     simp[MEM_MAP] >> rpt strip_tac >>
     qpat_assum `EVERY _ (internal_fn_descriptors ifns)`
       (qspec_then `y` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `fn_entry_label fn = SOME "__deploy"` by
    (mp_tac (Q.SPECL [`T`,`rp`,`runtime_bc`,`cap`,`args`,`0`,
      `ifns`,`ce0`,`stmts`,`pay`,`nr`,`key`,`trans`,`unit`,`fn`]
      ctor_checked_run_entry_label) >> simp[]) >>
  drule_all ctor_code_setup_extension >> strip_tac >>
  drule_all ctor_code_tail_extensions >> strip_tac >>
  `fn_has_code (initial_compile_state "__deploy") sa fn /\
   fn_has_code sa sb fn /\ fn_has_code sb sj fn /\
   fn_has_code st_exit st_final fn` by
    (simp[Abbr `fn`] >> irule ctor_code_intervals_contained >> simp[]) >>
  `cs_extends (initial_compile_state "__deploy") st_pay` by
    (Cases_on `pay` >> fs[comp_return_def, cs_extends_refl] >>
     `cs_appends (comp_bind (emit_op CALLVALUE []) (\cv.
          comp_bind (emit_op ISZERO [cv]) (\v. emit_void ASSERT [v])))` by
       (irule cs_appends_bind >> simp[cs_appends_emit_helpers] >>
        gen_tac >> irule cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
     fs[cs_appends_def]) >>
  `cs_extends st_pay sa` by
    (mp_tac (Q.SPECL [`T`,`cap`,`ce0`,`args`,`0`,`nr`,`key`,`trans`,
       `st_pay`,`st_pay`,`imm`,`st1`,`cenv1`,`st2`,`st3`,`exit_lbl`,`sa`]
       ctor_code_setup_extension) >> simp[comp_return_def]) >>
  `fn_has_code (initial_compile_state "__deploy") st_pay fn` by
    (mp_tac (Q.SPECL [`initial_compile_state "__deploy"`,`st_pay`,`sa`,`fn`]
       fn_has_code_split) >> simp[]) >>
  qexistsl_tac [`st_pay`,`imm`,`st1`,`cenv1`,`st2`,`st3`,`exit_lbl`,`sa`,`sb`,
    `sj`,`old_bb`,`st_exit`,`st_epilogue`,`st_final`,`fn`] >>
  simp[]
QED
