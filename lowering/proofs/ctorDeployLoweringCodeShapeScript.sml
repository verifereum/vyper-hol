Theory ctorDeployLoweringCodeShape
Ancestors
  ctorShapeProps ctorRegisterShape loweringShapeProps loweringShapeDefs
  loweringShapeRules moduleLowering compileEnv context emitHelper unitShapeDefs
  venomInst vyperCompiler list fragExec stmtLoweringMono ctorRegisterArgs
  exprLoweringProps

Theorem ctor_code_fixed_region_plain[local]:
  !sz. shape_step F compiler_label (\st. T)
    (compile_fixed_region_with_id sz)
    (\p st. plain_operand st (SND p).buf_operand)
Proof
  gen_tac >> simp[compile_fixed_region_with_id_def] >>
  irule shape_step_bind >> qexists_tac `\id st. T` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_id >> simp[shape_stable_def]) >>
  qx_gen_tac `id` >> BETA_TAC >>
  irule shape_step_bind >>
  qexists_tac `\out st. plain_operand st (Var out)` >> reverse conj_tac
  >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`]
        shape_step_fresh_var) >> simp[shape_stable_def]) >>
  qx_gen_tac `out` >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st (Var out)` >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  `shape_stable (\st. plain_operand st (Var out))` by
    (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  mp_tac (Q.SPECL [`F`, `compiler_label`,
    `\st. plain_operand st (Var out)`,
    `mk_inst id ASSIGN [Lit 0w] [out]`] shape_step_emit) >>
  simp[label_or_plain_def, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_read0_opcode_def, label_positions_ok_def, operand_case_not_label,
    is_terminator_def, is_param_opcode_def]
QED

Theorem ctor_code_cenv_exit_shape[local]:
  cenv_shape_ok st cenv /\ cenv.ce_return_pc = NONE /\ jump_label_ok lbl ==>
  cenv_shape_ok st (cenv with ce_ctor_exit_label := SOME lbl)
Proof
  strip_tac >> gvs[cenv_shape_ok_def] >> metis_tac[]
QED

Theorem ctor_code_tail_shape:
  !cenv body imm nr key trans runtime_size immutables_len.
    cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label
      (\st. cenv_shape_ok st cenv /\ plain_operand st imm)
      (do (if nr then compile_nonreentrant_lock key trans F else return ());
          exit_lbl <- fresh_label "ctor_exit";
          compile_stmts (cenv with ce_ctor_exit_label := SOME exit_lbl)
            NoLoop NoneT body;
          cs <- comp_get;
          (if block_is_terminated cs then return ()
           else emit_inst JMP [Label exit_lbl] []);
          new_block exit_lbl;
          (if nr then compile_nonreentrant_unlock key trans F else return ());
          compile_constructor_epilogue runtime_size immutables_len imm od)
      (\u st. T)
Proof
  rpt gen_tac >> strip_tac >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. cenv_shape_ok st cenv /\ plain_operand st imm` >>
  reverse conj_tac >- suspend "lock" >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\lbl st. (cenv_shape_ok st cenv /\ plain_operand st imm) /\
    compiler_label lbl` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >> ho_match_mp_tac shape_stable_conj >>
      simp[cenv_shape_ok_stable] >> rw[shape_stable_def] >>
      metis_tac[plain_operand_mono]) >>
  qx_gen_tac `lbl` >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm /\ compiler_label lbl` >>
  reverse conj_tac >- suspend "body" >>
  gen_tac >> BETA_TAC >> suspend "finish"
QED

Resume ctor_code_tail_shape[lock]:
  Cases_on `nr` >> simp[]
  >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `key`, `trans`, `F`]
        compile_nonreentrant_lock_shape) >>
      simp[shape_step_def] >> rpt strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      `cenv_shape_ok st' cenv` by
        (mp_tac (Q.SPEC `cenv` cenv_shape_ok_stable) >>
         rw[shape_stable_def] >> metis_tac[]) >>
      metis_tac[plain_operand_mono]) >>
  irule shape_step_return >> simp[]
QED

Resume ctor_code_tail_shape[body]:
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  qspecl_then [`cenv with ce_ctor_exit_label := SOME lbl`,
    `NoLoop`, `NoneT`, `ss`] mp_tac (CONJUNCT2 compile_stmt_shape) >>
  simp[shape_step_def, loop_ctx_shape_ok_def] >>
  rpt strip_tac >>
  `cenv_shape_ok st (cenv with ce_ctor_exit_label := SOME lbl)` by
    (irule ctor_code_cenv_exit_shape >> simp[] >>
     gvs[jump_label_ok_def]) >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[plain_operand_mono]
QED

Resume ctor_code_tail_shape[finish]:
  irule shape_step_bind >>
  qexists_tac `\cs st. plain_operand st imm /\ compiler_label lbl` >>
  reverse conj_tac
  >- simp[shape_step_def, comp_get_def, shape_extends_refl] >>
  gen_tac >> BETA_TAC >>
  irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm /\ compiler_label lbl` >>
  reverse conj_tac
  >- (IF_CASES_TAC >- (irule shape_step_return >> simp[]) >>
      irule shape_step_conseq >> irule_at Any shape_step_emit_inst_guarded >>
      qexists_tac `\st. plain_operand st imm /\ compiler_label lbl` >>
      qexists_tac `compiler_label` >> simp[] >> conj_tac
      >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        jump_label_ok_def, label_positions_ok_def, is_terminator_def,
        is_read0_opcode_def, operand_case_not_label, is_param_opcode_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm` >>
  reverse conj_tac
  >- (`shape_stable (\st. plain_operand st imm)` by
        (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. plain_operand st imm`, `lbl`]
        shape_step_new_block) >>
      simp[shape_step_def] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      metis_tac[plain_operand_mono, shape_stable_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. plain_operand st imm` >> reverse conj_tac
  >- (Cases_on `nr` >> simp[]
      >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `key`, `trans`, `F`]
            compile_nonreentrant_unlock_shape) >>
          simp[shape_step_def] >> rpt strip_tac >>
          first_x_assum drule_all >> strip_tac >> metis_tac[plain_operand_mono]) >>
      irule shape_step_return >> simp[]) >>
  gen_tac >> BETA_TAC >> irule compile_constructor_epilogue_shape
QED

Finalise ctor_code_tail_shape[local]

Theorem ctor_code_prefix_shape:
  !cenv body pay nr key trans runtime_size immutables_len args data_size.
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body ==>
    shape_step F compiler_label (\st. T)
      (do (if ~pay then
             do cv <- emit_op CALLVALUE [];
                no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
           else return ());
          imm <- (if immutables_len > 0 then
                    do p <- compile_fixed_region_with_id immutables_len;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca :=
              (if immutables_len > 0 then SOME imm else NONE)) args 0 data_size;
          (if nr then compile_nonreentrant_lock key trans F else return ());
          lbl <- fresh_label "ctor_exit";
          compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT body;
          cs <- comp_get;
          (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
          new_block lbl;
          (if nr then compile_nonreentrant_unlock key trans F else return ());
          compile_constructor_epilogue runtime_size immutables_len imm od)
      (\u st. T)
Proof
  ntac 10 gen_tac >> strip_tac >> irule shape_step_ignore_bind >>
  qexists_tac `\u st. T` >> reverse conj_tac >- suspend "pay" >>
  gen_tac >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\imm st. plain_operand st imm` >> reverse conj_tac
  >- suspend "allocate" >>
  qx_gen_tac `imm` >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\ce st. cenv_shape_ok st ce /\ plain_operand st imm /\
    ce.ce_return_pc = NONE` >> reverse conj_tac >- suspend "register" >>
  qx_gen_tac `ce` >> BETA_TAC >>
  irule shape_step_conseq >> irule_at Any extbodies_assume >>
  qexists_tac `ce.ce_return_pc = NONE` >>
  qexists_tac `\u st. T` >>
  qexists_tac `\st. cenv_shape_ok st ce /\ plain_operand st imm` >>
  qexists_tac `compiler_label` >> simp[] >>
  strip_tac >> irule ctor_code_tail_shape >> simp[]
QED

Resume ctor_code_prefix_shape[pay]:
  Cases_on `pay` >> simp[]
  >- (irule shape_step_return >> simp[]) >>
  irule shape_step_bind >> qexists_tac `\cv st. plain_operand st cv` >>
  reverse conj_tac
  >- (mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`, `CALLVALUE`, `[]`]
        shape_step_emit_op) >>
      simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        label_positions_ok_def, is_terminator_def, is_read0_opcode_def,
        is_param_opcode_def]) >>
  qx_gen_tac `cv` >> BETA_TAC >> irule shape_step_bind >>
  qexists_tac `\v st. plain_operand st v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_emit_op_guarded >>
      qexists_tac `\st. plain_operand st cv` >>
      qexists_tac `compiler_label` >> simp[] >> conj_tac
      >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        label_positions_ok_def, is_terminator_def, is_read0_opcode_def,
        is_param_opcode_def, operand_case_not_label, plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `v` >> BETA_TAC >>
  rewrite_tac[extbodies_emit_inst_void |> GSYM] >>
  irule shape_step_conseq >> irule_at Any shape_step_emit_inst_guarded >>
  qexists_tac `\st. plain_operand st v` >> qexists_tac `compiler_label` >>
  simp[] >> conj_tac
  >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  simp[label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    label_positions_ok_def, is_terminator_def, is_read0_opcode_def,
    is_param_opcode_def, operand_case_not_label, plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def]
QED

Resume ctor_code_prefix_shape[allocate]:
  IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st (SND p).buf_operand` >>
      reverse conj_tac >- irule ctor_code_fixed_region_plain >>
      gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_return >> simp[plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def]
QED

Resume ctor_code_prefix_shape[register]:
  qmatch_goalsub_abbrev_tac `compile_register_constructor_args ce0 args 0 data_size` >>
  `!st. plain_operand st imm ==> cenv_shape_ok st ce0` by
    (rpt strip_tac >> simp[Abbr `ce0`] >>
     irule cenv_shape_ok_install_imm_alloca >> simp[] >>
     metis_tac[cenv_static_ok_shape_ok]) >>
  `ce0.ce_return_pc = NONE` by simp[Abbr `ce0`] >>
  qspecl_then [`args`, `ce0`, `0`, `data_size`] mp_tac
    compile_register_constructor_args_shape >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  metis_tac[plain_operand_mono]
QED

Finalise ctor_code_prefix_shape

Theorem ctor_code_prefix_certificates:
  !cenv body pay nr key trans runtime_size cap args data_size st_final.
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body /\
    (do (if ~pay then
           do cv <- emit_op CALLVALUE [];
              no_val <- emit_op ISZERO [cv]; emit_void ASSERT [no_val] od
         else return ());
        imm <- (if cap > 0 then
                  do p <- compile_fixed_region_with_id cap;
                     return (SND p).buf_operand od
                else return (Lit 0w));
        ce <- compile_register_constructor_args
          (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
          args 0 data_size;
        (if nr then compile_nonreentrant_lock key trans F else return ());
        lbl <- fresh_label "ctor_exit";
        compile_stmts (ce with ce_ctor_exit_label := SOME lbl) NoLoop NoneT body;
        cs <- comp_get;
        (if block_is_terminated cs then return () else emit_inst JMP [Label lbl] []);
        new_block lbl;
        (if nr then compile_nonreentrant_unlock key trans F else return ());
        compile_constructor_epilogue runtime_size cap imm od)
      (initial_compile_state "__deploy") = ((),st_final) ==>
    shape_state st_final /\
    shape_extends F jump_label_ok (initial_compile_state "__deploy") st_final /\
    all_blocks st_final <> [] /\
    (HD (all_blocks st_final)).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks st_final))) /\
    EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions) (all_blocks st_final)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctor_code_prefix_shape >>
  rewrite_tac[shape_step_def] >> disch_then drule >>
  simp[shape_state_initial_compile_state] >> strip_tac >>
  `shape_extends F jump_label_ok (initial_compile_state "__deploy") st_final` by
    (irule shape_extends_LP_mono >> qexists_tac `compiler_label` >>
     simp[jump_label_ok_def]) >>
  drule initial_entry_blocks_shape >> simp[]
QED

Theorem ctor_code_primitives_append:
  (!sz. cs_appends (compile_fixed_region_with_id sz)) /\
  (!key trans view. cs_appends (compile_nonreentrant_lock key trans view)) /\
  (!key trans view. cs_appends (compile_nonreentrant_unlock key trans view)) /\
  (!sz cap imm. cs_appends (compile_constructor_epilogue sz cap imm))
Proof
  `!sz. cs_appends (compile_alloc_buffer sz)` by
    (rw[cs_appends_def] >>
     qspecl_then [`sz`, `st`] mp_tac ci_mono_compile_alloc_buffer >>
     simp[ci_mono_def]) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[compile_fixed_region_with_id_def, compile_nonreentrant_lock_def,
    compile_nonreentrant_unlock_def, compile_constructor_epilogue_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
    rw[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]) >>
  simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_code_setup_appends:
  !pay cap cenv args data_size nr key trans.
    cs_appends
      (do (if pay then return () else
             do cv <- emit_op CALLVALUE [];
                v <- emit_op ISZERO [cv]; emit_void ASSERT [v] od);
          imm <- (if cap > 0 then
                    do p <- compile_fixed_region_with_id cap;
                       return (SND p).buf_operand od
                  else return (Lit 0w));
          ce <- compile_register_constructor_args
            (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
            args 0 data_size;
          (if nr then compile_nonreentrant_lock key trans F else return ());
          fresh_label "ctor_exit" od)
Proof
  rpt gen_tac >> rpt IF_CASES_TAC >>
  rpt (FIRST [irule cs_appends_bind, irule cs_appends_ignore_bind] >>
    rw[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return,
      ctor_code_primitives_append, ctor_registration_appends]) >>
  simp[cs_appends_prims, cs_appends_emit_helpers, cs_appends_return,
    ctor_code_primitives_append, ctor_registration_appends]
QED

Theorem ctor_code_tail_extensions:
  !cenv body sa sb sj lbl old_bb st_exit nr key trans st_epilogue sz cap imm st_final.
    compile_stmts cenv NoLoop NoneT body sa = ((),sb) /\
    (if block_is_terminated sb then return ()
     else emit_inst JMP [Label lbl] []) sb = ((),sj) /\
    new_block lbl sj = (old_bb,st_exit) /\
    (if nr then compile_nonreentrant_unlock key trans F else return ())
      st_exit = ((),st_epilogue) /\
    compile_constructor_epilogue sz cap imm st_epilogue = ((),st_final) ==>
    cs_extends sa sb /\ cs_extends sb sj /\ cs_extends sj st_exit /\
    cs_extends st_exit st_epilogue /\ cs_extends st_epilogue st_final /\
    cs_extends st_exit st_final /\ cs_extends sa st_final
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sb` by
    (qpat_x_assum `compile_stmts _ _ _ _ _ = _` mp_tac >>
     metis_tac[compile_stmt_cs_mono, cs_mono_def]) >>
  `cs_extends sb sj` by
    (Cases_on `block_is_terminated sb` >>
     gvs[comp_return_def, cs_extends_refl] >>
     metis_tac[cs_extends_emit_inst]) >>
  `cs_extends sj st_exit` by metis_tac[cs_extends_new_block] >>
  `cs_extends st_exit st_epilogue` by
    (Cases_on `nr` >> gvs[comp_return_def, cs_extends_refl] >>
     metis_tac[ctor_code_primitives_append, cs_appends_def]) >>
  `cs_extends st_epilogue st_final` by
    metis_tac[ctor_code_primitives_append, cs_appends_def] >>
  metis_tac[cs_extends_trans]
QED

Theorem ctor_code_setup_extension:
  !pay cap cenv args data_size nr key trans start st_pay imm st1 ce st2 st3 lbl sa.
    (if pay then return () else
       do cv <- emit_op CALLVALUE [];
          v <- emit_op ISZERO [cv]; emit_void ASSERT [v] od) start = ((),st_pay) /\
    (if cap > 0 then
       do p <- compile_fixed_region_with_id cap; return (SND p).buf_operand od
     else return (Lit 0w)) st_pay = (imm,st1) /\
    compile_register_constructor_args
      (cenv with ce_imm_alloca := (if cap > 0 then SOME imm else NONE))
      args 0 data_size st1 = (ce,st2) /\
    (if nr then compile_nonreentrant_lock key trans F else return ()) st2 = ((),st3) /\
    fresh_label "ctor_exit" st3 = (lbl,sa) ==>
    cs_extends start sa
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac ctor_code_setup_appends >>
  disch_then (qspecl_then [`pay`, `cap`, `cenv`, `args`, `data_size`, `nr`,
    `key`, `trans`] mp_tac) >>
  rewrite_tac[cs_appends_def] >>
  disch_then (qspec_then `start` mp_tac) >>
  simp[comp_ignore_bind_def, comp_bind_def]
QED
