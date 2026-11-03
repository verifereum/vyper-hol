Theory ctorGeneratorShape
Ancestors
  ctorShapeProps ctorRegisterShape loweringShapeProps loweringShapeDefs
  loweringShapeRules moduleLowering compileEnv context emitHelper unitShapeDefs
  venomInst vyperCompiler list

Theorem deploy_fixed_region_plain[local]:
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

Theorem deploy_cenv_imm_shape[local]:
  cenv_shape_ok st (cenv with ce_imm_alloca := imm) <=>
  cenv_shape_ok st cenv
Proof
  simp[cenv_shape_ok_def]
QED

Theorem deploy_cenv_exit_shape[local]:
  cenv_shape_ok st cenv /\ cenv.ce_return_pc = NONE /\ jump_label_ok lbl ==>
  cenv_shape_ok st (cenv with ce_ctor_exit_label := SOME lbl)
Proof
  strip_tac >> gvs[cenv_shape_ok_def] >> metis_tac[]
QED

Theorem deploy_initial_shape[local]:
  shape_state (initial_compile_state "__deploy")
Proof
  simp[initial_compile_state_def, shape_state_def, opaque_insts_ok_def,
       state_insts_def, all_blocks_def]
QED

Theorem deploy_entry_blocks_shape[local]:
  !st. shape_extends F jump_label_ok (initial_compile_state "__deploy") st ==>
    all_blocks st <> [] /\
    (HD (all_blocks st)).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks st))) /\
    EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions) (all_blocks st)
Proof
  gen_tac >> strip_tac >>
  `state_insts (initial_compile_state "__deploy") = [] /\
   MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__deploy")) =
     ["__deploy"]`
    by simp[initial_compile_state_def, state_insts_def, all_blocks_def] >>
  qpat_x_assum `shape_extends _ _ _ _` mp_tac >>
  rewrite_tac[shape_extends_def] >> strip_tac >>
  drule state_insts_cs_extends >>
  drule block_labels_cs_extends >>
  asm_rewrite_tac [] >> rpt strip_tac >>
  qpat_x_assum `MAP _ (all_blocks (initial_compile_state _)) = _` kall_tac >>
  qpat_x_assum `state_insts (initial_compile_state _) = _` kall_tac >>
  fs[state_insts_def, EVERY_FLAT, EVERY_MAP] >>
  Cases_on `all_blocks st` >> gvs[] >>
  qpat_x_assum `EVERY (lowered_inst_ok F) _` mp_tac >>
  qpat_x_assum `_ ++ _ = added_insts _ _` (fn th => rewrite_tac[GSYM th]) >>
  simp[EVERY_FLAT, EVERY_MAP]
QED

Theorem deploy_fallthrough_shape[local]:
  !lbl. jump_label_ok lbl ==>
    shape_step F compiler_label (\st. T)
      (do cs <- comp_get;
          if block_is_terminated cs then return ()
          else emit_inst JMP [Label lbl] [] od) (\x st. T)
Proof
  rpt strip_tac >>
  irule shape_step_bind >> qexists_tac `\cs st. T` >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> IF_CASES_TAC
      >- (irule shape_step_return >> simp[]) >>
      mp_tac (Q.SPECL [`F`, `compiler_label`, `\st. T`,
        `JMP`, `[Label lbl]`, `[]`] shape_step_emit_inst) >>
      simp[shape_stable_def, label_or_plain_def,
           stackPlanTypesTheory.is_label_operand_def, lowered_inst_ok_def,
           mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
           inst_jump_labels_ok_def, is_terminator_def, is_read0_opcode_def,
           label_positions_ok_def, operand_case_not_label, is_param_opcode_def]) >>
  simp[shape_step_def, comp_get_def, shape_extends_refl]
QED

Theorem deploy_constructor_tail_shape:
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

Resume deploy_constructor_tail_shape[lock]:
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

Resume deploy_constructor_tail_shape[body]:
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  qspecl_then [`cenv with ce_ctor_exit_label := SOME lbl`,
    `NoLoop`, `NoneT`, `ss`] mp_tac (CONJUNCT2 compile_stmt_shape) >>
  simp[shape_step_def, loop_ctx_shape_ok_def] >>
  rpt strip_tac >>
  `cenv_shape_ok st (cenv with ce_ctor_exit_label := SOME lbl)` by
    (irule deploy_cenv_exit_shape >> simp[] >>
     gvs[jump_label_ok_def]) >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[plain_operand_mono]
QED

Resume deploy_constructor_tail_shape[finish]:
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
      simp[shape_step_def] >> rpt strip_tac >>
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

Finalise deploy_constructor_tail_shape[local]

Theorem deploy_constructor_prefix_shape:
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
  strip_tac >> irule deploy_constructor_tail_shape >> simp[]
QED

Resume deploy_constructor_prefix_shape[pay]:
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
Resume deploy_constructor_prefix_shape[allocate]:
  IF_CASES_TAC
  >- (irule shape_step_bind >>
      qexists_tac `\p st. plain_operand st (SND p).buf_operand` >>
      reverse conj_tac >- irule deploy_fixed_region_plain >>
      gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]) >>
  irule shape_step_return >> simp[plain_operand_def,
    stackPlanTypesTheory.is_label_operand_def]
QED
Resume deploy_constructor_prefix_shape[register]:
  qmatch_goalsub_abbrev_tac `compile_register_constructor_args ce0 args 0 data_size` >>
  `!st. cenv_shape_ok st ce0` by
    (simp[Abbr `ce0`, deploy_cenv_imm_shape] >>
     metis_tac[cenv_static_ok_shape_ok]) >>
  `ce0.ce_return_pc = NONE` by simp[Abbr `ce0`] >>
  qspecl_then [`args`, `ce0`, `0`, `data_size`] mp_tac
    compile_register_constructor_args_shape >>
  simp[shape_step_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  metis_tac[plain_operand_mono]
QED

Finalise deploy_constructor_prefix_shape[local]

Theorem compile_generate_deploy_shape:
  !has_constructor runtime_size immutables_len constructor_args data_size
   ctor_internal_fns cenv body is_payable is_nonreentrant nkey use_transient st1.
    compile_generate_deploy has_constructor runtime_size immutables_len
      constructor_args data_size ctor_internal_fns cenv body is_payable
      is_nonreentrant nkey use_transient (initial_compile_state "__deploy") =
        ((), st1) /\
    (has_constructor ==>
      cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
      ~supported_stmts_expr_exists expr_shape_root body /\
      EVERY internal_fn_shape_ok ctor_internal_fns) ==>
    shape_state st1 /\
    ?entry_blocks segs.
      all_blocks st1 = entry_blocks ++ FLAT segs /\
      entry_blocks <> [] /\ (HD entry_blocks).bb_label = "__deploy" /\
      EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry_blocks)) /\
      EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions) entry_blocks /\
      LIST_REL internal_segment_ok
        (internal_fn_descriptors (if has_constructor then ctor_internal_fns else []))
        segs
Proof
  rpt gen_tac >> Cases_on `has_constructor` >> simp[] >> strip_tac
  >- suspend "present"
  >> suspend "absent"
QED

Resume compile_generate_deploy_shape[present]:
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  drule_all deploy_constructor_prefix_shape >>
  disch_then (qspecl_then [`is_payable`, `is_nonreentrant`, `nkey`, `use_transient`]
    (qspecl_then [`runtime_size`, `immutables_len`, `constructor_args`, `data_size`]
      assume_tac)) >>
  qmatch_asmsub_abbrev_tac `shape_step F compiler_label (\st. T) prefix _` >>
  `compile_generate_deploy T runtime_size immutables_len constructor_args
     data_size ctor_internal_fns cenv ss is_payable is_nonreentrant nkey
     use_transient = comp_ignore_bind prefix
       (compile_internal_fn_bodies ctor_internal_fns)` by
    simp[compile_generate_deploy_def, Abbr `prefix`, comp_ignore_bind_def,
      comp_bind_assoc] >>
  qpat_x_assum `compile_generate_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >>
  Cases_on `prefix (initial_compile_state "__deploy")` >>
  rename1 `prefix _ = (prefix_result, entry_st)` >>
  Cases_on `prefix_result` >>
  simp[comp_ignore_bind_def, comp_bind_def] >> strip_tac >>
  qpat_x_assum `shape_step _ _ _ _ _` mp_tac >> simp[shape_step_def] >>
  disch_then drule >> simp[deploy_initial_shape] >> strip_tac >>
  `shape_extends F jump_label_ok (initial_compile_state "__deploy") entry_st` by
    (irule shape_extends_LP_mono >>
     qexists_tac `compiler_label` >> simp[jump_label_ok_def]) >>
  drule deploy_entry_blocks_shape >> strip_tac >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  conj_tac >- simp[] >>
  qexistsl_tac [`all_blocks entry_st`, `segs`] >> simp[]
QED

Resume compile_generate_deploy_shape[absent]:
  gvs[compile_generate_deploy_def, comp_ignore_bind_def, comp_return_def,
    comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  mp_tac (Q.SPECL [`runtime_size`, `immutables_len`] compile_simple_deploy_shape) >>
  simp[shape_step_def] >> disch_then drule >>
  simp[deploy_initial_shape] >> strip_tac >>
  rename1 `shape_state st1` >>
  `shape_extends F jump_label_ok (initial_compile_state "__deploy") st1` by
    (irule shape_extends_LP_mono >> qexists_tac `compiler_label` >>
     simp[jump_label_ok_def]) >>
  drule deploy_entry_blocks_shape >> strip_tac >>
  qexistsl_tac [`all_blocks st1`, `[]`] >> simp[internal_fn_descriptors_def]
QED

Finalise compile_generate_deploy_shape
