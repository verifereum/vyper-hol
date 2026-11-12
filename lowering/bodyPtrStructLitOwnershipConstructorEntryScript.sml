Theory bodyPtrStructLitOwnershipConstructorEntry
Ancestors
  bodyPtrStructLitOwnershipConstructorRegistration bodyPtrStructLitOwnershipImmutable
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipControlFrame
  bodyPtrStructLitOwnershipLock bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps ctorRegisterShape loweringShapeProps
  loweringShapeDefs loweringShapeRules moduleLowering compileEnv context

Theorem structlit_cenv_ctor_exit_shape:
  cenv_shape_ok s ce /\ ce.ce_return_pc = NONE /\ jump_label_ok lbl ==>
  cenv_shape_ok s (ce with ce_ctor_exit_label := SOME lbl)
Proof
  strip_tac >> gvs[cenv_shape_ok_def] >> metis_tac[]
QED

Theorem alloc_run_constructor_immutable_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s)
    (if ilen > 0 then
       do r <- compile_fixed_region_with_id ilen; return (SND r).buf_operand od
     else return (Lit 0w))
    (\imm s. shape_state s /\ R s /\ plain_operand s imm)
Proof
  strip_tac >> IF_CASES_TAC >> simp[]
  >- (irule alloc_run_bind >>
      qexists `\r s. shape_state s /\ R s /\
        plain_operand s (SND r).buf_operand /\ fresh_outputs s` >>
      reverse conj_tac >- simp[alloc_run_fixed_region_frame] >>
      gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl, plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem alloc_run_constructor_registration_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_register_constructor_args ce args offset data_size)
    (\ce' s. shape_state s /\ R s /\ cenv_shape_ok s ce' /\
      ce'.ce_return_pc = ce.ce_return_pc /\
      ce'.ce_alloca_locals = ce.ce_alloca_locals)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_frame >>
  irule_at Any compile_register_constructor_args_shape >> simp[] >>
  irule_at Any alloc_run_compile_register_constructor_args_shape >>
  qexists `R` >> simp[]
QED

Theorem alloc_run_constructor_lock_label:
  ce.ce_return_pc = NONE ==>
  alloc_run (\s. shape_state s /\ plain_operand s imm /\ cenv_shape_ok s ce)
    (do (if nr then compile_nonreentrant_lock key tr F else return ());
        lbl <- fresh_label "ctor_exit"; return (imm,ce,lbl) od)
    (\(imm',ce',lbl) s. shape_state s /\ imm' = imm /\ ce' = ce /\
      plain_operand s imm /\ jump_label_ok lbl /\
      cenv_shape_ok s (ce' with ce_ctor_exit_label := SOME lbl))
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ (plain_operand s imm /\ cenv_shape_ok s ce)` >>
  reverse conj_tac
  >- (Cases_on `nr`
      >- (simp[] >> irule alloc_run_conseq >>
          irule_at Any alloc_run_nonreentrant_lock_frame >>
          qexists `\s. plain_operand s imm /\ cenv_shape_ok s ce` >>
          mp_tac (Q.INST [`ce` |-> `ce`] cenv_shape_ok_stable) >>
          simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\lbl s. shape_state s /\ (plain_operand s imm /\ cenv_shape_ok s ce) /\
    compiler_label lbl /\ label_sfx "ctor_exit" lbl` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_fresh_label_frame >>
      qexists `\s. plain_operand s imm /\ cenv_shape_ok s ce` >> simp[] >>
      mp_tac (Q.INST [`ce` |-> `ce`] cenv_shape_ok_stable) >>
          simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl,
    jump_label_ok_def] >> rpt strip_tac >>
  irule structlit_cenv_ctor_exit_shape >> simp[jump_label_ok_def]
QED

Theorem alloc_run_constructor_entry:
  cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals ==>
  alloc_run shape_state
    (do imm <- (if ilen > 0 then
           do r <- compile_fixed_region_with_id ilen; return (SND r).buf_operand od
         else return (Lit 0w));
        ce' <- compile_register_constructor_args
          (ce with ce_imm_alloca := (if ilen > 0 then SOME imm else NONE)) args 0 data_size;
        (if nr then compile_nonreentrant_lock key tr F else return ());
        lbl <- fresh_label "ctor_exit"; return (imm,ce',lbl) od)
    (\(imm,ce',lbl) s. shape_state s /\ plain_operand s imm /\ jump_label_ok lbl /\
      cenv_shape_ok s (ce' with ce_ctor_exit_label := SOME lbl) /\ ce'.ce_alloca_locals)
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\imm s. shape_state s /\ plain_operand s imm` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_constructor_immutable_frame >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\ce' s. shape_state s /\ plain_operand s v /\ cenv_shape_ok s ce' /\
    ce'.ce_return_pc = NONE /\ ce'.ce_alloca_locals` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_constructor_registration_frame >>
      qexists `\s. plain_operand s v` >>
      simp[shape_stable_def] >> conj_tac
      >- metis_tac[plain_operand_mono] >> rpt strip_tac >>
      irule cenv_shape_ok_install_imm_alloca >> simp[cenv_static_ok_shape_ok] >>
      Cases_on `ilen > 0` >> gvs[]) >>
  gen_tac >> simp[] >>
  mp_tac (Q.INST [`ce` |-> `v'`, `imm` |-> `v`, `nr` |-> `nr`,
    `key` |-> `key`, `tr` |-> `tr`] alloc_run_constructor_lock_label) >>
  simp[comp_ignore_bind_def, alloc_run_def] >> rpt strip_tac >>
  first_x_assum drule_all >> simp[] >>
  PairCases_on `v''` >> simp[] >> metis_tac[]
QED
