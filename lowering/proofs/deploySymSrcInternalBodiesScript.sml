Theory deploySymSrcInternalBodies
Ancestors
  deploySymSrcHistory runtimeSymSrcEmissionProbe runtimeSymSrcPackageTransport
  runtimeSymSrcInstructions moduleLowering compileEnv loweringShapeDefs list

Theorem deploy_sym_internal_fn_bodies_cond:
  !xs.
    (!lbl ce params rb nr key trans view ctor len body rt s u s'.
       MEM (lbl,ce,params,rb,nr,key,trans,view,ctor,len,body,rt) xs /\
       EVERY deploy_sym_inst (state_insts s) /\ s.cs_current_insts = [] /\
       compile_internal_function ce params rb nr key trans view ctor len body rt s = (u,s') ==>
       EVERY deploy_sym_inst (state_insts s')) ==>
    !s u s'. EVERY deploy_sym_inst (state_insts s) /\
      compile_internal_fn_bodies xs s = (u,s') ==>
      EVERY deploy_sym_inst (state_insts s')
Proof
  Induct
  >- simp[compile_internal_fn_bodies_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `EVERY deploy_sym_inst (state_insts cs')` by
    (mp_tac (runtime_sym_new_block |> Q.INST [`label` |-> `h0`, `st` |-> `s`]) >> simp[]) >>
  `cs'.cs_current_insts = []` by
    (qpat_x_assum `new_block _ _ = _` mp_tac >> simp[new_block_def] >>
     strip_tac >> pop_assum (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `!lbl ce params rb nr key trans view ctor len body rt s s'. _`
    (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!lbl. _` (qspec_then `h0` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `_ ==> !s s'. _` mp_tac >>
  impl_tac
  >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  disch_then drule_all >> simp[]
QED

Theorem deploy_sym_classified_internal_bodies_cond:
  supported_program tops /\ ~program_reads_self_code tops /\
  (!ce bindings body ret params rb nr key tr view ct len s u s'.
     runtime_sym_env ce /\ supported_stmts tops bindings body /\
     ~supported_stmts_expr_exists is_self_code body /\
     EVERY deploy_sym_inst (state_insts s) /\ s.cs_current_insts = [] /\
     compile_internal_function ce params rb nr key tr view ct len body ret s = (u,s') ==>
     EVERY deploy_sym_inst (state_insts s')) ==>
  !s u s'. EVERY deploy_sym_inst (state_insts s) /\
    compile_internal_fn_bodies
      (MAP (set_internal_package_target target o
         package_internal_fn tops trans keys ctor imm)
         (FST (SND (classify_functions tops)))) s = (u,s') ==>
    EVERY deploy_sym_inst (state_insts s')
Proof
  strip_tac >> match_mp_tac deploy_sym_internal_fn_bodies_cond >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  qpat_x_assum `(_,_,_,_,_,_,_,_,_,_,_,_) = _` (assume_tac o SYM) >>
  drule_all runtime_sym_internal_source >> strip_tac >>
  drule runtime_sym_internal_package_fields >> strip_tac >> gvs[] >>
  drule runtime_sym_internal_environment >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED
