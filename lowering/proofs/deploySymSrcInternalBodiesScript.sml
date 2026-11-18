Theory deploySymSrcInternalBodies
Ancestors
  deploySymSrcHistory runtimeSymSrcFunctionLists runtimeSymSrcPackageTransport
  runtimeSymSrcInstructions compileVyper moduleLowering compileEnv loweringShapeDefs list

Theorem deploy_sym_classified_internal_bodies_cond:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\ ~program_reads_self_code tops /\
  (!ce bindings body ret params rb nr key tr view ct len s u s'.
     runtime_sym_env tops ce /\ supported_stmts tops bindings body /\
     ~supported_stmts_expr_exists is_self_code body /\
     EVERY deploy_sym_inst (state_insts s) /\ s.cs_current_insts = [] /\
     compile_internal_function ce params rb nr key tr view ct len body ret s = (u,s') ==>
     EVERY deploy_sym_inst (state_insts s')) ==>
  !s u s'. EVERY deploy_sym_inst (state_insts s) /\
    compile_internal_fn_bodies
      (MAP (set_internal_package_target target o
         package_internal_fn tops trans keys ctor imm)
         (order_internals names (FST (SND (classify_functions tops))))) s = (u,s') ==>
    EVERY deploy_sym_inst (state_insts s')
Proof
  strip_tac >> match_mp_tac runtime_sym_internal_fn_bodies >>
  rpt gen_tac >> strip_tac >> gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  qpat_x_assum `(_,_,_,_,_,_,_,_,_,_,_,_) = _` (assume_tac o SYM) >>
  drule_all runtime_sym_internal_source >> strip_tac >>
  drule runtime_sym_internal_package_fields >> strip_tac >> gvs[] >>
  drule_all runtime_sym_internal_environment >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >> simp[]
QED
