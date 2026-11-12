Theory ctorDeployMemoryRunMemEntrySourceDefaults
Ancestors
  ctorDeployLoweringNoCtor ctorDeployLoweringFrame
  ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs
  vyperInterpreter vyperState vyperContext compileEnv

Theorem ctor_source_send_value_immutables:
  send_call_value mut cx s = (INL (),s') ==> s'.immutables = s.immutables
Proof
  simp[send_call_value_def, transfer_value_def, COND_RATOR,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.update_accounts_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ctor_source_start_immutables:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  es0.immutables = am_c.immutables
Proof
  strip_tac >>
  `~nr` by (drule_all deploy_ctor_not_nonreentrant >> simp[]) >>
  gvs[deploy_ctor_start_def, lock_if_nr_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  drule ctor_source_send_value_immutables >> simp[initial_state_def]
QED

Theorem ctor_source_start_default_lookup:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  ?tv. FLOOKUP (get_source_immutables NONE
          (case ALOOKUP es0.immutables tx.target of SOME m => m | NONE => []))
         name = SOME (tv,default_value tv) /\
       evaluate_type (type_env tops) ty = SOME tv /\
       type_memory_size tv =
         type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty
Proof
  strip_tac >>
  drule_all ctor_source_start_immutables >> strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    gvs[deploy_source_ok_def, deploy_typing_ok_def] >>
  pop_assum strip_assume_tac >>
  gvs[deploy_ctor_start_def] >>
  drule_all no_ctor_checked_initial_lookup >> strip_tac >>
  `v = default_value tv` by metis_tac[no_ctor_initial_defaults] >>
  gvs[] >>
  reverse conj_tac >- metis_tac[no_ctor_checked_type_size] >>
  simp[] >>
  irule no_ctor_constants_preserve_lookup >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_source_start_default_present:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  ?imms tv.
    ALOOKUP es0.immutables tx.target = SOME imms /\
    FLOOKUP (get_source_immutables NONE imms) name =
      SOME (tv,default_value tv) /\
    evaluate_type (type_env tops) ty = SOME tv /\
    type_memory_size tv =
      type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty
Proof
  strip_tac >> drule_all ctor_source_start_default_lookup >> strip_tac >>
  Cases_on `ALOOKUP es0.immutables tx.target` >>
  gvs[get_source_immutables_def]
QED

Theorem ctor_source_start_immutable_default:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  ALOOKUP es0.immutables tx.target = SOME imms /\
  FLOOKUP (get_source_immutables NONE imms) name = SOME (tv,v) ==>
  v = default_value tv /\
  evaluate_type (type_env tops) ty = SOME tv /\
  type_memory_size tv =
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty
Proof
  strip_tac >> drule_all ctor_source_start_default_lookup >> simp[]
QED
