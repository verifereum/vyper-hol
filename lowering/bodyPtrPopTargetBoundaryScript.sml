Theory bodyPtrPopTargetBoundary
Ancestors bodyPtrPopPlaceBoundary bodyPtrPopMutualBoundary supportedStmts
  supportedTargets exprLowering emitHelper compileEnv bodyPtrPopCompilerBoundary
  bodyPtrPopMaterialization bodyPtrPopArithmeticBoundary venomInst

Theorem pop_target_info_subscript:
  supported_target_info tops bindings (SubscriptTarget bt key) = SOME pt ==>
  supported_expr tops key /\
  ?base_pt. supported_target_info tops bindings bt = SOME base_pt
Proof
  simp[supported_target_info_def] >>
  Cases_on `supported_expr tops key` >> simp[] >>
  Cases_on `supported_target_info tops bindings bt` >> simp[]
QED

Theorem pop_target_info_attribute:
  supported_target_info tops bindings (AttributeTarget bt fname) = SOME pt ==>
  ?base_pt. supported_target_info tops bindings bt = SOME base_pt
Proof
  simp[supported_target_info_def] >>
  Cases_on `supported_target_info tops bindings bt` >> simp[]
QED

Theorem pop_target_root_boundary:
  !bt. ((?name. bt = NameTarget name) \/
    (?id. bt = TopLevelNameTarget id)) /\
    pop_comp_boundary sa /\ compile_get_target_ptr cfn ce bt sa = (r,sb) ==>
    pop_comp_boundary sb
Proof
  Cases >> simp[] >> rpt strip_tac >>
  gvs[compile_get_target_ptr_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[comp_return_def])
QED

Theorem pop_get_target_ptr_boundary:
  (!ty e s v t. supported_expr tops e /\ pop_comp_boundary s /\
    cfn ce ty e s = (v,t) ==> pop_comp_boundary t) ==>
  !bt sa r sb. (supported_target tops bindings bt \/
    IS_SOME (supported_target_info tops bindings bt)) /\
    pop_comp_boundary sa /\
    compile_get_target_ptr cfn ce bt sa = (r,sb) ==> pop_comp_boundary sb
Proof
  strip_tac >>
  `(!e:expr. T) /\ !bt sa r sb.
    (supported_target tops bindings bt \/
      IS_SOME (supported_target_info tops bindings bt)) /\
    pop_comp_boundary sa /\
    compile_get_target_ptr cfn ce bt sa = (r,sb) ==> pop_comp_boundary sb`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_target_root_boundary >>
      disch_then irule >> simp[])
  >- (rpt strip_tac >>
      drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_target_root_boundary >>
      disch_then irule >> simp[])
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume pop_get_target_ptr_boundary[subscript]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `supported_expr tops e /\
    ((?id. bt = TopLevelNameTarget id) \/
     IS_SOME (supported_target_info tops bindings bt))` by
    (Cases_on `IS_SOME (supported_target_info tops bindings (SubscriptTarget bt e))`
     >- (Cases_on `supported_target_info tops bindings (SubscriptTarget bt e)` >>
         gvs[] >> drule pop_target_info_subscript >>
         strip_tac >> simp[]) >>
     gvs[] >> Cases_on `bt` >> gvs[supported_target_def]) >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once compile_get_target_ptr_def] >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[pop_target_root_boundary])) >>
  rpt strip_tac >>
  qpat_x_assum `!sa r sb. _` kall_tac >>
  Cases_on `SND (SND x)` >> gvs[] >>
  TRY (rename1 `SOME pt` >> Cases_on `pt` >> gvs[]) >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [gvs[comp_return_def] >> NO_TAC,
     (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
      disch_then irule >> simp[] >> rpt strip_tac >> first_x_assum drule_all >> simp[]),
     (drule_at (Pat `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`)
        pop_compile_array_subscript_boundary >> disch_then irule >> simp[] >>
      rpt strip_tac >> drule_all pop_ptr_load_boundary >> simp[]),
     (qpat_x_assum `(if guard then _ else _) _ = _` mp_tac >>
      IF_CASES_TAC >> simp[comp_return_def] >> strip_tac >> gvs[] >>
      drule_all pop_compile_keccak256_key_boundary >> simp[]),
     (drule_all pop_compile_mapping_subscript_boundary >> simp[])]
QED

Resume pop_get_target_ptr_boundary[attribute]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `(?id. bt = TopLevelNameTarget id) \/
     IS_SOME (supported_target_info tops bindings bt)` by
    (Cases_on `IS_SOME (supported_target_info tops bindings (AttributeTarget bt s))`
     >- (Cases_on `supported_target_info tops bindings (AttributeTarget bt s)` >>
         gvs[] >> drule pop_target_info_attribute >> strip_tac >> simp[]) >>
     gvs[] >> Cases_on `bt` >> gvs[supported_target_def]) >>
  qpat_x_assum `compile_get_target_ptr _ _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once compile_get_target_ptr_def] >> strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[pop_target_root_boundary])) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >>
  (conj_tac >- (rpt strip_tac >>
    drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >>
    disch_then irule >> simp[])) >>
  rpt strip_tac >> gvs[comp_return_def]
QED

Finalise pop_get_target_ptr_boundary

Theorem pop_compile_target_boundary:
  (supported_target tops bindings bt \/
   IS_SOME (supported_target_info tops bindings bt)) /\
  pop_comp_boundary sa /\
  compile_get_target_ptr compile_expr ce bt sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_get_target_ptr_boundary >>
  disch_then irule >> simp[] >> qexistsl [`bindings`, `tops`] >>
  simp[] >> rpt strip_tac >> drule_all pop_compile_supported_boundary >> simp[]
QED

Theorem pop_compile_aug_target_boundary:
  supported_aug_target tops bindings bt /\ pop_comp_boundary sa /\
  compile_get_target_ptr compile_expr ce bt sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`) pop_compile_target_boundary >>
  disch_then irule >> simp[] >> qexistsl [`bindings`, `tops`] >>
  disj2_tac >> Cases_on `supported_target_info tops bindings bt` >>
  gvs[supported_aug_target_def] >> Cases_on `x` >> gvs[]
QED
