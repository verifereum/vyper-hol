(* Legacy statement helper migration: stale pointer declarations remain here. *)
Theory bodyIntCallStmtHelperLabels
Ancestors
  bodyIntCallStmtHelperSoundLabels

Theorem compiler_block_tail_target_name:
  compiler_block_tail (compile_get_target_ptr ce (NameTarget id))
Proof
  simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_block_tail_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_target_top:
  compiler_block_tail (compile_get_target_ptr ce (TopLevelNameTarget nsid))
Proof
  simp[compile_get_target_ptr_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[compiler_block_tail_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_target_attribute:
  compiler_block_tail (compile_get_target_ptr ce bt) ==>
  compiler_block_tail (compile_get_target_ptr ce (AttributeTarget bt fname))
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]
QED

Theorem compiler_block_tail_target_subscript:
  compiler_block_tail (compile_get_target_ptr ce bt) /\
  compiler_block_tail (lower_value compile_expr ce (expr_type e) e) ==>
  compiler_block_tail (compile_get_target_ptr ce (SubscriptTarget bt e))
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  rename1 `SND (SND result)` >> Cases_on `SND (SND result)` >> simp[]
  >- suspend "array" >>
  rename1 `SND (SND result) = SOME place` >> Cases_on `place` >> simp[]
  >- suspend "map" >> suspend "array_value"
QED

Resume compiler_block_tail_target_subscript[array]:
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_array_subscript >> simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Resume compiler_block_tail_target_subscript[map]:
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_block_tail_mapping_helpers, compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_mapping_helpers, compiler_block_tail_primitives]
QED

Resume compiler_block_tail_target_subscript[array_value]:
  irule compiler_block_tail_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >> reverse conj_tac
  >- (irule compiler_block_tail_array_subscript >> simp[compiler_block_tail_primitives]) >>
  simp[compiler_block_tail_primitives]
QED

Finalise compiler_block_tail_target_subscript

Theorem compiler_label_hoare_target_name:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (NameTarget id))
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_target_top:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (TopLevelNameTarget nsid))
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[compile_get_target_ptr_def, LET_THM] >>
  Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[compiler_label_hoare_typed_primitives] >>
  rename1 `FLOOKUP _ _ = SOME loc` >> Cases_on `loc` >> simp[compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_target_attribute:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt) (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (AttributeTarget bt fname))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_context_primitives, compiler_label_hoare_typed_primitives]
QED

Theorem compiler_label_hoare_target_subscript:
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt) (\r out. compiler_label_reservation origin pending out) /\
  compiler_label_hoare (compiler_label_reservation origin pending)
    (lower_value compile_expr ce (expr_type e) e)
    (\r out. compiler_label_reservation origin pending out) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce (SubscriptTarget bt e))
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[Once compile_get_target_ptr_def] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> simp[LET_THM] >>
  rename1 `SND (SND result)` >> Cases_on `SND (SND result)` >> simp[]
  >- suspend "array" >>
  rename1 `SND (SND result) = SOME place` >> Cases_on `place` >> simp[]
  >- suspend "map" >> suspend "array_value"
QED

Resume compiler_label_hoare_target_subscript[array]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_array_subscript >> simp[compiler_label_hoare_context_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Resume compiler_label_hoare_target_subscript[map]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_label_hoare_mapping_helpers, compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_mapping_helpers, compiler_label_hoare_typed_primitives]
QED

Resume compiler_label_hoare_target_subscript[array_value]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (irule compiler_label_hoare_array_subscript >> simp[compiler_label_hoare_context_primitives]) >>
  simp[compiler_label_hoare_typed_primitives]
QED

Finalise compiler_label_hoare_target_subscript

Theorem compiler_block_tail_target_info:
  !target ce pt.
    supportedTargets$supported_target_info tops bindings target = SOME pt /\
    ~supportedExprTraverse$target_has_internal_call target ==>
    compiler_block_tail (compile_get_target_ptr ce target)
Proof
  `((!e:expr. T) /\ (!target. !ce pt.
      supportedTargets$supported_target_info tops bindings target = SOME pt /\
      ~supportedExprTraverse$target_has_internal_call target ==>
      compiler_block_tail (compile_get_target_ptr ce target)))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- simp[compiler_block_tail_target_name]
  >- simp[compiler_block_tail_target_top]
  >- (drule_all supported_target_info_subscript_expr >> strip_tac >>
      irule compiler_block_tail_target_subscript >> reverse conj_tac
      >- (gvs[supportedExprTraverseTheory.target_has_internal_call_def,
              supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]) >>
      irule compiler_block_tail_lower_value >>
      metis_tac[compiler_block_tail_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  drule supported_target_info_attribute_target_base >> strip_tac >>
  irule compiler_block_tail_target_attribute >>
  gvs[supportedExprTraverseTheory.target_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]
QED

Theorem compiler_label_hoare_target_info:
  !target ce pt origin pending.
    supportedTargets$supported_target_info tops bindings target = SOME pt /\
    ~supportedExprTraverse$target_has_internal_call target ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_get_target_ptr ce target)
      (\r out. compiler_label_reservation origin pending out)
Proof
  `((!e:expr. T) /\ (!target. !ce pt origin pending.
      supportedTargets$supported_target_info tops bindings target = SOME pt /\
      ~supportedExprTraverse$target_has_internal_call target ==>
      compiler_label_hoare (compiler_label_reservation origin pending)
        (compile_get_target_ptr ce target)
        (\r out. compiler_label_reservation origin pending out)))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- simp[compiler_label_hoare_target_name]
  >- simp[compiler_label_hoare_target_top]
  >- (drule_all supported_target_info_subscript_expr >> strip_tac >>
      irule compiler_label_hoare_target_subscript >> reverse conj_tac
      >- (gvs[supportedExprTraverseTheory.target_has_internal_call_def,
              supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]) >>
      irule compiler_label_hoare_lower_value >>
      metis_tac[compiler_label_hoare_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  drule supported_target_info_attribute_target_base >> strip_tac >>
  irule compiler_label_hoare_target_attribute >>
  gvs[supportedExprTraverseTheory.target_has_internal_call_def,
      supportedExprTraverseTheory.supported_expr_exists_def] >> metis_tac[]
QED

Theorem compiler_block_tail_supported_target:
  supportedStmts$supported_target tops bindings target /\
  ~supportedExprTraverse$target_has_internal_call target ==>
  compiler_block_tail (compile_get_target_ptr ce target)
Proof
  Cases_on `target` >>
  simp[compiler_block_tail_target_name, compiler_block_tail_target_top] >>
  rename1 `supported_target tops bindings (_ bt _)` >> Cases_on `bt` >>
  simp[supportedStmtsTheory.supported_target_def] >> rpt strip_tac
  >- (irule compiler_block_tail_target_subscript >> reverse conj_tac
      >- simp[compiler_block_tail_target_top] >>
      irule compiler_block_tail_lower_value >>
      gvs[supportedExprTraverseTheory.target_has_internal_call_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          GSYM supportedExprTraverseTheory.expr_has_internal_call_def] >>
      metis_tac[compiler_block_tail_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  irule compiler_block_tail_target_attribute >> simp[compiler_block_tail_target_top]
QED

Theorem compiler_label_hoare_supported_target:
  supportedStmts$supported_target tops bindings target /\
  ~supportedExprTraverse$target_has_internal_call target ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce target)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `target` >>
  simp[compiler_label_hoare_target_name, compiler_label_hoare_target_top] >>
  rename1 `supported_target tops bindings (_ bt _)` >> Cases_on `bt` >>
  simp[supportedStmtsTheory.supported_target_def] >> rpt strip_tac
  >- (irule compiler_label_hoare_target_subscript >> reverse conj_tac
      >- simp[compiler_label_hoare_target_top] >>
      irule compiler_label_hoare_lower_value >>
      gvs[supportedExprTraverseTheory.target_has_internal_call_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          GSYM supportedExprTraverseTheory.expr_has_internal_call_def] >>
      metis_tac[compiler_label_hoare_supported_expr, supportedExprsTheory.supported_expr_def]) >>
  irule compiler_label_hoare_target_attribute >> simp[compiler_label_hoare_target_top]
QED

Theorem compiler_block_tail_tuple_store_all:
  !tys targets vals.
    (!bt. MEM (BaseTarget bt) targets ==>
      compiler_block_tail (compile_get_target_ptr ce bt)) ==>
    compiler_block_tail (compile_tuple_store_all ce tys targets vals)
Proof
  Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, compiler_block_tail_primitives] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def, LET_THM] >> rpt strip_tac
  >- suspend "base" >>
  irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives] >>
  metis_tac[MEM]
QED

Resume compiler_block_tail_tuple_store_all[base]:
  irule compiler_block_tail_bind >> reverse conj_tac >- metis_tac[MEM] >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind, LET_THM] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[compiler_block_tail_store_at_loc, compiler_block_tail_assign_value,
           compiler_block_tail_primitives]) >>
  metis_tac[MEM]
QED

Finalise compiler_block_tail_tuple_store_all

Theorem compiler_label_hoare_tuple_store_all:
  !tys targets vals.
    (!bt. MEM (BaseTarget bt) targets ==>
      compiler_label_hoare (compiler_label_reservation origin pending)
        (compile_get_target_ptr ce bt)
        (\r out. compiler_label_reservation origin pending out)) ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_tuple_store_all ce tys targets vals)
      (\r out. compiler_label_reservation origin pending out)
Proof
  Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[compile_tuple_store_all_def, compiler_label_hoare_typed_primitives] >>
  rename1 `target::targets` >> Cases_on `target` >>
  simp[compile_tuple_store_all_def, comp_ignore_bind_def, LET_THM] >> rpt strip_tac
  >- suspend "base" >>
  irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_typed_primitives] >>
  metis_tac[MEM]
QED

Resume compiler_label_hoare_tuple_store_all[base]:
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac >- metis_tac[MEM] >>
  gen_tac >> BETA_TAC >> simp[tuple_comp_return_bind, LET_THM] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (rpt IF_CASES_TAC >>
      simp[compiler_label_hoare_store_at_loc, compiler_label_hoare_assign_value,
           compiler_label_hoare_typed_primitives]) >>
  metis_tac[MEM]
QED

Finalise compiler_label_hoare_tuple_store_all

Theorem compiler_block_tail_tuple_unpack:
  (!bt. MEM (BaseTarget bt) targets ==>
    compiler_block_tail (compile_get_target_ptr ce bt)) ==>
  compiler_block_tail (compile_tuple_unpack ce ty may_stage targets src_op)
Proof
  strip_tac >> simp[compile_tuple_unpack_def, LET_THM] >>
  IF_CASES_TAC >> simp[compiler_block_tail_primitives] >>
  irule compiler_block_tail_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_block_tail_primitives, comp_ignore_bind_def] >>
      irule compiler_block_tail_bind >>
      simp[compiler_block_tail_primitives, compiler_block_tail_alloc_buffer,
           tuple_comp_return_bind] >>
      gen_tac >> irule compiler_block_tail_bind >> simp[compiler_block_tail_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_block_tail_bind >>
  simp[compiler_block_tail_tuple_load_all, compiler_block_tail_tuple_store_all]
QED

Theorem compiler_label_hoare_tuple_unpack:
  (!bt. MEM (BaseTarget bt) targets ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_get_target_ptr ce bt)
      (\r out. compiler_label_reservation origin pending out)) ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_tuple_unpack ce ty may_stage targets src_op)
    (\r out. compiler_label_reservation origin pending out)
Proof
  strip_tac >> simp[compile_tuple_unpack_def, LET_THM] >>
  IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives,
                        compiler_label_hoare_context_primitives] >>
  irule compiler_label_hoare_preserving_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[compiler_label_hoare_typed_primitives, comp_ignore_bind_def] >>
      irule compiler_label_hoare_preserving_bind >>
      simp[compiler_label_hoare_typed_primitives, compiler_label_hoare_alloc_buffer,
           tuple_comp_return_bind] >>
      gen_tac >> irule compiler_label_hoare_preserving_bind >> simp[compiler_label_hoare_typed_primitives]) >>
  gen_tac >> BETA_TAC >> irule compiler_label_hoare_preserving_bind >>
  simp[compiler_label_hoare_tuple_load_all, compiler_label_hoare_tuple_store_all]
QED

Theorem compiler_block_tail_assign_base_target:
  supported_assignment tops bindings (BaseTarget bt) e /\
  ~target_has_internal_call bt ==>
  compiler_block_tail (compile_get_target_ptr ce bt)
Proof
  simp[supported_assignment_def] >> strip_tac
  >- metis_tac[compiler_block_tail_supported_target] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
  metis_tac[compiler_block_tail_target_info]
QED

Theorem compiler_label_hoare_assign_base_target:
  supported_assignment tops bindings (BaseTarget bt) e /\
  ~target_has_internal_call bt ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[supported_assignment_def] >> strip_tac
  >- metis_tac[compiler_label_hoare_supported_target] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
  metis_tac[compiler_label_hoare_target_info]
QED


Theorem compiler_label_hoare_target_info_general:
  !target ce pt origin pending.
    supportedTargets$supported_target_info tops bindings target = SOME pt ==>
    compiler_label_hoare (compiler_label_reservation origin pending)
      (compile_get_target_ptr ce target)
      (\r out. compiler_label_reservation origin pending out)
Proof
  `((!e:expr. T) /\ (!target. !ce pt origin pending.
      supportedTargets$supported_target_info tops bindings target = SOME pt ==>
      compiler_label_hoare (compiler_label_reservation origin pending)
        (compile_get_target_ptr ce target)
        (\r out. compiler_label_reservation origin pending out)))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt strip_tac
  >- simp[compiler_label_hoare_target_name]
  >- simp[compiler_label_hoare_target_top]
  >- (gvs[supportedTargetsTheory.supported_target_info_def, AllCaseEqs()] >>
      (irule compiler_label_hoare_target_subscript >> reverse conj_tac
       >- metis_tac[] >>
       irule compiler_label_hoare_lower_value >>
       metis_tac[compiler_label_hoare_supported_expr_general, supported_expr_def])) >>
  drule supported_target_info_attribute_target_base >> strip_tac >>
  irule compiler_label_hoare_target_attribute >> metis_tac[]
QED

Theorem compiler_label_hoare_supported_target_general:
  supportedStmts$supported_target tops bindings target ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce target)
    (\r out. compiler_label_reservation origin pending out)
Proof
  Cases_on `target` >>
  simp[compiler_label_hoare_target_name, compiler_label_hoare_target_top] >>
  rename1 `supported_target tops bindings (_ bt _)` >> Cases_on `bt` >>
  simp[supportedStmtsTheory.supported_target_def] >> rpt strip_tac
  >- (irule compiler_label_hoare_target_subscript >> reverse conj_tac
      >- simp[compiler_label_hoare_target_top] >>
      irule compiler_label_hoare_lower_value >>
      metis_tac[compiler_label_hoare_supported_expr_general, supported_expr_def]) >>
  irule compiler_label_hoare_target_attribute >> simp[compiler_label_hoare_target_top]
QED

Theorem compiler_label_hoare_assign_base_target_general:
  supported_assignment tops bindings (BaseTarget bt) e ==>
  compiler_label_hoare (compiler_label_reservation origin pending)
    (compile_get_target_ptr ce bt)
    (\r out. compiler_label_reservation origin pending out)
Proof
  simp[supported_assignment_def] >> strip_tac
  >- metis_tac[compiler_label_hoare_supported_target_general] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  rename1 `supported_target_info _ _ _ = SOME pt` >> Cases_on `pt` >> gvs[] >>
  metis_tac[compiler_label_hoare_target_info_general]
QED

