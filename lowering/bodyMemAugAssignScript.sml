(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   augmented assignment.  The same split as S1's body_augassign_case, each
   subcase in its own bodyMemAugAssign* leaf. *)
Theory bodyMemAugAssign
Ancestors
  bodyMemoryPreds
  bodyMemAugAssignLocal bodyMemAugAssignTopWord bodyMemAugAssignAttrLocal
  bodyMemAugAssignAttrStorage bodyMemAugAssignOther

Theorem body_augassign_mem_case:
  !cx ty t bop e.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\ body_base_target_mem_ok cx t ==>
    body_stmt_mem_ok cx (AugAssign ty t bop e)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?id. t = NameTarget id`
  >- (pop_assum strip_assume_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_augassign_local_mem >> simp[]) >>
  Cases_on `?nsid. t = TopLevelNameTarget nsid /\
                   supported_scalar_target tops nsid`
  >- (pop_assum strip_assume_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
      PairCases_on `nsid` >>
      drule_all body_augassign_toplevel_word_mem >> simp[]) >>
  Cases_on `?id fld. t = AttributeTarget (NameTarget id) fld`
  >- (pop_assum strip_assume_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
      drule_all body_augassign_attr_local_mem >> simp[]) >>
  Cases_on `?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                       supported_storage_field_write tops nsid fld`
  >- (pop_assum strip_assume_tac >> qpat_x_assum `t = _` SUBST_ALL_TAC >>
      PairCases_on `nsid` >>
      drule_all body_augassign_attr_storage_mem >> simp[]) >>
  drule_all body_augassign_other_mem >> simp[]
QED
