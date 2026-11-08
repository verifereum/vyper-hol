(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   assignment to a tuple target.  As S1's body_assign_tuple_case: a widened
   right-hand side (bodyMemAssignTupleWidened), a tuple of locals
   (bodyMemAssignTupleLocals), of local, scalar toplevel and storage
   word-field targets (bodyMemAssignTupleTargets), and the rest
   (bodyMemAssignTupleOther). *)
Theory bodyMemAssignTuple
Ancestors
  bodyMemoryPreds bodyMemAssignTupleLocals bodyMemAssignTupleTargets
  bodyMemAssignTupleOther bodyMemAssignTupleWidened

Theorem body_assign_tuple_mem_case:
  !cx gs e.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_mem_ok cx (TupleTarget gs) v) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (Assign (TupleTarget gs) e)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- suspend "same" >>
  Cases_on `EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                                FLOOKUP env.var_types id = SOME ty /\
                                0 < type_memory_bytes cenv ty) \/
                       (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                               supported_scalar_target tops nsid) \/
                       (?nsid fld fty.
                          g = BaseTarget
                                (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                          supported_storage_field_write tops nsid fld /\
                          type_place_target env
                            (AttributeTarget (TopLevelNameTarget nsid) fld) =
                            SOME (Type fty) /\ is_word_type fty)) gs`
  >- (drule_all body_assign_tuple_widened_call_mem >> simp[]) >>
  drule_all body_assign_tuple_widened_other_mem >> simp[]
QED

Resume body_assign_tuple_mem_case[same]:
  Cases_on `?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
                  EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids`
  >- (pop_assum (REPEAT_TCL CHOOSE_THEN (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qpat_x_assum `gs = _` SUBST_ALL_TAC >>
      drule_all body_assign_tuple_locals_mem >> simp[]) >>
  Cases_on `EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                                FLOOKUP env.var_types id = SOME ty /\
                                0 < type_memory_bytes cenv ty) \/
                       (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                               supported_scalar_target tops nsid) \/
                       (?nsid fld fty.
                          g = BaseTarget
                                (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                          supported_storage_field_write tops nsid fld /\
                          type_place_target env
                            (AttributeTarget (TopLevelNameTarget nsid) fld) =
                            SOME (Type fty) /\ is_word_type fty)) gs`
  >- (drule_all body_assign_tuple_targets_mem >> simp[]) >>
  drule_all body_assign_tuple_other_mem >> simp[]
QED

Finalise body_assign_tuple_mem_case
