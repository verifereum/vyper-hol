Theory augAssignFullImmutableWriteSource
Ancestors
  bodyImmutableAugAssignStore bodyFullPreds exprLoweringProps

Theorem augassign_immutable_write_source_joint:
  body_inv tops ctx cenv cx /\ cx.in_deploy /\
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (cenv.ce_module,id) = SOME ty /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  value_has_type tv v /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables cenv.ce_module imms) id = SOME (tv,old) /\
  write_place cx (ImmutablePlace cenv.ce_module id []) v es = (res,es') /\
  u = (mstore off (typed_val_to_w256 tv v) s with vs_inst_idx := pc) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s)
  ==>
  res = INL () /\
  es' = (es with immutables :=
    (cx.txn.target,update_immutable cenv.ce_module id tv v imms)::
      ADELKEY cx.txn.target es.immutables) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es' u) /\
  val_in_memory tv v off u.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) u.vs_memory)
Proof
  strip_tac >>
  drule_all immutable_augassign_write_source >> strip_tac >> gvs[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!H. _` (drule_then assume_tac) >>
      simp[stmt_state_rel_inst_idx] >>
      irule immutable_augassign_store >> metis_tac[]) >>
  simp[] >> metis_tac[immutable_augassign_word_representation]
QED
