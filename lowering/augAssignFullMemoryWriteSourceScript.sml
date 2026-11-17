(* The source memory write and its concrete all-horizon machine relation. *)
Theory augAssignFullMemoryWriteSource
Ancestors
  bodySimAugPlaceStore stmtSimAugAssignPlaceMemory exprLoweringProps
  gasOutcomeFull

Theorem augassign_memory_write_source_joint:
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) a
    (SOME LocMemory) (Type ty) /\
  store_lays_out etv ptv v /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv v /\
  write_place cx (MemoryPlace id path) v es = (res,es') /\
  stmt_res_ok lctx res /\
  u = (mstore (w2n a) (typed_val_to_w256 etv v) s with vs_inst_idx := pc) /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s) ==>
  res = INL () /\
  (!H. valid_horizon cx st0 H es'.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es' u)
Proof
  strip_tac >>
  `res = INL ()` by (irule aug_place_memory_write_success >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
  irule aug_place_memory_write_state_rel >> metis_tac[]
QED
