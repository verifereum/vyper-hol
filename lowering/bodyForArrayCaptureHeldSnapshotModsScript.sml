(* Recover the selected memory place from the typed source run. *)
Theory bodyForArrayCaptureHeldSnapshotMods
Ancestors
  bodyForArrayHeldInstallRouteMods bodyForArrayInstallBackingMods
  exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalStoragePreservation vyperTypeInvariants vyperTypeValues
  vyperTypeExprSoundness

Theorem held_capture_place_type[local]:
  expr_body_pre_mods mods c cx env e start /\
  eval_expr cx e start = (INL (PlaceR (MemoryPlace name path)),em) /\
  expr_type e = ArrayT sty bd /\
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) ==>
  runtime_place_typed cx em (MemoryPlace name path) (ArrayTV tv bd)
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_all_then strip_assume_tac eval_expr_success_storage_facts >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_consistent_def,env_consistent_def,env_context_consistent_def] >>
  qpat_x_assum `eval_result_typed _ _ _` mp_tac >>
  simp[eval_result_typed_def]
QED

Theorem for_array_capture_held_snapshot_mods:
  expr_body_pre_mods mods c cx env e start /\
  eval_expr cx e start = (INL (PlaceR (MemoryPlace name path)),em) /\
  expr_type e = ArrayT sty bd /\
  expr_sim_inv_mods mods c cx env em /\
  evaluate_type (get_tenv cx) (ArrayT sty bd) = SOME (ArrayTV tv bd) /\
  vv_post_mods H ctx func c cx e es sa0 sbExpr s0 em
    (PlaceR (MemoryPlace name path)) (LocatedValue ann p) r /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  read_result cx (PlaceR (MemoryPlace name path)) em = (INL (ArrayV av),em) /\
  array_length_frame sbExpr r Gr traw z Gz tz /\
  local_ptrs_reserved c sbExpr /\ local_ptrs_reserved c saL /\
  copy_old_operand sbExpr p.ptr_operand /\ copy_old_operand saL p.ptr_operand /\
  eval_operand p.ptr_operand z = SOME a /\
  ptr_mem_ok cx (ArrayT sty bd) (ArrayV av) p.ptr_operand Gz tz z /\
  (0 < type_memory_size (ArrayTV tv bd) ==>
   w2n a + type_memory_size (ArrayTV tv bd) <= z.vs_alloca_next) /\
  for_array_install_frame_mods saL z Gz tz G' tn' t ==>
  for_array_entry_route_mods c cx lo (sty,bd,LocMemory) (em,sbExpr,z,Gz,tz)
    (p.ptr_operand,a) vs (ForArrayHeld name path av) hor vs em G' tn' t
Proof
  strip_tac >>
  drule_all_then assume_tac held_capture_place_type >>
  `evaluate_type (get_tenv cx) sty = SOME tv` by
    (drule evaluate_type_ArrayT_cases >> simp[]) >>
  drule_all_then assume_tac for_array_install_backing_mods >>
  drule_all_then MATCH_ACCEPT_TAC for_array_held_install_route_mods
QED
