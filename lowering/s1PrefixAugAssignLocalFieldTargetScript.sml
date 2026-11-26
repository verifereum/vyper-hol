Theory s1PrefixAugAssignLocalFieldTarget
Ancestors
  bodyAugPlaceTarget targetPlaceSim s1PrefixFrame
  vyperInterpreter vyperState vyperStorageTrace vyperEvalMisc
  vyperPlaceFrames vyperProtectedImmutableFrame list

Theorem eval_target_local_field_state[local]:
  eval_target_place cx (AttributeTarget (NameTarget id) fld) st = (res,st') ==>
  st' = st
Proof
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  Cases_on `eval_base_place cx (NameTarget id) st` >>
  drule_then SUBST_ALL_TAC eval_base_place_NameTarget_preserves_state >>
  rename1 `eval_base_place cx (NameTarget id) st = (ans,st)` >>
  Cases_on `ans` >> simp[bind_def] >>
  drule_then SUBST_ALL_TAC eval_name_target_memory_root >>
  Cases_on `extend_place cx (PlaceR (MemoryPlace id [])) (AttrSubscript fld) st` >>
  drule_then SUBST_ALL_TAC extend_place_PlaceR_state >>
  rename1 `extend_place _ _ _ st = (ans,st)` >>
  Cases_on `ans` >> simp[bind_def] >>
  metis_tac[get_place_state]
QED

Theorem augassign_local_field_target_prefix_entry:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) ==>
  (?pt. supported_target_info tops bindings (AttributeTarget (NameTarget id) fld) = SOME pt) /\
  ~immutable_root cx (AttributeTarget (NameTarget id) fld) /\
  !P st0 es s G tn. ~s.vs_halted ==>
    gas_prefix_full P cx st0 (eval_target_place cx (AttributeTarget (NameTarget id) fld))
      (es,s,G,tn)
Proof
  strip_tac >> conj_tac
  >- (irule aug_place_supported_stmt_target_info >>
      qpat_assum `supported_stmt _ _ _` (irule_at Any) >>
      qpat_assum `body_inv _ _ _ _` (irule_at Any) >> simp[]) >>
  simp[immutable_root_def,target_root_def] >> rpt strip_tac >>
  irule gas_prefix_full_no_outcome >> simp[evaluate_storage_trace_frame] >>
  rpt strip_tac >> drule_then SUBST_ALL_TAC eval_target_local_field_state >> simp[]
QED
