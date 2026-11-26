(* Local-name target preparation for the ordinary AugAssign route. *)
Theory s1PrefixAugAssignNameTarget
Ancestors
  augAssignFullTargetRoutes targetPlaceSim bodyPtrPopTargetFragTransport
  s1PrefixFrame vyperEvalMisc vyperPlaceFrames vyperStorageTrace vyperInterpreter
  vyperState

Theorem augassign_name_target_prefix_entry:
  supported_stmt tops bindings (AugAssign aty (NameTarget id) bop e) ==>
  (?pt. supported_target_info tops bindings (NameTarget id) = SOME pt) /\
  ~immutable_root cx (NameTarget id) /\
  (!st0 es s G tn. ~s.vs_halted ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_target_place cx (NameTarget id)) (es,s,G,tn))
Proof
  strip_tac >> simp[immutable_root_def,target_root_def] >>
  conj_tac >- metis_tac[augassign_name_target_info] >>
  rpt strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame] >>
  rpt gen_tac >> rewrite_tac[eval_target_place_as_bind] >>
  Cases_on `eval_base_place cx (NameTarget id) (es with gas_obs := gobs)` >>
  drule_then SUBST_ALL_TAC eval_base_place_NameTarget_preserves_state >>
  Cases_on `q` >> simp[bind_def] >-
    (strip_tac >> drule_then SUBST_ALL_TAC get_place_state >> simp[]) >>
  strip_tac >> gvs[]
QED
