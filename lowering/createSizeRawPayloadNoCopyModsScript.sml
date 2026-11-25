(* A nonword raw payload can be kept when its suffix cannot mutate it. *)
Theory createSizeRawPayloadNoCopyMods
Ancestors
  createCtorSnapshotTypingMods exprBodyPreProps exprSimHypsDefs
  exprReasonOperand exprLowering compileEnv context

Theorem raw_payload_snapshot_no_copy_static_mods:
  compile_expr ce (expr_type e) e ca = (v,cm) /\
  expr_body_pre_mods mods ce cx env e p /\
  ~exprs_can_mutate ce rest /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_snapshot_vv ce (exprs_can_mutate ce rest)
    (ext_call_arg_value (lowered_value_type ce e) v) cm = (saved,cn) ==>
  cm = cn
Proof
  strip_tac >>
  `~is_word_type (expr_type e)` by
    (drule ctor_snapshot_word_types_mods >> simp[]) >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     conj_tac
     >- (drule expr_body_pre_mods_inv >> simp[expr_sim_inv_mods_def])
     >> metis_tac[expr_body_pre_mods_well_typed]) >>
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) v))` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `v` >>
     gvs[reason_result_shape_def, ext_call_arg_value_def, vv_type_def]) >>
  gvs[compile_snapshot_vv_def, comp_return_def]
QED
