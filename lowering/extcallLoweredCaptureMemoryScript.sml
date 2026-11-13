(* Captured values at the physical layout used by the extcall tuple. *)
Theory extcallLoweredCaptureMemory
Ancestors
  extcallLoweredRepresentation externalReturnSelectedSuffix exprSimIfExpCompat
  exprSimSource exprSimHypsDefs vyperTypeInvariants loweringPosts
  exprSimDefs exprLowering compileEnv vyperState vyperInterpreter

Theorem extcall_post_lowered_classify:
  expr_body_pre ce cx env e es ==>
  post_value_type ce e = lowered_value_type ce e \/
  is_bytestring_type (post_value_type ce e) /\
  is_bytestring_type (lowered_value_type ce e)
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    gvs[expr_body_pre_def] >>
  Cases_on `?a f args d. e = Call a (IntCall f) args d`
  >- (gvs[] >> drule_all return_intcall_post_lowered >> simp[]) >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_not_int_call >> metis_tac[]) >>
  `!id t. FLOOKUP env.var_types id = SOME t ==>
    well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  drule_all ifexp_lowered_type_classify >> strip_tac >> gvs[]
QED

Theorem extcall_nonword_lowered_holds:
  expr_body_pre ce cx env e es /\
  vv_holds ce cx (post_value_type ce e) (Value v) vv ee s /\
  ~is_word_type (post_value_type ce e) /\
  ~is_word_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME ltv /\
  value_has_type ltv v /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory ==>
     post_value_type ce e = lowered_value_type ce e) ==>
  vv_holds ce cx (lowered_value_type ce e) (Value v) vv ee s
Proof
  strip_tac >>
  drule_all extcall_post_lowered_classify >> strip_tac >> gvs[] >>
  Cases_on `vv`
  >- (gvs[vv_holds_def, expr_val_rel_def, read_result_def, return_def] >>
      metis_tac[extcall_nonword_lowered_memory]) >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[vv_holds_def, read_result_def, return_def] >>
      metis_tac[extcall_nonword_lowered_memory]) >>
  metis_tac[]
QED
