(* Physical return typing for internal-call conversion operands. *)
Theory bodyMemTbConvertCallSource
Ancestors
  exprSimHyps exprSimHypsDefs memoryLocalRhsProps valueCopyBytes
  exprSimConvertBytes vyperTypeSystem vyperTypeInvariants exprLowering

Theorem convert_call_read_lowered_typed:
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx) es =
    (INL v,ee) ==>
  value_runtime_typed env
    (lowered_value_type ce (Call ann (IntCall fid) args drv)) v
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env (Call ann (IntCall fid) args drv)` by
    gvs[expr_body_pre_def] >>
  `?sig. FLOOKUP env.fn_sigs fid = SOME sig` by
    (Cases_on `fid` >> gvs[well_typed_expr_def]) >>
  `value_runtime_typed env sig.ret_ty v` by
    metis_tac[internal_call_read_signature_typed] >>
  `ce.ce_func_return_type (nsid_to_string fid) = sig.ret_ty` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  gvs[lowered_value_type_def]
QED

Theorem convert_call_lowered_bytestring:
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  is_bytestring_type ann ==>
  is_bytestring_type (lowered_value_type ce (Call ann (IntCall fid) args drv))
Proof
  strip_tac >>
  `well_typed_expr env (Call ann (IntCall fid) args drv) /\
   expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  Cases_on `fid` >>
  gvs[well_typed_expr_def] >>
  fs[expr_sim_inv_def] >>
  gvs[lowered_value_type_def, type_widens_to_def] >>
  metis_tac[compileEnvTheory.arg_type_fits_bytestring_source]
QED

Theorem convert_call_read_footprint:
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  is_bytestring_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx) es =
    (INL v,ee) ==>
  val_footprint tv v <=
    type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv))
Proof
  strip_tac >>
  drule_all convert_call_read_lowered_typed >> strip_tac >>
  `value_runtime_typed env ann v` by
    metis_tac[memory_rhs_read_annotation_typed, vyperASTTheory.expr_type_def] >>
  `is_bytestring_type (lowered_value_type ce (Call ann (IntCall fid) args drv))` by
    metis_tac[convert_call_lowered_bytestring] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  `type_memory_bytes ce (lowered_value_type ce (Call ann (IntCall fid) args drv)) =
   type_memory_size tv'` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  simp[] >> irule bytestring_val_footprint_le >> metis_tac[]
QED

Theorem convert_call_read_zero_empty:
  expr_body_pre ce cx env (Call ann (IntCall fid) args drv) es /\
  (lowered_value_type ce (Call ann (IntCall fid) args drv) =
     BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type ce (Call ann (IntCall fid) args drv) = BaseT (StringT 0)) /\
  bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx) es =
    (INL v,ee) ==>
  v = BytesV [] \/ v = StringV ""
Proof
  metis_tac[convert_call_read_lowered_typed, value_runtime_typed_zero_bytestring_empty]
QED
