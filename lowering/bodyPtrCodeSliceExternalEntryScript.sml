Theory bodyPtrCodeSliceExternalEntry
Ancestors
  bodyPtrCodeSliceSelf bodyPtrCodeSliceExternalJoin exprSimSliceExtcodeTyped
  exprSimSliceExtcodeContext exprSimSliceSource exprSimPrecompiles
  exprSimCalldataSlice exprSimHyps vyperTypeSystem exprBopLowering
  exprLowering vyperInterpreter vyperContext compileEnv exprSimSource
  exprSimHypsDefs exprSimWordArgs

Theorem code_slice_external_typing:
  expr_body_pre cenv cx env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) es ==>
  ann = BaseT (BytesT (Dynamic n)) /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_type a = BaseT AddressT /\
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [a]; start; len]
Proof
  strip_tac >>
  `well_typed_expr env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len])` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  fs[well_typed_expr_def, well_typed_builtin_app_def,
     account_item_type_def, vyperASTTheory.expr_type_def]
QED

Theorem code_slice_external_operand_pre:
  expr_body_pre cenv cx env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) es /\
  expr_sim_inv cenv cx env ee ==>
  expr_body_pre cenv cx env start ee /\ expr_body_pre cenv cx env len ee
Proof
  strip_tac >> drule code_slice_external_typing >> strip_tac >>
  `well_typed_expr env
    (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len])` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  `~is_extcode start /\ ~is_extcode len` by
    (fs[well_typed_expr_def] >>
     conj_tac >> strip_tac >> drule_all well_typed_extcode_type >> simp[]) >>
  conj_tac >> irule expr_body_pre_builtin_arg >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >> simp[]
QED

Theorem code_slice_external_lowering:
  ~is_self_code (Builtin ct (Acc Code) [a]) /\
  compile_expr cenv ty
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n)
      [Builtin ct (Acc Code) [a]; start; len]) sa = (vv,sb) ==>
  ?sop lop sm sn out dst sp aop sq r.
    lower_value compile_expr cenv ty start sa = (sop,sm) /\
    lower_value compile_expr cenv ty len sm = (lop,sn) /\
    compile_slice_out_buf (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sn =
      ((out,dst),sp) /\
    lower_value compile_expr cenv ty a sp = (aop,sq) /\
    compile_slice_extcode aop sop lop out dst sq = (r,sb) /\
    vv = LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)
Proof
  strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       lower_value_child_call, is_self_code_def, is_extcode_def, extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_extcode addr_op start_op len_op out_buf out_data st4` >>
  gvs[as_ptr_val_def] >> metis_tac[exprSimSliceExtcodeTheory.slice_extcode_shape]
QED

(* Retain source replay while strengthening a pointer outcome's success post. *)
Theorem code_slice_ptr_outcome_with_exec:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn t. Q res ee G tn t /\
      ?marks raw. ee = raw with gas_obs := [] /\
        gas_marked_exec F (ctx,func) source (es,s0) marks res raw (OK t)) R
Proof
  strip_tac >> irule gasOutcomeMarkedPtrTheory.gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> rpt strip_tac >> simp[] >>
  drule gasSummaryComposePtrTheory.gas_marked_exec_ptr_exec >>
  disch_then (irule_at Any) >> simp[]
QED
