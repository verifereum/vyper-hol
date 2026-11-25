(* Source typing at the actual lowered type, allowing widened internal returns. *)
Theory bodyPtrSignedConvertSourceTyping
Ancestors exprSimHyps memoryLocalRhsProps bodyPtrSignedConvertLayout bodySim
  supportedExprs supportedExprForms vyperTypeSystem exprLowering exprSimHypsDefs compileEnv
  vyperTypeEvalProofs exprBodyPreProps
Libs monadsyntax

Theorem internal_call_lowered_bytestring:
  supported_expr tops (Call ty (IntCall id) args d) /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env (Call ty (IntCall id) args d) es /\
  is_bytestring_type ty ==>
  is_bytestring_type
    (lowered_value_type cenv (Call ty (IntCall id) args d))
Proof
  PairCases_on `id` >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  gvs[well_typed_expr_def] >>
  `cenv.ce_func_return_type (nsid_to_string (id0,id1)) = sig.ret_ty` by
    (`expr_sim_inv_mods [(NONE,cx_tops cx)] cenv cx env es` by
       fs[expr_sim_inv_split_def] >>
     drule_all expr_sim_inv_mods_return_type >> simp[]) >>
  fs[lowered_value_type_def] >>
  metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source]
QED

Theorem source_lowered_bytestring:
  !cenv e tops cx env es.
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) ==>
  is_bytestring_type (lowered_value_type cenv e)
Proof
  recInduct lowered_value_type_ind >>
  rpt strip_tac >>
  gvs[lowered_value_type_def, is_bytestring_type_def, vyperASTTheory.expr_type_def]
  >~ [`is_bytestring_type (concat_buffer_type _ _)`]
  >- (rw[concat_buffer_type_def] >>
      CASE_TAC >> simp[is_bytestring_type_def] >>
      CASE_TAC >> simp[is_bytestring_type_def]) >>
  drule_all internal_call_lowered_bytestring >>
  simp[lowered_value_type_def]
QED

Theorem source_read_lowered_layout:
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  is_bytestring_type (lowered_value_type cenv e) /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
       value_has_type tv v /\
       type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv
Proof
  strip_tac >> conj_tac
  >- (drule_all source_lowered_bytestring >> simp[]) >>
  drule_all memory_rhs_read_lowered_typed >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >> drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem source_read_zero_bytes:
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  v = BytesV []
Proof
  strip_tac >> drule_all memory_rhs_read_lowered_typed >>
  strip_tac >> drule_then strip_assume_tac expr_body_pre_static_facts >>
  drule_all memory_rhs_runtime_layout >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem source_read_zero_string:
  expr_body_pre cenv cx env e es /\ supported_expr tops e /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  lowered_value_type cenv e = BaseT (StringT 0) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  v = StringV []
Proof
  strip_tac >> drule_all memory_rhs_read_lowered_typed >>
  strip_tac >> drule_then strip_assume_tac expr_body_pre_static_facts >>
  drule_all memory_rhs_runtime_layout >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem bytestring_typed_value_view:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  (?n bs. ty = BaseT (BytesT (Dynamic n)) /\ v = BytesV bs /\ LENGTH bs <= n) \/
  (?n str. ty = BaseT (StringT n) /\ v = StringV str /\ LENGTH str <= n)
Proof
  Cases_on `ty` >> simp[is_bytestring_type_def] >>
  rename1 `is_bytestring_type (BaseT bt)` >> Cases_on `bt` >>
  simp[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
  TRY (rename1 `is_bytestring_type (BaseT (BytesT bd))` >>
       Cases_on `bd` >> simp[is_bytestring_type_def,
                             vyperValueTheory.evaluate_type_def]) >>
  strip_tac >> gvs[] >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def]
QED

Theorem source_read_bytestring_view:
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es') ==>
  (?n bs. expr_type e = BaseT (BytesT (Dynamic n)) /\
          v = BytesV bs /\ LENGTH bs <= n) \/
  (?n str. expr_type e = BaseT (StringT n) /\
           v = StringV str /\ LENGTH str <= n)
Proof
  strip_tac >> drule_all exprSimHypsTheory.memory_rhs_read_annotation_typed >>
  strip_tac >> drule_then strip_assume_tac expr_body_pre_static_facts >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  drule_all bytestring_typed_value_view >> simp[]
QED

Theorem source_lowered_nonzero_capacity:
  supported_expr tops e /\ supported_program tops /\
  get_module_code cx NONE = SOME tops /\
  cenv.ce_func_return_type = build_func_return_type tops /\
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) ==>
  64 <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  strip_tac >> drule_all source_lowered_bytestring >> strip_tac >>
  irule bytestring_nonzero_capacity >> simp[]
QED

(* Internal return layout is supplied by the body contract, even when the
   source annotation widens the signature's return type. *)
Theorem body_internal_return_signature_mods[local]:
  expr_body_pre_mods mods cenv cx env (Call ann (IntCall id) args drv) es ==>
  ?sig. FLOOKUP env.fn_sigs id = SOME sig /\
        cenv.ce_func_return_type (nsid_to_string id) = sig.ret_ty
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then mp_tac expr_body_pre_mods_well_typed >>
  Cases_on `id` >> simp[well_typed_expr_def] >>
  rpt strip_tac >> drule_all expr_sim_inv_mods_return_type >> metis_tac[]
QED

Theorem body_internal_lowered_bytestring[local]:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
  is_bytestring_type ann ==>
  is_bytestring_type (lowered_value_type cenv (Call ann (IntCall id) args drv))
Proof
  strip_tac >>
  drule_all_then assume_tac body_inv_expr_body_pre_mods >>
  drule_then strip_assume_tac body_internal_return_signature_mods >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  Cases_on `id` >>
  gvs[well_typed_expr_def, lowered_value_type_def] >>
  metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source]
QED

Theorem body_source_lowered_bytestring:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) ==>
  is_bytestring_type (lowered_value_type cenv e)
Proof
  map_every qid_spec_tac [`es`,`env`,`cx`,`e`,`cenv`] >>
  recInduct lowered_value_type_ind >> rpt strip_tac >>
  gvs[lowered_value_type_def, is_bytestring_type_def, vyperASTTheory.expr_type_def]
  >~ [`is_bytestring_type (concat_buffer_type _ _)`]
  >- (rw[concat_buffer_type_def] >>
      CASE_TAC >> simp[is_bytestring_type_def] >>
      CASE_TAC >> simp[is_bytestring_type_def]) >>
  drule_all body_internal_lowered_bytestring >> simp[lowered_value_type_def]
QED

Theorem body_source_read_lowered_layout:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
  is_bytestring_type (lowered_value_type cenv e) /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
       value_has_type tv v /\
       type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv
Proof
  strip_tac >> conj_tac
  >- (drule_all body_source_lowered_bytestring >> simp[]) >>
  drule_all memory_rhs_read_lowered_typed_unwidened >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >> drule_all memory_rhs_runtime_layout >> simp[]
QED

Theorem body_source_lowered_nonzero_capacity:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) ==>
  64 <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  strip_tac >> drule_all body_source_lowered_bytestring >> strip_tac >>
  irule bytestring_nonzero_capacity >> simp[]
QED

Theorem body_source_lowered_zero_empty:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  (lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
   lowered_value_type cenv e = BaseT (StringT 0)) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
  v = BytesV [] \/ v = StringV []
Proof
  strip_tac >> drule_all memory_rhs_read_lowered_typed_unwidened >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >> drule_all memory_rhs_runtime_layout >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED
