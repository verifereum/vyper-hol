(*
 * The value lowering hands out for a string reason (#637)
 *
 * The revert of a Raise or Assert with a reason encodes the reason's
 * compiled value: a memory or stack value (stmtSimReasonExpr's
 * reason_vv_ok) or a storage or transient pointer (stmtSimReasonStorage's
 * reason_storage_vv), or a pointer into code (reason_code_vv), which an
 * immutable gives.  With every local held through a variable pointer, a
 * well-typed string expression compiles to one of the three, the same one
 * at every compile state.
 *
 * TOP-LEVEL:
 *   reason_code_vv             — the reason's value is a pointer into code
 *   compile_expr_string_reason
 *
 * Helper:
 *   reason_result_shape, reason_uniform_shape — the kind of value
 *                                compile_expr gives, at every compile state
 *   reason_typable             — an expression or a place the typing takes
 *)

Theory exprReasonOperand
Ancestors
  exprWordOperand exprOperandVar exprSafeOperand stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage exprLowering exprCallBounds compileEnv context vyperTypeSystem vyperAST

(* The reason's value_vv is a pointer to a value of a type that is not a
   word type (a string) in code: an immutable's value. *)
Definition reason_code_vv_def:
  reason_code_vv vv <=>
    ?t p. vv = LocatedValue t p /\ ~is_word_type t /\ p.ptr_location = LocCode
End

Definition reason_result_shape_def:
  (reason_result_shape t loc (StackValue t' op) <=>
    t' = t /\ loc = LocMemory /\ (!l. op <> Label l)) /\
  (reason_result_shape t loc (LocatedValue t' p) <=>
    t' = t /\ p.ptr_location = loc /\ (!l. p.ptr_operand <> Label l))
End

Theorem reason_result_shape_memory[local]:
  reason_result_shape (BaseT (StringT n)) LocMemory vv ==>
  reason_vv_ok vv
Proof
  Cases_on `vv` >>
  simp[reason_result_shape_def, reason_vv_ok_def, reason_vv_def,
       is_word_type_def] >> metis_tac[]
QED

Theorem reason_result_shape_storage[local]:
  reason_result_shape (BaseT (StringT n)) loc vv /\
  (loc = LocStorage \/ loc = LocTransient) ==>
  reason_storage_vv vv
Proof
  Cases_on `vv` >>
  simp[reason_result_shape_def, reason_storage_vv_def, is_word_type_def] >>
  metis_tac[]
QED

Theorem reason_result_shape_code[local]:
  reason_result_shape (BaseT (StringT n)) LocCode vv ==> reason_code_vv vv
Proof
  Cases_on `vv` >>
  simp[reason_result_shape_def, reason_code_vv_def, is_word_type_def]
QED

Theorem reason_compile_name[local]:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  compile_name_vv cenv t id sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  simp[compile_name_vv_def, comp_return_def, reason_result_shape_def,
       mk_ptr_def] >> strip_tac >> gvs[reason_result_shape_def, mk_ptr_def, comp_return_def]
QED

Theorem reason_compile_toplevelname[local]:
  ?loc. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
    !sa vv sb. compile_expr_body f g h cenv ty (TopLevelName t nsid) sa = (vv,sb) ==>
      reason_result_shape t loc vv
Proof
  Cases_on `FLOOKUP cenv.ce_module_vars nsid`
  >- (qexists_tac `LocMemory` >>
      simp[compile_expr_body_def, expr_type_def] >> rpt gen_tac >>
      rpt (pairarg_tac >> gvs[]) >>
      rpt strip_tac >> gvs[reason_result_shape_def]) >>
  rename1 `FLOOKUP _ _ = SOME bnd` >> Cases_on `bnd` >> gvs[] >>
  simp[compile_expr_body_def, expr_type_def]
  >- (qexists_tac `LocMemory` >> simp[] >> rpt gen_tac >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      gvs[reason_result_shape_def])
  >- (qexists_tac `LocStorage` >>
      simp[reason_result_shape_def, mk_ptr_def])
  >- (qexists_tac `LocTransient` >>
      simp[reason_result_shape_def, mk_ptr_def])
  >- (qexists_tac `LocCode` >>
      simp[reason_result_shape_def, mk_ptr_def]) >>
  qexists_tac `LocMemory` >> simp[] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[reason_result_shape_def]
QED

Theorem reason_pop_operand[local]:
  compile_dynarray_pop bop ws es load_opc store_opc sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[compile_dynarray_pop_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem reason_projection_operand[local]:
  (compile_mapping_subscript bop key sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_tuple_subscript bop off sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_array_subscript bop idx dyn sc ws es is_signed load_opc sa = (op,sb) ==>
   !l. op <> Label l)
Proof
  rpt conj_tac >>
  simp[compile_mapping_subscript_def, compile_tuple_subscript_def,
       compile_array_subscript_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem reason_compile_attribute[local]:
  (!sa vv sb. f cenv ty base_e sa = (vv,sb) ==>
     reason_result_shape (expr_type base_e) loc vv) /\
  compile_attribute f cenv ret_ty ty base_e fld sa = (vv,sb) ==>
  reason_result_shape ret_ty loc vv
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule emit_op_safe_operand >>
  Cases_on `base_vv` >>
  gvs[reason_result_shape_def, vv_location_def, mk_ptr_def, safe_operand_def]
QED

Theorem reason_compile_subscript[local]:
  (!sa vv sb. f cenv ty base_e sa = (vv,sb) ==>
     reason_result_shape (expr_type base_e) loc vv) /\
  compile_subscript f cenv ret_ty ty base_e idx_e sa = (vv,sb) ==>
  reason_result_shape ret_ty loc vv
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `base_vv` >>
  gvs[reason_result_shape_def, vv_location_def, vv_operand_def] >>
  (Cases_on `place_type cenv base_e`
  >- (gvs[comp_bind_def, comp_return_def, LET_THM] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[reason_result_shape_def, mk_ptr_def] >>
      metis_tac[reason_projection_operand]) >>
  rename1 `place_type cenv base_e = ValPT base_ty` >> Cases_on `base_ty` >>
  gvs[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_projection_operand])
QED

(* The location a target's pointer lives in comes from its root name, at
   every compile state. *)
Theorem reason_target_ptr_loc[local]:
  !bt. ?lo. (!l. lo = SOME l ==>
               l = LocMemory \/ l = LocStorage \/ l = LocTransient \/ l = LocCode) /\
    !sa r sb. compile_get_target_ptr cfn cenv bt sa = (r,sb) ==> FST (SND r) = lo
Proof
  measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[compile_get_target_ptr_def]
  >- (BasicProvers.every_case_tac >> simp[comp_return_def])
  >- (simp[LET_THM] >> BasicProvers.every_case_tac >> simp[comp_return_def]) >>
  rename1 `compile_get_target_ptr cfn cenv b` >>
  first_x_assum (qspec_then `b` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `lo` >> simp[] >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  BasicProvers.every_case_tac >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >> res_tac >> gvs[]
QED

Theorem reason_compile_pop[local]:
  ?loc. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
    !sa vv sb. compile_expr_body f g h cenv ty (Pop t target) sa = (vv,sb) ==>
      reason_result_shape t loc vv
Proof
  qspecl_then [`target`] strip_assume_tac
    (Q.GENL [`cfn`, `cenv`] reason_target_ptr_loc |> Q.SPECL [`f`, `cenv`]) >>
  qexists_tac `case lo of SOME l => l | NONE => LocMemory` >>
  conj_tac >- (Cases_on `lo` >> simp[]) >>
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> res_tac >> gvs[reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_pop_operand]
QED

Theorem reason_alloc_operand[local]:
  compile_alloc_buffer sz sa = (buf,sb) ==> !l. buf.buf_operand <> Label l
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem reason_bytelike_operand[local]:
  compile_bytelike_literal bs maxlen sa = (buf,sb) ==>
  !l. buf.buf_operand <> Label l
Proof
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_compile_literal[local]:
  compile_literal_vv t lit sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  Cases_on `lit`
  >- (Cases_on `b` >>
      simp[compile_literal_vv_def, comp_return_def] >>
      rpt strip_tac >> gvs[reason_result_shape_def]) >>
  simp[compile_literal_vv_def, comp_return_def, comp_bind_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[reason_result_shape_def, base_ptr_def]
  >~ [`compile_bytelike_literal _ _ _ = _`] >-
    (drule (GEN_ALL reason_bytelike_operand) >> simp[]) >>
  Cases_on `t` >> gvs[comp_return_def, comp_bind_def, reason_result_shape_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[comp_return_def, comp_bind_def, reason_result_shape_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[comp_return_def, comp_bind_def, reason_result_shape_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[reason_result_shape_def, base_ptr_def] >>
  metis_tac[reason_bytelike_operand]
QED

Theorem reason_compile_ifexp[local]:
  compile_expr_body f g h cenv ty (IfExp t cond_e then_e else_e) sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[AllCaseEqs(), reason_result_shape_def, mk_ptr_def]
QED

Theorem reason_compile_structlit[local]:
  compile_expr_body f g h cenv ty (StructLit t nm fields) sa = (vv,sb) ==>
  reason_result_shape t LocMemory vv
Proof
  simp[compile_expr_body_def, expr_type_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[reason_result_shape_def, base_ptr_def] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_stack_result[local]:
  as_stack_val t res = (vv,sb) /\ word_result_ok sb vv ==>
  reason_result_shape t LocMemory vv
Proof
  Cases_on `res` >> simp[as_stack_val_def] >> strip_tac >>
  gvs[word_result_ok_def, reason_result_shape_def, safe_operand_def]
QED

Theorem reason_builtin_scalar[local]:
  (bi = Not \/ bi = Neg \/ bi = Abs \/ bi = BlockHash \/ bi = BlobHash \/
   bi = Ceil \/ bi = Floor \/ bi = AddMod \/ bi = MulMod \/ bi = PowMod256 \/
   bi = ECRecover \/ bi = CalldataLen \/ (?item. bi = Env item)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_scalar] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[reason_stack_result]
QED

Theorem reason_builtin_hash[local]:
  (bi = Keccak256 \/ bi = Sha256) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_hash] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[reason_stack_result]
QED

Theorem reason_builtin_len[local]:
  compile_builtin_dispatch_body f cenv vt ty Len args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_len] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[as_stack_val_def] >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[reason_stack_result]
QED

Theorem reason_builtin_bop[local]:
  compile_builtin_dispatch_body f cenv vt ty (Bop bop) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  strip_tac >>
  `word_result_ok sb vv` by metis_tac[word_builtin_bop] >>
  gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  metis_tac[reason_stack_result]
QED

Theorem reason_ensure_memory_operand[local]:
  (!l. p <> Label l) /\
  compile_ensure_in_memory p loc bytes wc ctor imm sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_unwrap_operand[local]:
  reason_result_shape t loc vv /\ unwrap_value cenv vv sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `vv` >>
  simp[reason_result_shape_def, unwrap_value_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  Cases_on `is_word_type t` >> gvs[]
  >- (drule compile_ptr_load_safe_operand >> simp[safe_operand_def]) >>
  Cases_on `p.ptr_location` >> gvs[comp_return_def] >>
  metis_tac[reason_ensure_memory_operand]
QED

Theorem reason_lower_operand[local]:
  (!sa vv sb. f cenv ty e sa = (vv,sb) ==>
     ?loc. reason_result_shape (expr_type e) loc vv) /\
  lower_value f cenv ty e sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[reason_unwrap_operand]
QED

Theorem reason_convert_operand[local]:
  (!l. v <> Label l) /\ compile_type_convert v conv sa = (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `conv`
  >~ [`compile_type_convert v ConvBytestringToBool`] >-
    (metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def])
  >~ [`compile_type_convert v (ConvBytestringToInt s n in_n)`] >-
    (metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def])
  >~ [`compile_type_convert v (ConvBytestringToDecimal d lo hi in_n)`] >-
    (metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def])
  >~ [`compile_type_convert v (ConvBytestringToBytesM m)`] >-
    (metis_tac[compile_type_convert_bytestring_safe, listTheory.MEM, safe_operand_def]) >>
  simp[compile_type_convert_def, compile_int_clamp_def,
       comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def,
                           comp_return_def, LET_THM]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       IF_CASES_TAC >>
       simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
       rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_safe_operand >> fs[safe_operand_def] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_type_builtin_convert[local]:
  (!sa op sb. lower_value f cenv (expr_type (HD args)) (HD args) sa = (op,sb)
               ==> !l. op <> Label l) /\
  compile_type_builtin_dispatch_body f cenv vt ty Convert rt args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  simp[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `COND _ _ _ = _` mp_tac >> IF_CASES_TAC
  >- (strip_tac >> gvs[reason_result_shape_def]) >>
  pop_assum kall_tac >> strip_tac >> Cases_on `rt` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >> strip_tac >>
  gvs[reason_result_shape_def] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[reason_convert_operand]
QED

Theorem reason_compile_named_modular[local]:
  (!ce rt at a bt b mt m s vv s'.
    compile_addmod_names ce rt at a bt b mt m s = (vv,s') ==>
    reason_result_shape rt LocMemory vv) /\
  (!ce rt at a bt b mt m s vv s'.
    compile_mulmod_names ce rt at a bt b mt m s = (vv,s') ==>
    reason_result_shape rt LocMemory vv) /\
  (!ce rt at a bt b s vv s'.
    compile_powmod256_names ce rt at a bt b s = (vv,s') ==>
    reason_result_shape rt LocMemory vv)
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  `word_result_ok s' vv` by metis_tac[word_compile_named_modular] >>
  gvs[compile_addmod_names_def, compile_mulmod_names_def,
      compile_powmod256_names_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[reason_stack_result]
QED

Theorem reason_slice_out_buf[local]:
  compile_slice_out_buf sz sa = ((buf,data),sb) ==> !l. buf <> Label l
Proof
  simp[builtinBytesTheory.compile_slice_out_buf_def, comp_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_slice_data[local]:
  compile_slice_data len data start lenop sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinBytesTheory.compile_slice_data_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_slice_adhoc[local]:
  (!start lenop sz sa op sb.
    compile_slice_calldata start lenop sz sa = (op,sb) ==> !l. op <> Label l) /\
  (!start lenop sz sa op sb.
    compile_slice_code start lenop sz sa = (op,sb) ==> !l. op <> Label l) /\
  (!addr start lenop buf data sa op sb.
    (!l. buf <> Label l) /\
    compile_slice_extcode addr start lenop buf data sa = (op,sb) ==>
    !l. op <> Label l)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[builtinBytesTheory.compile_slice_calldata_def,
       builtinBytesTheory.compile_slice_code_def,
       builtinBytesTheory.compile_slice_extcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[reason_slice_out_buf]
QED

Theorem reason_ec_points[local]:
  (!p q sa op sb. compile_ecadd_points p q sa = (op,sb) ==> !l. op <> Label l) /\
  (!p scalar sa op sb. compile_ecmul_point p scalar sa = (op,sb) ==>
                         !l. op <> Label l)
Proof
  conj_tac >> rpt gen_tac >>
  simp[builtinMiscTheory.compile_ecadd_points_def,
       builtinMiscTheory.compile_ecmul_point_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_uint2str[local]:
  compile_uint2str v digits sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinStringsTheory.compile_uint2str_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  ntac 10 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem reason_builtin_fresh[local]:
  ((?n. bi = CalldataSlice n) \/ bi = ECAdd \/ bi = ECMul \/
   (?n. bi = Concat n) \/ (?n. bi = Slice n) \/ (?n. bi = Uint2Str n)) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`LocatedValue _ (base_ptr _)`] >-
    (gvs[reason_result_shape_def, base_ptr_def] >>
     metis_tac[reason_alloc_operand]) >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_slice_adhoc, reason_slice_out_buf, reason_slice_data,
            reason_ec_points, reason_uint2str]
QED

Theorem reason_builtin_makearray[local]:
  compile_builtin_dispatch_body f cenv vt ty (MakeArray et bd) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  Cases_on `et` >>
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def, mk_ptr_def] >>
  metis_tac[compiler_make_tuple_result, compiler_make_array_result,
            reason_alloc_operand]
QED

Theorem reason_acc_operand[local]:
  (!sa op sb. lower_value f cenv (BaseT AddressT) e sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_acc f cenv e item sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `item` >> simp[compile_acc_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem reason_wei_operand[local]:
  (!v scale signed sa op sb. (!l. v <> Label l) /\
    compile_as_wei_value_int v scale signed sa = (op,sb) ==> !l. op <> Label l) /\
  (!v scale divisor sa op sb.
    compile_as_wei_value_decimal v scale divisor sa = (op,sb) ==> !l. op <> Label l)
Proof
  conj_tac >> rpt gen_tac >>
  simp[builtinMiscTheory.compile_as_wei_value_int_def,
       builtinMiscTheory.compile_as_wei_value_decimal_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[emit_op_safe_operand, safe_operand_def]
QED

Theorem reason_method_operand[local]:
  compile_method_id_runtime ty v flag sa = (op,sb) ==> !l. op <> Label l
Proof
  Cases_on `flag`
  >- (metis_tac[exprSafeOperandBuiltinsTheory.compile_method_id_word_safe_operand,
                 safe_operand_def]) >>
  simp[builtinHashingTheory.compile_method_id_runtime_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_builtin_acc[local]:
  (!sa op sb. lower_value f cenv (BaseT AddressT) (HD args) sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_builtin_dispatch_body f cenv vt ty (Acc item) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def] >>
  metis_tac[reason_acc_operand]
QED

Theorem reason_builtin_as_wei_value[local]:
  (!sa op sb. lower_value f cenv (expr_type (HD args)) (HD args) sa = (op,sb) ==>
               !l. op <> Label l) /\
  compile_builtin_dispatch_body f cenv vt ty (AsWeiValue denom) args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def] >>
  metis_tac[reason_wei_operand]
QED

Theorem reason_builtin_method_id[local]:
  compile_builtin_dispatch_body f cenv vt ty MethodId args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  simp[compile_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()]
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[reason_compile_literal]
  >~ [`as_ptr_val _ _ _ = _`] >-
    (qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
     Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
     strip_tac >> gvs[reason_result_shape_def, mk_ptr_def] >>
     metis_tac[reason_method_operand]) >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def] >>
  metis_tac[reason_method_operand]
QED

Theorem reason_empty_operand[local]:
  compile_builtin_empty_complex sz bs sa = (buf,sb) ==> !l. buf.buf_operand <> Label l
Proof
  simp[builtinSimpleTheory.compile_builtin_empty_complex_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `bs` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[] >> metis_tac[reason_alloc_operand]
QED

Theorem reason_abi_encode_operand[local]:
  lower_abi_encode ensure mid src info maxlen sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_encode_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_abi_decode_operand[local]:
  lower_abi_decode data info mn mx sz sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_decode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_type_builtin_nonconvert[local]:
  tb <> Convert /\
  type_builtin_result_ok tenv tb vt rt (MAP expr_type args) /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  Cases_on `tb` >>
  simp[type_builtin_result_ok_def, compile_type_builtin_dispatch_body_def,
       LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[reason_result_shape_def]
  >~ [`if is_word_type _ then _ else _`] >-
    (gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
     gvs[reason_result_shape_def, base_ptr_def] >>
     metis_tac[reason_empty_operand])
  >~ [`as_stack_val _ _ = _`] >-
    (qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_stack_val vt res` >>
     Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
     strip_tac >> gvs[reason_result_shape_def] >>
     drule exprSafeOperandBuiltinsTheory.compile_extract32_load_safe_operand >>
     strip_tac >>
     metis_tac[exprSafeOperandBuiltinsTheory.compile_clamp_basetype_safe_operand,
               safe_operand_def]) >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_ptr_val vt LocMemory res` >>
  Cases_on `res` >> gvs[as_ptr_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_abi_encode_operand, reason_abi_decode_operand]
QED

Theorem reason_default_return_operand[local]:
  (!l. result <> Label l) /\
  compile_default_return_path cenv rt dt buf result def addr skip mn mx info sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[compile_default_return_path_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem reason_external_call_operand[local]:
  compile_external_call_kwargs cenv addr vals tys memsz abisz mid retsz mn outsz
    static value gas skip hasdef def rt dt einfo dinfo sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[compile_external_call_kwargs_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `retsz = 0`
  >- simp[comp_return_def] >>
  simp[] >> Cases_on `hasdef` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_default_return_operand, reason_alloc_operand]
QED

Theorem reason_raw_call_outbuf_operand[local]:
  compile_raw_call_outbuf mx sa = ((out_val,out_ptr),sb) ==>
  !l. out_val <> Label l
Proof
  simp[builtinSystemTheory.compile_raw_call_outbuf_def, LET_THM, comp_bind_def,
       comp_return_def] >>
  IF_CASES_TAC >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand]
QED

Theorem reason_raw_call_finish_operand[local]:
  (!l. out_val <> Label l) /\
  compile_raw_call_finish addr data len gas value ct mx rof out_val out_ptr sa =
    (op,sb) ==>
  !l. op <> Label l
Proof
  Cases_on `ct` >> Cases_on `rof` >> Cases_on `mx > 0` >>
  simp[builtinSystemTheory.compile_raw_call_finish_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[reason_alloc_operand, emit_op_safe_operand, safe_operand_def]
QED

(* Both raw_call forms: splitting off a second argument is needed for the
   byte-string form and harmless for the msg.data one. *)
val reason_raw_call_tac =
  Cases_on `args` >-
    (simp[compile_call_def, LET_THM] >> strip_tac >>
     rpt (pairarg_tac >> gvs[]) >> gvs[reason_result_shape_def]) >>
  Cases_on `t` >> simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_raw_call_finish_operand, reason_raw_call_outbuf_operand]

Theorem reason_compile_call[local]:
  compile_call f cenv rt ty target args default_ret sa = (vv,sb) ==>
  reason_result_shape rt LocMemory vv
Proof
  Cases_on `target`
  >~ [`RawCallTarget`] >- reason_raw_call_tac
  >~ [`RawCallCalldataTarget`] >- reason_raw_call_tac >>
  simp[compile_call_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[reason_result_shape_def]
  >~ [`cenv.ce_func_info name = info`] >- suspend "internal"
  >~ [`compile_call f cenv rt ty (ExtCall b b0 p l) args default_ret sa = _`]
    >- suspend "external"
  >~ [`as_stack_val rt (compile_create_call f cenv ck salted rof args sa)`]
    >- suspend "create"
  >> suspend "send"
QED

Resume reason_compile_call[internal]:
  Cases_on `returns_count > 0` >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[reason_result_shape_def, base_ptr_def] >>
  metis_tac[reason_alloc_operand, emit_op_safe_operand, safe_operand_def]
QED

Resume reason_compile_call[external]:
  PairCases_on `p` >> Cases_on `args` >>
  gvs[compile_call_def, LET_THM, reason_result_shape_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), reason_result_shape_def, mk_ptr_def] >>
  metis_tac[reason_external_call_operand]
QED

Resume reason_compile_call[create]:
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val rt res` >>
  Cases_on `res` >> gvs[as_stack_val_def, markerTheory.Abbrev_def] >>
  strip_tac >> gvs[reason_result_shape_def] >>
  metis_tac[exprSafeOperandBuiltinsTheory.compile_create_call_safe_operand,
            safe_operand_def]
QED

Resume reason_compile_call[send]:
  Cases_on `args` >> gvs[reason_result_shape_def] >>
  rename1 `list_CASE tail _ _` >> Cases_on `tail` >>
  gvs[reason_result_shape_def] >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[reason_result_shape_def]) >>
  simp[reason_result_shape_def]
QED

Finalise reason_compile_call

Theorem reason_builtin_dispatch_body[local]:
  (!t e sa op sb. MEM e args /\ lower_value f cenv t e sa = (op,sb) ==>
                   !l. op <> Label l) /\
  (((?item. bi = Acc item) \/ (?denom. bi = AsWeiValue denom)) ==> args <> []) /\
  compile_builtin_dispatch_body f cenv vt ty bi args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  Cases_on `bi` >> strip_tac
  >~ [`Bop bop`] >- metis_tac[reason_builtin_bop]
  >~ [`Len`] >- metis_tac[reason_builtin_len]
  >~ [`MakeArray et bd`] >- metis_tac[reason_builtin_makearray]
  >~ [`MethodId`] >- metis_tac[reason_builtin_method_id]
  >~ [`Acc item`] >- suspend "acc"
  >~ [`AsWeiValue denom`] >- suspend "wei" >>
  metis_tac[reason_builtin_scalar, reason_builtin_hash, reason_builtin_fresh]
QED

Resume reason_builtin_dispatch_body[acc]:
  irule reason_builtin_acc >> goal_assum (drule_at Any) >>
  Cases_on `args` >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  metis_tac[]
QED

Resume reason_builtin_dispatch_body[wei]:
  irule reason_builtin_as_wei_value >> goal_assum (drule_at Any) >>
  Cases_on `args` >> gvs[compile_builtin_dispatch_body_def, LET_THM] >>
  metis_tac[]
QED

Finalise reason_builtin_dispatch_body

Theorem reason_type_builtin_dispatch_body[local]:
  (!t e sa op sb. MEM e args /\ lower_value f cenv t e sa = (op,sb) ==>
                   !l. op <> Label l) /\
  (tb = Convert ==> args <> []) /\
  type_builtin_result_ok tenv tb vt rt (MAP expr_type args) /\
  compile_type_builtin_dispatch_body f cenv vt ty tb rt args sa = (vv,sb) ==>
  reason_result_shape vt LocMemory vv
Proof
  Cases_on `tb = Convert`
  >- (strip_tac >> gvs[] >> irule reason_type_builtin_convert >>
      goal_assum (drule_at Any) >> Cases_on `args` >> gvs[] >> metis_tac[]) >>
  metis_tac[reason_type_builtin_nonconvert]
QED

Definition reason_uniform_shape_def:
  reason_uniform_shape f cenv ty e <=>
    ?loc. (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient \/ loc = LocCode) /\
      !sa vv sb. f cenv ty e sa = (vv,sb) ==>
        reason_result_shape (expr_type e) loc vv
End

Definition reason_typable_def:
  reason_typable env e <=>
    well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt
End

Theorem reason_typable_expr[local]:
  well_typed_expr env e ==> reason_typable env e
Proof
  simp[reason_typable_def]
QED

Theorem reason_typable_subscript[local]:
  reason_typable env (Subscript ann base_e idx_e) ==> reason_typable env base_e
Proof
  simp[reason_typable_def, well_typed_expr_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem reason_typable_attribute[local]:
  reason_typable env (Attribute ann base_e fld) ==> well_typed_expr env base_e
Proof
  simp[reason_typable_def, well_typed_expr_def]
QED

Theorem reason_typable_name[local]:
  reason_typable env (Name ann id) ==> FLOOKUP env.var_types id = SOME ann
Proof
  simp[reason_typable_def, well_typed_expr_def]
QED

Theorem reason_typable_builtin[local]:
  reason_typable env (Builtin ann bi args) ==> well_typed_expr env (Builtin ann bi args)
Proof
  simp[reason_typable_def, well_typed_expr_def]
QED

Theorem reason_typable_type_builtin[local]:
  reason_typable env (TypeBuiltin ann tb rt args) ==>
  well_typed_expr env (TypeBuiltin ann tb rt args)
Proof
  simp[reason_typable_def, well_typed_expr_def]
QED

Theorem reason_compile_expr_body[local]:
  (!e'. expr_size e' < expr_size e /\ reason_typable env e' ==>
         reason_uniform_shape f cenv ty e') /\
  (!ann bi args sa vv sb.
     well_typed_expr env (Builtin ann bi args) /\
     g cenv ann ty bi args sa = (vv,sb) ==>
     reason_result_shape ann LocMemory vv) /\
  (!ann tb rt args sa vv sb.
     well_typed_expr env (TypeBuiltin ann tb rt args) /\
     h cenv ann ty tb rt args sa = (vv,sb) ==>
     reason_result_shape ann LocMemory vv) /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  reason_typable env e ==>
  reason_uniform_shape (compile_expr_body f g h) cenv ty e
Proof
  Cases_on `e` >> strip_tac
  >~ [`Subscript ann base_e idx_e`] >- suspend "subscript"
  >~ [`Attribute ann base_e fld`] >- suspend "attribute"
  >~ [`Builtin ann bi args`] >- suspend "builtin"
  >~ [`TopLevelName ann nsid`] >-
    (gvs[reason_uniform_shape_def, expr_type_def] >>
     irule reason_compile_toplevelname >> simp[])
  >~ [`Pop ann target`] >-
    (gvs[reason_uniform_shape_def, expr_type_def] >>
     irule reason_compile_pop >> simp[]) >>
  simp[reason_uniform_shape_def] >> qexists_tac `LocMemory` >> simp[] >>
  rpt gen_tac >> strip_tac
  >~ [`IfExp ann cond th el`] >-
    metis_tac[reason_compile_ifexp, expr_type_def]
  >~ [`StructLit ann name fields`] >-
    metis_tac[reason_compile_structlit, expr_type_def] >>
  gvs[compile_expr_body_def, expr_type_def, LET_THM]
  >~ [`compile_name_vv _ _ _ _ = _`] >-
    (drule reason_typable_name >> metis_tac[reason_compile_name])
  >~ [`compile_literal_vv _ _ _ = _`] >- metis_tac[reason_compile_literal]
  >~ [`compile_call _ _ _ _ _ _ _ _ = _`] >- metis_tac[reason_compile_call]
  >~ [`h cenv _ ty _ _ _ sa = _`] >- metis_tac[reason_typable_type_builtin] >>
  simp[reason_result_shape_def]
QED

Resume reason_compile_expr_body[subscript]:
  `reason_uniform_shape f cenv ty base_e` by
    (first_x_assum irule >>
     simp[expr_size_def] >>
     metis_tac[reason_typable_subscript, reason_typable_attribute, reason_typable_expr]) >>
  qpat_x_assum `reason_uniform_shape _ _ _ _` mp_tac >>
  rewrite_tac[reason_uniform_shape_def, expr_type_def] >>
  disch_then (qx_choose_then `loc` strip_assume_tac) >>
  qexists_tac `loc` >> simp[] >> rpt strip_tac >>
  gvs[compile_expr_body_def, expr_type_def] >>
  metis_tac[reason_compile_subscript]
QED

Resume reason_compile_expr_body[attribute]:
  `reason_uniform_shape f cenv ty base_e` by
    (first_x_assum irule >>
     simp[expr_size_def] >>
     metis_tac[reason_typable_subscript, reason_typable_attribute, reason_typable_expr]) >>
  qpat_x_assum `reason_uniform_shape _ _ _ _` mp_tac >>
  rewrite_tac[reason_uniform_shape_def, expr_type_def] >>
  disch_then (qx_choose_then `loc` strip_assume_tac) >>
  qexists_tac `loc` >> simp[] >> rpt strip_tac >>
  gvs[compile_expr_body_def, expr_type_def] >>
  metis_tac[reason_compile_attribute]
QED

Theorem reason_compile_expr_builtin_shape_classify[local]:
  compile_expr_body f g h cenv ty (Builtin ann bi args) sa = (vv,sb) ==>
  g cenv ann ty bi args sa = (vv,sb) \/ reason_result_shape ann LocMemory vv
Proof
  Cases_on `bi = AddMod` >- (gvs[] >> suspend "add") >>
  Cases_on `bi = MulMod` >- (gvs[] >> suspend "mul") >>
  Cases_on `bi = PowMod256` >- (gvs[] >> suspend "pow") >>
  Cases_on `bi` >> gvs[] >>
  simp[compile_expr_body_def, expr_type_def,
       word_list_result_elim, word_expr_result_elim]
QED

Resume reason_compile_expr_builtin_shape_classify[add]:
  Cases_on `args` >- simp[compile_expr_body_def, expr_type_def] >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  metis_tac[reason_compile_named_modular]
QED

Resume reason_compile_expr_builtin_shape_classify[mul]:
  Cases_on `args` >- simp[compile_expr_body_def, expr_type_def] >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::Name _ _::m::rest` >>
  Cases_on `m` >> simp[] >>
  Cases_on `rest` >> simp[] >>
  metis_tac[reason_compile_named_modular]
QED

Resume reason_compile_expr_builtin_shape_classify[pow]:
  Cases_on `args` >- simp[compile_expr_body_def, expr_type_def] >>
  rename1 `a::rest` >>
  Cases_on `a` >> simp[compile_expr_body_def, expr_type_def] >>
  Cases_on `rest` >> simp[] >>
  rename1 `Name _ _::b::rest` >>
  Cases_on `b` >> simp[] >>
  Cases_on `rest` >> simp[]
  >- metis_tac[reason_compile_named_modular] >>
  simp[word_expr_result_elim, word_list_result_elim]
QED

Finalise reason_compile_expr_builtin_shape_classify

Resume reason_compile_expr_body[builtin]:
  simp[reason_uniform_shape_def, expr_type_def] >>
  qexists_tac `LocMemory` >> simp[] >>
  map_every qx_gen_tac [`sa`, `vv`, `sb`] >>
  drule reason_typable_builtin >> strip_tac >>
  strip_tac >>
  drule reason_compile_expr_builtin_shape_classify >>
  strip_tac >> metis_tac[]
QED

Finalise reason_compile_expr_body

Theorem reason_compile_uniform[local]:
  (!cenv ty e (sa:compile_state) env.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
      reason_typable env e ==> reason_uniform_shape compile_expr cenv ty e) /\
  (!cenv ann ty bi args (sa:compile_state) env.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
      well_typed_expr env (Builtin ann bi args) ==>
    !s vv s'. compile_builtin_dispatch cenv ann ty bi args s = (vv,s') ==>
      reason_result_shape ann LocMemory vv) /\
  (!cenv ann ty tb rt args (sa:compile_state) env.
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
      well_typed_expr env (TypeBuiltin ann tb rt args) ==>
    !s vv s'. compile_type_builtin_dispatch cenv ann ty tb rt args s = (vv,s') ==>
      reason_result_shape ann LocMemory vv)
Proof
  ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- suspend "expr"
  >- suspend "builtin"
  >> suspend "type_builtin"
QED

Resume reason_compile_uniform[expr]:
  rpt strip_tac >>
  simp[reason_uniform_shape_def, Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule (SRULE [reason_uniform_shape_def] reason_compile_expr_body) >>
  qexists_tac `env` >> simp[] >>
  conj_tac >-
    (rpt strip_tac >> simp[] >>
     rewrite_tac[GSYM reason_uniform_shape_def] >>
     first_x_assum irule >> simp[] >> qexists_tac `env` >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> simp[builtin_child_callback_def] >>
     Cases_on `list_size expr_size args < expr_size e` >> simp[]
     >- metis_tac[] >>
     simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
     rpt (pairarg_tac >> gvs[reason_result_shape_def])) >>
  rpt gen_tac >> simp[type_child_callback_def] >>
  Cases_on `list_size expr_size args < expr_size e` >> simp[]
  >- metis_tac[] >>
  simp[invalid_expr_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[reason_result_shape_def])
QED

Resume reason_compile_uniform[builtin]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule reason_builtin_dispatch_body >>
  goal_assum (drule_at (Pat `compile_builtin_dispatch_body`)) >>
  conj_tac >- suspend "builtin_operand" >>
  gvs[well_typed_expr_def] >>
  Cases_on `bi` >> gvs[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[]
QED

Resume reason_compile_uniform[type_builtin]:
  gvs[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[Once compile_expr_raw_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> strip_tac >>
  irule reason_type_builtin_dispatch_body >>
  goal_assum (drule_at (Pat `compile_type_builtin_dispatch_body`)) >>
  qexists_tac `env.type_defs` >>
  conj_tac >- suspend "type_operand" >>
  gvs[well_typed_expr_def] >> strip_tac >>
  gvs[well_typed_type_builtin_args_def] >> Cases_on `args` >> gvs[]
QED

Resume reason_compile_uniform[builtin_operand]:
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lower_value`) reason_lower_operand >> disch_then irule >>
  Cases_on `expr_size e < list_size expr_size args` >> simp[]
  >- suspend "builtin_operand_valid" >>
  simp[invalid_expr_call_def, LET_THM] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[reason_result_shape_def]) >>
  metis_tac[reason_stack_result]
QED

Resume reason_compile_uniform[builtin_operand_valid]:
  `well_typed_expr env e` by
    (qpat_x_assum `well_typed_expr env _` mp_tac >>
     simp[well_typed_expr_def] >> strip_tac >>
     irule exprSimHypsTheory.well_typed_exprs_member >> metis_tac[]) >>
  `reason_uniform_shape compile_expr cenv t e` by
    (first_x_assum irule >> simp[] >> qexists_tac `env` >>
     simp[reason_typable_def]) >>
  fs[reason_uniform_shape_def] >> metis_tac[]
QED

Resume reason_compile_uniform[type_operand]:
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `lower_value`) reason_lower_operand >> disch_then irule >>
  Cases_on `expr_size e < list_size expr_size args` >> simp[]
  >- suspend "type_operand_valid" >>
  simp[invalid_expr_call_def, LET_THM] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[reason_result_shape_def]) >>
  metis_tac[reason_stack_result]
QED

Resume reason_compile_uniform[type_operand_valid]:
  `well_typed_expr env e` by
    (qpat_x_assum `well_typed_expr env _` mp_tac >>
     simp[well_typed_expr_def] >> strip_tac >>
     irule exprSimHypsTheory.well_typed_exprs_member >> metis_tac[]) >>
  `reason_uniform_shape compile_expr cenv t e` by
    (first_x_assum irule >> simp[] >> qexists_tac `env` >>
     simp[reason_typable_def]) >>
  fs[reason_uniform_shape_def] >> metis_tac[]
QED

Finalise reason_compile_uniform

Theorem compile_expr_reason_uniform[local]:
  well_typed_expr env e /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
  reason_uniform_shape compile_expr cenv ty e
Proof
  strip_tac >> irule (cj 1 reason_compile_uniform) >>
  simp[] >> qexists_tac `env` >> simp[reason_typable_def]
QED

(* Why it holds: only TopLevelName, Pop (infer_array_location) and the
   base a Subscript or Attribute passes through give a location other
   than memory: storage, transient, or code for an immutable.  That
   location is a function of cenv and the shape of e, not of the compile
   state.  The operands are literals, emitted variables, or a local's
   PtrVar (Var p), which well_typed_expr reaches only for names in
   env.var_types; ConvBytestringCast passes its argument's operand on.
   Bases and arguments have any type, so an induction needs a statement
   about every expression, not only strings. *)
Theorem compile_expr_string_reason:
  !cenv env e n.
    well_typed_expr env e /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
            ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
    expr_type e = BaseT (StringT n) ==>
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_vv_ok vv) \/
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_storage_vv vv) \/
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) ==>
                reason_code_vv vv)
Proof
  rpt strip_tac >>
  drule_all compile_expr_reason_uniform >>
  disch_then (qspec_then `expr_type e` mp_tac) >>
  rewrite_tac[reason_uniform_shape_def] >> strip_tac >>
  gvs[] >>
  metis_tac[reason_result_shape_memory, reason_result_shape_storage,
            reason_result_shape_code]
QED
