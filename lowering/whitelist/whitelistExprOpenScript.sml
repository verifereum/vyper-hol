(*
 * compile_expr keeps its block open: the builtin forms outside the
 * supported subset
 *
 * TOP-LEVEL:
 *   compile_len_open, compile_calldatalen_open, compile_keccak256_open,
 *   compile_sha256_open, compile_ceil_open, compile_floor_open,
 *   compile_method_id_open, compile_concat_open, compile_slice_open
 *                         — compile_builtin_dispatch_body for that builtin
 *   compile_extract32_open — compile_type_builtin_dispatch_body for Extract32
 *   compile_flag_member_open — compile_expr for a FlagMember
 *
 * Not and CalldataSlice are already covered for every argument type by
 * compile_dispatch_not_open and compile_dispatch_terminal_open.
 *)

Theory whitelistExprOpen
Ancestors
  exprOpenPrimitives exprOpenBuiltins exprLowering compileEnv context emitHelper venomInst
  builtinSimple builtinMisc builtinBytes builtinHashing list pair

(* ----- helpers ----- *)

Theorem compile_keccak256_word_open[local]:
  !v sa r sb. compile_keccak256_word v sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_keccak256_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_keccak256_bytes_open[local]:
  !p sa r sb. compile_keccak256_bytes p sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_keccak256_bytes_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_keccak256_bytesm_open[local]:
  !v m sa r sb. compile_keccak256_bytesm v m sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_sha256_word_open[local]:
  !v sa r sb. compile_sha256_word v sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_sha256_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_sha256_bytes_open[local]:
  !p sa r sb. compile_sha256_bytes p sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_sha256_bytes_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_sha256_bytesm_open[local]:
  !v m sa r sb. compile_sha256_bytesm v m sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_sha256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_floor_helper_open[local]:
  !v d sa r sb. compile_floor v d sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_floor_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_ceil_helper_open[local]:
  !v d sa r sb. compile_ceil v d sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_ceil_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_method_id_runtime_open[local]:
  !ty v b sa r sb.
    compile_method_id_runtime ty v b sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_method_id_runtime_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> Cases_on `b` >>
  simp[comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
  >- (drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_assert_slice_bounds_open[local]:
  !s l n sa r sb.
    compile_assert_slice_bounds s l n sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_slice_data_open[local]:
  !len data s l size sa r sb.
    compile_slice_data len data s l size sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_slice_data_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_slice_code_open[local]:
  !s l size sa r sb.
    compile_slice_code s l size sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_slice_code_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> rename1 `compile_slice_out_buf _ _ = (bufs,cs)` >>
  PairCases_on `bufs` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_slice_extcode_open[local]:
  !a s l buf data sa r sb.
    compile_slice_extcode a s l buf data sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_slice_extcode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_extract32_load_open[local]:
  !len data s sa r sb.
    compile_extract32_load len data s sa = (r,sb) ==> ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_extract32_load_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_clamp_basetype_open[local]:
  !v ty sa r sb.
    ~block_is_terminated sa /\ compile_clamp_basetype v ty sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> Cases_on `ty` >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt`) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
  simp[compile_clamp_basetype_def, comp_return_def] >>
  rpt IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[clamp_and_return_open, emit_void_terminated, is_terminator_def]
QED

(* ----- the dispatch cases ----- *)

Theorem compile_len_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty Len args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[oneline as_stack_val_def, AllCaseEqs()] >>
  strip_tac >> gvs[compile_builtin_len_def] >>
  drule compile_ptr_load_open >> simp[]
QED

Theorem compile_calldatalen_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty CalldataLen args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_builtin_dispatch_body_def, compile_builtin_calldatasize_def,
       oneline as_stack_val_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem compile_keccak256_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty Keccak256 args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> gvs[]
  >- (gvs[oneline as_stack_val_def, AllCaseEqs()] >>
      drule compile_keccak256_bytes_open >> simp[]) >>
  Cases_on `expr_type (HD args)` >> gvs[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  imp_res_tac compile_keccak256_word_open >> imp_res_tac compile_keccak256_bytesm_open >>
  gvs[]
QED

Theorem compile_sha256_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty Sha256 args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> gvs[]
  >- (gvs[oneline as_stack_val_def, AllCaseEqs()] >>
      drule compile_sha256_bytes_open >> simp[]) >>
  Cases_on `expr_type (HD args)` >> gvs[] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[]) >>
  gvs[oneline as_stack_val_def, AllCaseEqs()] >>
  imp_res_tac compile_sha256_word_open >> imp_res_tac compile_sha256_bytesm_open >>
  gvs[]
QED

Theorem compile_ceil_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty Ceil args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[oneline as_stack_val_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule compile_ceil_helper_open >> simp[]
QED

Theorem compile_floor_open:
  !cfn cenv rty ty args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty Floor args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  pairarg_tac >> simp[oneline as_stack_val_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule compile_floor_helper_open >> simp[]
QED

Theorem compile_method_id_open:
  !cfn cenv rty ty args sa vv sb.
    ~block_is_terminated sa /\
    compile_builtin_dispatch_body cfn cenv rty ty MethodId args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `method_id_literal (HD args)` >> gvs[]
  >- (Cases_on `rty = BaseT (BytesT (Fixed 4))` >>
      gvs[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
      drule compile_method_id_runtime_open >> simp[]) >>
  drule_all compile_literal_vv_open >> simp[]
QED

Theorem compile_concat_open:
  !cfn cenv rty ty n args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty (Concat n) args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem compile_slice_open:
  !cfn cenv rty ty n args sa vv sb.
    compile_builtin_dispatch_body cfn cenv rty ty (Slice n) args sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_builtin_dispatch_body_def] >> strip_tac >>
  Cases_on `is_msg_data (HD args)` >> gvs[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
      drule compile_slice_calldata_open >> simp[]) >>
  Cases_on `is_self_code (HD args)` >> gvs[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
      drule compile_slice_code_open >> simp[]) >>
  Cases_on `is_extcode (HD args)` >> gvs[]
  >- (rpt (pairarg_tac >> gvs[]) >>
      gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
      drule compile_slice_extcode_open >> simp[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[oneline as_ptr_val_def, AllCaseEqs()] >>
  drule compile_slice_data_open >> simp[]
QED

Theorem compile_extract32_open:
  !cfn cenv vty ty rty args sa vv sb.
    compile_type_builtin_dispatch_body cfn cenv vty ty Extract32 rty args sa =
      (vv,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[oneline as_stack_val_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_clamp_basetype _ _ _ = _`) compile_clamp_basetype_open >>
  disch_then irule >> metis_tac[compile_extract32_load_open]
QED

Theorem compile_flag_member_open:
  !cenv aty ann fl m sa vv sb.
    ~block_is_terminated sa /\
    compile_expr cenv aty (FlagMember ann fl m) sa = (vv,sb) ==>
    ~block_is_terminated sb
Proof
  simp[Once compile_expr_def]
QED
