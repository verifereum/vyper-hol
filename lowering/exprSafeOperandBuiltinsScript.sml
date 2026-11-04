(*
 * The safe operands of the lowering's builtins, calls and names (#636)
 *
 * safe_operand (exprSafeOperand) of each builtin helper's result, and
 * word_result_ok of the value compile_call, compile_attribute,
 * compile_subscript, compile_name_vv and compile_literal_vv hand out at a
 * word type.
 *
 * TOP-LEVEL: one *_safe_operand or *_word_result_ok lemma per word helper;
 *   *_not_label boundaries for allocated and forwarded non-word results.
 *
 * Helpers: subscript_pop_not_label and ec_arith_result_not_label share the
 *   result-origin proofs across their respective lowering operations;
 *   compile_default_return_result exposes the return pointer retained by
 *   an external call's default path.
 *)

Theory exprSafeOperandBuiltins
Ancestors
  exprSafeOperand
  exprLoweringProps freshWrites compileEnv emitHelper context
  exprLowering exprCallBounds vyperTypeSystem vyperValue vyperAST vyperTypeBuiltins
  builtinSimple builtinMath builtinHashing builtinMisc builtinBytes builtinSystem

(* Non-label result origins, also for non-word types. *)

Theorem subscript_pop_not_label:
  (compile_mapping_subscript bop kop sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_array_subscript bop idx dyn cnt ws sz signed load sa = (op,sb) ==>
     !l. op <> Label l) /\
  (compile_dynarray_pop bop ws sz lopc sopc sa = (op,sb) ==>
     !l. op <> Label l)
Proof
  rpt conj_tac >>
  simp[compile_mapping_subscript_def, compile_array_subscript_def,
       compile_dynarray_pop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule emit_op_safe_operand >> simp[safe_operand_def]
QED

Theorem ec_arith_result_not_label:
  (compile_ecadd_points p1 p2 sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_ecmul_point p scalar sa = (op,sb) ==> !l. op <> Label l)
Proof
  conj_tac >>
  simp[compile_ecadd_points_def, compile_ecmul_point_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem compile_attribute_safe_operand:
  compile_attribute cfn cenv ret_ty ty base_e fname sa = (vv,sb) ==>
  safe_operand sb (vv_operand vv)
Proof
  simp[compile_attribute_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[emit_op_safe_operand]
QED

Theorem compile_subscript_not_label:
  compile_subscript cfn cenv rt ty base_e idx_e sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_subscript_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `place_type cenv base_e` >> simp[]
  >- (simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
      simp[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
      metis_tac[cj 1 subscript_pop_not_label]) >>
  rename1 `ValPT bty` >> Cases_on `bty` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  metis_tac[cj 2 subscript_pop_not_label, emit_op_safe_operand,
            compile_tuple_subscript_def, safe_operand_def]
QED

Theorem lower_abi_decode_not_label:
  lower_abi_decode data_op info amin amax bytes sa = (op,sb) ==> !l. op <> Label l
Proof
  simp[builtinAbiTheory.lower_abi_decode_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED

Theorem compile_empty_not_label:
  compile_builtin_empty_complex bytes bs sa = (buf,sb) ==>
  !l. buf.buf_operand <> Label l
Proof
  Cases_on `bs` >>
  simp[builtinSimpleTheory.compile_builtin_empty_complex_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[alloc_buffer_not_label]
QED


Theorem compile_builtin_abs_safe_operand:
  compile_builtin_abs v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_builtin_abs_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_select_safe_operand]
QED

Theorem compile_builtin_len_safe_operand:
  compile_builtin_len ctor imm ptr_op loc sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_builtin_len_def] >> metis_tac[compile_ptr_load_safe_operand]
QED

Theorem compile_acc_safe_operand:
  (acc = Address ==>
     !s r s'. lower_value cfn cenv (BaseT AddressT) e s = (r,s') ==>
                safe_operand s' r) /\
  compile_acc cfn cenv e acc sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `acc` >>
  simp[compile_acc_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand, safe_operand_Lit]
QED

Theorem compile_env_var_safe_operand:
  compile_env_var item sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `item` >> simp[compile_env_var_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_keccak256_word_safe_operand:
  compile_keccak256_word v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_keccak256_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_keccak256_bytes_safe_operand:
  compile_keccak256_bytes v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_keccak256_bytes_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_keccak256_bytesm_safe_operand:
  compile_keccak256_bytesm v m sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_sha256_word_safe_operand:
  compile_sha256_word v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_sha256_word_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_sha256_bytes_safe_operand:
  compile_sha256_bytes v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_sha256_bytes_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_sha256_bytesm_safe_operand:
  compile_sha256_bytesm v m sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_sha256_bytesm_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_ecrecover_safe_operand:
  compile_ecrecover h v r s sa = (op,sb) ==> safe_operand sb op
Proof
  simp[compile_ecrecover_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_blockhash_safe_operand:
  compile_blockhash v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_blockhash_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_blobhash_safe_operand:
  compile_blobhash v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_blobhash_def] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_floor_safe_operand:
  compile_floor v d sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_floor_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_ceil_safe_operand:
  compile_ceil v d sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_ceil_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_as_wei_value_int_safe_operand:
  safe_operand sa v /\ compile_as_wei_value_int v scale signed sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `scale = 1` >> Cases_on `signed` >>
  simp[compile_as_wei_value_int_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  gvs[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_extract32_load_safe_operand:
  compile_extract32_load l d v sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_extract32_load_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_clamp_basetype_returns:
  !v ty sa r sb. compile_clamp_basetype v ty sa = (r,sb) ==>
    r = v /\ sa.cs_next_var <= sb.cs_next_var
Proof
  ho_match_mp_tac compile_clamp_basetype_ind >>
  rw[compile_clamp_basetype_def, clamp_and_return_def, emit_op_def,
     emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
     fresh_id_def, fresh_var_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> imp_res_tac compile_clamp_next_var >> gvs[]
QED

Theorem compile_clamp_basetype_safe_operand:
  safe_operand sa v /\ compile_clamp_basetype v ty sa = (r,sb) ==>
  safe_operand sb r
Proof
  metis_tac[compile_clamp_basetype_returns, safe_operand_mono]
QED

Theorem compile_method_id_word_safe_operand:
  compile_method_id_runtime ty v T sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_method_id_runtime_def, comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[emit_op_safe_operand]
QED

(* Equality results stay safe while the remaining comparisons are emitted.
   Both folds preserve a safe accumulator, including their empty case. *)
Theorem emit_membership_eqs_safe_operand:
  !xs needle sa cs sb.
    emit_membership_eqs needle xs sa = (cs,sb) ==>
    EVERY (safe_operand sb) cs
Proof
  Induct >> simp[emit_membership_eqs_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_rename_tac `emit_membership_eqs needle xs st = (cs,sb)` >>
  qspecl_then [`xs`, `needle`, `st`] mp_tac ci_mono_emit_membership_eqs >>
  simp[ci_mono_def] >> strip_tac >>
  qpat_x_assum `!needle sa cs sb. _` drule_all >> strip_tac >> simp[] >>
  drule emit_op_safe_operand >> strip_tac >>
  irule safe_operand_mono >> qexists_tac `st` >> simp[]
QED

Theorem fold_membership_or_safe_operand:
  !xs acc sa r sb.
    safe_operand sa acc /\ fold_membership_or acc xs sa = (r,sb) ==>
    safe_operand sb r
Proof
  Induct >> simp[fold_membership_or_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand]
QED

Theorem fold_membership_and_safe_operand:
  !xs acc sa r sb.
    safe_operand sa acc /\ fold_membership_and acc xs sa = (r,sb) ==>
    safe_operand sb r
Proof
  Induct >> simp[fold_membership_and_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[emit_op_safe_operand]
QED

Theorem compile_list_membership_in_safe_operand:
  compile_list_membership_in needle xs sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_list_membership_in_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  drule emit_membership_eqs_safe_operand >> strip_tac >>
  qmatch_assum_rename_tac `EVERY (safe_operand st) cs` >>
  Cases_on `cs` >> gvs[comp_return_def] >>
  drule_all fold_membership_or_safe_operand >> simp[]
QED

Theorem compile_list_membership_notin_safe_operand:
  compile_list_membership_notin needle xs sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_list_membership_notin_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_rename_tac `emit_membership_eqs needle xs sa = (cs,st)` >>
  Cases_on `cs` >> gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule emit_op_safe_operand >> strip_tac >>
  drule_all fold_membership_and_safe_operand >> simp[]
QED

Theorem fresh_var_counter_mono[local]:
  fresh_var sa = (v,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> qspec_then `sa` mp_tac ci_mono_fresh_var >>
  simp[ci_mono_def]
QED

Theorem fresh_label_counter_mono[local]:
  fresh_label prefix sa = (v,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> qspecl_then [`prefix`, `sa`] mp_tac ci_mono_fresh_label >>
  simp[ci_mono_def]
QED

Theorem new_block_counter_mono[local]:
  new_block label sa = (v,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> qspecl_then [`label`, `sa`] mp_tac ci_mono_new_block >>
  simp[ci_mono_def]
QED

Theorem emit_inst_counter_mono[local]:
  emit_inst opc args outs sa = (v,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> qspecl_then [`opc`, `args`, `outs`, `sa`] mp_tac ci_mono_emit_inst >>
  simp[ci_mono_def]
QED

Theorem emit_op_counter_mono[local]:
  emit_op opc args sa = (v,sb) ==> sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> qspecl_then [`opc`, `args`, `sa`] mp_tac ci_mono_emit_op >>
  simp[ci_mono_def]
QED

Theorem compile_ptr_load_next_var:
  compile_ptr_load ctor imm loc p sa = (v,sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `ctor` >> Cases_on `imm` >> Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def, emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem membership_bind_safe[local]:
  ((!s v t. m s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
   (!v s r t. safe_operand s op /\ k v s = (r,t) ==> safe_operand t r)) ==>
  !s r t. safe_operand s op /\ comp_bind m k s = (r,t) ==>
    safe_operand t r
Proof
  rpt strip_tac >> gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  irule safe_operand_mono >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem membership_ignore_bind_safe[local]:
  ((!s v t. m s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
   (!s r t. safe_operand s op /\ k s = (r,t) ==> safe_operand t r)) ==>
  !s r t. safe_operand s op /\ comp_ignore_bind m k s = (r,t) ==>
    safe_operand t r
Proof
  rpt strip_tac >> gvs[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  irule safe_operand_mono >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem membership_fresh_bind_safe[local]:
  (!z s r t. safe_operand s (Var z) /\ k z s = (r,t) ==>
    safe_operand t r) ==>
  !s r t. comp_bind fresh_var k s = (r,t) ==> safe_operand t r
Proof
  rpt strip_tac >> gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  metis_tac[fresh_var_safe_operand]
QED

Theorem membership_bind_counter_mono[local]:
  ((!s v t. m s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
   (!v s r t. k v s = (r,t) ==> s.cs_next_var <= t.cs_next_var)) ==>
  !s r t. comp_bind m k s = (r,t) ==> s.cs_next_var <= t.cs_next_var
Proof
  rpt strip_tac >> gvs[comp_bind_def] >> pairarg_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem membership_ignore_bind_counter_mono[local]:
  ((!s v t. m s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
   (!s r t. k s = (r,t) ==> s.cs_next_var <= t.cs_next_var)) ==>
  !s r t. comp_ignore_bind m k s = (r,t) ==>
    s.cs_next_var <= t.cs_next_var
Proof
  rpt strip_tac >> gvs[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_array_membership_loop_safe_operand:
  (!p s v t. loader p s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
  compile_array_membership_loop needle arr len sz off loader bound isin sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `bound` >> Cases_on `isin` >> Cases_on `off > 0` >>
  simp[compile_array_membership_loop_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  strip_tac >>
  ntac 8 (pairarg_tac >> gvs[]) >>
  ntac 8 (pairarg_tac >> gvs[]) >>
  ntac 8 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `!p s v t. _` drule_all >> strip_tac >>
  imp_res_tac emit_op_safe_operand >>
  imp_res_tac fresh_var_safe_operand >>
  imp_res_tac fresh_var_counter_mono >>
  imp_res_tac fresh_label_counter_mono >>
  imp_res_tac new_block_counter_mono >>
  imp_res_tac emit_inst_counter_mono >>
  imp_res_tac emit_op_counter_mono >>
  irule safe_operand_mono >>
  goal_assum (drule_at (Pat `safe_operand _ _`)) >> decide_tac
QED

Theorem compile_var_array_membership_safe_operand:
  compile_var_array_membership cenv needle vv ty isin sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[compile_var_array_membership_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_array_membership_loop_safe_operand, compile_ptr_load_next_var]
QED

(* Keep the membership safety interface closed under the HOL kernel. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles then ()
     else raise Fail "admitted membership operand-safety theorem"
  end)
  [emit_membership_eqs_safe_operand, fold_membership_or_safe_operand,
   fold_membership_and_safe_operand, compile_list_membership_in_safe_operand,
   compile_list_membership_notin_safe_operand,
   compile_array_membership_loop_safe_operand,
   compile_var_array_membership_safe_operand];

(* ===== Calls, names, subscripts and literals ===== *)

Theorem as_stack_val_word_result_ok:
  (!r sb. result = (r,sb) ==> safe_operand sb r) /\
  as_stack_val ty result = (vv,sb) ==> word_result_ok sb vv
Proof
  Cases_on `result` >> simp[as_stack_val_def] >>
  strip_tac >> gvs[word_result_ok_def]
QED

Theorem compile_raw_call_finish_zero_safe_operand:
  compile_raw_call_finish addr p len gas value ct 0 rof ov optr sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `ct` >> Cases_on `rof` >>
  simp[compile_raw_call_finish_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_label_def, new_block_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def,
       compile_alloc_buffer_def] >>
  strip_tac >> gvs[] >>
  simp[safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem compile_external_call_zero_safe_operand:
  compile_external_call_kwargs cenv addr vals tys memsz abisz mid 0 minsz retsz
    static value gas skip default dop rt dt einfo dinfo sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[compile_external_call_kwargs_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[])
QED

(* Both raw_call forms: splitting off a second argument is needed for the
   byte-string form and harmless for the msg.data one. *)
val word_raw_call_tac =
  Cases_on `args` >-
    (simp[compile_call_def, LET_THM] >> strip_tac >>
     rpt (pairarg_tac >> gvs[]) >> gvs[word_result_ok_def]) >>
  Cases_on `t` >> simp[compile_call_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `r.rcf_max_outsize = 0` >> gvs[word_result_ok_def] >>
  metis_tac[compile_raw_call_finish_zero_safe_operand]

Theorem compile_call_word_result_ok:
  is_word_type rt /\ compile_call cfn cenv rt ty target args default_ret sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `target`
  >~ [`RawCallTarget`] >- word_raw_call_tac
  >~ [`RawCallCalldataTarget`] >- word_raw_call_tac >>
  simp[compile_call_def, LET_THM] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  gvs[word_result_ok_def]
  >~ [`cenv.ce_func_info name = info`] >- suspend "internal"
  >~ [`compile_call cfn cenv rt ty (ExtCall b b0 p l) args default_ret sa = _`]
    >- suspend "external"
  >> suspend "send"
QED

Resume compile_call_word_result_ok[internal]:
  Cases_on `returns_count > 0` >> Cases_on `return_buf` >>
  gvs[word_result_ok_def] >> rpt (pairarg_tac >> gvs[word_result_ok_def]) >>
  metis_tac[emit_op_safe_operand]
QED

Resume compile_call_word_result_ok[external]:
  PairCases_on `p` >> Cases_on `args` >>
  gvs[compile_call_def, LET_THM, word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[word_result_ok_def] >>
  qpat_x_assum `(if _ then _ else _) = (vv,sb)` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[word_result_ok_def] >>
  metis_tac[compile_external_call_zero_safe_operand]
QED

Resume compile_call_word_result_ok[send]:
  Cases_on `args` >> gvs[word_result_ok_def] >> rename1 `list_CASE args1 _ _` >>
  Cases_on `args1` >> gvs[word_result_ok_def] >>
  rename1 `LENGTH args2 = if flag then 1 else 0` >>
  Cases_on `LENGTH args2 = if flag then 1 else 0` >> gvs[word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Finalise compile_call_word_result_ok

Theorem as_ptr_val_word_result_ok:
  is_word_type ty /\ as_ptr_val ty loc result = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `result` >> simp[as_ptr_val_def, word_result_ok_def] >>
  strip_tac >> gvs[word_result_ok_def]
QED

Theorem compile_attribute_word_result_ok:
  is_word_type rt /\ compile_attribute cfn cenv rt ty e fld sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  simp[compile_attribute_def, LET_THM, comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem compile_subscript_word_result_ok:
  is_word_type rt /\ compile_subscript cfn cenv rt ty e idx sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  reverse (Cases_on `place_type cenv e`)
  >- (rename1 `place_type cenv e = ValPT bt` >> Cases_on `bt` >>
      simp[compile_subscript_def, LET_THM, comp_bind_def, comp_return_def] >>
      strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  simp[compile_subscript_def, LET_THM, comp_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Theorem compile_builtin_calldatasize_safe_operand:
  compile_builtin_calldatasize sa = (r,sb) ==> safe_operand sb r
Proof
  simp[compile_builtin_calldatasize_def] >> metis_tac[emit_op_safe_operand]
QED

Theorem compile_name_vv_word_result_ok:
  is_word_type ty /\ compile_name_vv cenv ty id sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[compile_name_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >-
    (strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME bnd` >> Cases_on `bnd` >>
  simp[compile_name_vv_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[word_result_ok_def]) >>
  gvs[word_result_ok_def]
QED

Theorem compile_literal_vv_word_result_ok:
  is_word_type ty /\ compile_literal_vv ty lit sa = (vv,sb) ==>
  word_result_ok sb vv
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, comp_return_def] >>
  rpt strip_tac
  >~ [`BoolL b`] >-
    (Cases_on `b` >> gvs[compile_literal_vv_def, comp_return_def, word_result_ok_def])
  >~ [`BytesV bs`] >-
    (Cases_on `ty` >> gvs[compile_literal_vv_def, comp_bind_def,
                          comp_return_def, word_result_ok_def] >>
     Cases_on `b` >> gvs[compile_literal_vv_def, comp_bind_def,
                         comp_return_def, word_result_ok_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[compile_literal_vv_def, comp_bind_def,
                         comp_return_def, word_result_ok_def] >>
     rpt (pairarg_tac >> gvs[word_result_ok_def])) >>
  gvs[word_result_ok_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

(* Calls return an allocated buffer or an instruction result. *)
Theorem compile_default_return_result:
  compile_default_return_path cenv rt dt buf res dop addr skip mn mx info sa =
    (op,sb) ==> op = res
Proof
  simp[compile_default_return_path_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[]
QED

Theorem compile_external_call_not_label:
  compile_external_call_kwargs cenv addr vals tys msz asz mid rsz mn rms
    stat value gas skip hasdef dop rt dt einfo dinfo sa = (op,sb) ==>
  !l. op <> Label l
Proof
  simp[compile_external_call_kwargs_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `rsz = 0` >> simp[comp_return_def] >>
  Cases_on `hasdef` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[compile_default_return_result, alloc_buffer_not_label]
QED

Theorem compile_internal_call_not_label:
  compile_call cfn cenv rt ty (IntCall fid) args drv sa = (vv,sb) ==>
  !l. vv_operand vv <> Label l
Proof
  simp[compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac alloc_buffer_not_label >>
  gvs[contextTheory.vv_operand_def, contextTheory.base_ptr_def]
QED

