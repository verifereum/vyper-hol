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
  builtinCreate

(* Non-label result origins, also for non-word types. *)

Theorem subscript_pop_not_label:
  (compile_mapping_subscript bop kop sa = (op,sb) ==> !l. op <> Label l) /\
  (compile_array_subscript bop idx dyn cnt ws sz signed load sa = (op,sb) ==>
     !l. op <> Label l) /\
  (compile_dynarray_pop bop ws sz is_ctor imm loc sa = (op,sb) ==>
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

Theorem membership_primitive_next_var[local]:
  (!s. s.cs_next_var <= (SND (fresh_var s)).cs_next_var) /\
  (!p s. s.cs_next_var <= (SND (fresh_label p s)).cs_next_var) /\
  (!l s. s.cs_next_var <= (SND (new_block l s)).cs_next_var) /\
  (!opc ops outs s. s.cs_next_var <= (SND (emit_inst opc ops outs s)).cs_next_var) /\
  (!opc ops s. s.cs_next_var <= (SND (emit_op opc ops s)).cs_next_var)
Proof
  rpt conj_tac >> rpt gen_tac
  >- (mp_tac (Q.SPEC `s` ci_mono_fresh_var) >> gvs[ci_mono_def])
  >- (mp_tac (Q.SPECL [`p`, `s`] ci_mono_fresh_label) >> gvs[ci_mono_def])
  >- (mp_tac (Q.SPECL [`l`, `s`] ci_mono_new_block) >> gvs[ci_mono_def])
  >- (mp_tac (Q.SPECL [`opc`, `ops`, `outs`, `s`] ci_mono_emit_inst) >>
      gvs[ci_mono_def]) >>
  mp_tac (Q.SPECL [`opc`, `ops`, `s`] ci_mono_emit_op) >> gvs[ci_mono_def]
QED

Theorem membership_bind_preserve[local]:
  (!s. s.cs_next_var <= (SND (f s)).cs_next_var) /\
  (!x s. safe_operand s op ==>
     safe_operand (SND (g x s)) (FST (g x s))) ==>
  !s. safe_operand s op ==>
    safe_operand (SND (comp_bind f g s)) (FST (comp_bind f g s))
Proof
  strip_tac >> gen_tac >> strip_tac >> simp[comp_bind_def] >>
  Cases_on `f s` >> simp[] >>
  first_x_assum irule >> irule safe_operand_mono >>
  qexists_tac `s` >> gvs[] >> metis_tac[pairTheory.SND]
QED

Theorem membership_ignore_preserve[local]:
  (!s. s.cs_next_var <= (SND (f s)).cs_next_var) /\
  (!s. safe_operand s op ==>
     safe_operand (SND (g s)) (FST (g s))) ==>
  !s. safe_operand s op ==>
    safe_operand (SND (comp_ignore_bind f g s))
                 (FST (comp_ignore_bind f g s))
Proof
  strip_tac >> pure_rewrite_tac[comp_ignore_bind_def] >>
  ho_match_mp_tac membership_bind_preserve >> simp[]
QED

Theorem membership_fresh_start[local]:
  (!v s. safe_operand s (Var v) ==>
    safe_operand (SND (g v s)) (FST (g v s))) ==>
  !s. safe_operand (SND (comp_bind fresh_var g s))
                  (FST (comp_bind fresh_var g s))
Proof
  strip_tac >> gen_tac >> simp[comp_bind_def] >>
  Cases_on `fresh_var s` >> simp[] >>
  first_x_assum irule >> metis_tac[fresh_var_safe_operand]
QED

Theorem compile_array_membership_loop_safe_operand:
  (!p s v t. loader p s = (v,t) ==> s.cs_next_var <= t.cs_next_var) /\
  compile_array_membership_loop needle arr len sz off loader bound isin sa = (r,sb) ==>
  safe_operand sb r
Proof
  strip_tac >>
  `!p s. s.cs_next_var <= (SND (loader p s)).cs_next_var` by
    (rpt gen_tac >> Cases_on `loader p s` >> gvs[] >> metis_tac[]) >>
  `!s. safe_operand
      (SND (compile_array_membership_loop needle arr len sz off loader bound isin s))
      (FST (compile_array_membership_loop needle arr len sz off loader bound isin s))` suffices_by
    (disch_then (qspec_then `sa` mp_tac) >> simp[]) >>
  Cases_on `bound` >> Cases_on `isin` >> Cases_on `off > 0` >>
  pure_rewrite_tac[compile_array_membership_loop_def] >>
  ho_match_mp_tac membership_fresh_start >>
  rpt (FIRST [ho_match_mp_tac membership_bind_preserve,
              ho_match_mp_tac membership_ignore_preserve,
              gen_tac] >>
       rpt conj_tac >> BETA_TAC) >>
  simp[membership_primitive_next_var, comp_return_def] >>
  metis_tac[emit_op_safe_operand, pairTheory.PAIR]
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
  compile_external_call_kwargs cenv addr vals tys memsz abisz mid retsz minsz
    outsz static value gas skip default dop NoneT dt einfo dinfo sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[compile_external_call_kwargs_def, LET_THM,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[])
QED

(* Creation always hands out a fresh CREATE/CREATE2 result, even when
   failure checking emits further instructions or starts a new block. *)
Theorem compile_check_create_result_safe_operand:
  safe_operand sa addr /\
  compile_check_create_result addr rof sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `rof` >>
  simp[compile_check_create_result_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, emit_inst_def, fresh_label_def,
       new_block_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  gvs[safe_operand_def, not_fresh_at_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Theorem emit_void_preserves_safe_operand:
  safe_operand sa r /\ emit_void opc ops sa = (u,sb) ==> safe_operand sb r
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[safe_operand_def, not_fresh_at_def]
QED

Theorem compile_create_dispatch_safe_operand:
  compile_create_dispatch code_ptr len value salt rof sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `salt` >> simp[compile_create_dispatch_def, comp_bind_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_check_create_result_safe_operand, emit_op_safe_operand]
QED

Theorem compile_create_copy_safe_operand:
  compile_create_copy target value salt rof sa = (r,sb) ==> safe_operand sb r
Proof
  Cases_on `salt` >> Cases_on `rof` >>
  simp[compile_create_copy_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_check_create_result_safe_operand, emit_op_safe_operand,
            emit_void_preserves_safe_operand]
QED

Theorem compile_create_blueprint_append_safe_operand:
  compile_create_blueprint_append target value salt offset code_size code_ptr len rof sa =
    (r,sb) ==> safe_operand sb r
Proof
  Cases_on `salt` >> Cases_on `rof` >>
  simp[compile_create_blueprint_append_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  metis_tac[compile_check_create_result_safe_operand, emit_op_safe_operand,
            emit_void_preserves_safe_operand]
QED

Theorem compile_raw_create_safe_operand:
  compile_raw_create cfn cenv bytecode value args salt rof sa = (r,sb) ==>
  safe_operand sb r
Proof
  simp[compile_raw_create_def, LET_THM, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  strip_tac >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  metis_tac[compile_create_dispatch_safe_operand]
QED

Theorem compile_create_call_safe_operand:
  compile_create_call cfn cenv ck salted rof args sa = (r,sb) ==>
  safe_operand sb r
Proof
  Cases_on `args`
  >- (simp[compile_create_call_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def] >>
      strip_tac >> pairarg_tac >> gvs[]) >>
  rename1 `target::rest` >> Cases_on `rest`
  >- (simp[compile_create_call_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def] >>
      strip_tac >> pairarg_tac >> gvs[]) >>
  simp[compile_create_call_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `ck` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  metis_tac[compile_create_dispatch_safe_operand, compile_create_copy_safe_operand,
            compile_create_blueprint_append_safe_operand, compile_raw_create_safe_operand]
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
  metis_tac[compile_raw_call_finish_zero_safe_operand,
            safe_operand_mono, ci_mono_emit_void, ci_mono_def, pairTheory.SND]

Theorem compile_call_steps_next_var[local]:
  (compile_stage_intcall_args cenv vals flags tys sa = (r1,sb) ==>
   sa.cs_next_var <= sb.cs_next_var) /\
  (emit_multi_op opc ops n sa = (r2,sb) ==>
   sa.cs_next_var <= sb.cs_next_var) /\
  (store_multi_results buf_op results offset sa = (r3,sb) ==>
   sa.cs_next_var <= sb.cs_next_var) /\
  (emit_void opc ops sa = (r4,sb) ==> sa.cs_next_var <= sb.cs_next_var)
Proof
  rpt conj_tac >> strip_tac
  >- (qspecl_then [`cenv`, `vals`, `flags`, `tys`, `sa`] mp_tac
        ci_mono_compile_stage_intcall_args >> simp[ci_mono_def])
  >- (qspecl_then [`opc`, `ops`, `n`, `sa`] mp_tac ci_mono_emit_multi_op >>
      simp[ci_mono_def])
  >- (qspecl_then [`buf_op`, `results`, `offset`, `sa`] mp_tac
        ci_mono_store_multi_results >> simp[ci_mono_def]) >>
  qspecl_then [`opc`, `ops`, `sa`] mp_tac ci_mono_emit_void >>
  simp[ci_mono_def]
QED

(* Closes safe_operand sb op from an assumption safe_operand st op and the
   cs_next_var chain from st to sb among the assumptions. *)
val safe_buf_mono_tac : tactic = fn (g as (asl, w)) =>
  let
    val opnd = rand w
    fun is_safe_of a =
      (case strip_comb a of
         (f, [_, x]) => same_const f ``safe_operand`` andalso aconv x opnd
       | _ => false)
    val st = hd (snd (strip_comb (valOf (List.find is_safe_of asl))))
  in
    (irule safe_operand_mono >> exists_tac st >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) g
  end

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
  >~ [`as_stack_val rt (compile_create_call cfn cenv ck salted rof args sa)`]
    >- suspend "create"
  >~ [`raw_log_topic_exprs _`] >- suspend "log"
  >~ [`compile_raw_revert _ _`] >- suspend "revert"
  >> suspend "send"
QED

Resume compile_call_word_result_ok[internal]:
  Cases_on `returns_count > 0` >> Cases_on `return_buf` >>
  gvs[word_result_ok_def, contextTheory.base_ptr_def] >>
  rpt (pairarg_tac >> gvs[word_result_ok_def, contextTheory.base_ptr_def]) >>
  imp_res_tac compile_call_steps_next_var >>
  imp_res_tac alloc_buffer_safe_operand >>
  disj2_tac >> Cases_on `return_buf_size > 0` >> gvs[] >>
  safe_buf_mono_tac
QED

Resume compile_call_word_result_ok[external]:
  PairCases_on `p` >> Cases_on `args` >>
  gvs[compile_call_def, LET_THM, word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[word_result_ok_def] >>
  qpat_x_assum `(if _ then _ else _) = (vv,sb)` mp_tac >>
  IF_CASES_TAC >> simp[] >> strip_tac >> gvs[word_result_ok_def] >>
  metis_tac[compile_external_call_zero_safe_operand]
QED

Resume compile_call_word_result_ok[create]:
  irule as_stack_val_word_result_ok >>
  metis_tac[compile_create_call_safe_operand]
QED

Resume compile_call_word_result_ok[send]:
  Cases_on `args` >> gvs[word_result_ok_def] >> rename1 `list_CASE args1 _ _` >>
  Cases_on `args1` >> gvs[word_result_ok_def] >>
  rename1 `LENGTH args2 = if flag then 1 else 0` >>
  Cases_on `LENGTH args2 = if flag then 1 else 0` >> gvs[word_result_ok_def] >>
  rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

(* These system calls return a literal placeholder on every path, including
   invalid arities. Split their argument shapes before destructing the lets. *)
Resume compile_call_word_result_ok[log]:
  Cases_on `args` >> gvs[word_result_ok_def] >> rename1 `list_CASE args1 _ _` >>
  Cases_on `args1` >> gvs[word_result_ok_def] >> rename1 `list_CASE args2 _ _` >>
  Cases_on `args2` >> gvs[word_result_ok_def] >>
  rename1 `expr_type data_e = BaseT (BytesT (Fixed 32))` >>
  Cases_on `expr_type data_e = BaseT (BytesT (Fixed 32))` >>
  gvs[word_result_ok_def] >> rpt (pairarg_tac >> gvs[word_result_ok_def])
QED

Resume compile_call_word_result_ok[revert]:
  Cases_on `args` >> gvs[word_result_ok_def] >> rename1 `list_CASE rest _ _` >>
  Cases_on `rest` >> gvs[word_result_ok_def] >>
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
  Cases_on `rt = NoneT` >> simp[comp_return_def] >>
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

