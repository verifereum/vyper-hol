(* Callback-parametric expression and call-argument operand boundaries. *)
Theory runtimeLabelExprCallbacks
Ancestors
  runtimeLabelExprPrimitives runtimeLabelBuiltinCore runtimeLabelBuiltinSystem runtimeLabelBuiltinArithmetic
  runtimeLabelPrimitives runtimeLabelValues runtimeLabelInvariant builtinBytes context compileEnv
  emitHelper venomInst list builtinSimple builtinSystem builtinMath builtinHashing
  builtinStrings builtinMisc builtinAbi builtinCreate exprLowering exprCallbackContracts

Theorem rb_compile_stage_intcall_args:
  !es flags tys. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_operand_ok) (compile_stage_intcall_args cfn ce es flags tys)
Proof
  Induct >> simp[compile_stage_intcall_args_def, rb_step_return] >>
  rpt strip_tac >> Cases_on `flags` >> Cases_on `tys` >>
  simp[compile_stage_intcall_args_def, LET_THM] >> BETA_TAC
  >~ [`compile_stage_intcall_args cfn ce (h::es) (flag::fs) (ty::ts)`]
  >- (Cases_on `flag` >> simp[compile_stage_intcall_args_def, LET_THM] >>
      BETA_TAC >- suspend "stack" >> suspend "memory")
  >> suspend "stack"
QED

Resume rb_compile_stage_intcall_args[stack]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (first_x_assum irule >> simp[]) >>
   simp[rb_step_return])
QED

Resume rb_compile_stage_intcall_args[memory]:
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (IF_CASES_TAC >> simp[rb_emit_void] >> IF_CASES_TAC >>
      simp[rb_compile_store_memory] >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >>
      simp[rb_compile_store_bytestring, rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED
Finalise rb_compile_stage_intcall_args

Theorem rb_lower_value:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce ty e) ==>
  rb_step rb_operand_ok (lower_value cfn ce ty e)
Proof
  strip_tac >> pure_rewrite_tac[lower_value_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >>
  BETA_TAC >> simp[rb_unwrap_value]
QED

Theorem rb_lower_value_with_loc:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce ty e) ==>
  rb_step (rb_operand_ok o FST) (lower_value_with_loc cfn ce ty e)
Proof
  strip_tac >> pure_rewrite_tac[lower_value_with_loc_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >>
  BETA_TAC >> simp[rb_unwrap_value, rb_step_return]
QED

Theorem rb_compile_multi_exprs:
  !es. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_operand_ok) (compile_multi_exprs cfn ce es)
Proof
  Induct >> simp[compile_multi_exprs_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_attribute:
  rb_step rb_value_ok (cfn ce ty e) ==>
  rb_step rb_value_ok (compile_attribute cfn ce ret_ty ty e fld)
Proof
  strip_tac >> pure_rewrite_tac[compile_attribute_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_value_operand, rb_step_return, rb_value_ok_def, rb_mk_ptr]
QED

Theorem rb_compile_make_tuple:
  !es tys buf off. rb_env_ok ce /\ rb_operand_ok buf /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_make_tuple cfn ce es tys buf off)
Proof
  Induct >> simp[compile_make_tuple_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `tys` >> simp[compile_make_tuple_def, rb_step_return] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem rb_compile_make_array_elems:
  !es buf idx. rb_env_ok ce /\ rb_operand_ok buf /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok
    (compile_make_array_elems cfn ce es et sz has_len buf idx)
Proof
  Induct >> simp[compile_make_array_elems_def, rb_step_return] >> rpt strip_tac >>
  pure_rewrite_tac[compile_make_array_elems_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem rb_compile_make_array:
  rb_env_ok ce /\ rb_operand_ok buf /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_make_array cfn ce es et sz has_len buf)
Proof
  strip_tac >> pure_rewrite_tac[compile_make_array_def] >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `has_len` >> simp[rb_emit_void, rb_step_return]) >>
  simp[rb_compile_make_array_elems]
QED

Theorem rb_compile_struct_lit:
  !flds buf off. rb_env_ok ce /\ rb_operand_ok buf /\
  (!nm e. MEM (nm,e) flds ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_struct_lit cfn ce ty flds buf off)
Proof
  Induct >> simp[compile_struct_lit_def, rb_step_return] >> rpt strip_tac >>
  PairCases_on `h` >> pure_rewrite_tac[compile_struct_lit_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> qexists_tac `h0` >> simp[]) >>
  gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_store_memory] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem rb_compile_store_abi_tuple:
  !args buf off. EVERY (rb_operand_ok o FST) args /\ rb_operand_ok buf ==>
  rb_step (K T) (compile_store_abi_tuple ce buf off args)
Proof
  Induct >> simp[compile_store_abi_tuple_def, rb_step_return] >> rpt strip_tac >>
  PairCases_on `h` >> gvs[] >>
  pure_rewrite_tac[compile_store_abi_tuple_def] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac
  >- (Cases_on `is_word_type h1` >> simp[rb_emit_void, rb_compile_copy_memory]) >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_concat:
  !es infos. rb_env_ok ce /\ rb_operand_ok dp /\ rb_operand_ok offp /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (K T) (compile_concat cfn ce es dp infos offp)
Proof
  Induct >> simp[compile_concat_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `infos` >> simp[compile_concat_def, rb_step_return] >>
  PairCases_on `h'` >> simp[compile_concat_def] >>
  Cases_on `h'0` >> simp[]
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
      rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
      first_x_assum irule >> simp[]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  rpt (irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac) >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_emit_void] >>
  first_x_assum irule >> simp[]
QED

Theorem rb_compile_materialize_vv:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_materialize_vv ce ty vv)
Proof
  strip_tac >> pure_rewrite_tac[compile_materialize_vv_def] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_store_memory, rb_step_return]
QED

Theorem rb_compile_ifexp_arm:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_ifexp_arm ce rty aty vv)
Proof
  strip_tac >> pure_rewrite_tac[compile_ifexp_arm_def] >>
  IF_CASES_TAC >- simp[rb_unwrap_value] >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_unwrap_value] >> gen_tac >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_store_memory, rb_step_return]
QED

Theorem rb_compile_snapshot_vv:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_value_ok (compile_snapshot_vv ce copy vv)
Proof
  strip_tac >> pure_rewrite_tac[compile_snapshot_vv_def] >>
  IF_CASES_TAC
  >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      simp[rb_unwrap_value, rb_step_return, rb_value_ok_def]) >>
  Cases_on `copy` >> simp[rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_materialize_vv, rb_step_return, rb_value_ok_def, rb_mk_ptr]
QED

Theorem rb_compile_abi_encode_args:
  !es. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_operand_ok) (compile_abi_encode_args cfn ce es)
Proof
  Induct >> simp[compile_abi_encode_args_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_materialize_vv, rb_unwrap_value]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_subscript:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce ty be) /\
  rb_step rb_value_ok (cfn ce (expr_type ie) ie) /\
  rb_step rb_value_ok (cfn ce ty ie) ==>
  rb_step rb_value_ok (compile_subscript cfn ce ret_ty ty be ie)
Proof
  strip_tac >> pure_rewrite_tac[compile_subscript_def] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_snapshot_vv, rb_step_return]) >>
  gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  reverse (Cases_on `place_type ce be`)
  >- (rename1 `ValPT bt` >> Cases_on `bt` >> simp[] >>
      pure_rewrite_tac[LET_THM] >> BETA_TAC
      >~ [`compile_tuple_subscript _ _`] >- suspend "tuple"
      >~ [`compile_tuple_subscript _ _`] >- suspend "tuple"
      >> suspend "array") >>
  simp[] >> irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[rb_compile_keccak256_key, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_mapping_subscript, rb_value_operand, rb_step_return,
       rb_value_ok_def, rb_mk_ptr]
QED

Resume rb_compile_subscript[tuple]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   simp[rb_compile_tuple_subscript, rb_value_operand, rb_step_return,
        rb_value_ok_def, rb_mk_ptr])
QED

Resume rb_compile_subscript[array]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   conj_tac >- simp[rb_step_return, rb_value_ok_def, rb_mk_ptr] >>
   irule rb_compile_array_subscript >> simp[rb_value_operand] >>
   gen_tac >> strip_tac >> irule rb_compile_ptr_load >> gvs[rb_env_ok_def])
QED
Finalise rb_compile_subscript

Theorem rb_every_zip_fst:
  !xs ys P. EVERY P xs ==> EVERY (P o FST) (ZIP (xs,ys))
Proof
  Induct >> Cases_on `ys` >> simp[listTheory.ZIP_def]
QED

Theorem rb_ext_call_arg_value:
  !vv. rb_value_ok vv ==> rb_value_ok (ext_call_arg_value ty vv)
Proof
  Cases >> simp[ext_call_arg_value_def, rb_value_ok_def]
QED

Theorem rb_compile_ext_call_args:
  !es tys. rb_env_ok ce /\
  (!e. MEM e es ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (EVERY rb_value_ok) (compile_ext_call_args cfn ce kws tys es)
Proof
  Induct >> simp[compile_ext_call_args_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `tys` >> simp[compile_ext_call_args_def, rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_snapshot_vv, rb_ext_call_arg_value] >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `EVERY rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  simp[rb_step_return]
QED

Theorem rb_compile_ext_call_kwarg:
  rb_env_ok ce /\ (!ty. rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step (rb_operand_ok o FST) (compile_ext_call_kwarg cfn ce rty k e)
Proof
  strip_tac >> pure_rewrite_tac[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC
  >- (pure_rewrite_tac[LET_THM] >> BETA_TAC >>
      irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      simp[rb_compile_materialize_vv, rb_step_return]) >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_lower_value, rb_step_return]
QED

Theorem rb_compile_ext_call_kwargs:
  !es ks. rb_env_ok ce /\
  (!e ty. MEM e es ==> rb_step rb_value_ok (cfn ce ty e)) ==>
  rb_step (\p. OPTION_ALL rb_operand_ok (FST p) /\
               OPTION_ALL rb_operand_ok (FST (SND p)) /\
               OPTION_ALL (rb_operand_ok o FST) (SND (SND p)))
    (compile_ext_call_kwargs cfn ce rty ks es)
Proof
  Induct >> simp[compile_ext_call_kwargs_def, rb_step_return] >> rpt strip_tac >>
  Cases_on `ks` >> simp[compile_ext_call_kwargs_def, rb_step_return] >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_ext_call_kwarg] >>
  Cases >> simp[] >> strip_tac >>
  irule rb_step_bind >>
  qexists_tac `\p. OPTION_ALL rb_operand_ok (FST p) /\
                   OPTION_ALL rb_operand_ok (FST (SND p)) /\
                   OPTION_ALL (rb_operand_ok o FST) (SND (SND p))` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[]) >>
  PairCases >> simp[] >> strip_tac >>
  rpt IF_CASES_TAC >> simp[rb_step_return]
QED

Theorem rb_compile_create_salt:
  !salt. rb_env_ok ce /\
  (!e. salt = SOME e ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (OPTION_ALL rb_operand_ok) (compile_create_salt cfn ce salt)
Proof
  Cases >> simp[compile_create_salt_def, rb_step_return] >> rpt strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_lower_value, rb_step_return]
QED

Theorem rb_compile_create_ctor_tuple:
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_create_ctor_tuple cfn ce args)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_ctor_tuple_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `EVERY rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_multi_vvs] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_extcall_store_values, rb_every_zip_fst, rb_step_return]
QED

(* Encoder antecedent: conjunct 2 of runtimeLabelABI$rb_abi_encode. *)
Theorem rb_compile_create_blueprint_args:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step (\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p))
    (compile_create_blueprint_args cfn ce raw args)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_blueprint_args_def] >>
  Cases_on `raw` >> simp[]
  >- (Cases_on `args` >> simp[]
      >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]) >>
      Cases_on `t` >> simp[]
      >- (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
          reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
          irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
          irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]) >>
  Cases_on `args = []` >> simp[rb_step_return] >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_ctor_tuple] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_step_return]
QED

Theorem rb_compile_create_snapshot:
  rb_env_ok ce /\ rb_value_ok vv ==>
  rb_step rb_operand_ok (compile_create_snapshot ce vv ty)
Proof
  strip_tac >> pure_rewrite_tac[compile_create_snapshot_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
  gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
  irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac >- simp[rb_step_return] >>
  Cases_on `vv_location vv` >> simp[]
  >- (irule rb_bind_emit_op >> BETA_TAC >> simp[rb_value_operand] >>
      gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
      simp[rb_value_operand, rb_compile_copy_memory_dynamic]) >>
  Cases_on `x'` >> simp[]
  >~ [`compile_imm_copy_to_memory _ _ _ _ _ _`]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- (irule rb_compile_imm_copy_to_memory >>
          gvs[rb_env_ok_def, rb_value_operand]) >> simp[rb_step_return])
  >~ [`compile_slot_to_memory _ _ _ _`]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_slot_to_memory, rb_value_operand, rb_step_return])
  >~ [`compile_slot_to_memory _ _ _ _`]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_compile_slot_to_memory, rb_value_operand, rb_step_return]) >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_value_operand] >>
  gen_tac >> strip_tac >> irule rb_bind_emit_op >> BETA_TAC >>
  simp[rb_value_operand, rb_compile_copy_memory_dynamic]
QED

Theorem rb_compile_raw_create:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce (expr_type be) be) /\
  rb_step rb_value_ok (cfn ce (expr_type ve) ve) /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) /\
  (!e. salt_e = SOME e ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_raw_create cfn ce be ve args salt_e rof)
Proof
  strip_tac >> pure_rewrite_tac[compile_raw_create_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_value_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_compile_create_snapshot] >> gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- simp[rb_lower_value] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
  irule rb_step_bind >>
  qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >> BETA_TAC >>
  reverse conj_tac
  >- (Cases_on `args = []` >> simp[rb_step_return] >>
      irule rb_step_bind >> qexists_tac `rb_buffer_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_alloc_buffer] >>
      gen_tac >> simp[rb_buffer_ok_def] >> strip_tac >>
      irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> conj_tac >- simp[rb_compile_copy_memory_dynamic] >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[rb_compile_create_ctor_tuple] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[] >> gen_tac >> strip_tac >>
      irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
      reverse conj_tac >- simp[] >> gen_tac >> strip_tac >>
      irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]) >>
  Cases >> simp[] >> strip_tac >>
  irule rb_step_bind >> qexists_tac `OPTION_ALL rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_create_salt, rb_compile_create_dispatch] >>
  Cases >> simp[rb_compile_create_dispatch]
QED

Theorem rb_compile_extcall_store_args:
  !es tys buf off. rb_env_ok ce /\ rb_operand_ok buf /\
    (!e ty. MEM e es ==> rb_step rb_value_ok (cfn ce ty e)) ==>
    rb_step (K T) (compile_extcall_store_args cfn ce es tys buf off)
Proof
  Induct >> simp[compile_extcall_store_args_def, rb_step_return] >>
  rpt gen_tac >> strip_tac >> Cases_on `tys` >>
  (pure_rewrite_tac[compile_extcall_store_args_def, LET_THM] >> BETA_TAC >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> simp[]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (IF_CASES_TAC >> simp[rb_step_return, rb_emit_op]) >>
  gen_tac >> strip_tac >> irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> reverse conj_tac
  >- (first_x_assum irule >> simp[]) >>
  rpt IF_CASES_TAC >> simp[rb_emit_void, rb_compile_store_bytestring])
QED

Theorem rb_compile_create_call:
  (!dst src info. rb_operand_ok dst /\ rb_operand_ok src ==>
     rb_step rb_operand_ok (compile_abi_encode_to_buf dst src info)) /\
  rb_env_ok ce /\
  (!e. MEM e args ==> rb_step rb_value_ok (cfn ce (expr_type e) e)) ==>
  rb_step rb_operand_ok (compile_create_call cfn ce ck has_salt rof args)
Proof
  strip_tac >> Cases_on `args` >> simp[compile_create_call_def]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]) >>
  Cases_on `t` >> simp[]
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]) >>
  IF_CASES_TAC
  >- (irule (Q.INST [`P` |-> `K T`] rb_step_ignore_bind) >> simp[rb_emit_inst, rb_step_return]) >>
  Cases_on `ck` >> simp[]
  >~ [`compile_raw_create _ _ _ _ _ _ _`]
  >- suspend "raw" >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_lower_value >> gvs[]) >> gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_lower_value >> gvs[]) >> gen_tac >> strip_tac)
  >~ [`compile_create_proxy_buf _`] >- suspend "proxy"
  >~ [`compile_create_copy _ _ _ _`] >- suspend "copy" >>
  suspend "blueprint"
QED

Resume rb_compile_create_call[raw]:
  irule rb_compile_raw_create >> simp[] >>
  Cases_on `has_salt` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  metis_tac[rich_listTheory.MEM_FRONT, rich_listTheory.MEM_LAST, MEM]
QED

Resume rb_compile_create_call[proxy]:
  Cases_on `has_salt` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_compile_create_proxy_buf] >>
   gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `OPTION_ALL rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_compile_create_salt >> gvs[]) >>
   Cases >> simp[rb_compile_create_dispatch])
QED
Resume rb_compile_create_call[copy]:
  Cases_on `has_salt` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  (irule rb_step_bind >> qexists_tac `OPTION_ALL rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_compile_create_salt >> gvs[]) >>
   Cases >> simp[rb_compile_create_copy])
QED
Resume rb_compile_create_call[blueprint]:
  Cases_on `has_salt` >> gvs[] >> Cases_on `t'` >> gvs[] >>
  (irule rb_step_bind >> qexists_tac `OPTION_ALL rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_compile_create_salt >> gvs[]) >>
   Cases >> simp[] >>
   (rpt strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac
   >- (rpt CASE_TAC >>
       simp[rb_step_return, runtimeLabelInvariantTheory.rb_operand_ok_def] >>
       irule rb_lower_value >> gvs[] >> Cases_on `t` >> gvs[]) >>
   gen_tac >> strip_tac >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- simp[rb_compile_create_blueprint_check] >>
   gen_tac >> strip_tac >>
   irule rb_step_bind >>
   qexists_tac `\p. rb_operand_ok (FST p) /\ rb_operand_ok (SND p)` >> BETA_TAC >>
   reverse conj_tac
   >- (irule rb_compile_create_blueprint_args >> simp[] >>
       metis_tac[MEM_TL, MEM]) >>
   Cases >> simp[rb_compile_create_blueprint_append]))
QED
Finalise rb_compile_create_call

Theorem rb_compile_get_target_ptr:
  !bt. rb_env_ok ce /\
    (!e ty. expr_size e < base_assignment_target_size bt ==>
      rb_step rb_value_ok (cfn ce ty e)) ==>
    rb_step (rb_operand_ok o FST) (compile_get_target_ptr cfn ce bt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[Once compile_get_target_ptr_def] >> strip_tac
  >- suspend "name"
  >- suspend "top"
  >- suspend "subscript" >>
  suspend "attribute"
QED
Resume rb_compile_get_target_ptr[name]:
  Cases_on `FLOOKUP ce.ce_vars s` >> simp[rb_step_return] >>
  rename1 `FLOOKUP _ _ = SOME loc` >>
  `rb_location_ok loc` by metis_tac[rb_env_ok_def] >>
  Cases_on `loc` >> gvs[rb_location_ok_def, rb_step_return]
QED
Resume rb_compile_get_target_ptr[top]:
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  Cases_on `FLOOKUP ce.ce_module_vars p` >> simp[rb_step_return] >>
  Cases_on `x` >> simp[rb_step_return]
QED
Resume rb_compile_get_target_ptr[subscript]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[] >> rpt strip_tac >>
    first_x_assum irule >> simp[] >> decide_tac) >>
  gen_tac >> simp[] >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  Cases_on `SND (SND x)` >> simp[]
  >- suspend "array" >>
  Cases_on `x'` >> simp[]
  >- suspend "map" >>
  suspend "array"
QED
Resume rb_compile_get_target_ptr[attribute]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok o FST` >> BETA_TAC >>
  reverse conj_tac >- (first_x_assum irule >> simp[] >> rpt strip_tac >>
    first_x_assum irule >> simp[] >> decide_tac) >>
  gen_tac >> simp[] >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  irule rb_bind_emit_op >> BETA_TAC >> simp[rb_step_return]
QED
Resume rb_compile_get_target_ptr[map]:
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (irule rb_lower_value >> simp[] >> first_x_assum irule >> simp[]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  reverse conj_tac >- (IF_CASES_TAC >> simp[rb_compile_keccak256_key, rb_step_return]) >>
  gen_tac >> strip_tac >>
  irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
  simp[rb_compile_mapping_subscript, rb_step_return]
QED
Resume rb_compile_get_target_ptr[array]:
  markerLib.RESUME_TAC >>
  (irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_lower_value >> simp[] >> first_x_assum irule >> simp[]) >>
   gen_tac >> strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
   irule rb_step_bind >> qexists_tac `rb_operand_ok` >> BETA_TAC >>
   reverse conj_tac >- (irule rb_compile_array_subscript >> simp[] >>
     rpt strip_tac >> irule rb_compile_ptr_load >> gvs[rb_env_ok_def]) >>
   simp[rb_step_return])
QED
Finalise rb_compile_get_target_ptr


Theorem rb_compile_acc:
  rb_env_ok ce /\ rb_step rb_value_ok (cfn ce (BaseT AddressT) e) ==>
  rb_step rb_operand_ok (compile_acc cfn ce e acc)
Proof
  strip_tac >> Cases_on `acc` >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX])) >>
  pure_rewrite_tac[compile_acc_def] >> simp[ETA_AX, rb_lower_value]
  >~ [`emit_inst INVALID [] [] _`]
  >- (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
        (Q.INST [`P` |-> `K T`] (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind))) >> BETA_TAC >>
      conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
        irule rb_emit_inst >> simp[]) >>
      pure_rewrite_tac[GSYM comp_return_def] >>
      CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_step_return >> simp[])
  >~ [`rb_step _ (\x. lower_value _ _ _ _ x)`]
  >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
      irule rb_lower_value >> simp[]) >>
  (ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   conj_tac >- (CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
     irule rb_lower_value >> simp[]) >> gen_tac >> strip_tac >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   simp[rb_emit_op] >>
   ho_match_mp_tac (SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
      (Q.ISPEC `rb_operand_ok` (Q.GEN `P` (CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def)))) rb_step_bind)))) >> BETA_TAC >>
   simp[rb_emit_op] >>
   CONV_TAC (RAND_CONV (DEPTH_CONV ETA_CONV)) >>
   irule rb_emit_op >> simp[])
QED

Theorem rb_as_stack_val:
  rb_step rb_operand_ok m ==>
  rb_step rb_value_ok (\st. as_stack_val ty (m st))
Proof
  simp[rb_step_def] >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> Cases_on `m st` >>
  simp[as_stack_val_def, rb_value_ok_def]
QED
