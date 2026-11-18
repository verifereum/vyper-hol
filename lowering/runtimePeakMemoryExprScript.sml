(* Allocation window coverage through expression and call lowering. *)
Theory runtimePeakMemoryExpr
Ancestors
  runtimePeakMemoryCode runtimePeakMemorySourceGate exprLowering exprLoweringProps
  compileEnv context builtinSystem builtinCreate emitHelper venomInst list

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

val windows_pure_tac = windows_tac [];

Theorem dalloca_windows_imm_load[local]:
  preserves_dalloca_windows window (compile_imm_load_word ctor imm off)
Proof
  Cases_on `imm` >> simp[compile_imm_load_word_def] >> windows_pure_tac
QED

Theorem dalloca_windows_imm_store[local]:
  preserves_dalloca_windows window (compile_imm_store_word imm off value)
Proof
  Cases_on `imm` >> simp[compile_imm_store_word_def] >> windows_pure_tac
QED

Theorem dalloca_windows_ptr_access:
  preserves_dalloca_windows window (compile_ptr_load ctor imm loc off) /\
  preserves_dalloca_windows window (compile_ptr_store ctor imm loc off value)
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_ptr_store_def, dalloca_windows_imm_load,
       dalloca_windows_imm_store, dalloca_windows_emit_helpers] >>
  windows_pure_tac >> simp[dalloca_windows_imm_store]
QED

Theorem dalloca_windows_word_copy[local]:
  preserves_dalloca_windows window
    (compile_word_copy_loop_base src dst count_op load_loc store_loc ctor imm)
Proof
  rewrite_tac[compile_word_copy_loop_base_def] >>
  windows_tac [dalloca_windows_ptr_access]
QED

Theorem dalloca_windows_imm_copy:
  !n off. preserves_dalloca_windows window
    (compile_imm_copy_to_memory ctor imm src dst n off)
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, dalloca_windows_return] >>
  simp[compile_lit_byte_offset_def] >>
  windows_tac [dalloca_windows_imm_load] >> fs[]
QED

Theorem dalloca_windows_ensure_in_memory[local]:
  preserves_dalloca_windows window
    (compile_ensure_in_memory op loc nwords nbytes ctor imm)
Proof
  Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, compile_storage_to_memory_def,
       compile_transient_to_memory_def, compile_word_copy_loop_def,
       compile_word_copy_loop_op_def] >>
  windows_tac [dalloca_windows_word_copy, dalloca_windows_imm_copy]
QED

Theorem dalloca_windows_unwrap_value:
  preserves_dalloca_windows window (unwrap_value cenv vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, dalloca_windows_return] >>
  windows_tac [dalloca_windows_ptr_access, dalloca_windows_ensure_in_memory]
QED

Theorem dalloca_windows_lower_value:
  preserves_dalloca_windows window (cfn cenv ty e) ==>
  preserves_dalloca_windows window (lower_value cfn cenv ty e)
Proof
  strip_tac >> rewrite_tac[lower_value_def] >>
  irule dalloca_windows_bind >> simp[dalloca_windows_unwrap_value]
QED

Theorem dalloca_windows_store_same_type[local]:
  preserves_dalloca_windows window (compile_store_memory cenv src dst ty ty)
Proof
  simp[compile_store_memory_def, compile_store_bytestring_def,
       compile_bytestring_copy_len_def] >> windows_pure_tac >>
  Cases_on `type_memory_bytes cenv ty` >>
  simp[compile_copy_memory_def, dalloca_windows_emit_helpers, dalloca_windows_return]
QED

Theorem dalloca_windows_materialize_vv:
  preserves_dalloca_windows window (compile_materialize_vv cenv ty vv)
Proof
  rewrite_tac[compile_materialize_vv_def] >>
  windows_tac [dalloca_windows_unwrap_value, dalloca_windows_store_same_type]
QED

Theorem dalloca_windows_ext_call_kwargs:
  !ks es.
    (!ty e. MEM e es ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
    preserves_dalloca_windows window
      (compile_ext_call_kwargs cfn cenv return_type ks es)
Proof
  Induct >> Cases_on `es` >> simp[compile_ext_call_kwargs_def, dalloca_windows_return] >>
  simp[compile_ext_call_kwarg_def] >> rpt strip_tac >>
  windows_tac [dalloca_windows_materialize_vv, dalloca_windows_lower_value] >>
  res_tac
QED

Theorem dalloca_windows_raw_call_calldata:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!ty e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window
    (compile_call cfn cenv ret_ty ty (RawCallCalldataTarget rcf) args default_ret)
Proof
  strip_tac >>
  rw[preserves_dalloca_windows_def] >>
  Cases_on `args`
  >- (`preserves_dalloca_windows window (emit_inst INVALID [] [])` by
        simp[dalloca_windows_emit_helpers] >>
      gvs[compile_call_def, LET_THM, pairTheory.UNCURRY_DEF,
          preserves_dalloca_windows_def] >>
      Cases_on `emit_inst INVALID [] [] st` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_call_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >>
  strip_tac >> gvs[] >>
  `preserves_dalloca_windows window (cfn cenv (BaseT AddressT) h)` by
    (first_x_assum match_mp_tac >> simp[]) >>
  `compiler_dalloca_windows window st1` by
    (drule dalloca_windows_lower_value >>
     simp[preserves_dalloca_windows_def] >> metis_tac[]) >>
  `!ety e. MEM e t ==> preserves_dalloca_windows window (cfn cenv ety e)` by
    metis_tac[] >>
  `compiler_dalloca_windows window st2` by
    (mp_tac (Q.SPECL [`rcf.rcf_kws`, `t`] (Q.INST [`return_type` |-> `NoneT`]
       dalloca_windows_ext_call_kwargs)) >>
     simp[preserves_dalloca_windows_def] >> metis_tac[]) >>
  `compiler_dalloca_windows window st3` by
    (Cases_on `gas_opt` >> gvs[] >>
     `preserves_dalloca_windows window (emit_op GAS [])` by
       simp[dalloca_windows_emit_helpers] >>
     fs[preserves_dalloca_windows_def] >> metis_tac[]) >>
  `compiler_dalloca_windows window st4` by
    (mp_tac (Q.INST [`max_outsize` |-> `rcf.rcf_max_outsize`]
      dalloca_windows_raw_call_outbuf) >> simp[preserves_dalloca_windows_def] >>
     metis_tac[]) >>
  `compiler_dalloca_windows window st6` by
    (mp_tac (Q.INST [`addr` |-> `addr_op`, `gas` |-> `gas_op`,
       `value` |-> `case value_opt of NONE => Lit 0w | SOME v => v`,
       `ty` |-> `if rcf.rcf_is_delegate then DelegateCall
                else if rcf.rcf_is_static then StaticCall else RegularCall`,
       `n` |-> `rcf.rcf_max_outsize`, `rev` |-> `rcf.rcf_revert_on_failure`,
       `out` |-> `out_val`, `dest` |-> `out_ptr`]
      dalloca_windows_msg_data_followed_by_call) >>
     simp[preserves_dalloca_windows_def, comp_bind_def] >>
     disch_then (qspecl_then [`st4`, `result_op`, `st6`] mp_tac) >> simp[]) >>
  Cases_on `rcf.rcf_max_outsize = 0` >> gvs[]
QED

Theorem dalloca_windows_create_salt[local]:
  (!ty e. salt = SOME e ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window (compile_create_salt cfn cenv salt)
Proof
  Cases_on `salt` >> simp[compile_create_salt_def, dalloca_windows_return] >>
  strip_tac >> windows_tac [dalloca_windows_lower_value]
QED

Theorem dalloca_windows_create_copy_call:
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!ty e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window
    (compile_create_call cfn cenv CreateCopyOf salted rof args)
Proof
  strip_tac >>
  Cases_on `args` >- (simp[compile_create_call_def] >> windows_pure_tac) >>
  Cases_on `t` >- (simp[compile_create_call_def] >> windows_pure_tac) >>
  gvs[compile_create_call_def, MEM] >>
  windows_tac [dalloca_windows_lower_value, dalloca_windows_create_copy] >>
  irule dalloca_windows_create_salt >>
  Cases_on `salted` >> gvs[] >> rpt strip_tac >> gvs[] >>
  Cases_on `t'` >> gvs[]
QED

Theorem dalloca_windows_compile_call_create_copy:
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!ty e. MEM e args ==> preserves_dalloca_windows window (cfn cenv ty e)) ==>
  preserves_dalloca_windows window
    (compile_call cfn cenv ret_ty ty (CreateTarget CreateCopyOf salted rof order)
      args default_ret)
Proof
  strip_tac >>
  `preserves_dalloca_windows window (compile_create_call cfn cenv CreateCopyOf salted rof args)`
    by metis_tac[dalloca_windows_create_copy_call] >>
  fs[preserves_dalloca_windows_def, compile_call_def, as_stack_val_def] >>
  rpt strip_tac >>
  Cases_on `compile_create_call cfn cenv CreateCopyOf salted rof args st` >>
  gvs[as_stack_val_def] >> metis_tac[]
QED

Theorem dalloca_windows_pair_return[local]:
  preserves_dalloca_windows window (\st. (f st,st))
Proof
  simp[preserves_dalloca_windows_def]
QED

Theorem dalloca_windows_pair_bind[local]:
  preserves_dalloca_windows window m /\
  (!v. preserves_dalloca_windows window (f v)) ==>
  preserves_dalloca_windows window
    (\st. (\(v,st1). f v st1) (m st))
Proof
  strip_tac >>
  `preserves_dalloca_windows window (comp_bind m f)` by
    metis_tac[dalloca_windows_bind] >>
  fs[preserves_dalloca_windows_def, comp_bind_def] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[]
QED

Theorem dalloca_windows_result_map[local]:
  preserves_dalloca_windows window m ==>
  preserves_dalloca_windows window (\st. (f (FST (m st)), SND (m st)))
Proof
  simp[preserves_dalloca_windows_def] >> rpt strip_tac >>
  Cases_on `m st` >> gvs[] >> metis_tac[]
QED
Theorem dalloca_windows_copy_memory:
  preserves_dalloca_windows window (compile_copy_memory dst src n) /\
  preserves_dalloca_windows window (compile_copy_memory_dynamic dst src length_op)
Proof
  Cases_on `n` >>
  simp[compile_copy_memory_def, compile_copy_memory_dynamic_def,
       dalloca_windows_return, dalloca_windows_emit_helpers]
QED

Theorem dalloca_windows_store_bytestring[local]:
  preserves_dalloca_windows window (compile_store_bytestring src dst)
Proof
  rewrite_tac[compile_store_bytestring_def, compile_bytestring_copy_len_def] >>
  windows_pure_tac
QED

Theorem dalloca_windows_store_memory_typed[local]:
  (!cenv dst dst_ty src src_ty.
    preserves_dalloca_windows window (compile_store_memory_typed cenv dst dst_ty src src_ty)) /\
  (!cenv dst src dst_tys src_tys dst_off src_off.
    preserves_dalloca_windows window
      (compile_typed_copy_fields cenv dst src dst_tys src_tys dst_off src_off)) /\
  (!cenv dst dst_elem src src_elem n.
    preserves_dalloca_windows window (compile_copy_sarray_typed cenv dst dst_elem src src_elem n)) /\
  (!cenv dst dst_elem cap src src_elem.
    preserves_dalloca_windows window
      (compile_copy_dynarray_typed cenv dst dst_elem cap src src_elem)) /\
  (!cenv dst src dst_fields src_fields dst_off src_off.
    preserves_dalloca_windows window
      (compile_struct_typed_copy cenv dst src dst_fields src_fields dst_off src_off))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `is_word_type dst_ty`
      >- (simp[Once compile_store_memory_typed_def] >> windows_pure_tac) >>
      Cases_on `is_bytestring_type dst_ty /\ is_bytestring_type src_ty`
      >- simp[Once compile_store_memory_typed_def, dalloca_windows_store_bytestring] >>
      Cases_on `acyclic_struct_metadata cenv.ce_struct_fields`
      >- (Cases_on `dst_ty` >> Cases_on `src_ty` >>
          TRY (rename1 `compile_store_memory_typed ccenv dst (ArrayT dt db) src (ArrayT st sb)` >>
               Cases_on `db` >> Cases_on `sb`) >> gvs[] >>
          simp[Once compile_store_memory_typed_def, LET_THM,
               dalloca_windows_copy_memory] >> metis_tac[]) >>
      simp[Once compile_store_memory_typed_def, dalloca_windows_emit_helpers])
  >- simp[Once compile_store_memory_typed_def, dalloca_windows_return]
  >- simp[Once compile_store_memory_typed_def, dalloca_windows_return]
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      windows_tac [compile_with_byte_offset_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_memory_bytes ccenv dst_ty = type_memory_bytes ccenv src_ty /\
                ~is_abi_dynamic cenv.ce_struct_fields dst_ty` >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      windows_tac [dalloca_windows_copy_memory] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `type_memory_bytes ccenv dst_ty = type_memory_bytes ccenv src_ty /\ dst_ty = src_ty` >> gvs[] >>
      simp[Once compile_store_memory_typed_def] >>
      windows_tac [dalloca_windows_copy_memory] >> metis_tac[])
  >- simp[Once compile_store_memory_typed_def, dalloca_windows_return] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP src_fields name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >> gvs[] >>
  simp[Once compile_store_memory_typed_def] >>
  windows_tac [compile_with_byte_offset_def] >> metis_tac[]
QED

Theorem dalloca_windows_store_memory:
  preserves_dalloca_windows window (compile_store_memory env src dst dst_ty src_ty)
Proof
  rewrite_tac[compile_store_memory_def] >>
  windows_tac [dalloca_windows_store_memory_typed, dalloca_windows_copy_memory,
               dalloca_windows_store_bytestring]
QED
