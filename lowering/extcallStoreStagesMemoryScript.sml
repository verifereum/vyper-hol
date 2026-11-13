(* The exact singleton compiler cut, including word and empty MCOPY cells. *)
Theory extcallStoreStagesMemory
Ancestors
  exprLowering exprLoweringProps compileEnv context fragExec emitHelper list

Theorem extcall_single_store_stages:
  compile_extcall_store_values ce [(vv,ty)] buf off sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?dst sm src su.
    emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
    unwrap_value ce vv sm = (src,su) /\
    (if is_word_type ty then emit_void MSTORE [dst;src]
     else if is_bytestring_type ty then compile_store_bytestring src dst
     else emit_void MCOPY [dst;src;Lit (n2w (type_memory_bytes ce ty))])
      su = ((),sb) /\
    ci_mono sa sm /\ ci_mono sm su /\ ci_mono su sb /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\ fn_has_code su sb func
Proof
  strip_tac >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ _ = _` mp_tac >>
  simp[compile_extcall_store_values_def,comp_bind_def,
       comp_ignore_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
  strip_tac >> gvs[] >>
  rename1 `fn_has_code sa sf func` >>
  rename1 `emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm)` >>
  rename1 `unwrap_value ce vv sm = (src,su)` >>
  `ci_mono sa sm /\ ci_mono sm su /\ ci_mono su sf` by
    (rpt conj_tac
     >- metis_tac[ci_mono_emit_op,pairTheory.SND]
     >- metis_tac[ci_mono_unwrap_value,pairTheory.SND] >>
     Cases_on `is_word_type ty` >> Cases_on `is_bytestring_type ty` >>
     gvs[] >> metis_tac[ci_mono_emit_void,ci_mono_compile_store_bytestring,
                       pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm su func /\ fn_has_code su sf func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split,cs_extends_trans]) >>
  simp[]
QED
