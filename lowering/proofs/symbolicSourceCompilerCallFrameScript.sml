Theory symbolicSourceCompilerCallFrame
Ancestors
  rich_list
  symbolicSourceCompilerFrame symbolicSourceCompilerExprFrame symbolicSourceCompilerCreateFrame
  exprLowering compileEnv
Libs symbolicSourceCompilerFrameLib

open symbolicSourceCompilerFrameLib

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

Theorem symbolic_frame_extcall_store_values:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst. symbolic_frame R (compile_store_bytestring v dst)) ==>
  !vs buf off. symbolic_frame R (compile_extcall_store_values cenv vs buf off)
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_values_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[compile_extcall_store_values_def] >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >> frame_tac
QED

Theorem symbolic_frame_default_return_path:
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!v dst dt st. symbolic_frame R (compile_store_memory cenv v dst dt st)) /\
  (!lo hi. symbolic_frame R (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. symbolic_frame R (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  symbolic_frame R (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)
Proof
  strip_tac >> Cases_on `skip` >> simp[compile_default_return_path_def] >> frame_tac
QED

Theorem symbolic_frame_abi_encode_value_rows[local]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!src dst ty. symbolic_frame R (compile_store_memory cenv src dst ty ty)) /\
  (!dst src info. symbolic_frame R (compile_abi_encode_to_buf dst src info)) ==>
  !rows dst cursor off.
    symbolic_frame R (compile_abi_encode_value_rows cenv dst cursor off rows)
Proof
  strip_tac >> Induct >> simp[compile_abi_encode_value_rows_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  Cases_on `is_abi_dynamic cenv.ce_struct_fields h1` >>
  simp[compile_abi_encode_value_rows_def, LET_THM] >> frame_tac
QED

Theorem symbolic_frame_abi_encode_values_to_buf:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!src dst ty. symbolic_frame R (compile_store_memory cenv src dst ty ty)) /\
  (!dst src info. symbolic_frame R (compile_abi_encode_to_buf dst src info)) ==>
  symbolic_frame R (compile_abi_encode_values_to_buf cenv dst rows)
Proof
  strip_tac >> drule symbolic_frame_abi_encode_value_rows >> simp[] >> strip_tac >>
  simp[compile_abi_encode_values_to_buf_def] >> frame_tac
QED

Theorem symbolic_frame_external_call_kwargs:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!dst rows. symbolic_frame R (compile_abi_encode_values_to_buf cenv dst rows)) /\
  (!rt dt buf res dop addr skip lo hi info.
     symbolic_frame R (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)) /\
  (!lo hi. symbolic_frame R (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. symbolic_frame R (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  symbolic_frame R (compile_external_call_kwargs cenv addr vals tys abi mid rabi lo rmem static value gas skip has_default dop rt dt dinfo)
Proof
  strip_tac >> simp[compile_external_call_kwargs_def] >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem symbolic_frame_stage_intcall_args:
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!v dst. symbolic_frame R (compile_store_bytestring v dst)) /\
  (!v dst dt st. symbolic_frame R (compile_store_memory cenv v dst dt st)) ==>
  !vs flags tys.
    (!e. MEM e vs ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
    symbolic_frame R (compile_stage_intcall_args cfn cenv vs flags tys)
Proof
  strip_tac >> Induct >> simp[compile_stage_intcall_args_def] >>
  rpt gen_tac >> Cases_on `flags` >> Cases_on `tys` >>
  simp[compile_stage_intcall_args_def] >>
  TRY (rename1 `compile_stage_intcall_args _ _ (_ :: _) (by_value :: _) (_ :: _)` >>
       Cases_on `by_value` >> simp[compile_stage_intcall_args_def]) >>
  strip_tac >> frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem symbolic_frame_abi_encode_args:
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!ty vv. symbolic_frame R (compile_materialize_vv cenv ty vv)) ==>
  !es. (!e. MEM e es ==> symbolic_frame R (cfn cenv (expr_type e) e)) ==>
  symbolic_frame R (compile_abi_encode_args cfn cenv es)
Proof
  strip_tac >> Induct >> simp[compile_abi_encode_args_def] >> rpt strip_tac >>
  match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> match_mp_tac symbolic_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[]) >> simp[]
QED

Theorem symbolic_frame_ext_call_kwarg:
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!ty vv. symbolic_frame R (compile_materialize_vv cenv ty vv)) /\
  (!ty. symbolic_frame R (cfn cenv ty e)) ==>
  symbolic_frame R (compile_ext_call_kwarg cfn cenv rt k e)
Proof
  strip_tac >> rw[compile_ext_call_kwarg_def] >>
  simp[symbolic_frame_lower_value]
QED

Theorem symbolic_frame_ext_call_kwargs:
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!ty vv. symbolic_frame R (compile_materialize_vv cenv ty vv)) ==>
  !es ks rt.
    (!e ty. MEM e es ==> symbolic_frame R (cfn cenv ty e)) ==>
    symbolic_frame R (compile_ext_call_kwargs cfn cenv rt ks es)
Proof
  strip_tac >> Induct >> Cases_on `ks` >> simp[compile_ext_call_kwargs_def] >>
  rpt strip_tac >> match_mp_tac symbolic_frame_bind >> conj_tac
  >- (irule symbolic_frame_ext_call_kwarg >> simp[]) >>
  simp[pairTheory.FORALL_PROD]
QED

(* The call equations pass state explicitly. Recover the bind closure in the
   same let form before descending through the continuations. *)
val state_let_frame =
  SIMP_RULE (srw_ss()) [LET_THM, SF ETA_ss]
    (CONV_RULE (RAND_CONV (RAND_CONV
      (REWR_CONV (GSYM ETA_AX) THENC ABS_CONV (REWR_CONV comp_bind_def))))
      symbolic_frame_bind);

val state_let_frame_step =
  ho_match_mp_tac state_let_frame >> BETA_TAC >>
  conj_tac >- simp[SF ETA_ss, symbolic_frame_lower_value] >> gen_tac;

Theorem symbolic_frame_return_pair[local]:
  symbolic_frame R ($, v)
Proof
  simp[symbolic_frame_def]
QED

val explicit_frame_tac =
  rpt (FIRST [
    state_let_frame_step,
    CHANGED_TAC (simp[LET_THM, SF ETA_ss, GSYM comp_return_def,
                      symbolic_frame_lower_value, symbolic_frame_return_pair]),
    pairarg_tac, IF_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

val eta_expand_compiler = CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM ETA_AX]));

Theorem symbolic_frame_store_words:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  !vs buf off. symbolic_frame R (compile_store_words buf vs off)
Proof
  strip_tac >> Induct >> rpt gen_tac >> Cases_on `off = 0` >>
  simp[compile_store_words_def]
QED

Theorem symbolic_frame_invert:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_invert v ty cenv)
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_invert_def]
QED

Theorem symbolic_frame_acc:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  symbolic_frame R (cfn cenv (BaseT AddressT) e) ==>
  symbolic_frame R (compile_acc cfn cenv e acc)
Proof
  strip_tac >> Cases_on `acc` >> eta_expand_compiler >>
  pure_rewrite_tac[compile_acc_def] >> explicit_frame_tac
QED

Theorem symbolic_frame_call_send:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!e ty. MEM e args ==> symbolic_frame R (cfn cenv ty e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) ==>
  symbolic_frame R (compile_call cfn cenv rt ty (Send gas) args dr)
Proof
  strip_tac >> Cases_on `args` >> eta_expand_compiler >>
  pure_rewrite_tac[compile_call_def] >> explicit_frame_tac
QED

Theorem symbolic_frame_call_raw_revert:
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!e ty. MEM e args ==> symbolic_frame R (cfn cenv ty e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v. symbolic_frame R (compile_raw_revert v)) ==>
  symbolic_frame R (compile_call cfn cenv rt ty RawRevert args dr)
Proof
  strip_tac >> Cases_on `args` >> eta_expand_compiler >>
  pure_rewrite_tac[compile_call_def] >> explicit_frame_tac
QED

Theorem symbolic_frame_call_selfdestruct:
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!e ty. MEM e args ==> symbolic_frame R (cfn cenv ty e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v. symbolic_frame R (compile_selfdestruct v)) ==>
  symbolic_frame R (compile_call cfn cenv rt ty SelfDestructTarget args dr)
Proof
  strip_tac >> Cases_on `args` >> eta_expand_compiler >>
  pure_rewrite_tac[compile_call_def] >> explicit_frame_tac
QED

Theorem symbolic_frame_call_raw:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!e ty. MEM e args ==> symbolic_frame R (cfn cenv ty e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> symbolic_frame R (cfn cenv ty e)) ==>
    symbolic_frame R (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. symbolic_frame R (compile_raw_call_outbuf n)) /\
  (!a p n g v ct sz rof ov op.
    symbolic_frame R (compile_raw_call_finish a p n g v ct sz rof ov op)) ==>
  symbolic_frame R (compile_call cfn cenv rt ty (RawCallTarget rcf) args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac) >>
  Cases_on `t`
  >- (eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac) >>
  `symbolic_frame R (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t')` by
    (first_x_assum irule >> simp[]) >>
  eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac
QED

Theorem symbolic_frame_call_raw_calldata:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!e ty. MEM e args ==> symbolic_frame R (cfn cenv ty e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> symbolic_frame R (cfn cenv ty e)) ==>
    symbolic_frame R (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!n. symbolic_frame R (compile_raw_call_outbuf n)) /\
  symbolic_frame R compile_msg_data_to_memory /\
  (!a p n g v ct sz rof ov op.
    symbolic_frame R (compile_raw_call_finish a p n g v ct sz rof ov op)) ==>
  symbolic_frame R (compile_call cfn cenv rt ty (RawCallCalldataTarget rcf) args dr)
Proof
  strip_tac >> Cases_on `args`
  >- (eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac) >>
  `symbolic_frame R (compile_ext_call_kwargs cfn cenv NoneT rcf.rcf_kws t)` by
    (first_x_assum irule >> simp[]) >>
  eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac
QED

Theorem symbolic_frame_call_external:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!e ty. MEM e args ==> symbolic_frame R (cfn cenv ty e)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!copy vv. symbolic_frame R (compile_snapshot_vv cenv copy vv)) /\
  (!es rt ks. (!e ty. MEM e es ==> symbolic_frame R (cfn cenv ty e)) ==>
    symbolic_frame R (compile_ext_call_kwargs cfn cenv rt ks es)) /\
  (!a vs ts az mid rz mn rb sc v g sk hd d rt dt di.
    symbolic_frame R (compile_external_call_kwargs cenv a vs ts az mid rz mn rb
      sc v g sk hd d rt dt di)) ==>
  symbolic_frame R (compile_call cfn cenv rt ty (ExtCall sc sk sig opts) args dr)
Proof
  strip_tac >> PairCases_on `sig` >> Cases_on `args`
  >- (eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac) >>
  `symbolic_frame R (lower_value cfn cenv (BaseT AddressT) h)` by
    simp[symbolic_frame_lower_value] >>
  `symbolic_frame R (compile_ext_call_args cfn cenv
      (DROP (LENGTH sig1) t)
      (MAP (lowered_value_type cenv) (TAKE (LENGTH sig1) t))
      (TAKE (LENGTH sig1) t))` by
    (irule symbolic_frame_ext_call_args >> simp[] >> metis_tac[MEM_TAKE, listTheory.MEM]) >>
  `symbolic_frame R (compile_ext_call_kwargs cfn cenv sig2 opts (DROP (LENGTH sig1) t))` by
    (first_x_assum irule >> metis_tac[MEM_DROP_IMP, listTheory.MEM]) >>
  eta_expand_compiler >> pure_rewrite_tac[compile_call_def] >> explicit_frame_tac
QED
