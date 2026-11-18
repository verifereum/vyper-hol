Theory symbolicSourceCompilerCallFrame
Ancestors symbolicSourceCompilerFrame symbolicSourceCompilerExprFrame symbolicSourceCompilerCreateFrame
  exprLowering compileEnv

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

fun frame_tac goal =
  (simp[comp_ignore_bind_def] >>
   rpt (match_mp_tac symbolic_frame_bind >> conj_tac
     >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) goal

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

Theorem symbolic_frame_external_call_kwargs:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!vs buf off. symbolic_frame R (compile_extcall_store_values cenv vs buf off)) /\
  (!dst src info. symbolic_frame R (compile_abi_encode_to_buf dst src info)) /\
  (!rt dt buf res dop addr skip lo hi info.
     symbolic_frame R (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)) /\
  (!lo hi. symbolic_frame R (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. symbolic_frame R (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  symbolic_frame R (compile_external_call_kwargs cenv addr vals tys mem abi mid rabi lo rmem static value gas skip has_default dop rt dt einfo dinfo)
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
