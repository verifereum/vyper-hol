Theory runtimeSymSrcDataExprCallbacks
Ancestors
  symbolicSourceCompilerCallFrame
  symbolicSourceCompilerCreateFrame
  symbolicSourceCompilerExprFrame
  runtimeSymSrcDataFrame exprLowering compileEnv

fun apply_symbolic_frame theorem =
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` theorem)))

Theorem runtime_data_frame_lower_value:
  runtime_data_frame (cfn cenv ty e) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) ==>
  runtime_data_frame (lower_value cfn cenv ty e)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_lower_value >> simp[]
QED

Theorem runtime_data_frame_lower_value_with_loc:
  runtime_data_frame (cfn cenv ty e) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) ==>
  runtime_data_frame (lower_value_with_loc cfn cenv ty e)
Proof
  simp[lower_value_with_loc_def]
QED

Theorem runtime_data_frame_as_stack_val:
  runtime_data_frame m ==>
  runtime_data_frame (\st. as_stack_val ty (m st))
Proof
  rw[runtime_data_frame_def] >> Cases_on `m st` >>
  gvs[as_stack_val_def] >> metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_as_ptr_val:
  runtime_data_frame m ==>
  runtime_data_frame (\st. as_ptr_val ty loc (m st))
Proof
  rw[runtime_data_frame_def] >> Cases_on `m st` >>
  gvs[as_ptr_val_def] >> metis_tac[pairTheory.SND]
QED

Theorem runtime_data_frame_multi_exprs:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) ==>
  !es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_multi_exprs cfn cenv es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_multi_exprs >> simp[]
QED

Theorem runtime_data_frame_make_tuple:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) ==>
  !es tys buf off.
    (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_make_tuple cfn cenv es tys buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_make_tuple >> simp[]
QED

Theorem runtime_data_frame_make_array_elems:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) ==>
  !es et sz lw buf idx.
    (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_make_array_elems cfn cenv es et sz lw buf idx)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_make_array_elems >> simp[]
QED

Theorem runtime_data_frame_make_array:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) /\
  (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_make_array cfn cenv es et sz lw buf)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_make_array >> simp[]
QED

Theorem runtime_data_frame_concat:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) ==>
  !es dp infos off.
    (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_concat cfn cenv es dp infos off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_concat >> simp[]
QED

fun apply_symbolic_frame theorem =
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data` (Q.GEN `R` theorem)))

Theorem runtime_data_frame_store_abi_tuple:
  (!dst src n. runtime_data_frame (compile_copy_memory dst src n)) ==>
  !vs buf off. runtime_data_frame (compile_store_abi_tuple cenv buf off vs)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_store_abi_tuple >> simp[]
QED

Theorem runtime_data_frame_materialize_vv:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) ==>
  runtime_data_frame (compile_materialize_vv cenv ty vv)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_materialize_vv >> simp[]
QED

Theorem runtime_data_frame_ifexp_arm:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) ==>
  runtime_data_frame (compile_ifexp_arm cenv rt at vv)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_ifexp_arm >> simp[]
QED

Theorem runtime_data_frame_snapshot_vv:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!ty vv. runtime_data_frame (compile_materialize_vv cenv ty vv)) ==>
  runtime_data_frame (compile_snapshot_vv cenv copy vv)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_snapshot_vv >> simp[]
QED

Theorem runtime_data_frame_struct_lit:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst ty sty. runtime_data_frame (compile_store_memory cenv v dst ty sty)) ==>
  !fields ty buf off.
    (!nm e. MEM (nm,e) fields ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_struct_lit cfn cenv ty fields buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_struct_lit >> simp[]
QED

Theorem runtime_data_frame_abi_encode_args:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!ty vv. runtime_data_frame (compile_materialize_vv cenv ty vv)) ==>
  !es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_abi_encode_args cfn cenv es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_abi_encode_args >> simp[]
QED

Theorem runtime_data_frame_ext_call_kwarg:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!ty vv. runtime_data_frame (compile_materialize_vv cenv ty vv)) /\
  (!ty. runtime_data_frame (cfn cenv ty e)) ==>
  runtime_data_frame (compile_ext_call_kwarg cfn cenv rt k e)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ext_call_kwarg >> simp[]
QED

Theorem runtime_data_frame_ext_call_kwargs:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!ty vv. runtime_data_frame (compile_materialize_vv cenv ty vv)) ==>
  !es ks rt.
    (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_ext_call_kwargs cfn cenv rt ks es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ext_call_kwargs >> simp[]
QED

Theorem runtime_data_frame_create_salt:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!e. opt = SOME e ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_salt cfn cenv opt)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_salt >> simp[]
QED
