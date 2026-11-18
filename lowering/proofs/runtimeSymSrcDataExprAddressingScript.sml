Theory runtimeSymSrcDataExprAddressing
Ancestors
  symbolicSourceCompilerAddressFrame
  runtimeSymSrcDataExprCallbacks runtimeSymSrcDataFrame exprLowering
  compileEnv targetPlaceLive targetPlaceSimCasesBase

fun apply_symbolic_frame theorem =
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` theorem)))

Theorem runtime_data_frame_attribute:
  runtime_data_frame (cfn cenv ty base_e) ==>
  runtime_data_frame (compile_attribute cfn cenv rt ty base_e fld)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_attribute >> simp[]
QED

Theorem runtime_data_frame_extcall_store_args:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst. runtime_data_frame (compile_store_bytestring v dst)) ==>
  !es tys buf off.
    (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_extcall_store_args cfn cenv es tys buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_extcall_store_args >> simp[]
QED

Theorem runtime_data_frame_get_target_ptr:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v b. runtime_data_frame (compile_keccak256_key v b)) /\
  (!v k. runtime_data_frame (compile_mapping_subscript v k)) /\
  (!b i d n ws sz si loc.
    runtime_data_frame (compile_array_subscript b i d n ws sz si
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))) ==>
  !t. (!e. MEM e (target_indices t) ==>
        runtime_data_frame (cfn cenv (expr_type e) e)) ==>
      runtime_data_frame (compile_get_target_ptr cfn cenv t)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_get_target_ptr >> simp[]
QED

Theorem runtime_data_frame_subscript:
  (!copy vv. runtime_data_frame (compile_snapshot_vv cenv copy vv)) /\
  runtime_data_frame (cfn cenv ty base_e) /\
  runtime_data_frame (cfn cenv ty idx_e) /\
  runtime_data_frame (cfn cenv (expr_type idx_e) idx_e) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v b. runtime_data_frame (compile_keccak256_key v b)) /\
  (!v k. runtime_data_frame (compile_mapping_subscript v k)) /\
  (!v off. runtime_data_frame (compile_tuple_subscript v off)) /\
  (!b i d n ws sz si loc.
    runtime_data_frame (compile_array_subscript b i d n ws sz si
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))) ==>
  runtime_data_frame (compile_subscript cfn cenv rt ty base_e idx_e)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_subscript >> simp[]
QED
