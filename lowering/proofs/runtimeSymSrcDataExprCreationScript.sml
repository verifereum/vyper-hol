Theory runtimeSymSrcDataExprCreation
Ancestors
  symbolicSourceCompilerCreateFrame
  runtimeSymSrcDataFrame runtimeSymSrcDataExprCallbacks exprLowering compileEnv

fun apply_symbolic_frame theorem =
  match_mp_tac (REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` theorem)))

Theorem runtime_data_frame_create_ctor_tuple:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vs p off. runtime_data_frame (compile_extcall_store_values cenv vs p off)) /\
  (!copy vv. runtime_data_frame (compile_snapshot_vv cenv copy vv)) /\
  (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_ctor_tuple cfn cenv es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_ctor_tuple >> simp[]
QED

Theorem runtime_data_frame_create_blueprint_args:
  (!copy vv. runtime_data_frame (compile_snapshot_vv cenv copy vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!p s enc. runtime_data_frame (compile_abi_encode_to_buf p s enc)) /\
  runtime_data_frame (compile_create_ctor_tuple cfn cenv es) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_blueprint_args cfn cenv raw later_es es)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_blueprint_args >> simp[]
QED

Theorem runtime_data_frame_create_snapshot:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!p d n loc. runtime_data_frame (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. runtime_data_frame (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) ==>
  runtime_data_frame (compile_create_snapshot cenv vv ty)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_snapshot >> simp[]
QED

Theorem runtime_data_frame_raw_create:
  runtime_data_frame (cfn cenv (expr_type bytecode) bytecode) /\
  runtime_data_frame (lower_value cfn cenv (expr_type value) value) /\
  (!vv ty. runtime_data_frame (compile_create_snapshot cenv vv ty)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) /\
  runtime_data_frame (compile_create_ctor_tuple cfn cenv es) /\
  (!d s enc. runtime_data_frame (compile_abi_encode_to_buf d s enc)) /\
  runtime_data_frame (compile_create_salt cfn cenv salt) /\
  (!p n v s b. runtime_data_frame (compile_create_dispatch p n v s b)) ==>
  runtime_data_frame (compile_raw_create cfn cenv bytecode value es salt rof)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_raw_create >> simp[]
QED

Theorem runtime_data_frame_create_call:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v. runtime_data_frame (compile_create_proxy_buf v)) /\
  (!p n v s b. runtime_data_frame (compile_create_dispatch p n v s b)) /\
  (!v w s b. runtime_data_frame (compile_create_copy v w s b)) /\
  (!is_lit v off. runtime_data_frame (compile_create_blueprint_check is_lit v off)) /\
  (!v w s off n p len b.
     runtime_data_frame (compile_create_blueprint_append v w s off n p len b)) /\
  (!es raw later_es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
     runtime_data_frame (compile_create_blueprint_args cfn cenv raw later_es es)) /\
  (!bytecode value es salt b.
     runtime_data_frame (cfn cenv (expr_type bytecode) bytecode) /\
     runtime_data_frame (cfn cenv (expr_type value) value) /\
     (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) /\
     (!e. salt = SOME e ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
     runtime_data_frame (compile_raw_create cfn cenv bytecode value es salt b)) /\
  (!e. MEM e args ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_call cfn cenv ck has_salt rof args)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_call >> simp[]
QED
