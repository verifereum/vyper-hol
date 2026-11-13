Theory runtimeSymSrcDataExprCreation
Ancestors
  runtimeSymSrcDataFrame runtimeSymSrcDataExprCallbacks exprLowering compileEnv

Theorem runtime_data_frame_create_ctor_tuple:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vs p off. runtime_data_frame (compile_extcall_store_values cenv vs p off)) /\
  runtime_data_frame (compile_multi_vvs cfn cenv es) ==>
  runtime_data_frame (compile_create_ctor_tuple cfn cenv es)
Proof
  strip_tac >> simp[compile_create_ctor_tuple_def, comp_ignore_bind_def]
QED

Theorem runtime_data_frame_create_blueprint_args:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!p s enc. runtime_data_frame (compile_abi_encode_to_buf p s enc)) /\
  runtime_data_frame (compile_create_ctor_tuple cfn cenv es) /\
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_blueprint_args cfn cenv raw es)
Proof
  strip_tac >> Cases_on `raw`
  >- (Cases_on `es` >> simp[compile_create_blueprint_args_def] >>
      Cases_on `t` >> simp[compile_create_blueprint_args_def,
        runtime_data_frame_lower_value] >>
      Cases_on `t'` >> simp[compile_create_blueprint_args_def]) >>
  rw[compile_create_blueprint_args_def] >> simp[]
QED

Theorem runtime_data_frame_create_snapshot:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!p d n loc. runtime_data_frame (compile_slot_to_memory p d n loc)) /\
  (!b a p d n off. runtime_data_frame (compile_imm_copy_to_memory b a p d n off)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) ==>
  runtime_data_frame (compile_create_snapshot cenv vv ty)
Proof
  strip_tac >> simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  match_mp_tac runtime_data_frame_bind >> simp[] >> gen_tac >>
  Cases_on `vv_location vv` >> simp[] >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> simp[]
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
  strip_tac >> simp[compile_raw_create_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >>
       gen_tac >> BETA_TAC) >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >>
           gen_tac >> BETA_TAC) >> simp[]) >>
  simp[pairTheory.FORALL_PROD]
QED

Theorem runtime_data_frame_create_call:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v. runtime_data_frame (compile_create_proxy_buf v)) /\
  (!p n v s b. runtime_data_frame (compile_create_dispatch p n v s b)) /\
  (!v w s b. runtime_data_frame (compile_create_copy v w s b)) /\
  (!v off. runtime_data_frame (compile_create_blueprint_check v off)) /\
  (!v w s off n p len b.
     runtime_data_frame (compile_create_blueprint_append v w s off n p len b)) /\
  (!es raw. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
     runtime_data_frame (compile_create_blueprint_args cfn cenv raw es)) /\
  (!bytecode value es salt b.
     runtime_data_frame (cfn cenv (expr_type bytecode) bytecode) /\
     runtime_data_frame (cfn cenv (expr_type value) value) /\
     (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) /\
     (!e. salt = SOME e ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
     runtime_data_frame (compile_raw_create cfn cenv bytecode value es salt b)) /\
  (!e. MEM e args ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_create_call cfn cenv ck has_salt rof args)
Proof
  strip_tac >> Cases_on `args` >> simp[compile_create_call_def] >>
  Cases_on `t` >> simp[compile_create_call_def] >>
  rename1 `target::value::rest` >>
  Cases_on `ck` >> Cases_on `has_salt` >>
  simp[compile_create_call_def, runtime_data_frame_lower_value,
       runtime_data_frame_create_salt] >>
  Cases_on `rest` >> simp[compile_create_call_def,
    runtime_data_frame_lower_value, runtime_data_frame_create_salt] >>
  gvs[] >>
  simp[runtime_data_frame_lower_value, runtime_data_frame_create_salt] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
       >- simp[runtime_data_frame_lower_value, runtime_data_frame_create_salt] >>
       gen_tac >> BETA_TAC) >>
  simp[]
  >~ [`compile_create_blueprint_args`]
  >- (Cases_on `t` >> gvs[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
           >- simp[runtime_data_frame_lower_value, runtime_data_frame_create_salt] >>
           gen_tac >> BETA_TAC) >>
      pairarg_tac >> simp[])
  >~ [`compile_create_blueprint_append`]
  >- (pairarg_tac >> simp[]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[rich_listTheory.MEM_FRONT, rich_listTheory.MEM_LAST, listTheory.MEM]
QED
