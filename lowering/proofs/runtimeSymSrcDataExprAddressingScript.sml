Theory runtimeSymSrcDataExprAddressing
Ancestors
  runtimeSymSrcDataExprCallbacks runtimeSymSrcDataFrame exprLowering
  compileEnv targetPlaceLive targetPlaceSimCasesBase

Theorem runtime_data_frame_attribute:
  runtime_data_frame (cfn cenv ty base_e) ==>
  runtime_data_frame (compile_attribute cfn cenv rt ty base_e fld)
Proof
  simp[compile_attribute_def]
QED

Theorem runtime_data_frame_extcall_store_args:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst. runtime_data_frame (compile_store_bytestring v dst)) ==>
  !es tys buf off.
    (!e ty. MEM e es ==> runtime_data_frame (cfn cenv ty e)) ==>
    runtime_data_frame (compile_extcall_store_args cfn cenv es tys buf off)
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_args_def] >>
  rpt gen_tac >> Cases_on `tys` >> rpt strip_tac >>
  simp[compile_extcall_store_args_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
       >- simp[runtime_data_frame_lower_value] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
       >- (rpt IF_CASES_TAC >> simp[]) >> gen_tac >> BETA_TAC) >> simp[]
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
  strip_tac >> ho_match_mp_tac base_assignment_target_induct >>
  rpt conj_tac
  >- (gen_tac >> simp[target_indices_def, compile_get_target_ptr_def] >>
      namedCases_on `FLOOKUP cenv.ce_vars id` ["", "binding"] >> simp[] >>
      Cases_on `binding` >> simp[])
  >- (gen_tac >> simp[target_indices_def, compile_get_target_ptr_def] >>
      namedCases_on `FLOOKUP cenv.ce_module_vars nsid` ["", "binding"] >> simp[] >>
      Cases_on `binding` >> simp[])
  >- (simp[target_indices_def, compile_get_target_ptr_def] >>
      rpt strip_tac >> match_mp_tac runtime_data_frame_bind >> conj_tac
      >- (first_x_assum irule >> simp[]) >>
      gen_tac >> BETA_TAC >>
      namedCases_on `SND (SND x)` ["", "pt"] >> simp[]
      >- simp[runtime_data_frame_lower_value] >>
      Cases_on `pt` >> simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
           >- simp[runtime_data_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[]) >>
  simp[target_indices_def, compile_get_target_ptr_def]
QED

Theorem runtime_data_frame_subscript:
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
  strip_tac >> simp[compile_subscript_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  namedCases_on `place_type cenv base_e` ["kt vt", "bt"]
  >- (simp[] >>
      rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
           >- simp[runtime_data_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[]) >>
  Cases_on `bt` >> simp[runtime_data_frame_lower_value]
QED
