Theory symbolicSourceCompilerAddressFrame
Ancestors
  symbolicSourceCompilerFrame symbolicSourceCompilerCreateFrame exprLowering compileEnv
  targetPlaceLive targetPlaceSimCasesBase

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind]];

Theorem symbolic_frame_attribute:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  symbolic_frame R (cfn cenv ty base_e) ==>
  symbolic_frame R (compile_attribute cfn cenv rt ty base_e fld)
Proof
  simp[compile_attribute_def]
QED

Theorem symbolic_frame_extcall_store_args:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v dst. symbolic_frame R (compile_store_bytestring v dst)) ==>
  !es tys buf off.
    (!e ty. MEM e es ==> symbolic_frame R (cfn cenv ty e)) ==>
    symbolic_frame R (compile_extcall_store_args cfn cenv es tys buf off)
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_args_def] >>
  rpt gen_tac >> Cases_on `tys` >> rpt strip_tac >>
  simp[compile_extcall_store_args_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
       >- simp[symbolic_frame_lower_value] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
       >- (rpt IF_CASES_TAC >> simp[]) >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_get_target_ptr:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v b. symbolic_frame R (compile_keccak256_key v b)) /\
  (!v k. symbolic_frame R (compile_mapping_subscript v k)) /\
  (!b i d n ws sz si loc.
    symbolic_frame R (compile_array_subscript b i d n ws sz si
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))) ==>
  !t. (!e. MEM e (target_indices t) ==>
        symbolic_frame R (cfn cenv (expr_type e) e)) ==>
      symbolic_frame R (compile_get_target_ptr cfn cenv t)
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
      rpt strip_tac >> match_mp_tac symbolic_frame_bind >> conj_tac
      >- (first_x_assum irule >> simp[]) >>
      gen_tac >> BETA_TAC >>
      namedCases_on `SND (SND x)` ["", "pt"] >> simp[]
      >- simp[symbolic_frame_lower_value] >>
      Cases_on `pt` >> simp[] >>
      rpt (match_mp_tac symbolic_frame_bind >> conj_tac
           >- simp[symbolic_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[]) >>
  simp[target_indices_def, compile_get_target_ptr_def]
QED

Theorem symbolic_frame_subscript:
  (!copy vv. symbolic_frame R (compile_snapshot_vv cenv copy vv)) /\
  symbolic_frame R (cfn cenv ty base_e) /\
  symbolic_frame R (cfn cenv ty idx_e) /\
  symbolic_frame R (cfn cenv (expr_type idx_e) idx_e) /\
  (!vv. symbolic_frame R (unwrap_value cenv vv)) /\
  (!v b. symbolic_frame R (compile_keccak256_key v b)) /\
  (!v k. symbolic_frame R (compile_mapping_subscript v k)) /\
  (!v off. symbolic_frame R (compile_tuple_subscript v off)) /\
  (!b i d n ws sz si loc.
    symbolic_frame R (compile_array_subscript b i d n ws sz si
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc))) ==>
  symbolic_frame R (compile_subscript cfn cenv rt ty base_e idx_e)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >>
  namedCases_on `place_type cenv base_e` ["kt vt", "bt"]
  >- (simp[] >>
      rpt (match_mp_tac symbolic_frame_bind >> conj_tac
           >- simp[symbolic_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[] >>
      rpt (match_mp_tac symbolic_frame_bind >> conj_tac
           >- simp[symbolic_frame_lower_value] >> gen_tac >> BETA_TAC) >>
      rpt IF_CASES_TAC >> simp[]) >>
  Cases_on `bt` >> simp[symbolic_frame_lower_value] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
       >- (rpt IF_CASES_TAC >> simp[symbolic_frame_lower_value]) >>
       gen_tac >> BETA_TAC) >> simp[]
QED
