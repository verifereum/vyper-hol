(* Captured parameter ages at actual compiler declaration boundaries. *)
Theory bodyPtrBytestringBuiltinsParameterAges
Ancestors
  moduleLowering intCallCallee exprSafeOperand emitHelper compileEnv list

Theorem internal_param_decls_safe_operands:
  !ps idx sa caps next sb.
  compile_internal_param_decls ps idx sa = ((caps,next),sb) ==>
  EVERY (\(name,is_stack,op). safe_operand sb op) caps
Proof
  Induct_on `ps`
  >- simp[compile_internal_param_decls_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[compile_internal_param_decls_def, comp_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  PairCases_on `rest_result` >> gvs[] >>
  drule internal_param_decls_projection >> strip_tac >>
  drule emit_op_safe_operand >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[] >> metis_tac[safe_operand_mono]
QED

(* Restrict this interface to ce_vars. Return buffers/PCs have separate
   installation points and are deliberately not hidden in this predicate. *)
Definition env_operand_age_def:
  env_operand_age ce s <=>
    !name op size. FLOOKUP ce.ce_vars name = SOME (PtrVar op size) ==>
                   safe_operand s op
End

Theorem env_operand_age_mono:
  env_operand_age ce sa /\ sa.cs_next_var <= sb.cs_next_var ==>
  env_operand_age ce sb
Proof
  rw[env_operand_age_def] >> metis_tac[safe_operand_mono]
QED

Theorem env_operand_age_update:
  env_operand_age ce s /\ safe_operand s op ==>
  env_operand_age (ce with ce_vars updated_by
    (\m. m |+ (name,PtrVar op (sz:num)))) s
Proof
  rw[env_operand_age_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem materialize_internal_params_grows:
  !caps ce sa ce' sb.
  materialize_internal_params ce caps sa = (ce',sb) ==>
  sa.cs_next_var <= sb.cs_next_var
Proof
  Induct_on `caps`
  >- simp[materialize_internal_params_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- metis_tac[] >>
      Cases_on `x` >> simp[] >>
      simp[comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >> strip_tac >>
      gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem materialize_internal_params_env_age:
  !caps ce sa ce' sb.
  env_operand_age ce sa /\
  EVERY (\(name,is_stack,op). safe_operand sa op) caps /\
  materialize_internal_params ce caps sa = (ce',sb) ==>
  env_operand_age ce' sb
Proof
  Induct_on `caps`
  >- simp[materialize_internal_params_def, comp_return_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[materialize_internal_params_def] >>
  Cases_on `h1` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- metis_tac[] >>
      Cases_on `x` >> simp[]
      >- (simp[comp_bind_def, comp_ignore_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
      drule emit_op_safe_operand >> strip_tac >>
      gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
      reverse conj_tac
      >- (irule env_operand_age_update >> simp[] >> conj_tac
          >- (irule env_operand_age_mono >> goal_assum (drule_at Any) >> simp[]) >>
          irule safe_operand_mono >> goal_assum (drule_at Any) >> simp[]) >>
      fs[EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      irule safe_operand_mono >> goal_assum (drule_at Any) >> simp[]) >>
      rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[env_operand_age_update]
QED

Theorem captured_operand_ages_mono:
  EVERY (\(name,is_stack,op). safe_operand sa op) caps /\
  sa.cs_next_var <= sb.cs_next_var ==>
  EVERY (\(name,is_stack,op). safe_operand sb op) caps
Proof
  rw[EVERY_MEM, pairTheory.FORALL_PROD] >>
  metis_tac[safe_operand_mono]
QED

Theorem internal_declarations_materialize_env_age:
  compile_internal_param_decls ps idx start = ((caps,next),declared) /\
  declared.cs_next_var <= sa.cs_next_var /\
  env_operand_age ce sa /\
  materialize_internal_params ce caps sa = (ce',sb) ==>
  env_operand_age ce' sb
Proof
  rpt strip_tac >> drule internal_param_decls_safe_operands >> strip_tac >>
  drule_all captured_operand_ages_mono >> strip_tac >>
  drule_all materialize_internal_params_env_age >> simp[]
QED
