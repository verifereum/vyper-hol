(* Compilation intervals and register reservations for augmented places. *)
Theory augAssignPlaceCompileMemory
Ancestors
  stmtSimAugAssignPlace stmtLoweringMono exprLoweringProps fragExec
  freshWrites compileEnv

Theorem aug_place_suffix_intervals[local]:
  emit_op load [dst] s0 = (cur,s1) /\
  lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE el s2 = (result,s3) /\
  emit_void store [dst;result] s3 = ((),sf) ==>
  ci_mono s0 s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`load`, `[dst]`, `s0`] ci_mono_emit_op) >>
  mp_tac (Q.SPECL [`store`, `[dst;result]`, `s3`] ci_mono_emit_void) >>
  drule (cj 2 compile_expr_grows) >>
  drule compile_binop_grows >> simp[ci_mono_def]
QED

Theorem aug_place_interval_frame[local]:
  ci_mono sa sb /\ local_ptrs_reserved cenv sa ==>
  local_ptrs_reserved cenv sb /\
  (!z. not_fresh_at sa z ==> not_fresh_at sb z)
Proof
  simp[ci_mono_def] >> strip_tac >> conj_tac
  >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[not_fresh_at_mono]
QED

Theorem aug_place_suffix_code[local]:
  ci_mono s0 s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
  fn_has_code s0 sf func ==>
  fn_has_code s0 s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func
Proof
  simp[ci_mono_def] >> strip_tac >>
  `cs_extends s2 sf` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sf` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem aug_place_compilation_mem:
  stmt_env cenv lctx ret_ty (AugAssign ty t bop e) sa = (c,sf) /\
  fn_has_code sa sf func /\ local_ptrs_reserved cenv sa ==>
  c = cenv /\
  ?r s0. compile_get_target_ptr compile_expr cenv t sa = (r,s0) /\
    ci_mono sa s0 /\ fn_has_code sa s0 func /\
    local_ptrs_reserved cenv s0 /\
    (!z. not_fresh_at sa z ==> not_fresh_at s0 z) /\
    ((FST (SND r) = NONE /\ emit_void INVALID [] s0 = ((),sf)) \/
     ?loc cur rhs result s1 s2 s3.
       FST (SND r) = SOME loc /\
       emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
         [FST r] s0 = (cur,s1) /\
       lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
       compile_binop bop cur rhs ty NONE
         (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
       emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
         [FST r;result] s3 = ((),sf) /\
       ci_mono s0 s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
       fn_has_code s0 s1 func /\ fn_has_code s1 s2 func /\
       fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
       local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
       local_ptrs_reserved cenv s3 /\
       (!z. not_fresh_at s0 z ==> not_fresh_at s1 z) /\
       (!z. not_fresh_at s1 z ==> not_fresh_at s2 z) /\
       (!z. not_fresh_at s2 z ==> not_fresh_at s3 z))
Proof
  strip_tac >> drule aug_place_code_parts >> strip_tac >> gvs[] >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,s0)` >>
  `ci_mono sa s0` by
    (qspec_then `t` (qspec_then `cenv` (qspec_then `sa` mp_tac))
       ci_mono_compile_get_target_ptr >> simp[]) >>
  drule_all aug_place_interval_frame >> strip_tac
  >- (mp_tac (Q.SPECL [`INVALID`, `[]`, `s0`] ci_mono_emit_void) >>
      simp[ci_mono_def] >> strip_tac >>
      fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  drule_all aug_place_suffix_intervals >> strip_tac >>
  `cs_extends s0 sf` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s0 func /\ fn_has_code s0 sf func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  drule_all aug_place_suffix_code >> strip_tac >>
  drule_all aug_place_interval_frame >> strip_tac >>
  drule_all aug_place_interval_frame >> strip_tac >>
  drule_all aug_place_interval_frame >> strip_tac >>
  simp[]
QED
