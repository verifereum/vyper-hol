(* Concrete compiler interval interface for request operands. *)
Theory exprExtRequestCode
Ancestors
  exprExtRequestShape stmtLoweringMono exprLoweringProps fragExec compileEnv
  exprLowering list pair

Theorem extrequest_kwargs_mono[local]:
  !ks es cenv rt sa.
    ci_mono sa (SND (compile_ext_call_kwargs compile_expr cenv rt ks es sa))
Proof
  Induct >> Cases_on `es` >> rpt gen_tac >>
  simp[compile_ext_call_kwargs_def, ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt gen_tac >> irule ci_mono_compile_ext_call_kwarg >>
      simp[cj 1 ci_mono_compile_expr_sa]) >>
  rpt strip_tac >> simp[pairTheory.UNCURRY] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt gen_tac >> first_x_assum irule) >>
  simp[pairTheory.UNCURRY, ci_mono_comp_return]
QED

Theorem extrequest_external_mono[local]:
  !ce addr vals tys mem abi mid cap min rmem stat value gas skip hd def rt dty
   enc dec sa.
    ci_mono sa (SND (compile_external_call_kwargs ce addr vals tys mem abi mid
      cap min rmem stat value gas skip hd def rt dty enc dec sa))
Proof
  rpt gen_tac >> rewrite_tac[extrequest_compile_kwargs_factor] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[extrequest_compile_prefix_mono] >>
  rpt gen_tac >> simp[pairTheory.UNCURRY] >>
  ho_match_mp_tac ci_mono_ignore_bind >>
  simp[extrequest_compile_step_mono, extrequest_compile_return_mono]
QED

Theorem extrequest_operand_code:
  lower_value compile_expr ce (BaseT AddressT) a sa = (addr,s1) /\
  compile_multi_vvs compile_expr ce xs s1 = (vals,s2) /\
  compile_ext_call_kwargs compile_expr ce rt opts kwargs s2 =
    ((value_opt,gas_opt,default_opt),s3) /\
  (case gas_opt of NONE => emit_op GAS [] s3 | SOME g => (g,s3)) = (gas,s4) /\
  compile_external_call_kwargs ce addr vals tys mem abi mid cap min rmem stat
    value gas skip hd def rt dty ei di s4 = (result,sb) /\
  fn_has_code sa sb func ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
  ci_mono s4 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\ fn_has_code s4 sb func
Proof
  strip_tac >>
  `ci_mono sa s1` by metis_tac[cj 2 ci_mono_compile_expr_sa, SND] >>
  `ci_mono s1 s2` by
    (`ci_mono s1 (SND (compile_multi_vvs compile_expr ce xs s1))` by
       (irule ci_mono_compile_multi_vvs >> simp[cj 1 ci_mono_compile_expr_sa]) >>
     gvs[]) >>
  `ci_mono s2 s3` by metis_tac[extrequest_kwargs_mono, SND] >>
  `ci_mono s3 s4` by
    (Cases_on `gas_opt`
     >- (gvs[] >> metis_tac[ci_mono_emit_op, SND]) >>
     gvs[ci_mono_refl]) >>
  `ci_mono s4 sb` by metis_tac[extrequest_external_mono, SND] >>
  simp[] >> fs[ci_mono_def] >>
  `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED
