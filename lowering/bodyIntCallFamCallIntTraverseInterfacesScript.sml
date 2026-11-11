(* Concrete compiler and continuation interfaces for deferred traversal. *)
Theory bodyIntCallFamCallIntTraverseInterfaces
Ancestors
  bodyIntCallJointContract bodyIntCallJointCallCore
  bodyIntCallFamCallIntCertificateIntro exprLoweringProps exprSimHyps

Theorem intcall_traverse_code_split:
  compile_expr ce (expr_type e) e b = (vv,c) /\
  compile_multi_vvs compile_expr ce tail c = (vs,d) /\
  fn_has_code b d func ==>
  fn_has_code b c func /\ fn_has_code c d func /\
  b.cs_next_id <= c.cs_next_id /\ b.cs_next_var <= c.cs_next_var /\
  c.cs_next_id <= d.cs_next_id /\ c.cs_next_var <= d.cs_next_var
Proof
  strip_tac >>
  `ci_mono b c` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `!st. ci_mono st (SND (compile_multi_vvs compile_expr ce tail st))` by
    (gen_tac >> irule ci_mono_compile_multi_vvs >>
     simp[compile_expr_ci_mono]) >>
  `ci_mono c d` by metis_tac[pairTheory.SND] >>
  gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]
QED

Theorem intcall_expr_cont_gas_obs:
  intcall_expr_cont fp ce env (es with gas_obs := gs) a s
    (ee with gas_obs := hs) b u <=>
  intcall_expr_cont fp ce env es a s ee b u
Proof
  simp[intcall_expr_cont_def, intcall_joint_res_gas_obs,
       loweringPostsTheory.locals_kept_def]
QED

(* The producer's admissibility premise follows at the live endpoint
   directly from typing and I; no list-wide gas-admissibility is needed. *)
Theorem intcall_traverse_child_admissible:
  expr_body_pre ce fp.jc_cx env e es /\
  intcall_joint_res fp ce env ee b u ==>
  gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok ee
Proof
  strip_tac >> irule expr_body_pre_vv_gas_admissible >>
  qexistsl [`ce`, `env`] >> irule expr_body_pre_state_transport >>
  conj_tac >- fs[intcall_joint_res_def] >>
  qexists `es` >> simp[]
QED
