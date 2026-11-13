(* A pure word operator followed by a local-memory place write. *)
Theory bodyIntCallFamStmtMutationAugPlaceMemorySuffix
Ancestors
  bodyIntCallFamStmtMutationBinopCont stmtSimAugAssignPlaceMemory
  bodyIntCallJointContract bodyIntCallFamCallIntCertificateIntro
  gasOutcome gasSummary fragGasMode vyperState exprBopSimProps valueEncodingProps

Theorem intcall_aug_memory_suffix_outcome:
  binop_frag_words fp.jc_ctx fp.jc_func ce fp.jc_cx
    bop ty ty NONE el [ty;expr_type e] cur rhs
    (val_to_w256 cur) (val_to_w256 rhs) ee /\
  intcall_frame_ok fp /\ intcall_expr_res fp ce env ee s2 s /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  expr_res_ok (bop_result fp.jc_cx ty bop [ty;expr_type e] cur rhs ee) /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  (bop_result fp.jc_cx ty bop [ty;expr_type e] cur rhs ee =
    case evaluate_binop bound ptv bop cur rhs of
      INL v => INL v | INR err => INR (Error err)) /\
  (!v. bop_result fp.jc_cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
    value_has_type ptv v /\ ?ff.
      write_place fp.jc_cx (MemoryPlace id path) v ee = (INL (),ff)) /\
  (!v ff. bop_result fp.jc_cx ty bop [ty;expr_type e] cur rhs ee = INL v /\
    write_place fp.jc_cx (MemoryPlace id path) v ee = (INL (),ff) ==>
    expr_sim_inv ce fp.jc_cx env ff) /\
  (!u v ff.
    gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
    intcall_expr_cont fp ce env ee s2 s ee s3 u /\
    eval_operand op u = SOME (val_to_w256 v) /\ word_value v /\
    value_has_type ptv v /\
    write_place fp.jc_cx (MemoryPlace id path) v ee = (INL (),ff) /\
    expr_sim_inv ce fp.jc_cx env ff ==>
    ?t. gas_marked_path F fp.jc_ctx fp.jc_func u 0 (OK t) /\
      intcall_joint_res fp ce env ff sf t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z. lookup_var z t = lookup_var z u) /\
      t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (lift_sum (evaluate_binop bound ptv bop cur rhs))
      (write_place fp.jc_cx (MemoryPlace id path))) (ee,s)
    (\res ff t. res = INL () /\ intcall_joint_res fp ce env ff sf t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z w. not_fresh_at s2 z /\ lookup_var z s = SOME w ==>
        lookup_var z t = SOME w) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      s.vs_alloca_next <= t.vs_alloca_next)
    (\res ff r. intcall_stmt_exit fp res ff r)
Proof
  strip_tac >> drule_all intcall_binop_frag_words_cont >> strip_tac
  >- suspend "normal"
  >> suspend "exception"
QED

Resume intcall_aug_memory_suffix_outcome[normal]:
  gvs[] >>
  `value_has_type ptv v /\ ?ff.
      write_place fp.jc_cx (MemoryPlace id path) v ee = (INL (),ff)` by
    metis_tac[] >>
  `expr_sim_inv ce fp.jc_cx env ff` by metis_tac[] >>
  first_x_assum (drule_at (Pat `intcall_expr_cont`)) >>
  disch_then drule_all >> strip_tac >>
  suspend "package_normal"
QED

Resume intcall_aug_memory_suffix_outcome[exception]:
  suspend "package_exception"
QED

Resume intcall_aug_memory_suffix_outcome[package_normal]:
  gvs[AllCaseEqs()] >>
  `gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t)` by
    (qpat_assum `gas_marked_path F _ _ s 0 (OK u)`
       (mp_then Any mp_tac gas_marked_path_then) >> simp[]) >>
  `!tail. bind (lift_sum (evaluate_binop bound ptv bop cur rhs))
       (write_place fp.jc_cx (MemoryPlace id path)) (ee with gas_obs := tail) =
       (INL (),ff with gas_obs := tail)` by
    (irule aug_place_pure_suffix_gas_obs >>
     simp[bind_def,lift_sum_def,return_def]) >>
  simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >> qexistsl [`INL ()`,`ff`,`OK t`] >>
  simp[gas_marked_exec_def,intcall_joint_res_gas_obs] >>
  gvs[intcall_expr_cont_def]
QED

Resume intcall_aug_memory_suffix_outcome[package_exception]:
  Cases_on `evaluate_binop bound ptv bop cur rhs` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  simp[gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >> qexistsl [`INR (Error y')`,`ee`,`r`] >>
  simp[gas_marked_exec_def,bind_def,lift_sum_def,raise_def,
       intcall_stmt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Finalise intcall_aug_memory_suffix_outcome
