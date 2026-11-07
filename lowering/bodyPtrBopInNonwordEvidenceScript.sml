(* Checked negation of the frozen membership instance; target unchanged. *)
Theory bodyPtrBopInNonwordEvidence
Ancestors
  bodyPtrBopInOutcomeRejection bodyPtrBopInMachineConditions
  bodyPtrBopInMachineFrame bodyPtrBopInJointSource bodyPtrBopInName
  bodyPtrBopInLocalSuffix bodyPtrBopInUnit bodyPtrBopInActualSuffix
  bodyPtrPreds bodyPtrDefs exprSimDefs vyperAST

Theorem joint_membership_not_vv_sim_ptr:
  ~expr_vv_sim_ptr NONE (equality_runtime_context equality_selector) PG
    (equality_runtime_function equality_selector) joint_cenv joint_cx
    (BaseT BoolT) local_membership_fixture joint_es
Proof
  strip_tac >> fs[expr_vv_sim_ptr_def] >>
  first_x_assum (qspecl_then
    [`actual_suffix_start equality_selector`, `actual_suffix_end equality_selector`,
     `StackValue (BaseT BoolT) (Var "%14")`, `joint_machine`,
     `joint_provenance`, `entry_taint`] mp_tac) >>
  simp[joint_membership_pointer_antecedents, joint_cenv_frame_fields] >>
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[IMP_CLAUSES] >>
  irule joint_membership_outcome_rejected >> rpt strip_tac >> gvs[]
QED

Theorem joint_membership_not_body_ptr_ok:
  ~body_expr_ptr_ok joint_cx local_membership_fixture
Proof
  strip_tac >> fs[body_expr_ptr_ok_def] >>
  first_x_assum (qspecl_then
    [`NONE`, `PG`, `equality_tops`,
     `equality_runtime_context equality_selector`,
     `equality_runtime_function equality_selector`, `joint_cenv`,
     `joint_env`, `BaseT BoolT`, `joint_es`] mp_tac) >>
  simp[joint_body_inv, joint_membership_pre, joint_membership_not_vv_sim_ptr]
QED

Theorem bop_in_expr_ptr_ok_counterexample:
  ~((In = In \/ In = NotIn) /\
    (builtin_args_length_ok (Bop In)
       (LENGTH [Name (BaseT (StringT 1)) "x";
         Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
           (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
           [Name (BaseT (StringT 1)) "y"]]) ==>
     body_exprs_ptr_ok joint_cx
       [Name (BaseT (StringT 1)) "x";
        Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
          (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
          [Name (BaseT (StringT 1)) "y"]]) ==>
    body_expr_ptr_ok joint_cx
      (Builtin (BaseT BoolT) (Bop In)
        [Name (BaseT (StringT 1)) "x";
         Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
           (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
           [Name (BaseT (StringT 1)) "y"]]))
Proof
  simp[local_membership_operands_ptr_ok,
       GSYM local_membership_fixture_def, joint_membership_not_body_ptr_ok]
QED
