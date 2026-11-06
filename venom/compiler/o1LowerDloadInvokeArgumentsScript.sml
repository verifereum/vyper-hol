(* Relocation-aware argument-vector transport. *)
Theory o1LowerDloadInvokeArguments
Ancestors
  o1LowerDloadJointCall o1LowerDloadJointScalar o1LowerDloadEnvironment
  o1LowerDloadJointRelation o1LowerDloadOccurrence ptrDiscipline
  venomExecSemantics venomState venomInst unitShapeDefs list finite_map pred_set

Theorem ld_env_operands_value:
  !ops args.
  ld_env_agree sites fn H tn s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) ops ==> MEM v (fn_ir_vars fn)) /\
  (!v. MEM (Var v) ops ==> ~retpc_var fn v) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  eval_operands ops s = SOME args ==>
  ?args'. eval_operands ops t = SOME args' /\ LENGTH args = LENGTH ops /\
    LENGTH args' = LENGTH args /\
    !k. k < LENGTH ops ==> ld_value_agree sites (op_prov H (EL k ops)) {}
      (EL k args) (EL k args')
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> rename1 `eval_operand h s = SOME x` >>
  `?y. eval_operand h t = SOME y /\
    ld_value_agree sites (op_prov H h) {} x y` by
    (drule_at (Pat `eval_operand _ _ = SOME _`) ld_env_operand_value >>
     simp[] >> metis_tac[]) >>
  qexists_tac `y::args'` >> simp[eval_operands_def] >>
  Cases >> simp[]
QED

Theorem ld_joint_invoke_arguments:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\ eval_operands ops s = SOME args ==>
  ?args'. eval_operands ops t = SOME args' /\ LENGTH args = LENGTH ops /\
    LENGTH args' = LENGTH args /\
    !k. k < LENGTH ops ==> ld_value_agree sites (op_prov H (EL k ops)) {}
      (EL k args) (EL k args')
Proof
  strip_tac >>
  `inst.inst_operands = Label nm::ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[ld_joint_source, occ_frame_reachable_projection] >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `!op. MEM op ops ==> op_taint tn op = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `!v. MEM (Var v) ops ==> MEM v (fn_ir_vars fn)` by
    metis_tac[ld_active_operand_ir_var, MEM] >>
  `!v. MEM (Var v) ops ==> ~retpc_var fn v` by
    (gen_tac >> disch_tac >> irule ld_active_operand_non_retpc >>
     simp[] >> qexistsl_tac [`inst`,`s`] >>
     simp[retpc_use_ok_def] >> metis_tac[MEM]) >>
  irule ld_env_operands_value >>
  metis_tac[ld_joint_environment, ld_joint_labels]
QED

Theorem ld_joint_boundary_call_invariant:
  ld_joint_boundary vs C C' lo D stk PG G tn caller callinst s t
    n a U B HP H sites X ts /\ ptr_discipline lo C vs /\
  opaque_use_ok caller /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  lookup_function nm C'.ctx_functions = SOME callee' /\
  ir_supply_covers_fn uc callee /\
  lower_dload_function_supply uc callee = (callee',uc') /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ?args' ct t1. eval_operands ops t = SOME args' /\
    setup_callee callee' args' t = SOME ct /\ enters_block callee' ct t1 /\
    s1.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    t1.vs_call_ctx.cc_address = t.vs_call_ctx.cc_address /\
    ld_joint_boundary vs C C' lo D
      (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1 t1
      (SUC n) n (<|of_owner := a; of_prov := H; of_params := HP |> :: U)
      B (MAP (op_prov H) ops) FEMPTY sites X (t::ts)
Proof
  strip_tac >> drule_all ld_joint_invoke_arguments >> strip_tac >>
  drule_all ld_joint_boundary_call >> strip_tac >>
  qexistsl_tac [`args'`, `ct`, `t1`] >> simp[]
QED
