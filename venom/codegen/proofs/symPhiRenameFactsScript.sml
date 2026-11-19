(* Shared stack-kind facts for postfix and own-mode PHI renaming. *)
Theory symPhiRenameFacts
Ancestors
  symInstKinds codegenSymRel stackPlanTypes stackPlanGen stackModel
  planWf genBlockSim rich_list list

Theorem LIST_REL_relabel_left:
  LIST_REL R xs ys /\
  (!sv. R (EL i xs) sv ==> R op sv) ==>
  LIST_REL R (LUPDATE op i xs) ys
Proof
  simp[LIST_REL_EL_EQN, EL_LUPDATE] >> rpt strip_tac >>
  IF_CASES_TAC >> metis_tac[]
QED

Theorem sym_kinds_ok_poke:
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!sv. op_kind_ok fn ret (stack_peek d ps.ps_stack) sv ==>
        op_kind_ok fn ret op sv) ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d op ps.ps_stack) ss
Proof
  simp[sym_kinds_ok_def] >> rpt strip_tac >>
  qexists `top` >> simp[] >>
  once_rewrite_tac[GSYM rich_listTheory.LIST_REL_REVERSE_EQ] >>
  pure_rewrite_tac[REVERSE_REVERSE, stack_poke_def] >>
  irule LIST_REL_relabel_left >>
  simp[stack_peek_def, rich_listTheory.LIST_REL_REVERSE1]
QED

Theorem phi_depth_operand:
  stack_get_phi_depth (FILTER is_var_operand ops) stk = SOME d ==>
  ?y. stack_peek d stk = Var y /\ MEM (Var y) ops
Proof
  strip_tac >>
  `d < LENGTH stk` by
    metis_tac[stack_get_phi_depth_def, planWfTheory.stack_find_bound, LENGTH_REVERSE] >>
  `MEM (stack_peek d stk) (FILTER is_var_operand ops)` by
    (gvs[stack_get_phi_depth_def, stack_peek_def] >>
     drule genBlockSimTheory.stack_find_el >>
     simp[EL_REVERSE, arithmeticTheory.PRE_SUB1]) >>
  Cases_on `stack_peek d stk` >>
  gvs[MEM_FILTER, stackPlanTypesTheory.is_var_operand_def]
QED

Theorem sym_phi_rename_own:
  ssa_form fn /\ retpc_shape_ok fn /\ label_flow_own_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  MEM x inst.inst_outputs /\ inst.inst_opcode = PHI /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
    ps.ps_stack = SOME d /\
  sym_kinds_ok cplan fn ret srest ps ss ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke d (Var x) ps.ps_stack) ss
Proof
  strip_tac >> drule phi_depth_operand >> strip_tac >>
  irule sym_kinds_ok_poke >> simp[] >> metis_tac[phi_var_output_kind_own]
QED
