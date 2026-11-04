Theory fnPlanLineageSuffix
Ancestors
  fnPlanLineageReplay stackPlanGen stackModel venomInst list rich_list

Theorem stack_find_append_hit:
  !xs p d ys. stack_find p xs = SOME d ==>
    stack_find p (xs ++ ys) = SOME d
Proof
  Induct_on `xs` >> simp[stack_find_def] >> rpt gen_tac >>
  Cases_on `p h` >> simp[stack_find_def] >>
  Cases_on `stack_find p xs` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem stack_get_depth_suffix_hit:
  stack_get_depth op suffix = SOME d ==>
  stack_get_depth op (prefix ++ suffix) = SOME d
Proof
  simp[stack_get_depth_def, REVERSE_APPEND, stack_find_append_hit]
QED

Theorem stack_get_phi_depth_suffix_hit:
  stack_get_phi_depth alternatives suffix = SOME d ==>
  stack_get_phi_depth alternatives (prefix ++ suffix) = SOME d
Proof
  simp[stack_get_phi_depth_def, REVERSE_APPEND, stack_find_append_hit]
QED

Theorem stack_get_phi_depth_suffix_compare:
  stack_get_phi_depth alternatives suffix = SOME d ==>
  stack_get_phi_depth alternatives (p ++ suffix) =
    stack_get_phi_depth alternatives (q ++ suffix)
Proof
  metis_tac[stack_get_phi_depth_suffix_hit]
QED

Theorem generate_inst_plan_jmp_suffix:
  generate_inst_plan liveness dfg cfg fn inst nl ih nit lbl ps = SOME (ops, ps') /\
  inst.inst_opcode = JMP /\
  join_target_ops liveness fn lbl inst = SOME targets ==>
  ?prefix. ps'.ps_stack = prefix ++ targets
Proof
  simp[generate_inst_plan_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), is_param_opcode_def, join_reached_def] >>
  metis_tac[]
QED

Theorem generate_block_insts_plan_jmp_suffix:
  !insts ps i ops ps'.
  generate_block_insts_plan liveness dfg cfg fn lbl ih np bl i insts ps =
    SOME (ops, ps') /\ insts <> [] /\ (LAST insts).inst_opcode = JMP /\
  join_target_ops liveness fn lbl (LAST insts) = SOME targets ==>
  ?prefix. ps'.ps_stack = prefix ++ targets
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> Cases_on `insts = []`
  >- (gvs[generate_block_insts_plan_def] >>
      gvs[AllCaseEqs()] >> metis_tac[generate_inst_plan_jmp_suffix]) >>
  simp[Once generate_block_insts_plan_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  first_x_assum irule >> gvs[LAST_DEF] >>
  goal_assum (drule_at Any)
QED

Theorem generate_block_plan_jmp_suffix:
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  non_param_insts bb <> [] /\ (LAST (non_param_insts bb)).inst_opcode = JMP /\
  join_target_ops liveness fn bb.bb_label (LAST (non_param_insts bb)) = SOME targets ==>
  ?prefix. ps'.ps_stack = prefix ++ targets
Proof
  simp[generate_block_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  metis_tac[generate_block_insts_plan_jmp_suffix]
QED
