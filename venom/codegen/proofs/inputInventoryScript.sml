(* Resources established by operand preparation, including repeated inputs.
   TOP-LEVEL: emit_input_plan_pending_counts.
   Helper: reserve one existing variable copy until its final input use. *)
Theory inputInventory
Ancestors
  operandInventory stackPlanGen stackPlanOps stackPlanTypes stackModel
  dfgDefs venomInst indexedLists list rich_list finite_map arithmetic

Definition operand_inventory_def:
  operand_inventory op (ps:plan_state) =
    LIST_ELEM_COUNT op ps.ps_stack + (if op IN FDOM ps.ps_spilled then 1 else 0)
End

Definition input_inventory_wf_def:
  input_inventory_wf done pending ps <=>
    !op. LIST_ELEM_COUNT op done +
      (if is_var_operand op /\ MEM op pending then 1 else 0) <=
      operand_inventory op ps
End

Theorem operand_inventory_positive:
  0 < operand_inventory op ps <=> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  Cases_on `op IN FDOM ps.ps_spilled` >>
  simp[operand_inventory_def, REWRITE_RULE [GREATER_DEF] LIST_ELEM_COUNT_MEM]
QED

Theorem emit_operand_inventory_mono:
  !opc nl op ps ops post x.
    emit_one_input opc nl op ps = (ops,post) ==>
    operand_inventory x ps <= operand_inventory x post
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`,`x`] emit_one_input_inventory_mono) >>
  asm_simp_tac (srw_ss()) [operand_inventory_def]
QED

Theorem emit_operand_inventory_inc:
  !opc nl op ps ops post.
    emit_one_input opc nl op ps = (ops,post) /\
    (~is_var_operand op \/
      ?v. op = Var v /\ MEM v nl /\
          (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled)) ==>
    operand_inventory op ps + 1 <= operand_inventory op post
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`] emit_one_input_inventory_inc) >>
  asm_simp_tac (srw_ss()) [operand_inventory_def]
QED

Theorem input_inventory_head_available:
  input_inventory_wf done (op::rest) ps /\ is_var_operand op ==>
  MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled
Proof
  rpt strip_tac >> rewrite_tac [GSYM operand_inventory_positive] >>
  qpat_x_assum `input_inventory_wf _ _ _` mp_tac >>
  simp[input_inventory_wf_def] >>
  disch_then (qspec_then `op` mp_tac) >> simp[] >> decide_tac
QED

Theorem emit_input_head_inventory_inc:
  !opc done rest nl op ps ops post.
    input_inventory_wf done (op::rest) ps /\
    emit_one_input opc (operand_vars rest ++ nl) op ps = (ops,post) /\
    (~is_var_operand op \/ MEM op rest) ==>
    operand_inventory op ps + 1 <= operand_inventory op post
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`opc`,`operand_vars rest ++ nl`,`op`,`ps`,`ops`,`post`]
    emit_operand_inventory_inc) >>
  (impl_tac >- (asm_rewrite_tac [] >> Cases_on `is_var_operand op` >> simp[] >>
    `MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
      (drule_all input_inventory_head_available >> simp[]) >>
    Cases_on `op` >> gvs[is_var_operand_def] >> rename1 `Var v` >>
    asm_simp_tac (srw_ss()) [MEM_operand_vars_eq_Var])) >>
  simp_tac bool_ss []
QED

Theorem emit_input_inventory_step:
  !opc done rest nl op ps ops post.
    input_inventory_wf done (op::rest) ps /\
    emit_one_input opc (operand_vars rest ++ nl) op ps = (ops,post) ==>
    input_inventory_wf (done ++ [op]) rest post
Proof
  rpt gen_tac >> strip_tac >> simp[input_inventory_wf_def] >> gen_tac >>
  rename1 `LIST_ELEM_COUNT x _ + _ <= _` >>
  `LIST_ELEM_COUNT x done +
    (if is_var_operand x /\ MEM x (op::rest) then 1 else 0) <=
    operand_inventory x ps` by fs[input_inventory_wf_def] >>
  `operand_inventory x ps <= operand_inventory x post` by
    (drule_all emit_operand_inventory_mono >> simp[]) >>
  reverse (Cases_on `x = op`)
  >- (gvs[LIST_ELEM_COUNT_THM] >> irule LESS_EQ_TRANS >>
      qexists_tac `operand_inventory x ps` >> asm_rewrite_tac []) >>
  gvs[LIST_ELEM_COUNT_THM] >>
  Cases_on `is_var_operand op` >> Cases_on `MEM op rest` >> gvs[] >>
  FIRST [decide_tac,
    `~is_var_operand op \/ MEM op rest` by simp[] >>
    mp_tac (Q.SPECL [`opc`,`done`,`rest`,`nl`,`op`,`ps`,`ops`,`post`]
      emit_input_head_inventory_inc) >>
    (impl_tac >- asm_rewrite_tac []) >> strip_tac >> decide_tac]
QED

Theorem emit_input_plan_inventory:
  !pending done opc nl ps ops post.
    input_inventory_wf done pending ps /\
    emit_input_plan opc pending nl ps = (ops,post) ==>
    input_inventory_wf (done ++ pending) [] post
Proof
  Induct >- simp[emit_input_plan_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars pending ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc pending nl mid` >>
  rename1 `emit_input_plan opc pending nl mid = (rest_ops,last)` >>
  `ops = step_ops ++ rest_ops /\ post = last` by
    (qpat_x_assum `emit_input_plan opc (h::pending) nl ps = _` mp_tac >>
     simp[Once emit_input_plan_def, LET_THM]) >> gvs[] >>
  `input_inventory_wf (done ++ [h]) pending mid` by
    (drule_all emit_input_inventory_step >> simp[]) >>
  first_x_assum (qspecl_then [`done ++ [h]`,`opc`,`nl`,`mid`,`rest_ops`,`last`]
    mp_tac) >> pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac []
QED

Theorem input_inventory_initial:
  (!op. MEM op operands /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  input_inventory_wf [] operands ps
Proof
  simp[input_inventory_wf_def, LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `is_var_operand op /\ MEM op operands` >> simp[] >>
  `0 < operand_inventory op ps` by
    (simp[operand_inventory_positive] >> first_x_assum irule >> simp[]) >>
  decide_tac
QED

Theorem emit_input_plan_pending_counts:
  !operands opc nl ps ops post.
    (!op. MEM op operands /\ is_var_operand op ==>
          MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (ops,post) ==>
    !op. LIST_ELEM_COUNT op operands <= operand_inventory op post
Proof
  rpt gen_tac >> strip_tac >>
  `input_inventory_wf [] operands ps` by
    (irule input_inventory_initial >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`operands`,`[]`,`opc`,`nl`,`ps`,`ops`,`post`]
    emit_input_plan_inventory) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[input_inventory_wf_def]
QED
