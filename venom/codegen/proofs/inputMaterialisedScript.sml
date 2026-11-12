(* Stack copies established by input emission, including repeated operands.
   TOP-LEVEL: emit_input_plan_materialised, materialised_operands_length.
   Helpers separate variable restoration from non-variable pushes. *)
Theory inputMaterialised
Ancestors
  inputInventory operandInventory stackPlanGen stackPlanOps stackPlanTypes
  stackModel dfgDefs list rich_list finite_map arithmetic

Theorem emit_operand_stack_count_mono:
  !opc nl op ps ops post x.
    emit_one_input opc nl op ps = (ops,post) ==>
    LIST_ELEM_COUNT x ps.ps_stack <= LIST_ELEM_COUNT x post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `x NOTIN FDOM ps.ps_spilled ==> x NOTIN FDOM post.ps_spilled` by
    (mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`,`x`]
      emit_one_input_preserves_not_spilled) >> asm_simp_tac (srw_ss()) []) >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`,`x`] emit_one_input_inventory_mono) >>
  asm_simp_tac (srw_ss()) [] >>
  Cases_on `x IN FDOM ps.ps_spilled` >>
  Cases_on `x IN FDOM post.ps_spilled` >> gvs[] >> decide_tac
QED

Theorem emit_operand_nonvar_stack_inc:
  !opc nl op ps ops post.
    ~is_var_operand op /\ emit_one_input opc nl op ps = (ops,post) ==>
    LIST_ELEM_COUNT op ps.ps_stack + 1 <= LIST_ELEM_COUNT op post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `post.ps_spilled = ps.ps_spilled` by
    (mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`]
      emit_one_input_nonvar_spilled_unchanged) >> asm_simp_tac (srw_ss()) []) >>
  mp_tac (Q.SPECL [`opc`,`nl`,`op`,`ps`] emit_one_input_inventory_inc) >>
  asm_simp_tac (srw_ss()) [] >>
  Cases_on `op IN FDOM ps.ps_spilled` >> simp[] >> decide_tac
QED

Theorem emit_input_plan_not_spilled:
  !operands opc nl ps ops post x.
    emit_input_plan opc operands nl ps = (ops,post) /\
    (x NOTIN FDOM ps.ps_spilled \/ (MEM x operands /\ is_var_operand x)) ==>
    x NOTIN FDOM post.ps_spilled
Proof
  Induct >- simp[emit_input_plan_def] >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  rename1 `emit_input_plan opc operands nl mid = (rest_ops,last)` >>
  `ops = step_ops ++ rest_ops /\ post = last` by
    (qpat_x_assum `emit_input_plan opc (h::operands) nl ps = _` mp_tac >>
     simp[Once emit_input_plan_def, LET_THM]) >>
  qpat_x_assum `post = last` SUBST_ALL_TAC >>
  `x NOTIN FDOM mid.ps_spilled \/ (MEM x operands /\ is_var_operand x)` by
    (Cases_on `x NOTIN FDOM ps.ps_spilled \/ (x = h /\ is_var_operand h)`
     >- (disj1_tac >> Cases_on `x NOTIN FDOM ps.ps_spilled`
         >- (mp_tac (Q.SPECL [`opc`,`operand_vars operands ++ nl`,
               `h`,`ps`,`x`] emit_one_input_preserves_not_spilled) >>
             asm_simp_tac (srw_ss()) []) >>
         `x = h /\ is_var_operand h` by fs[] >> gvs[] >>
         mp_tac (Q.SPECL [`opc`,`operand_vars operands ++ nl`,`h`,`ps`]
           emit_one_input_var_not_spilled) >> asm_simp_tac (srw_ss()) []) >>
     gvs[]) >>
  first_x_assum (qspecl_then [`opc`,`nl`,`mid`,`rest_ops`,`last`,`x`] mp_tac) >>
  asm_rewrite_tac []
QED

Theorem emit_input_plan_nonvar_counts:
  !operands opc nl ps ops post x.
    ~is_var_operand x /\ emit_input_plan opc operands nl ps = (ops,post) ==>
    LIST_ELEM_COUNT x ps.ps_stack + LIST_ELEM_COUNT x operands <=
      LIST_ELEM_COUNT x post.ps_stack
Proof
  Induct >- simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ nl) h ps` >>
  rename1 `emit_one_input _ _ _ _ = (step_ops,mid)` >>
  Cases_on `emit_input_plan opc operands nl mid` >>
  rename1 `emit_input_plan opc operands nl mid = (rest_ops,last)` >>
  `ops = step_ops ++ rest_ops /\ post = last` by
    (qpat_x_assum `emit_input_plan opc (h::operands) nl ps = _` mp_tac >>
     simp[Once emit_input_plan_def, LET_THM]) >> gvs[] >>
  first_x_assum (qspecl_then [`opc`,`nl`,`mid`,`rest_ops`,`last`,`x`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
  >- (mp_tac (Q.SPECL [`opc`,`operand_vars operands ++ nl`,`h`,
        `ps`,`step_ops`,`mid`] emit_operand_nonvar_stack_inc) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> decide_tac) >>
  mp_tac (Q.SPECL [`opc`,`operand_vars operands ++ nl`,`h`,`ps`,
    `step_ops`,`mid`,`x`] emit_operand_stack_count_mono) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> decide_tac
QED

Theorem emit_input_plan_materialised:
  !operands opc nl ps ops post.
    (!op. MEM op operands /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    emit_input_plan opc operands nl ps = (ops,post) ==>
    !op. LIST_ELEM_COUNT op operands <= LIST_ELEM_COUNT op post.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`operands`,`opc`,`nl`,`ps`,`ops`,`post`]
    emit_input_plan_pending_counts) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gen_tac >> Cases_on `is_var_operand op`
  >- (Cases_on `MEM op operands`
      >- (`op NOTIN FDOM post.ps_spilled` by
            (mp_tac (Q.SPECL [`operands`,`opc`,`nl`,`ps`,`ops`,`post`,`op`]
              emit_input_plan_not_spilled) >> asm_simp_tac (srw_ss()) []) >>
          qpat_assum `!op. LIST_ELEM_COUNT op operands <= _`
            (mp_tac o REWRITE_RULE [operand_inventory_def] o Q.SPEC `op`) >>
          asm_simp_tac (srw_ss()) []) >>
      fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  mp_tac (Q.SPECL [`operands`,`opc`,`nl`,`ps`,`ops`,`post`,`op`]
    emit_input_plan_nonvar_counts) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >> decide_tac
QED

Theorem materialised_operands_length:
  !(operands:'a list) stack.
    (!op. LIST_ELEM_COUNT op operands <= LIST_ELEM_COUNT op stack) ==>
    LENGTH operands <= LENGTH stack
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `MEM h stack` by
    (qpat_assum `!op. LIST_ELEM_COUNT op (h::operands) <= _`
       (qspec_then `h` assume_tac) >>
     fs[LIST_ELEM_COUNT_THM, GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  qpat_assum `MEM h stack` (mp_tac o REWRITE_RULE [MEM_SPLIT]) >>
  disch_then (qx_choose_then `front` (qx_choose_then `back` strip_assume_tac)) >>
  gvs[] >>
  `!op. LIST_ELEM_COUNT op operands <= LIST_ELEM_COUNT op (front ++ back)` by
    (qx_gen_tac `op` >> qpat_assum `!op. LIST_ELEM_COUNT op (h::operands) <= _`
       (qspec_then `op` assume_tac) >>
     Cases_on `h = op` >> fs[LIST_ELEM_COUNT_THM] >> decide_tac) >>
  first_x_assum (qspec_then `front ++ back` mp_tac) >>
  asm_simp_tac (srw_ss()) [] >> decide_tac
QED
