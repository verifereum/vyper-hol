(* Recover concrete input words from an exactly prepared planner suffix.
   TOP-LEVEL: prepared_operands_values.
   Shared by instructions consuming any number of prepared operands. *)
Theory preparedStackValues
Ancestors
  codegenRel stackOpSim stackModel venomState
  list rich_list arithmetic finite_map

Theorem plan_stack_rel_snoc_values:
  !lo vs prefix op stk.
    plan_stack_rel lo vs (SNOC op prefix) stk /\ op <> dead_stack_marker ==>
    ?value rest. stk = value::rest /\ operand_val vs lo op = SOME value /\
      plan_stack_rel lo vs prefix rest
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH stk = SUC (LENGTH prefix)` by
    (drule plan_stack_rel_length >> simp[]) >>
  Cases_on `stk` >> gvs[] >>
  rename1 `plan_stack_rel lo vs (SNOC op prefix) (value::rest)` >>
  conj_tac
  >- (drule plan_stack_rel_hd >> simp[]) >>
  mp_tac (Q.SPECL [`lo`,`vs`,`SNOC op prefix`,`value::rest`,`1`]
    plan_stack_rel_pop) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac)) >>
  simp[TAKE_SNOC]
QED

Theorem plan_stack_rel_eval_prefix:
  !operands values prefix lo vs stk.
    EVERY (\op. op <> dead_stack_marker) operands /\
    (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
    eval_operands operands vs = SOME values /\
    plan_stack_rel lo vs (prefix ++ REVERSE operands) stk ==>
    ?rest. stk = values ++ rest
Proof
  Induct
  >- (simp[eval_operands_def] >> rpt strip_tac >> gvs[] >>
      qexists_tac `stk` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `eval_operand h vs = operand_val vs lo h` by
    (qpat_assum `!op. MEM op (h::operands) ==> _`
       (qspec_then `h` mp_tac) >> simp[]) >>
  `!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op` by
    (qx_gen_tac `op` >> strip_tac >>
     qpat_assum `!op. MEM op (h::operands) ==> _`
       (qspec_then `op` mp_tac) >> asm_simp_tac (srw_ss()) []) >>
  qpat_x_assum `!op. MEM op (h::operands) ==> _` kall_tac >>
  Cases_on `eval_operand h vs` >> gvs[eval_operands_def] >>
  rename1 `SOME value = operand_val vs lo h` >>
  qpat_x_assum `SOME value = operand_val vs lo h` (assume_tac o SYM) >>
  Cases_on `eval_operands operands vs` >> gvs[] >>
  rename1 `eval_operands operands vs = SOME tail_values` >>
  `plan_stack_rel lo vs (SNOC h (prefix ++ REVERSE operands)) stk` by
    fs[REVERSE_DEF, SNOC_APPEND, APPEND_ASSOC] >>
  mp_tac (Q.SPECL [`lo`,`vs`,`prefix ++ REVERSE operands`,`h`,`stk`]
    plan_stack_rel_snoc_values) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `actual` (qx_choose_then `tail` strip_assume_tac)) >>
  `actual = value` by fs[] >>
  first_x_assum (qspecl_then [`tail_values`,`prefix`,`lo`,`vs`,`tail`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `rest` strip_assume_tac) >>
  qexists_tac `rest` >> asm_simp_tac (srw_ss()) []
QED

Theorem prepared_operands_values:
  !lo ps vs st operands values.
    venom_asm_rel lo ps vs st /\
    ps.ps_stack = stack_pop (LENGTH operands) ps.ps_stack ++ operands /\
    EVERY (\op. op <> dead_stack_marker) operands /\
    (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
    eval_operands (REVERSE operands) vs = SOME values ==>
    ?rest. st.as_stack = values ++ rest
Proof
  rpt gen_tac >> strip_tac >>
  `plan_stack_rel lo vs
    (stack_pop (LENGTH operands) ps.ps_stack ++ operands)
    st.as_stack` by
    (qpat_assum `ps.ps_stack = _` (fn shape =>
       ONCE_REWRITE_TAC [GSYM shape]) >>
     qpat_assum `venom_asm_rel lo ps vs st`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [venom_asm_rel_def])) >>
  qpat_x_assum `ps.ps_stack = _` kall_tac >>
  mp_tac (Q.SPECL [`REVERSE (operands:operand list)`,`values`,
    `stack_pop (LENGTH (operands:operand list)) ps.ps_stack`,`lo`,`vs`,`st.as_stack`]
    plan_stack_rel_eval_prefix) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_REVERSE] >>
    rpt strip_tac >> qpat_assum `!op. MEM op operands ==> _`
      (qspec_then `op` mp_tac) >> asm_simp_tac (srw_ss()) [])) >>
  simp_tac bool_ss []
QED
