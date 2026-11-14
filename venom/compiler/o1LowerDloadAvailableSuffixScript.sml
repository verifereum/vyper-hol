(* Relocated payloads need only availability while executing a discarded suffix. *)
Theory o1LowerDloadAvailableSuffix
Ancestors
  venomExecSemantics venomExecProps venomState venomInst
  o1LowerDloadJointAssign list finite_map pred_set gasEvents

Theorem ld_available_operand:
  s.vs_labels = t.vs_labels /\
  (!v. v IN V ==> (IS_SOME (FLOOKUP s.vs_vars v) <=>
                   IS_SOME (FLOOKUP t.vs_vars v))) /\
  (!v. op = Var v ==> v IN V) ==>
  (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

Theorem ld_available_update:
  (!v. v IN V ==> (IS_SOME (FLOOKUP s.vs_vars v) <=>
                   IS_SOME (FLOOKUP t.vs_vars v))) ==>
  !v. v IN V ==>
    (IS_SOME (FLOOKUP (update_var out x s).vs_vars v) <=>
     IS_SOME (FLOOKUP (update_var out y t).vs_vars v))
Proof
  strip_tac >> gen_tac >> Cases_on `out = v` >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_available_suffix_abort:
  !d s t bb bb' ri fuel C C' reason s1 V.
  s.vs_labels = t.vs_labels /\
  (!v. v IN V ==> (IS_SOME (FLOOKUP s.vs_vars v) <=>
                   IS_SOME (FLOOKUP t.vs_vars v))) /\
  (!k. k <= d ==> get_instruction bb (s.vs_inst_idx + k) =
                  get_instruction bb' (t.vs_inst_idx + k)) /\
  get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
  ri.inst_opcode = REVERT /\
  (!k ii. k < d /\ get_instruction bb (s.vs_inst_idx + k) = SOME ii ==>
          ii.inst_opcode = ASSIGN) /\
  (!k ii v. k <= d /\ get_instruction bb (s.vs_inst_idx + k) = SOME ii /\
            MEM (Var v) ii.inst_operands ==> v IN V) /\
  exec_block fuel C bb s = Abort reason s1 ==>
  ?t1. exec_block fuel C' bb' t = Abort reason t1
Proof
  Induct_on `d`
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      `get_instruction bb' t.vs_inst_idx = SOME ri` by metis_tac[] >>
      qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
      simp[Once exec_block_def] >>
      simp[step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      simp[AllCaseEqs()] >> strip_tac >>
      gvs[] >>
      `IS_SOME (eval_operand off_op s) <=> IS_SOME (eval_operand off_op t)` by
        (irule ld_available_operand >> metis_tac[MEM]) >>
      `IS_SOME (eval_operand sz_op s) <=> IS_SOME (eval_operand sz_op t)` by
        (irule ld_available_operand >> metis_tac[MEM]) >>
      Cases_on `eval_operand off_op t` >> gvs[] >>
      Cases_on `eval_operand sz_op t` >> gvs[] >>
      simp[Once exec_block_def] >> simp[step_inst_non_invoke] >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `cur.inst_opcode = ASSIGN` by
    (qpat_x_assum `!k ii. k < SUC d /\ _ ==> _` (qspec_then `0` mp_tac) >>
     simp[NoAsms] >> metis_tac[]) >>
  `get_instruction bb' t.vs_inst_idx = SOME cur` by
    (qpat_x_assum `!k. k <= SUC d ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  qpat_x_assum `exec_block fuel C bb s = _` mp_tac >>
  simp[Once exec_block_def] >> simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs(), is_terminator_def] >> strip_tac >>
  `!vv. op1 = Var vv ==> vv IN V` by
    (rpt strip_tac >>
     qpat_x_assum `!k ii v. _` (qspec_then `0` mp_tac) >>
     simp[NoAsms] >> disch_then irule >>
     qexists_tac `cur` >> simp[]) >>
  `IS_SOME (eval_operand op1 s) <=> IS_SOME (eval_operand op1 t)` by
    (irule ld_available_operand >> metis_tac[]) >>
  Cases_on `eval_operand op1 t` >- gvs[] >>
  rename1 `eval_operand op1 t = SOME w` >>
  qpat_x_assum `v8 = []` SUBST_ALL_TAC >>
  pure_once_rewrite_tac[exec_block_def] >>
  pure_asm_rewrite_tac[] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[is_terminator_def] >>
  first_x_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  disch_then irule >>
  qpat_x_assum `update_var out v s = s''` (SUBST_ALL_TAC o SYM) >>
  simp[update_var_def, arithmeticTheory.ADD_CLAUSES] >>
  conj_tac
  >- (qexists_tac `V` >> conj_tac
      >- (rpt strip_tac >> Cases_on `out = v'` >>
          simp[FLOOKUP_UPDATE]) >>
      rpt strip_tac >>
      qpat_x_assum `!k ii v. k <= SUC d /\ _ ==> _`
        (qspec_then `SUC k` mp_tac) >>
      simp[NoAsms, arithmeticTheory.ADD_CLAUSES] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k ii. k < SUC d /\ _ ==> _`
        (qspec_then `SUC k` mp_tac) >>
      simp[NoAsms, arithmeticTheory.ADD_CLAUSES] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k. k <= SUC d ==> _`
        (qspec_then `SUC k` mp_tac) >>
      simp[NoAsms, arithmeticTheory.ADD_CLAUSES] >> metis_tac[]) >>
  qexists_tac `ri` >>
  gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM]
QED

(* A finite assignment suffix ending at REVERT cannot reach a GAS site,
   including when fetching or executing an assignment fails early. *)
Theorem ld_assign_suffix_events:
  !d s.
    get_instruction bb (s.vs_inst_idx + d) = SOME ri /\
    ri.inst_opcode = REVERT /\
    (!k ii. k < d /\ get_instruction bb (s.vs_inst_idx + k) = SOME ii ==>
            ii.inst_opcode = ASSIGN) ==>
    gas_events_block fuel C owner bb s = []
Proof
  Induct_on `d`
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >>
      Cases_on `step_inst fuel C ri s` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once gas_events_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `cur.inst_opcode = ASSIGN` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[Once gas_events_block_def, gas_events_step_def, is_terminator_def] >>
  Cases_on `step_inst fuel C cur s` >> simp[] >>
  first_x_assum irule >>
  gvs[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >>
  qpat_x_assum `!k ii. _` (qspec_then `SUC k` mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED
