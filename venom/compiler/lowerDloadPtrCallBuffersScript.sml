Theory lowerDloadPtrCallBuffers
Ancestors
  lowerDloadPtrResidualInterfaces lowerDloadPtrHash lowerDloadPtrRegion
  lowerDloadPtrPhi lowerDloadPtrRel lowerDloadPtrBlockEntry lowerDloadPtrCall
  lowerDloadPtrAggregate pointerConfinedDefs memLocDefs finite_map pred_set
  ptrDiscipline contextCodegenRel codegenRel venomExecSemantics venomState arithmetic list

Theorem dload_call_clean_slice:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL \/
   i.inst_opcode = DELEGATECALL \/ i.inst_opcode = CREATE \/
   i.inst_opcode = CREATE2) /\
  mem_read_ops i = SOME ops /\ ops.iao_ofst = a /\
  MEM (w2n x,w2n z) (source_memory_read_ranges i s) /\
  access_ok lo G f i s /\ ~in_revert_forward f s /\
  taint_ok f tn i s /\ ~about_to_revert f i s /\
  dload_live_layout lo sf tf fs /\ dload_memory_match lo fs tn un s t /\
  dload_value_word fs {} (op_prov G a) q x y ==>
  TAKE (w2n z) (DROP (w2n x) s.vs_memory ++ REPLICATE (w2n z) 0w) =
  TAKE (w2n z) (DROP (w2n y) t.vs_memory ++ REPLICATE (w2n z) 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `w2n z = 0` >- simp[] >>
  `(lo < w2n x + w2n z \/ op_prov G a <> NONE) ==>
    ?b n. op_prov G a = SOME (b,n) /\ b <= w2n x /\
      w2n x + w2n z <= b+n` by
    (rpt strip_tac >>
     `?v b n. a = Var v /\ FLOOKUP G v = SOME (b,n) /\
       b <= w2n x /\ w2n x + w2n z <= b+n` by
       (fs[access_ok_def] >>
        qpat_x_assum `!off len. MEM (off,len) (source_memory_read_ranges i s) /\ _ ==> _`
          (qspecl_then [`w2n x`, `w2n z`] mp_tac) >>
        simp[wordsTheory.w2n_eq_0] >> strip_tac >> gvs[] >> metis_tac[]) >>
     gvs[op_prov_def] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `((w2n x = w2n y /\ w2n x + w2n z <= lo) \/
     (?owner id b c n d. dload_live_site fs owner id b c n /\
       w2n x = b+d /\ w2n y = c+d /\ d+w2n z <= n))` assume_tac
  >- (drule_all dload_value_contained_region >> simp[]) >>
  `!k. k < w2n z ==> w2n x+k NOTIN tn.t_mem` by
    (fs[taint_ok_def] >> rpt strip_tac >>
     qpat_x_assum `!off len j. _` (qspecl_then [`w2n x`, `w2n z`, `w2n x+k`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  irule dload_memory_clean_slice >> metis_tac[]
QED


Theorem dload_call_operand_safety:
  ((i.inst_opcode = CALL /\
    i.inst_operands = [gas;addr;value;a;sz;r;rs] /\
    MEM op [addr;value;sz;rs]) \/
   (i.inst_opcode = STATICCALL /\
    i.inst_operands = [gas;addr;a;sz;r;rs] /\
    MEM op [addr;sz;rs])) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\ taint_ok f tn i s ==>
  op_prov G op = NONE /\
  (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {})
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v. op = Var v ==> v NOTIN pv` by
    (rpt strip_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_read_ops_def, mem_write_ops_def] >>
     qpat_x_assum `!v. _` (qspec_then `v` mp_tac) >>
     simp[] >>
     Cases_on `a = Var v` >> Cases_on `r = Var v` >> gvs[] >>
     rpt (IF_CASES_TAC >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]) >>
  gvs[taint_ok_def] >> gen_tac >> strip_tac >>
  qpat_x_assum `!op'. _ \/ op_taint tn op' = {}`
    (qspec_then `arg` mp_tac) >> gvs[]
QED

Theorem dload_call_success_inputs:
  (i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL) /\
  step_inst fuel C i t = OK t' ==>
  (!op. MEM op i.inst_operands ==> eval_operand op t <> NONE) /\
  (i.inst_opcode = CALL /\ t.vs_call_ctx.cc_static ==>
    eval_operand (EL 2 i.inst_operands) t = SOME 0w)
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dload_call_evaluated_inputs:
  ((i.inst_opcode = CALL /\
    i.inst_operands = [gas;addr;value;a;sz;r;rs]) \/
   (i.inst_opcode = STATICCALL /\
    i.inst_operands = [gas;addr;a;sz;r;rs])) /\
  ptr_use_ok P pv i /\ FDOM G SUBSET pv /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  ~in_revert_forward f s /\ ~about_to_revert f i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. MEM (Var v) (TL i.inst_operands) ==> v IN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel C i t = OK t' ==>
  (!op. MEM op i.inst_operands ==> eval_operand op s <> NONE) /\
  (!op. MEM op (if i.inst_opcode = CALL then [addr;value;sz;rs]
               else [addr;sz;rs]) ==>
    eval_operand op s = eval_operand op t) /\
  (!op x y. MEM op [a;r] /\ eval_operand op s = SOME x /\
    eval_operand op t = SOME y ==>
    dload_value_word fs {} (op_prov G op) (op_prov H op) x y) /\
  (!x y z. eval_operand a s = SOME x /\ eval_operand a t = SOME y /\
    eval_operand sz s = SOME z ==>
    MEM (w2n x,w2n z) (source_memory_read_ranges i s) /\
    read_memory (w2n x) (w2n z) s = read_memory (w2n y) (w2n z) t) /\
  (!x z. eval_operand r s = SOME x /\ eval_operand rs s = SOME z ==>
    MEM (w2n x,w2n z) (source_memory_write_ranges i s)) /\
  (i.inst_opcode = CALL /\ s.vs_call_ctx.cc_static ==>
    eval_operand value s = SOME 0w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `step_inst _ _ _ _ = OK _`) dload_call_success_inputs >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!op. MEM op i.inst_operands ==>
     (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> eval_operand op s <> NONE` by
    metis_tac[] >>
  `dload_vars_match fs V G H tn un s t` by metis_tac[dload_boundary_vars] >>
  `!op. MEM op (if i.inst_opcode = CALL then [addr;value;sz;rs]
                 else [addr;sz;rs]) ==>
     op_prov G op = NONE /\
     (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {})` by
    (gen_tac >> disch_tac >> irule dload_call_operand_safety >>
     gvs[] >> metis_tac[]) >>
  `!op. MEM op (if i.inst_opcode = CALL then [addr;value;sz;rs]
                 else [addr;sz;rs]) ==>
     eval_operand op s = eval_operand op t` by
    (rpt strip_tac >> drule scalar_operand_equal >>
     disch_then irule >> gvs[] >> metis_tac[]) >>
  `!op x y. MEM op [a;r] /\ eval_operand op s = SOME x /\
     eval_operand op t = SOME y ==>
     dload_value_word fs {} (op_prov G op) (op_prov H op) x y` by
    (rpt strip_tac >>
     `op_taint tn op = {}` by (gvs[] >> metis_tac[]) >>
     `!v. op = Var v ==> v IN V` by (gvs[] >> metis_tac[]) >>
     drule_all dload_matched_operand >> simp[]) >>
  simp[] >> rpt conj_tac
  >- suspend "call_read_inputs"
  >- suspend "call_write_inputs"
  >> suspend "call_static_guard"
QED

Resume dload_call_evaluated_inputs[call_read_inputs]:
  rpt strip_tac >>
  `MEM (w2n x,w2n z) (source_memory_read_ranges i s)` by
    (gvs[source_memory_read_ranges_def, memory_range_of_operands_def,
         AllCaseEqs()] >>
     (Cases_on `eval_operand gas s` >> gvs[] >>
      Cases_on `eval_operand addr t` >> gvs[] >>
      Cases_on `eval_operand r s` >> gvs[] >>
      Cases_on `eval_operand rs t` >> gvs[] >>
      Cases_on `eval_operand value t` >> gvs[] >> metis_tac[])) >>
  `dload_live_layout lo s.vs_alloca_next t.vs_alloca_next fs /\
   dload_memory_match lo fs tn un s t` by metis_tac[dload_boundary_core_def] >>
  `dload_value_word fs {} (op_prov G a) (op_prov H a) x y` by simp[] >>
  `?ops. mem_read_ops i = SOME ops /\ ops.iao_ofst = a` by
    (gvs[mem_read_ops_def] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `i.inst_opcode = CALL \/ i.inst_opcode = STATICCALL \/
     i.inst_opcode = DELEGATECALL \/ i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2`
    assume_tac >- metis_tac[] >>
  drule_all dload_call_clean_slice >> simp[read_memory_def]
QED

Resume dload_call_evaluated_inputs[call_write_inputs]:
  rpt strip_tac >>
  gvs[source_memory_write_ranges_def, AllCaseEqs()] >>
  Cases_on `eval_operand gas s` >> gvs[] >>
  Cases_on `eval_operand addr t` >> gvs[] >>
  Cases_on `eval_operand a s` >> gvs[] >>
  Cases_on `eval_operand sz t` >> gvs[] >>
  Cases_on `eval_operand value t` >> gvs[] >> metis_tac[]
QED

Resume dload_call_evaluated_inputs[call_static_guard]:
  rpt strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[dload_equal_environment_call_ctx, dload_boundary_core_def] >>
  gvs[]
QED

Finalise dload_call_evaluated_inputs
