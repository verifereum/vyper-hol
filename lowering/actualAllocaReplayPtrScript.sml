(* Same physical run for actual-site allocation and pointer ghosts, including replay. *)
Theory actualAllocaReplayPtr
Ancestors
  actualAllocExec actualDecoderAllocationPtr emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs fragExec venomExecSemantics venomState venomInst vyperCompiler ptrDiscipline
  allocaFrontierBound allocaBudgetProps finite_map words arithmetic list pred_set

Theorem fresh_vars_wrt_update_not_fresh:
  fresh_vars_wrt limit s /\ not_fresh_at limit out ==>
  fresh_vars_wrt limit (update_var out w s)
Proof
  rw[fresh_vars_wrt_def, not_fresh_at_def, update_var_def] >> metis_tac[]
QED

Theorem actual_word_alloca_credit_run:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas sa.cs_next_id = SOME entry ==>
    ?p. entry = (p,32) /\ p + 32 <= s.vs_alloca_next) /\
  fresh_vars_wrt limit s /\
  not_fresh_at limit (STRING #"%" (toString sa.cs_next_var)) ==>
  ?t p. run_inst_seq (emitted_insts sa sb) s = OK t /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,32) /\
    p + 32 < dimword (:256) /\
    (case FLOOKUP s.vs_allocas sa.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (slot,sz) => p = slot) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt limit t /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> sa.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
        s.vs_alloca_next + 32 < dimword (:256)) \/
     (?base. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (base,32) /\
       base + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)))
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ins (fn_insts fn)` >>
  `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w] /\
    ins.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
    ins.inst_id = sa.cs_next_id /\ alloca_size ins = 32` by
    simp[Abbr `ins`, mk_inst_def, alloca_size_def,
      dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  `!entry. FLOOKUP s.vs_allocas ins.inst_id = SOME entry ==>
    ?p. entry = (p,32) /\ p + 32 <= s.vs_alloca_next` by simp[] >>
  drule_all actual_word_alloca_physical_credit >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (drule_all actual_word_alloca_fresh_run >> strip_tac >>
      drule_all actual_alloca_slots_preserved >> strip_tac >>
      drule_all actual_alloca_frontier_preserved >>
      disch_then (qspec_then `site` assume_tac) >>
      drule_all actual_literal_alloca_frame >> strip_tac >>
      `fresh_vars_wrt limit t` by
        (fs[update_var_def, fresh_vars_wrt_def, not_fresh_at_def] >> metis_tac[]) >>
      qexistsl_tac [`t`, `s.vs_alloca_next`] >>
      simp[run_inst_seq_def, Abbr `ins`, FLOOKUP_UPDATE]) >>
  gvs[] >>
  `FLOOKUP s.vs_allocas ins.inst_id = SOME (p,32)` by simp[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  drule_all actual_alloca_slots_preserved >> strip_tac >>
  drule_all actual_alloca_frontier_preserved >>
  disch_then (qspec_then `site` assume_tac) >>
  drule_all actual_literal_alloca_frame >> strip_tac >>
  `fresh_vars_wrt limit t` by
    (gvs[] >> irule fresh_vars_wrt_update_not_fresh >> simp[]) >>
  qexists `t` >>
  simp[run_inst_seq_def, Abbr `ins`, FLOOKUP_UPDATE] >> decide_tac
QED

Theorem actual_word_alloca_replay_ptr:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  alloca_inv s /\ alloca_frontier_inv budget_ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget budget_ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas sa.cs_next_id = SOME entry ==>
    ?p. entry = (p,32) /\ p + 32 <= s.vs_alloca_next) /\
  fresh_vars_wrt limit s /\
  not_fresh_at limit (STRING #"%" (toString sa.cs_next_var)) ==>
  ?t H u q p.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    ip = Var q /\ lookup_var q t = SOME (n2w p) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,32) /\
    p + 32 < dimword (:256) /\
    (case FLOOKUP s.vs_allocas sa.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (slot,sz) => p = slot) /\
    alloca_inv t /\ alloca_frontier_inv budget_ctx fn site t /\
    s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt limit t /\
    fresh_vars_wrt limit (t with vs_inst_idx := SUC s.vs_inst_idx) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
      FLOOKUP t.vs_allocas id = SOME entry) /\
    (!id. id <> sa.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem DIFF {a | p <= a /\ a < p + 32} =
      tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  strip_tac >> drule_all actual_word_alloca_credit_run >> strip_tac >>
  drule_at (Pos (el 2)) actual_alloca_endpoint_exact_ptr_core >>
  simp[] >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  gvs[AllCaseEqs()] >>
  qexistsl_tac [`H`,`u`] >>
  fs[fresh_vars_wrt_def]
QED

(* A replay consumes no further site credit, even when its output is already bound. *)
Theorem emitted_alloca_occupied_frame:
  emit_op ALLOCA [Lit (n2w n)] sa = (ip,sb) /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,n) /\
  n < dimword (:256) /\ run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = update_var (STRING #"%" (toString sa.cs_next_var)) (n2w p) s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  remaining_alloca_budget insts t = remaining_alloca_budget insts s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  strip_tac >> gvs[update_var_def, remaining_alloca_budget_def]
QED

Theorem actual_word_alloca_twice_ptr:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  alloca_inv s /\ alloca_frontier_inv budget_ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget budget_ctx < dimword (:256) /\
  (!entry. FLOOKUP s.vs_allocas sa.cs_next_id = SOME entry ==>
    ?p. entry = (p,32) /\ p + 32 <= s.vs_alloca_next) /\
  fresh_vars_wrt limit s /\
  not_fresh_at limit (STRING #"%" (toString sa.cs_next_var)) ==>
  ?t v H u J z q p.
    ip = Var q /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    lookup_var q t = SOME (n2w p) /\
    run_inst_seq (emitted_insts sa sb)
      (t with vs_inst_idx := LENGTH sa.cs_current_insts) = OK v /\
    lookup_var q v = SOME (n2w p) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,32) /\
    v.vs_allocas = t.vs_allocas /\ v.vs_alloca_next = t.vs_alloca_next /\
    remaining_alloca_budget insts v = remaining_alloca_budget insts t /\
    alloca_inv v /\ alloca_frontier_inv budget_ctx fn site v /\
    fresh_vars_wrt limit v /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    ptr_covers J z q (v with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g a w. g = G /\ a = tn /\ w = s)
      (\g a w. g = H /\ a = u /\ w = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    frag_exec_ptr cx ctx PG sa sb
      (\g a w. g = H /\ a = u /\ w = (t with vs_inst_idx := LENGTH sa.cs_current_insts))
      (\g a w. g = J /\ a = z /\ w = (v with vs_inst_idx := SUC (LENGTH sa.cs_current_insts))) R /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower t /\ ~ctx_has_dalloca ctx' /\
      t.vs_current_bb = sa.cs_current_bb /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG J z
        (v with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sa.cs_current_insts))
Proof
  strip_tac >>
  drule_all actual_word_alloca_replay_ptr >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  `!entry. FLOOKUP (t with vs_inst_idx := LENGTH sa.cs_current_insts).vs_allocas
      sa.cs_next_id = SOME entry ==>
    ?base. entry = (base,32) /\
      base + 32 <= (t with vs_inst_idx := LENGTH sa.cs_current_insts).vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `fresh_vars_wrt limit (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    fs[fresh_vars_wrt_def] >>
  `alloca_inv (t with vs_inst_idx := LENGTH sa.cs_current_insts) /\
    alloca_frontier_inv budget_ctx fn site
      (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by simp[] >>
  drule_at (Pos (el 4)) actual_word_alloca_replay_ptr >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`u`,`cx`,`ctx`,`R`,`PG`,`H`] strip_assume_tac) >>
  drule_at (Pos (el 4)) emitted_alloca_occupied_frame >>
  simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >> strip_tac >>
  qpat_x_assum `!insts. _` (qspec_then `insts` strip_assume_tac) >>
  gvs[] >> qexistsl_tac [`H`,`u`,`H'`,`u'`] >>
  simp[remaining_alloca_budget_def, allocas_from_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[allocas_from_def] >> gvs[]
QED
