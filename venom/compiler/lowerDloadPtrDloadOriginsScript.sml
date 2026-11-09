Theory lowerDloadPtrDloadOrigins
Ancestors lowerDloadPtrBackwardNext lowerDloadPtrJointBudget
  lowerDloadPtrSourceInv lowerDloadPtrRel lowerDloadPtrPhase
  lowerDloadDefs ptrDiscipline venomExecSemantics venomState
  finite_map list words pred_set

Theorem dload_source_step_call_context:
  i.inst_opcode = DLOAD /\ step_inst fuel C i s = OK s1 ==>
  s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), update_var_def,
      exec_read1_def]
QED

Theorem dload_supply_positive_prefix_alloca_domain:
  lower_dload_inst_supply supply i = (xs,next) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  0 < n /\ n <= 4 /\
  dload_prefix_match fuel C PH xs n t H un t4 H4 un4 ==>
  FDOM t4.vs_allocas = (EL 0 xs).inst_id INSERT FDOM t.vs_allocas
Proof
  strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `n = 1` >- suspend "one" >>
  Cases_on `n = 2` >- suspend "two" >>
  Cases_on `n = 3` >- suspend "three" >>
  `n = 4` by decide_tac >> suspend "four"
QED

Resume dload_supply_positive_prefix_alloca_domain[one]:
  gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `1 = SUC 0` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), exec_alloca_def] >>
  strip_tac >> gvs[update_var_def, AllCaseEqs(), FLOOKUP_DEF, EXTENSION] >>
  metis_tac[]
QED

Resume dload_supply_positive_prefix_alloca_domain[two]:
  gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `2 = SUC (SUC 0)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), exec_alloca_def] >>
  strip_tac >> gvs[update_var_def, AllCaseEqs(), FLOOKUP_DEF, EXTENSION] >>
  metis_tac[]
QED

Resume dload_supply_positive_prefix_alloca_domain[three]:
  gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `3 = SUC (SUC (SUC 0))` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := SUC (SUC _)) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[write_memory_with_expansion_def] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), exec_alloca_def] >>
  strip_tac >> gvs[update_var_def, AllCaseEqs(), FLOOKUP_DEF, EXTENSION] >>
  metis_tac[]
QED

Resume dload_supply_positive_prefix_alloca_domain[four]:
  gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `4 = SUC (SUC (SUC (SUC 0)))` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := SUC (SUC (SUC _))) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := SUC (SUC _)) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[write_memory_with_expansion_def] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(), exec_alloca_def] >>
  strip_tac >> gvs[update_var_def, AllCaseEqs(), FLOOKUP_DEF, EXTENSION] >>
  metis_tac[]
QED

Finalise dload_supply_positive_prefix_alloca_domain

Theorem dload_supply_prefix_alloca_domain:
  lower_dload_inst_supply supply i = (xs,next) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  dload_prefix_match fuel C PH xs 4 t H un t4 H4 un4 ==>
  FDOM t4.vs_allocas = (EL 0 xs).inst_id INSERT FDOM t.vs_allocas
Proof
  strip_tac >> irule dload_supply_positive_prefix_alloca_domain >>
  conj_tac >- metis_tac[] >>
  qpat_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`
    (irule_at (Pat `dload_prefix_match`)) >> simp[]
QED

Theorem dload_positive_prefix_scratch_budget:
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g j t /\
  vs.vs_allocas = FEMPTY /\ callee_first names C.ctx_functions /\
  LENGTH (r::rs) = LENGTH (f::MAP (\c. c.cf_fn) cs) /\
  LENGTH (f::MAP (\c. c.cf_fn) cs) = LENGTH (g::MAP (\d. d.cf_fn) ds) /\
  (!k. k < LENGTH (f::MAP (\c. c.cf_fn) cs) ==>
    ?q q'. lower_dload_function_supply q (EL k (f::MAP (\c. c.cf_fn) cs)) =
      (EL k (g::MAP (\d. d.cf_fn) ds),q')) /\
  (!k. k < LENGTH (r::rs) ==> (EL k (r::rs)).dr_scratch =
    FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {ci.inst_id | MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs)))}) /\
  lower_dload_inst_supply supply i = (xs,next) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  0 < n /\ n <= 4 /\
  dload_prefix_match fuel C' PH0 xs n t0 H0 un0 t H un /\
  (EL 0 xs).inst_id NOTIN {ci.inst_id | MEM ci (fn_insts f)} ==>
  SUM (MAP (\r. CARD r.dr_scratch)
    ((r with dr_scratch := (EL 0 xs).inst_id INSERT r.dr_scratch)::rs)) <=
      ctx_dload_count C
Proof
  strip_tac >>
  `FDOM t.vs_allocas = (EL 0 xs).inst_id INSERT FDOM t0.vs_allocas` by
    (irule dload_supply_positive_prefix_alloca_domain >>
     conj_tac >- metis_tac[] >>
     qpat_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`
       (irule_at (Pat `dload_prefix_match`)) >> simp[]) >>
  irule dload_joint_runtime_scratch_budget >>
  conj_tac >- metis_tac[] >>
  qpat_assum `frame_reachable vs C _ _ _ _ _ _ _`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' _ _ _ _ _ _ _`
    (irule_at (Pat `frame_reachable`)) >> simp[] >>
  reverse conj_tac >- gvs[] >>
  gen_tac >> strip_tac >> Cases_on `k` >> fs[]
  >- (qpat_x_assum `!k. k < SUC (LENGTH rs) ==> _`
        (qspec_then `0` mp_tac) >>
      `~(?ci. (HD xs).inst_id = ci.inst_id /\ MEM ci (fn_insts f))` by metis_tac[] >>
      simp[EXTENSION] >> metis_tac[]) >>
  qpat_x_assum `!k. k < SUC (LENGTH rs) ==> _`
    (qspec_then `SUC n'` mp_tac) >> simp[]
QED

Theorem dload_positive_prefix_fresh_reserve:
  frame_reachable vs C cs PG G tn f i s /\
  frame_reachable vs C' ds PH H un g j t /\
  vs.vs_allocas = FEMPTY /\ callee_first names C.ctx_functions /\
  LENGTH (r::rs) = LENGTH (f::MAP (\c. c.cf_fn) cs) /\
  LENGTH (f::MAP (\c. c.cf_fn) cs) = LENGTH (g::MAP (\d. d.cf_fn) ds) /\
  (!k. k < LENGTH (f::MAP (\c. c.cf_fn) cs) ==>
    ?q q'. lower_dload_function_supply q (EL k (f::MAP (\c. c.cf_fn) cs)) =
      (EL k (g::MAP (\d. d.cf_fn) ds),q')) /\
  (!k. k < LENGTH (r::rs) ==> (EL k (r::rs)).dr_scratch =
    FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
      {ci.inst_id | MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs)))}) /\
  lower_dload_inst_supply supply i = (xs,next) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] /\
  0 < n /\ n <= 4 /\
  dload_prefix_match fuel C' PH0 xs n t0 H0 un0 t H un /\
  (EL 0 xs).inst_id NOTIN {ci.inst_id | MEM ci (fn_insts f)} /\
  dload_table_stack (r::rs) (s::MAP (\c. c.cf_state) cs)
    (t0::MAP (\d. d.cf_state) ds) /\
  dload_headroom_ok C f i s ==>
  (FLOOKUP t0.vs_allocas (EL 0 xs).inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword(:256))
Proof
  rpt strip_tac >>
  `SUM (MAP (\r. CARD r.dr_scratch)
     ((r with dr_scratch := (EL 0 xs).inst_id INSERT r.dr_scratch)::rs)) <=
       ctx_dload_count C` by
    (irule dload_positive_prefix_scratch_budget >>
     conj_tac >- metis_tac[] >>
     qpat_assum `frame_reachable vs C _ _ _ _ _ _ _`
       (irule_at (Pat `frame_reachable`)) >>
     qpat_assum `frame_reachable vs C' _ _ _ _ _ _ _`
       (irule_at (Pat `frame_reachable`)) >>
     qpat_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _`
       (irule_at (Pat `dload_prefix_match`)) >> simp[] >> metis_tac[]) >>
  `r.dr_scratch = FDOM t0.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)}` by
    (qpat_x_assum `!k. k < LENGTH (r::rs) ==> _`
       (qspec_then `0` mp_tac) >> simp[]) >>
  `FINITE r.dr_scratch /\ (EL 0 xs).inst_id NOTIN r.dr_scratch` by
    fs[FLOOKUP_DEF] >>
  drule dload_table_stack_current >> strip_tac >>
  gvs[dload_headroom_ok_def, CARD_INSERT, FLOOKUP_DEF] >> decide_tac
QED
