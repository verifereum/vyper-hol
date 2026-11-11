Theory concretizePtrEndpointOrigin
Ancestors concretizePtrLifetime concretizePtrChronologicalHistory
  concretizePtrAllocationOwnership concretizeAnalysisBoundary
  concretizePtrAllocationOrigins concretizePtrActivationSupport
  ptrDisciplineEmptyTaint venomExecSemantics venomState venomInst
  venomMemProps list rich_list finite_map

Theorem ptr_step_lookup_origin[local]:
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' /\
  FLOOKUP s'.vs_allocas aid = SOME site ==>
  FLOOKUP s.vs_allocas aid = SOME site \/
  (inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
   FLOOKUP s.vs_allocas aid = NONE)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  metis_tac[step_inst_non_alloca_preserves_allocas]
QED

Theorem ptr_chrono_lookup_origin_step:
  ptr_chrono_step ctx a b /\ a.po_inst.inst_opcode <> DALLOCA /\
  d <= LENGTH b.po_stack /\
  FLOOKUP (ptr_bottom_state d b).vs_allocas aid = SOME site ==>
  d <= LENGTH a.po_stack /\
  (FLOOKUP (ptr_bottom_state d a).vs_allocas aid = SOME site \/
   (LENGTH a.po_stack = d /\ a.po_inst.inst_opcode = ALLOCA /\
    a.po_inst.inst_id = aid /\ FLOOKUP a.po_state.vs_allocas aid = NONE /\
    ?fuel sa'. step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
      FLOOKUP sa'.vs_allocas aid = SOME site))
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> strip_tac >>
  gvs[ptr_bottom_state_def, ptr_obs_states_def, ptr_observe_def]
  >- (Cases_on `LENGTH stk - d` >> gvs[] >>
      metis_tac[ptr_step_lookup_origin])
  >- (drule ptr_alloc_enters_fields >> strip_tac >>
      `inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      Cases_on `LENGTH stk - d` >> gvs[] >>
      metis_tac[ptr_step_lookup_origin])
  >- (Cases_on `d = SUC (LENGTH stk)`
      >- (gvs[] >> drule setup_callee_empty_allocas >> strip_tac >>
          drule enters_block_allocas >> strip_tac >> gvs[]) >>
      `d <= LENGTH stk` by decide_tac >>
      `SUC (LENGTH stk) - d = SUC (LENGTH stk - d)` by decide_tac >>
      fs[]) >>
  drule ptr_alloc_return_fields >> strip_tac >>
  `SUC (LENGTH stk) - d = SUC (LENGTH stk - d)` by decide_tac >>
  Cases_on `LENGTH stk - d` >> fs[] >>
  `SUC (LENGTH stk) - d = SUC (SUC n)` by decide_tac >> simp[]
QED

Theorem ptr_chrono_endpoint_birth:
  !vs0 ctx h endpoint. ptr_chrono_history vs0 ctx h endpoint ==>
  !j d aid site.
    vs0.vs_allocas = FEMPTY /\
    (!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
    j < LENGTH h /\ d <= LENGTH (EL j h).po_stack /\
    FLOOKUP (ptr_bottom_state d (EL j h)).vs_allocas aid = SOME site ==>
    ?i fuel sa'. i < j /\ LENGTH (EL i h).po_stack = d /\
      (EL i h).po_inst.inst_opcode = ALLOCA /\
      (EL i h).po_inst.inst_id = aid /\
      FLOOKUP (EL i h).po_state.vs_allocas aid = NONE /\
      step_inst fuel ctx (EL i h).po_inst (EL i h).po_state = OK sa' /\
      FLOOKUP sa'.vs_allocas aid = SOME site /\
      (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
      FLOOKUP (ptr_bottom_state d (EL (SUC i) h)).vs_allocas aid = SOME site
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      gvs[ptr_bottom_state_def, ptr_obs_states_def, ptr_observe_def] >>
      drule enters_block_allocas >> strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA` by
    (rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  Cases_on `j < LENGTH h`
  >- (qpat_x_assum `!j d aid site. _` (qspecl_then [`j`,`d`,`aid`,`site`] mp_tac) >>
      fs[EL_APPEND_EQN] >> strip_tac >> qexistsl [`i`,`fuel`,`sa'`] >>
      `i < LENGTH h /\ SUC i < LENGTH h` by decide_tac >>
      simp[EL_APPEND_EQN] >> rpt strip_tac >>
      `k < LENGTH h` by decide_tac >> simp[EL_APPEND_EQN] >>
      first_x_assum irule >> decide_tac) >>
  `j = LENGTH h` by gvs[] >> gvs[EL_APPEND_EQN] >>
  drule ptr_chrono_history_end >> strip_tac >>
  `PRE (LENGTH h) < LENGTH h /\ EL (PRE (LENGTH h)) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `endpoint.po_inst.inst_opcode <> DALLOCA` by metis_tac[] >>
  drule_all ptr_chrono_lookup_origin_step >> strip_tac
  >- (qpat_x_assum `!j d aid site. _`
        (qspecl_then [`PRE (LENGTH h)`,`d`,`aid`,`site`] mp_tac) >>
      simp[] >> strip_tac >> qexistsl [`i`,`fuel`,`sa'`] >>
      `i < LENGTH h /\ SUC i < LENGTH h` by decide_tac >>
      simp[] >> rpt strip_tac >> Cases_on `k < LENGTH h`
      >- (simp[] >> first_x_assum irule >> decide_tac) >>
      `k = LENGTH h` by decide_tac >> simp[]) >>
  qexistsl [`PRE (LENGTH h)`,`fuel`,`sa'`] >>
  `SUC (PRE (LENGTH h)) = LENGTH h` by decide_tac >>
  simp[] >> rpt strip_tac >> Cases_on `k < LENGTH h`
  >- (`k = PRE (LENGTH h)` by decide_tac >> gvs[]) >>
  `k = LENGTH h` by decide_tac >> simp[]
QED

Theorem ptr_chrono_last_write_index:
  !j. (?k. i <= k /\ k < j /\ ptr_chrono_write ctx x (EL k h)) ==>
  ?w. i <= w /\ w < j /\ ptr_chrono_write ctx x (EL w h) /\
      (!k. w < k /\ k < j ==> ~ptr_chrono_write ctx x (EL k h))
Proof
  Induct >> simp[] >> strip_tac >>
  Cases_on `i <= j /\ ptr_chrono_write ctx x (EL j h)`
  >- (qexists `j` >> simp[] >> rpt strip_tac >> decide_tac) >>
  `k < j` by (Cases_on `k = j` >> gvs[]) >>
  `?w. i <= w /\ w < j /\ ptr_chrono_write ctx x (EL w h) /\
        (!k. w < k /\ k < j ==> ~ptr_chrono_write ctx x (EL k h))` by
    metis_tac[] >>
  qexists `w` >> simp[] >> rpt strip_tac >> Cases_on `k' = j`
  >- gvs[] >>
  `k' < j` by decide_tac >> metis_tac[]
QED

Theorem ptr_chrono_fresh_last_write_index:
  ptr_chrono_history vs0 ctx h endpoint /\
  h = pre ++ [a] ++ tail /\ tail <> [] /\
  a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' /\ x NOTIN endpoint.po_taint.t_mem ==>
  ?w. LENGTH pre < w /\ w + 1 < LENGTH h /\
      ptr_chrono_write ctx x (EL w h) /\
      ptr_observation_reachable vs0 ctx (EL w h) /\
      (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write ctx x (EL k h))
Proof
  strip_tac >> drule_all ptr_chrono_fresh_write_index >> strip_tac >>
  `k < PRE (LENGTH h)` by decide_tac >>
  `?w. SUC (LENGTH pre) <= w /\ w < PRE (LENGTH h) /\
        ptr_chrono_write ctx x (EL w h) /\
        (!k. w < k /\ k < PRE (LENGTH h) ==> ~ptr_chrono_write ctx x (EL k h))` by
    (irule ptr_chrono_last_write_index >> qexists `k` >> simp[]) >>
  qpat_x_assum `h = pre ++ [a] ++ tail` kall_tac >>
  `w + 1 < LENGTH h /\ w < LENGTH h` by decide_tac >>
  `ptr_observation_reachable vs0 ctx (EL w h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
     metis_tac[]) >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED
