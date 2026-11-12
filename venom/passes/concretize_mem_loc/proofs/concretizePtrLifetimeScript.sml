Theory concretizePtrLifetime
Ancestors concretizePtrChronologicalHistory concretizePtrAllocationOwnership
  concretizePtrAllocationOrigins concretizePtrActivationSupport
  ptrDisciplineEmptyTaint venomExecSemantics
  venomState venomInst venomMemProps list rich_list finite_map

Definition ptr_obs_states_def:
  ptr_obs_states obs = obs.po_state :: MAP (\f. f.cf_state) obs.po_stack
End

Definition ptr_bottom_state_def:
  ptr_bottom_state d obs = EL (LENGTH obs.po_stack - d) (ptr_obs_states obs)
End

Theorem ptr_chrono_bottom_lookup_step:
  ptr_chrono_step ctx a b /\ a.po_inst.inst_opcode <> DALLOCA /\
  d <= LENGTH a.po_stack /\ d <= LENGTH b.po_stack /\
  FLOOKUP (ptr_bottom_state d a).vs_allocas aid = SOME site ==>
  FLOOKUP (ptr_bottom_state d b).vs_allocas aid = SOME site
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_bottom_state_def, ptr_obs_states_def, ptr_observe_def]
  >- (Cases_on `LENGTH stk - d` >> gvs[] >>
      metis_tac[ptr_step_allocas_extend])
  >- (drule ptr_alloc_enters_fields >> strip_tac >>
      `inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      Cases_on `LENGTH stk - d` >> gvs[] >>
      metis_tac[ptr_step_allocas_extend])
  >- (`SUC (LENGTH stk) - d = SUC (LENGTH stk - d)` by decide_tac >> simp[]) >>
  `SUC (LENGTH stk) - d = SUC (LENGTH stk - d)` by decide_tac >>
  gvs[] >> drule ptr_alloc_return_fields >> strip_tac >>
  Cases_on `LENGTH stk - d` >> gvs[]
QED

Theorem ptr_chrono_history_adjacent:
  !vs0 ctx h endpoint. ptr_chrono_history vs0 ctx h endpoint ==>
    !k. SUC k < LENGTH h ==> ptr_chrono_step ctx (EL k h) (EL (SUC k) h)
Proof
  ho_match_mp_tac ptr_chrono_history_strongind >> conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  Cases_on `SUC k < LENGTH h`
  >- (simp[EL_APPEND_EQN] >> metis_tac[]) >>
  `SUC k = LENGTH h` by gvs[] >>
  simp[EL_APPEND_EQN] >>
  `k = PRE (LENGTH h)` by decide_tac >> gvs[LAST_EL]
QED

Theorem ptr_chrono_bottom_lookup_interval:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (!k. i <= k /\ k < j ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
  FLOOKUP (ptr_bottom_state d (EL i h)).vs_allocas aid = SOME site ==>
  FLOOKUP (ptr_bottom_state d (EL j h)).vs_allocas aid = SOME site
Proof
  qid_spec_tac `j` >> Induct >> rpt strip_tac
  >- gvs[] >>
  Cases_on `i = SUC j` >- gvs[] >>
  `i <= j` by decide_tac >>
  `FLOOKUP (ptr_bottom_state d (EL j h)).vs_allocas aid = SOME site` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  irule ptr_chrono_bottom_lookup_step >>
  conj_tac >- (first_x_assum irule >> decide_tac) >>
  qexistsl [`EL j h`,`ctx`] >> simp[] >>
  metis_tac[ptr_chrono_history_adjacent]
QED

Theorem ptr_chrono_bottom_owner_identity:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (!k. i <= k /\ k < j ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
  FLOOKUP (ptr_bottom_state d (EL i h)).vs_allocas aid = SOME (b,sz) /\
  b <= x /\ x < b + sz /\
  ptr_active_alloc_geometry (ptr_obs_states (EL j h)) /\
  n < LENGTH (ptr_obs_states (EL j h)) /\
  FLOOKUP (EL n (ptr_obs_states (EL j h))).vs_allocas aid' = SOME (b',sz') /\
  b' <= x /\ x < b' + sz' ==>
  n = LENGTH (EL j h).po_stack - d /\ aid' = aid /\ (b',sz') = (b,sz)
Proof
  strip_tac >>
  `FLOOKUP (ptr_bottom_state d (EL j h)).vs_allocas aid = SOME (b,sz)` by
    metis_tac[ptr_chrono_bottom_lookup_interval] >>
  `LENGTH (EL j h).po_stack - d < LENGTH (ptr_obs_states (EL j h))` by
    simp[ptr_obs_states_def] >>
  `n = LENGTH (EL j h).po_stack - d /\ aid' = aid` by
    (irule ptr_active_alloc_unique_owner >>
     qexistsl [`b'`,`b`,`ptr_obs_states (EL j h)`,`sz'`,`sz`,`x`] >>
     simp[GSYM ptr_bottom_state_def]) >>
  gvs[ptr_bottom_state_def]
QED

(* This boundary is conditional on continuous presence at every intermediate
   observation. An allocation's fresh lookup starts at its successor observation.
   Transport to a writer in that interval first, then use simultaneous geometry
   to identify its local-or-saved owner. Endpoint depths alone do not discharge
   this guard. Backward protected production demand, retirement/reallocation and
   non-revert history coverage remain separate obligations. *)
