Theory concretizePtrOwnedActualInitializer
Ancestors concretizePtrActualWrites concretizePtrEndpointOrigin
  concretizePtrOwnerPath concretizePtrChronologicalHistory ptrDiscipline
  list rich_list finite_map

Theorem ptr_endpoint_owned_actual_initializer:
  ptr_chrono_history vs C h endpoint /\ vs.vs_allocas = FEMPTY /\
  (!k. k < LENGTH h ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
  d <= LENGTH endpoint.po_stack /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= x /\ x < b + sz /\ x NOTIN endpoint.po_taint.t_mem ==>
  ?w. SUC w < LENGTH h /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
                                  (EL (SUC w) h).po_state) /\
    x NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!k. w < k /\ SUC k < LENGTH h ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                       (EL (SUC k) h).po_state)) /\
    (!k. w <= k /\ k < LENGTH h ==>
      d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz))
Proof
  strip_tac >> drule ptr_chrono_history_end >> strip_tac >>
  `PRE (LENGTH h) < LENGTH h /\ EL (PRE (LENGTH h)) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `?i fuel sa'. i < PRE (LENGTH h) /\ LENGTH (EL i h).po_stack = d /\
    (EL i h).po_inst.inst_opcode = ALLOCA /\ (EL i h).po_inst.inst_id = aid /\
    FLOOKUP (EL i h).po_state.vs_allocas aid = NONE /\
    step_inst fuel C (EL i h).po_inst (EL i h).po_state = OK sa' /\
    FLOOKUP sa'.vs_allocas aid = SOME (b,sz) /\
    (!k. i <= k /\ k <= PRE (LENGTH h) ==> d <= LENGTH (EL k h).po_stack) /\
    FLOOKUP (ptr_bottom_state d (EL (SUC i) h)).vs_allocas aid = SOME (b,sz)` by
    (irule ptr_chrono_endpoint_birth >>
     simp[GSYM ptr_owner_view_state] >> metis_tac[]) >>
  `i < LENGTH h /\ SUC i < LENGTH h` by decide_tac >>
  `h = TAKE i h ++ [EL i h] ++ DROP (SUC i) h` by
    metis_tac[TAKE_DROP_SUC, APPEND, APPEND_ASSOC] >>
  `DROP (SUC i) h <> []` by
    (Cases_on `DROP (SUC i) h` >> fs[LENGTH_DROP]) >>
  `x IN new_site_bytes (EL i h).po_state sa'` by
    (simp[new_site_bytes_def] >> disj1_tac >>
     qexistsl [`aid`,`b`,`sz`] >> fs[FLOOKUP_DEF]) >>
  drule_all ptr_chrono_fresh_last_actual_index >> simp[LENGTH_TAKE] >> strip_tac >>
  qpat_x_assum `h = _` kall_tac >>
  qexists `k` >> simp[] >> rpt strip_tac >>
  irule ptr_owner_view_lookup_interval >> simp[] >> conj_tac
  >- (qexists `SUC i` >> simp[ptr_owner_view_state]) >>
  metis_tac[]
QED
