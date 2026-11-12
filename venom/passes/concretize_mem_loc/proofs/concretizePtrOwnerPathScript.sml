Theory concretizePtrOwnerPath
Ancestors
  concretizePtrLifetime concretizePtrChronologicalHistory
  concretizePtrCallAncestry concretizePtrHistoryUsed
  ptrDiscipline venomExecSemantics venomState venomInst
  frameCfgBoundary frameHistoryCfg venomInstProps
  list rich_list finite_map

Definition ptr_owner_view_def:
  ptr_owner_view d obs =
    if d = LENGTH obs.po_stack then
      <| cf_fn := obs.po_fn; cf_inst := obs.po_inst; cf_state := obs.po_state;
         cf_params := obs.po_params; cf_prov := obs.po_prov;
         cf_tvar := obs.po_taint.t_var |>
    else EL (LENGTH obs.po_stack - d - 1) obs.po_stack
End

Theorem ptr_owner_view_current[simp]:
  ptr_owner_view (LENGTH obs.po_stack) obs =
    <| cf_fn := obs.po_fn; cf_inst := obs.po_inst; cf_state := obs.po_state;
       cf_params := obs.po_params; cf_prov := obs.po_prov;
       cf_tvar := obs.po_taint.t_var |>
Proof
  simp[ptr_owner_view_def]
QED

Theorem ptr_owner_view_state:
  d <= LENGTH obs.po_stack ==>
  (ptr_owner_view d obs).cf_state = ptr_bottom_state d obs
Proof
  strip_tac >> simp[ptr_owner_view_def, ptr_bottom_state_def, ptr_obs_states_def] >>
  Cases_on `d = LENGTH obs.po_stack` >> simp[] >>
  Cases_on `LENGTH obs.po_stack - d` >- gvs[] >>
  `LENGTH obs.po_stack - (d + 1) = n` by decide_tac >>
  simp[EL_MAP]
QED

Theorem ptr_owner_view_step_function:
  ptr_chrono_step ctx a b /\
  d <= LENGTH a.po_stack /\ d <= LENGTH b.po_stack ==>
  (ptr_owner_view d a).cf_fn = (ptr_owner_view d b).cf_fn
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_owner_view_def, ptr_observe_def] >>
  Cases_on `d = LENGTH stk` >> gvs[arithmeticTheory.ADD1] >>
  `LENGTH stk - d = SUC (LENGTH stk - (d + 1))`
    by decide_tac >> asm_rewrite_tac[listTheory.EL, listTheory.TL]
QED

(* The return boundary retains the caller's suspended state, not the state
   of a different activation with the same function name. *)
Definition ptr_owner_transition_def:
  ptr_owner_transition ctx f g <=>
    f.cf_fn = g.cf_fn /\
    (f = g \/
     (active_inst g.cf_fn g.cf_inst g.cf_state /\
      ((?fuel s'. active_inst f.cf_fn f.cf_inst f.cf_state /\
          ~is_terminator f.cf_inst.inst_opcode /\
          f.cf_inst.inst_opcode <> INVOKE /\
          step_inst fuel ctx f.cf_inst f.cf_state = OK s' /\
          g.cf_state = s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) \/
       (?fuel s'. active_inst f.cf_fn f.cf_inst f.cf_state /\
          is_terminator f.cf_inst.inst_opcode /\
          step_inst fuel ctx f.cf_inst f.cf_state = OK s' /\
          ~s'.vs_halted /\ enters_block f.cf_fn s' g.cf_state) \/
       (?ret s_end s'.
          bind_outputs f.cf_inst.inst_outputs ret.iret_values
            (adopt_return_fmp ret (merge_callee_state f.cf_state s_end)) = SOME s' /\
          g.cf_state = s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx))))
End

Theorem ptr_owner_view_step:
  ptr_chrono_step ctx a b /\
  d <= LENGTH a.po_stack /\ d <= LENGTH b.po_stack ==>
  ptr_owner_transition ctx (ptr_owner_view d a) (ptr_owner_view d b)
Proof
  strip_tac >> qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_owner_view_def, ptr_observe_def] >>
  Cases_on `d = LENGTH stk` >> gvs[arithmeticTheory.ADD1]
  >- (simp[ptr_owner_transition_def, arithmeticTheory.ADD1] >> metis_tac[])
  >- simp[ptr_owner_transition_def]
  >- (simp[ptr_owner_transition_def, arithmeticTheory.ADD1] >> metis_tac[])
  >- simp[ptr_owner_transition_def]
  >- simp[ptr_owner_transition_def]
  >- (`LENGTH stk - d = SUC (LENGTH stk - (d + 1))` by decide_tac >>
      asm_rewrite_tac[listTheory.EL, listTheory.TL] >>
      simp[ptr_owner_transition_def])
  >- (simp[ptr_owner_transition_def, arithmeticTheory.ADD1] >> metis_tac[])
  >> `LENGTH stk - d = SUC (LENGTH stk - (d + 1))` by decide_tac >>
     asm_rewrite_tac[listTheory.EL, listTheory.TL] >>
     simp[ptr_owner_transition_def]
QED

Theorem ptr_owner_view_interval_function:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) ==>
  (ptr_owner_view d (EL i h)).cf_fn = (ptr_owner_view d (EL j h)).cf_fn
Proof
  qid_spec_tac `j` >> Induct >> rpt strip_tac
  >- gvs[] >>
  Cases_on `i = SUC j` >- gvs[] >>
  `i <= j` by decide_tac >>
  `(ptr_owner_view d (EL i h)).cf_fn =
   (ptr_owner_view d (EL j h)).cf_fn` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `(ptr_owner_view d (EL j h)).cf_fn =
   (ptr_owner_view d (EL (SUC j) h)).cf_fn` suffices_by metis_tac[] >>
  irule ptr_owner_view_step_function >>
  rpt conj_tac
  >- (first_x_assum irule >> decide_tac)
  >- (first_x_assum irule >> decide_tac) >>
  qexists `ctx` >> metis_tac[ptr_chrono_history_adjacent]
QED

Definition ptr_owner_trace_def:
  ptr_owner_trace d h i j =
    GENLIST (\n. ptr_owner_view d (EL (i + n) h)) (SUC j - i)
End

Theorem ptr_owner_trace_projection:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  LENGTH (EL i h).po_stack = d /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) ==>
  LENGTH (ptr_owner_trace d h i j) = SUC j - i /\
  (!n. n < SUC j - i ==>
    EL n (ptr_owner_trace d h i j) = ptr_owner_view d (EL (i + n) h) /\
    (EL n (ptr_owner_trace d h i j)).cf_fn = (EL i h).po_fn) /\
  (!n. SUC n < SUC j - i ==>
    ptr_owner_transition ctx (EL n (ptr_owner_trace d h i j))
      (EL (SUC n) (ptr_owner_trace d h i j)))
Proof
  strip_tac >> simp[ptr_owner_trace_def, EL_GENLIST] >> conj_tac
  >- (rpt strip_tac >>
      `(ptr_owner_view d (EL i h)).cf_fn =
       (ptr_owner_view d (EL (i + n) h)).cf_fn` by
        (irule ptr_owner_view_interval_function >>
         rpt conj_tac
         >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
         >- decide_tac
         >- decide_tac >>
         metis_tac[]) >>
      gvs[ptr_owner_view_def]) >>
  rpt strip_tac >>
  `SUC (i + n) < LENGTH h` by decide_tac >>
  `i + SUC n = SUC (i + n)` by decide_tac >>
  `d <= LENGTH (EL (i + n) h).po_stack /\
   d <= LENGTH (EL (SUC (i + n)) h).po_stack` by
    (conj_tac >> first_x_assum irule >> decide_tac) >>
  metis_tac[ptr_owner_view_step, ptr_chrono_history_adjacent]
QED

Theorem ptr_owner_view_lookup_interval:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (!k. i <= k /\ k < j ==> (EL k h).po_inst.inst_opcode <> DALLOCA) /\
  FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME site ==>
  FLOOKUP (ptr_owner_view d (EL j h)).cf_state.vs_allocas aid = SOME site
Proof
  strip_tac >>
  `d <= LENGTH (EL i h).po_stack /\ d <= LENGTH (EL j h).po_stack` by
    metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  gvs[ptr_owner_view_state] >>
  metis_tac[ptr_chrono_bottom_lookup_interval]
QED

Theorem ptr_owner_frame_active:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  active_inst fn inst s /\
  EVERY (\f. active_inst f.cf_fn f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> simp[] >> rpt strip_tac >> simp[]
QED

Theorem ptr_owner_view_active:
  ptr_observation_reachable vs0 ctx obs /\ d <= LENGTH obs.po_stack ==>
  active_inst (ptr_owner_view d obs).cf_fn (ptr_owner_view d obs).cf_inst
    (ptr_owner_view d obs).cf_state /\
  (d < LENGTH obs.po_stack ==> (ptr_owner_view d obs).cf_inst.inst_opcode = INVOKE)
Proof
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule ptr_owner_frame_active >> strip_tac >>
  Cases_on `d = LENGTH obs.po_stack` >> simp[ptr_owner_view_def] >>
  `LENGTH obs.po_stack - (d + 1) < LENGTH obs.po_stack` by decide_tac >>
  gvs[EVERY_EL] >> metis_tac[]
QED

Theorem ptr_owner_transition_route:
  wf_function f.cf_fn /\ active_inst f.cf_fn f.cf_inst f.cf_state /\
  ptr_owner_transition ctx f g ==>
  ptr_history_route f.cf_fn f.cf_inst f.cf_state g.cf_inst g.cf_state
Proof
  simp[ptr_owner_transition_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[ptr_history_route_rules]
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      irule (cj 2 ptr_history_route_rules) >>
      conj_tac >- simp[] >>
      qexistsl [`f.cf_inst`,`f.cf_state`] >> simp[] >>
      metis_tac[ptr_history_route_rules])
  >- (drule_all active_terminator_cfg_transition >> strip_tac >>
      irule (cj 3 ptr_history_route_rules) >>
      conj_tac >- simp[] >>
      qexistsl [`f.cf_inst`,`f.cf_state`] >> simp[] >>
      metis_tac[ptr_history_route_rules]) >>
  drule return_binding_current_bb >> strip_tac >>
  irule (cj 2 ptr_history_route_rules) >>
  conj_tac >- simp[] >>
  qexistsl [`f.cf_inst`,`f.cf_state`] >> simp[] >>
  metis_tac[ptr_history_route_rules]
QED

Theorem ptr_owner_route_trans[local]:
  !fn j t k u. ptr_history_route fn j t k u ==>
    !i s. ptr_history_route fn i s j t ==> ptr_history_route fn i s k u
Proof
  ho_match_mp_tac ptr_history_route_ind >> rpt strip_tac >>
  metis_tac[ptr_history_route_rules]
QED

Theorem ptr_owner_interval_route:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  wf_function (ptr_owner_view d (EL i h)).cf_fn /\
  active_inst (ptr_owner_view d (EL i h)).cf_fn
    (ptr_owner_view d (EL i h)).cf_inst (ptr_owner_view d (EL i h)).cf_state ==>
  ptr_history_route (ptr_owner_view d (EL i h)).cf_fn
    (ptr_owner_view d (EL i h)).cf_inst (ptr_owner_view d (EL i h)).cf_state
    (ptr_owner_view d (EL j h)).cf_inst (ptr_owner_view d (EL j h)).cf_state
Proof
  qid_spec_tac `j` >> Induct >> rpt strip_tac
  >- (gvs[] >> metis_tac[ptr_history_route_rules]) >>
  Cases_on `i = SUC j` >- (gvs[] >> metis_tac[ptr_history_route_rules]) >>
  `i <= j` by decide_tac >>
  `ptr_history_route (ptr_owner_view d (EL i h)).cf_fn
    (ptr_owner_view d (EL i h)).cf_inst (ptr_owner_view d (EL i h)).cf_state
    (ptr_owner_view d (EL j h)).cf_inst (ptr_owner_view d (EL j h)).cf_state` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `(ptr_owner_view d (EL i h)).cf_fn =
   (ptr_owner_view d (EL j h)).cf_fn` by
    (irule ptr_owner_view_interval_function >> rpt conj_tac
     >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
     >- decide_tac >- simp[] >> metis_tac[]) >>
  `active_inst (ptr_owner_view d (EL j h)).cf_fn
    (ptr_owner_view d (EL j h)).cf_inst (ptr_owner_view d (EL j h)).cf_state` by
    (irule (cj 1 ptr_owner_view_active) >>
     conj_tac >- (first_x_assum irule >> decide_tac) >>
     qexistsl [`ctx`,`vs0`] >>
     drule ptr_chrono_history_reachable >> simp[EVERY_EL] >>
     strip_tac >> first_x_assum irule >> decide_tac) >>
  `ptr_owner_transition ctx (ptr_owner_view d (EL j h))
    (ptr_owner_view d (EL (SUC j) h))` by
    (irule ptr_owner_view_step >> rpt conj_tac
     >- (first_x_assum irule >> decide_tac)
     >- (first_x_assum irule >> decide_tac) >>
     metis_tac[ptr_chrono_history_adjacent]) >>
  `wf_function (ptr_owner_view d (EL j h)).cf_fn` by metis_tac[] >>
  drule_all ptr_owner_transition_route >>
  metis_tac[ptr_owner_route_trans]
QED
