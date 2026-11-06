Theory concretizeLayoutSelectedBaseInterface
Ancestors frameSelectedSimulation concretizeLayoutAlignedControl
  concretizeLayoutPhaseExternal concretizeLayoutPhaseCorridor
  frameFiniteJointDecoration frameSelectedDecoration concretizeLayoutEntryFlags
  concretizeLayoutScopedPhase concretizeLayoutPhaseOrigin frameControlAgreement
  venomExecSemantics venomInst list arithmetic

(* Source-only lookahead.  The semantic endpoint remains at n; this edge is
   consumed by the enclosing block, not by the base-step simulation. *)
Definition layout_base_lookahead_def:
  layout_base_lookahead C q0 path q n i s <=>
    !p. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      step_inst_base i s = OK p ==>
      ?fuel qn. selected_segment C q0 path n q
        [(SOME (OriginOrdinary fuel p),qn)] qn
End

Definition layout_base_witness_def:
  (layout_base_witness D lo vs0 C C' q0 es qs qend q n i s j t (INL a) <=>
    ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qend a s t /\
    get_instruction a.lop_origin.lbo_source s.vs_inst_idx = SOME i /\
    get_instruction a.lop_origin.lbo_target t.vs_inst_idx = SOME j) /\
  (layout_base_witness D lo vs0 C C' q0 es qs qend q n i s j t (INR a) <=>
    ~a.ltp_pending /\ layout_corridor_entry C a s t /\
    get_instruction a.ltp_origin.lbo_source s.vs_inst_idx = SOME i /\
    get_instruction a.ltp_origin.lbo_target t.vs_inst_idx = SOME j)
End

Theorem layout_base_lookahead_term:
  is_terminator i.inst_opcode ==>
  layout_base_lookahead C q0 path q n i s
Proof
  simp[layout_base_lookahead_def]
QED

Theorem layout_base_lookahead_exit:
  decorated_step C i s r q n w qe d /\ (!p. r <> OK p) ==>
  layout_base_lookahead C q0 path q n i s
Proof
  simp[layout_base_lookahead_def] >> rpt strip_tac >>
  qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[decorated_step_cases] >> simp[] >> metis_tac[]
QED

Theorem layout_base_lookahead_next:
  decorated_step C i s (OK post) q n ws qm ds /\
  decoration_consumes C i q post qm ev qn /\
  selected_segment C q0 path n q (ws ++ [(ev,qn)] ++ wb) qe ==>
  layout_base_lookahead C q0 path q n i s
Proof
  simp[layout_base_lookahead_def] >> rpt strip_tac >>
  `ws = [] /\ qm = q /\ post = p` by
    (qpat_x_assum `decorated_step _ _ _ _ _ _ _ _ _` mp_tac >>
     once_rewrite_tac[decorated_step_cases] >> simp[] >> metis_tac[]) >>
  gvs[decoration_consumes_def] >>
  `joint_segment C q [(SOME (OriginOrdinary fuel p),qn)] qn /\
   joint_segment C qn wb qe` by
    (qpat_x_assum `selected_segment _ _ _ _ _ _ _` mp_tac >>
     simp[selected_segment_def, joint_segment_def] >> metis_tac[]) >>
  qexistsl [`fuel`, `qn`] >>
  irule (cj 1 selected_segment_parts) >>
  conj_tac >- simp[] >> qexistsl [`qe`, `wb`] >> simp[]
QED

Theorem layout_base_lookahead_edge:
  layout_base_lookahead C q0 path q n i s /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK post ==>
  ?fuel qn. n < LENGTH path /\
    EL n (MAP FST path) = SOME (OriginOrdinary fuel post) /\
    EL n (q0::MAP SND path) = q /\
    EL (SUC n) (q0::MAP SND path) = qn /\
    joint_transition C q (SOME (OriginOrdinary fuel post)) qn
Proof
  simp[layout_base_lookahead_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule selected_segment_indices >> strip_tac >>
  drule selected_singleton_event >> strip_tac >>
  qexists `fuel` >> simp[] >>
  fs[selected_segment_def, joint_segment_def, EL_APPEND_EQN]
QED

(* Pending payloads are indexed by the unconsumed endpoint. *)
Definition layout_base_pending_def:
  (layout_base_pending D lo vs0 C C' q0 es qs qend n (INL a) s t <=>
    a.lop_pending /\ a.lop_cursor = SUC n /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qend a s t) /\
  (layout_base_pending D lo vs0 C C' q0 es qs qend n (INR a) s t <=>
    a.ltp_pending /\ layout_corridor_entry C a s t)
End

Definition layout_base_success_def:
  layout_base_success D lo vs0 C C' q0 es qs qend n a s t <=>
    ?b. layout_phase_origin b = layout_phase_origin a /\
      layout_base_pending D lo vs0 C C' q0 es qs qend n b s t /\
      s.vs_halted = t.vs_halted
End

Definition layout_selected_base_entry_def:
  layout_selected_base_entry D lo vs0 C C' q0 path es qs qend q n i s j t <=>
    layout_base_lookahead C q0 path q n i s /\
    (?a. layout_base_witness D lo vs0 C C' q0 es qs qend q n i s j t a)
End

(* A single deterministic target base result serves every compatible origin.
   No target execution or outcome payload occurs in the entry relation. *)
Theorem layout_base_witness_repackage:
  (?a. Witness a) /\
  (!a. Witness a ==> ?r'. step_inst_base j t = r' /\ Payload a r') ==>
  ?r'. step_inst_base j t = r' /\ (!a. Witness a ==> Payload a r')
Proof
  metis_tac[]
QED

Theorem layout_base_corridor_assign:
  layout_base_witness D lo vs0 C C' q0 es qs qend q n i s j t (INR a) /\
  a.ltp_remaining = SUC remaining /\ step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_base_success D lo vs0 C C' q0 es qs qend n (INR a) post tpost
Proof
  simp[layout_base_witness_def] >> strip_tac >>
  drule_all layout_corridor_assign >> strip_tac >> gvs[] >>
  simp[layout_base_success_def] >>
  qexists `INR (a with <|ltp_pending := T; ltp_remaining := remaining|>)` >>
  simp[layout_base_pending_def, layout_phase_origin_def] >>
  fs[layout_corridor_entry_def]
QED

Theorem layout_base_corridor_revert:
  layout_base_witness D lo vs0 C C' q0 es qs qend q n i s j t (INR a) /\
  a.ltp_remaining = 0 /\ step_inst_base i s = Abort k post ==>
  ?tpost. step_inst_base j t = Abort k tpost /\
    dead_result_rel D (Abort k post) (Abort k tpost)
Proof
  simp[layout_base_witness_def] >> strip_tac >>
  drule_all layout_corridor_revert >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem layout_base_corridor_normalize:
  layout_base_pending D lo vs0 C C' q0 es qs qend n (INR a) s t ==>
  layout_corridor_entry C (a with ltp_pending := F)
    (s with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC t.vs_inst_idx) /\
  (a with ltp_pending := F).ltp_origin = a.ltp_origin
Proof
  simp[layout_base_pending_def] >> strip_tac >>
  drule layout_corridor_administrative >> simp[]
QED

Theorem layout_base_external:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\ taint_within D C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  layout_base_lookahead C q0 path q n inst s /\
  layout_base_witness D lo vs0 C C' q0 es qs qend q n inst s inst t (INL a) /\
  q = JointConfig stk PG G tn fn inst s oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  ~joint_read_exempt q /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  MEM inst.inst_opcode [CALL; STATICCALL; CREATE; CREATE2; DELEGATECALL] /\
  step_inst_base inst s = OK post ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    layout_base_success D lo vs0 C C' q0 es qs qend n (INL a) post tpost
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  drule_all layout_base_lookahead_edge >> strip_tac >>
  gvs[layout_base_witness_def, layout_aligned_entry_def] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_external_trace_step >>
  disch_then (drule_at (Pat `_ .lop_config = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `callee_first _ _`)) >>
  disch_then (drule_at (Pat `EVERY (fn_ptr_ok _) _`)) >>
  disch_then (drule_at (Pat `_ .lop_ids = _ :: _`)) >>
  disch_then (drule_at (Pat `_ .lop_anns = _ :: _`)) >>
  disch_then (drule_at (Pat `EL _ _ = SOME (OriginOrdinary _ _)`)) >>
  simp[] >> strip_tac >>
  fs[layout_phase_ok_abort_def, layout_phase_entry_def] >>
  `step_inst 0 C inst s = OK post /\ step_inst 0 C' inst t = OK tpost` by
    simp[step_inst_non_invoke] >>
  `control_agree post tpost` by
    (irule control_agree_step >>
     goal_assum (drule_at (Pat `step_inst _ C _ _ = OK _`)) >>
     goal_assum (drule_at (Pat `step_inst _ C' _ _ = OK _`)) >> simp[]) >>
  simp[layout_base_success_def] >>
  qexists `INL k` >> simp[layout_base_pending_def, layout_aligned_entry_def] >>
  metis_tac[layout_ordinary_entry_halted_agree]
QED

val _ = export_theory();
