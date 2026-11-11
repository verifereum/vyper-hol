Theory concretizeLayoutPhaseOrigin
Ancestors concretizeLayoutLocalReturnCopy frameTerminalCallOrigins
  framePhaseCertificates frameRankedTerminalCorridor concretizeLayoutSupplement
  concretizeLayoutReaderContext frameJointTrace frameJointTransition
  frameResolvedTrace frameActivationLifetime frameRelocationLocal
  frameRelocationTaintOrder frameRelocationGuardedValues frameActivationLookup
  ptrDiscipline venomExecSemantics venomState venomInst finite_map ctxLookupAgreeHelpers
  concretizeLayoutCalleeRoots venomInstProps

Datatype:
  layout_block_origin = <| lbo_source : basic_block;
    lbo_target : basic_block; lbo_entry : venom_state |>
End

Datatype:
  layout_ordinary_phase = <| lop_origin : layout_block_origin;
    lop_pending : bool; lop_cursor : num; lop_bound : num;
    lop_config : joint_config;
    lop_ids : num list;
    lop_anns : ((((num # num) # (num # num)) option list #
      (string, (num # num) # (num # num)) fmap) list);
    lop_target_taint : taint |>
End

Datatype:
  layout_terminal_phase = <| ltp_origin : layout_block_origin;
    ltp_pending : bool; ltp_remaining : num |>
End

Definition layout_phase_normalize_def:
  layout_phase_normalize pending s =
    if pending then s with vs_inst_idx := SUC s.vs_inst_idx else s
End

Definition layout_ordinary_state_def:
  layout_ordinary_state D lo C' q0 es qs g s t <=>
    case g.lop_config of JointConfig stk PG G tn fn inst a oms om hs h =>
      a = layout_phase_normalize g.lop_pending s /\
      ?birth ids rp rv anns.
        g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
        parameter_roots (\i x y. clean_resolved_root
          (activation_lookup (0:num) (concretize_positions C')
            (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (resolved_parameter_entry rp i) x y)
          s.vs_params t.vs_params /\
        local_rel (\u. F)
          (guarded_ptr (retpc_var fn)
            (activation_lookup (0:num) (concretize_positions C')
              (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
          (guarded_bytes (retpc_var fn) rv tn)
          (joint_relocation_demand lo (concretize_positions C') q0 es qs g.lop_cursor)
          concretize_local_obs s t /\
        relocation_taint_le
          (joint_relocation_demand lo (concretize_positions C') q0 es qs g.lop_cursor)
          tn g.lop_target_taint /\
        concretize_supplement D tn s t /\ relocation_env s t /\
        relocation_reader_context s t /\ s.vs_code = t.vs_code /\
        s.vs_data_section = t.vs_data_section /\ s.vs_initial_fmp = t.vs_initial_fmp
End

(* Pending entries name the next trace point, and retain the actual successful
   event which produced the unnormalized instruction output. *)
Definition layout_ordinary_trace_def:
  layout_ordinary_trace vs0 C q0 es qs q g s <=>
    joint_trace vs0 C q0 es qs q /\
    g.lop_cursor < LENGTH (q0::qs) /\
    EL g.lop_cursor (q0::qs) = g.lop_config /\
    resolved_config_ok g.lop_config g.lop_ids g.lop_anns /\
    lifetime_ok g.lop_bound g.lop_ids g.lop_config /\
    (g.lop_pending ==>
      ?c fuel. g.lop_cursor = SUC c /\ c < LENGTH es /\
        EL c es = SOME (OriginOrdinary fuel s) /\
        joint_transition C (EL c (q0::qs)) (EL c es) g.lop_config)
End

Definition layout_ordinary_entry_def:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t <=>
    terminal_call_prefix C g.lop_origin.lbo_source g.lop_origin.lbo_entry
      (layout_phase_normalize g.lop_pending s) /\
    layout_ordinary_trace vs0 C q0 es qs q g s /\
    layout_ordinary_state D lo C' q0 es qs g s t
End

Definition layout_terminal_entry_def:
  layout_terminal_entry C g s t <=>
    terminal_call_prefix C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry
      (layout_phase_normalize g.ltp_pending s) /\
    ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_remaining
      (layout_phase_normalize g.ltp_pending s)
      (layout_phase_normalize g.ltp_pending t) /\
    revert_forward_at g.ltp_origin.lbo_source
      (layout_phase_normalize g.ltp_pending s).vs_inst_idx
End

Definition layout_phase_origin_def:
  (layout_phase_origin (INL g) = g.lop_origin) /\
  (layout_phase_origin (INR g) = g.ltp_origin)
End

Definition layout_phase_begins_def:
  layout_phase_begins g bb p <=>
    (layout_phase_origin g).lbo_source = bb /\
    (layout_phase_origin g).lbo_entry = p
End

Definition layout_phase_entry_def:
  (layout_phase_entry D lo vs0 C C' q0 es qs q (INL g) s t <=>
    layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t) /\
  (layout_phase_entry D lo vs0 C C' q0 es qs q (INR g) s t <=>
    layout_terminal_entry C g s t)
End

(* Deliberately partial: this is not the complete driver outcome relation. *)
Definition layout_phase_ok_abort_def:
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g h r r' <=>
    case (r,r') of
      (OK s,OK t) => layout_phase_origin g = layout_phase_origin h /\
        layout_phase_entry D lo vs0 C C' q0 es qs q h s t
    | (Abort a s,Abort b t) => a = b /\ dead_result_rel D (Abort a s) (Abort b t)
    | _ => F
End

Theorem layout_phase_normalize_ready[simp]:
  layout_phase_normalize F s = s
Proof
  simp[layout_phase_normalize_def]
QED

Theorem layout_phase_normalize_pending[simp]:
  layout_phase_normalize T s = s with vs_inst_idx := SUC s.vs_inst_idx
Proof
  simp[layout_phase_normalize_def]
QED

Theorem layout_terminal_origin_exclusion:
  layout_terminal_entry C g s t ==>
  ~finite_block C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry (OK u)
Proof
  simp[layout_terminal_entry_def] >> rpt strip_tac >>
  metis_tac[terminal_call_revert_no_finite_ok]
QED

Theorem layout_phase_ok_origin:
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g h (OK s) (OK t) ==>
  layout_phase_origin g = layout_phase_origin h /\
  layout_phase_entry D lo vs0 C C' q0 es qs q h s t
Proof
  simp[layout_phase_ok_abort_def]
QED

Theorem layout_phase_terminal_origins:
  phase_terminal_origins C layout_phase_begins
    (layout_phase_ok_abort D lo vs0 C C' q0 es qs q)
Proof
  simp[phase_terminal_origins_def, layout_phase_begins_def,
    layout_phase_ok_abort_def, layout_phase_entry_def, layout_phase_origin_def] >>
  rpt strip_tac >> drule layout_terminal_origin_exclusion >> metis_tac[]
QED

Theorem layout_ordinary_ready:
  ~g.lop_pending ==>
  (layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t <=>
    terminal_call_prefix C g.lop_origin.lbo_source g.lop_origin.lbo_entry s /\
    layout_ordinary_trace vs0 C q0 es qs q g s /\
    layout_ordinary_state D lo C' q0 es qs g s t)
Proof
  simp[layout_ordinary_entry_def]
QED

Theorem layout_ordinary_pending:
  g.lop_pending ==>
  (layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t <=>
    terminal_call_prefix C g.lop_origin.lbo_source g.lop_origin.lbo_entry
      (s with vs_inst_idx := SUC s.vs_inst_idx) /\
    layout_ordinary_trace vs0 C q0 es qs q g s /\
    layout_ordinary_state D lo C' q0 es qs g s t)
Proof
  simp[layout_ordinary_entry_def]
QED

Theorem layout_terminal_ready:
  ~g.ltp_pending ==>
  (layout_terminal_entry C g s t <=>
    terminal_call_prefix C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry s /\
    ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_remaining s t /\
    revert_forward_at g.ltp_origin.lbo_source s.vs_inst_idx)
Proof
  simp[layout_terminal_entry_def]
QED

Theorem layout_terminal_pending:
  g.ltp_pending ==>
  (layout_terminal_entry C g s t <=>
    terminal_call_prefix C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry
      (s with vs_inst_idx := SUC s.vs_inst_idx) /\
    ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_remaining
      (s with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC t.vs_inst_idx) /\
    revert_forward_at g.ltp_origin.lbo_source (SUC s.vs_inst_idx))
Proof
  simp[layout_terminal_entry_def]
QED

Theorem layout_origin_initialize:
  terminal_call_prefix C bb
    (s with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (layout_phase_normalize F (s with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  simp[terminal_call_prefix_rules]
QED

Theorem layout_origin_successful_step:
  terminal_call_prefix C bb p s /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst fuel C i s = OK post /\
  post.vs_inst_idx = s.vs_inst_idx ==>
  terminal_call_prefix C bb p (layout_phase_normalize T post)
Proof
  strip_tac >>
  `terminal_call_edge C bb s (layout_phase_normalize T post)` by
    (simp[terminal_call_edge_def] >> metis_tac[]) >>
  `terminal_call_prefix C bb s (layout_phase_normalize T post)` by
    metis_tac[terminal_call_prefix_rules] >>
  metis_tac[terminal_call_prefix_trans]
QED

Theorem layout_origin_pending_ready:
  layout_phase_normalize T s =
    layout_phase_normalize F (s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[]
QED

Theorem layout_origin_prefix_splice:
  terminal_call_prefix C bb p (layout_phase_normalize pending s) /\
  terminal_call_prefix C bb (layout_phase_normalize pending s)
    (layout_phase_normalize pending' t) ==>
  terminal_call_prefix C bb p (layout_phase_normalize pending' t)
Proof
  metis_tac[terminal_call_prefix_trans]
QED

Theorem layout_phase_begins_splice:
  layout_phase_begins g bb p /\
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g h (OK s) (OK t) ==>
  layout_phase_begins h bb p
Proof
  strip_tac >> drule layout_phase_ok_origin >>
  strip_tac >> gvs[layout_phase_begins_def]
QED

Theorem layout_terminal_pending_outcome:
  g.ltp_pending /\ layout_phase_origin h = g.ltp_origin /\
  terminal_call_prefix C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry
    (layout_phase_normalize T s) /\
  ranked_terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_remaining
    (layout_phase_normalize T s) (layout_phase_normalize T t) /\
  revert_forward_at g.ltp_origin.lbo_source (layout_phase_normalize T s).vs_inst_idx ==>
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q h (INR g) (OK s) (OK t)
Proof
  simp[layout_phase_ok_abort_def, layout_phase_origin_def,
    layout_phase_entry_def, layout_terminal_entry_def]
QED

Theorem layout_terminal_administrative:
  g.ltp_pending /\ layout_terminal_entry C g s t ==>
  layout_terminal_entry C (g with ltp_pending := F)
    (layout_phase_normalize T s) (layout_phase_normalize T t)
Proof
  strip_tac >> gvs[layout_terminal_entry_def]
QED

Theorem layout_phase_ok_splice:
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g h (OK s) (OK t) /\
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q h k (OK u) (OK v) ==>
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g k (OK u) (OK v)
Proof
  simp[layout_phase_ok_abort_def] >> metis_tac[]
QED

Theorem layout_ordinary_trace_target_taint[simp]:
  layout_ordinary_trace vs0 C q0 es qs q (k with lop_target_taint := un) post <=>
  layout_ordinary_trace vs0 C q0 es qs q k post
Proof
  simp[layout_ordinary_trace_def]
QED

Theorem layout_ordinary_state_intro:
  k.lop_config = JointConfig stk PG G tn fn inst
    (layout_phase_normalize k.lop_pending s) oms om hs h /\
  k.lop_ids = birth::ids /\ k.lop_anns = (rp,rv)::anns /\
  parameter_roots (\i x y. clean_resolved_root
    (activation_lookup (0:num) (concretize_positions C')
      (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (resolved_parameter_entry rp i) x y)
    s.vs_params t.vs_params /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs k.lop_cursor)
    concretize_local_obs s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs k.lop_cursor)
    tn k.lop_target_taint /\
  concretize_supplement D tn s t /\ relocation_env s t /\
  relocation_reader_context s t /\ s.vs_code = t.vs_code /\
  s.vs_data_section = t.vs_data_section /\ s.vs_initial_fmp = t.vs_initial_fmp ==>
  layout_ordinary_state D lo C' q0 es qs k s t
Proof
  strip_tac >> simp[layout_ordinary_state_def] >>
  qexistsl_tac [`birth`, `ids`, `rp`, `rv`, `anns`] >> simp[]
QED

Theorem layout_ordinary_pending_outcome:
  layout_phase_origin h = k.lop_origin /\
  terminal_call_prefix C k.lop_origin.lbo_source k.lop_origin.lbo_entry
    (layout_phase_normalize k.lop_pending s) /\
  layout_ordinary_trace vs0 C q0 es qs q k s /\
  layout_ordinary_state D lo C' q0 es qs k s t ==>
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q h (INL k) (OK s) (OK t)
Proof
  simp[layout_phase_ok_abort_def, layout_phase_origin_def,
    layout_phase_entry_def, layout_ordinary_entry_def]
QED

Theorem layout_returncopy_pending_adapter:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ~ctx_has_dalloca C /\ fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\ EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  ~joint_read_exempt (EL g.lop_cursor (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst fuel C inst s = OK post /\ post.vs_inst_idx = s.vs_inst_idx /\
  k.lop_pending /\ k.lop_origin = g.lop_origin /\
  k.lop_cursor = SUC g.lop_cursor /\ k.lop_ids = g.lop_ids /\
  k.lop_anns = g.lop_anns /\
  k.lop_config = JointConfig stk PG G (step_taint inst s post tn) fn next
    (layout_phase_normalize T post) oms om hs' h' /\
  layout_ordinary_trace vs0 C q0 es qs q k post ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q (INL g)
      (INL (k with lop_target_taint := step_taint inst t tpost g.lop_target_taint))
      (OK post) (OK tpost)
Proof
  strip_tac >>
  `terminal_call_prefix C g.lop_origin.lbo_source g.lop_origin.lbo_entry s /\
   layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    metis_tac[layout_ordinary_ready] >>
  `terminal_call_prefix C k.lop_origin.lbo_source k.lop_origin.lbo_entry
    (layout_phase_normalize k.lop_pending post)` by
    (asm_rewrite_tac[] >> irule layout_origin_successful_step >>
     goal_assum (drule_at Any) >> simp[is_terminator_def] >> metis_tac[]) >>
  qpat_x_assum `layout_ordinary_trace _ _ _ _ _ _ g s` mp_tac >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ g s t` mp_tac >>
  simp[layout_ordinary_trace_def, layout_ordinary_state_def] >> rpt strip_tac >>
  drule_all concretize_returncopy_local_complete >> strip_tac >>
  `post.vs_initial_fmp = tpost.vs_initial_fmp` by
    metis_tac[step_inst_initial_fmp, step_inst_base_initial_fmp] >>
  `post.vs_params = s.vs_params /\ tpost.vs_params = t.vs_params` by
    (conj_tac >- (irule step_preserves_params >> goal_assum (drule_at Any) >>
      simp[is_terminator_def]) >>
     irule step_preserves_params >>
     qexistsl_tac [`C`, `0`, `inst`] >>
     simp[step_inst_non_invoke, is_terminator_def]) >>
  qexists_tac `tpost` >> asm_rewrite_tac[] >>
  irule layout_ordinary_pending_outcome >>
  simp[layout_phase_origin_def] >>
  (conj_tac >-
    (qpat_x_assum `terminal_call_prefix _ _ _ (layout_phase_normalize _ _)` mp_tac >>
     simp[])) >>
  irule layout_ordinary_state_intro >> simp[] >>
  goal_assum (drule_at (Pat `_ = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`anns`, `birth`, `ids`, `rp`, `rv`] >> simp[]
QED

val _ = export_theory();
