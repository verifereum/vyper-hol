Theory concretizeLayoutPhaseOrigin
Ancestors concretizeLayoutLocalReturnCopy frameTerminalCallOrigins
  framePhaseCertificates frameTerminalCorridor concretizeLayoutSupplement
  concretizeLayoutReaderContext frameJointTrace frameJointTransition
  frameResolvedTrace frameActivationLifetime frameRelocationLocal
  frameRelocationTaintOrder frameRelocationGuardedValues frameActivationLookup
  ptrDiscipline venomExecSemantics venomState venomInst finite_map

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
    ltp_pending : bool; ltp_end : num |>
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
        s.vs_data_section = t.vs_data_section
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
    terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_end
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
    terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_end s t /\
    revert_forward_at g.ltp_origin.lbo_source s.vs_inst_idx)
Proof
  simp[layout_terminal_entry_def]
QED

Theorem layout_terminal_pending:
  g.ltp_pending ==>
  (layout_terminal_entry C g s t <=>
    terminal_call_prefix C g.ltp_origin.lbo_source g.ltp_origin.lbo_entry
      (s with vs_inst_idx := SUC s.vs_inst_idx) /\
    terminal_entry g.ltp_origin.lbo_source g.ltp_origin.lbo_target g.ltp_end
      (s with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC t.vs_inst_idx) /\
    revert_forward_at g.ltp_origin.lbo_source (SUC s.vs_inst_idx))
Proof
  simp[layout_terminal_entry_def]
QED

val _ = export_theory();
