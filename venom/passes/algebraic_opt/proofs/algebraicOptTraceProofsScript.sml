Theory algebraicOptTraceProofs
Ancestors
  algebraicOptReachabilityProofs venomState venomExecSemantics list rich_list pair

(* A single real transition, not the reflexive initial prefix. PHIs are atomic. *)
Inductive ao_source_step:
  (!ctx fn k s bb p.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_step ctx fn (SUC k,T,s)
      (k,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
  (!ctx fn k s bb inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t ==>
    ao_source_step ctx fn (k,F,s)
      (k,F,t with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!ctx fn k s bb inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\
    step_inst k ctx inst s = OK t /\ ~t.vs_halted ==>
    ao_source_step ctx fn (k,F,s) (k,T,t))
End

Definition ao_source_trace_def:
  ao_source_trace ctx fn ([]:(num # bool # venom_state) list) = T /\
  ao_source_trace ctx fn [a] = T /\
  ao_source_trace ctx fn (a::b::rest) =
    (ao_source_step ctx fn a b /\ ao_source_trace ctx fn (b::rest))
End

Theorem ao_source_step_prefix:
  !ctx fn a b.
    ao_source_step ctx fn a b ==>
    !s0 n. ao_source_prefix ctx fn s0 n (FST a) (FST (SND a)) (SND (SND a)) ==>
      ao_source_prefix ctx fn s0 n (FST b) (FST (SND b)) (SND (SND b))
Proof
  ho_match_mp_tac ao_source_step_ind >> simp[] >> rpt strip_tac >>
  metis_tac[ao_source_prefix_rules]
QED

Theorem ao_source_trace_snoc:
  !trace ctx fn a.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    ao_source_step ctx fn (LAST trace) a ==>
    ao_source_trace ctx fn (trace ++ [a])
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `trace` >> simp[ao_source_trace_def] >>
  metis_tac[APPEND, NOT_CONS_NIL]
QED

Theorem ao_source_trace_extend:
  !ctx fn start a b.
    ao_source_step ctx fn a b /\
    (?trace. trace <> [] /\ HD trace = start /\ LAST trace = a /\
      ao_source_trace ctx fn trace) ==>
    ?trace. trace <> [] /\ HD trace = start /\ LAST trace = b /\
      ao_source_trace ctx fn trace
Proof
  rpt strip_tac >> qexists `trace ++ [b]` >>
  simp[LAST_APPEND_CONS] >> conj_tac
  >- (Cases_on `trace` >> gvs[]) >>
  irule ao_source_trace_snoc >> simp[]
QED

Theorem ao_source_prefix_has_trace:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s ==>
    ?trace. trace <> [] /\ HD trace = (n,T,s0) /\
      LAST trace = (k,phase,s) /\ ao_source_trace ctx fn trace
Proof
  ho_match_mp_tac ao_source_prefix_ind >> conj_tac
  >- (rpt gen_tac >> qexists `[(n,T,s0)]` >> simp[ao_source_trace_def]) >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  irule ao_source_trace_extend >>
  qexists `LAST trace` >>
  (conj_tac >- (qexists `trace` >> simp[])) >>
  gvs[] >> metis_tac[ao_source_step_rules]
QED

Theorem ao_source_trace_replay:
  !trace ctx fn s0 n.
    trace <> [] /\ ao_source_trace ctx fn trace /\
    ao_source_prefix ctx fn s0 n
      (FST (HD trace)) (FST (SND (HD trace))) (SND (SND (HD trace))) ==>
    ao_source_prefix ctx fn s0 n
      (FST (LAST trace)) (FST (SND (LAST trace))) (SND (SND (LAST trace)))
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `trace` >> simp[ao_source_trace_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  drule ao_source_step_prefix >> simp[]
QED

Theorem ao_source_prefix_trace_iff:
  !ctx fn s0 n k phase s.
    ao_source_prefix ctx fn s0 n k phase s <=>
    ?trace. trace <> [] /\ HD trace = (n,T,s0) /\
      LAST trace = (k,phase,s) /\ ao_source_trace ctx fn trace
Proof
  rpt gen_tac >> eq_tac
  >- metis_tac[ao_source_prefix_has_trace] >>
  strip_tac >> drule ao_source_trace_replay >>
  disch_then (qspecl_then [`ctx`,`fn`,`s0`,`n`] mp_tac) >>
  simp[ao_source_prefix_rules]
QED

(* Split the ACTUAL list; neither direction chooses another history. *)
Theorem ao_source_trace_split:
  !front ctx fn a back.
    ao_source_trace ctx fn (front ++ a::back) <=>
    ao_source_trace ctx fn (front ++ [a]) /\ ao_source_trace ctx fn (a::back)
Proof
  Induct >> simp[ao_source_trace_def] >>
  rpt gen_tac >> Cases_on `front`
  >- simp[ao_source_trace_def] >>
  rule_assum_tac (REWRITE_RULE [APPEND]) >>
  simp[NoAsms, ao_source_trace_def] >> metis_tac[]
QED

Theorem ao_source_trace_transition_split:
  !front ctx fn a b back.
    ao_source_trace ctx fn (front ++ a::b::back) <=>
    ao_source_trace ctx fn (front ++ [a]) /\
    ao_source_step ctx fn a b /\ ao_source_trace ctx fn (b::back)
Proof
  rpt gen_tac >> once_rewrite_tac[ao_source_trace_split] >>
  simp[ao_source_trace_def]
QED

(* The two endpoints carry the full common predecessor state, including
   previous-block selection. There is no intermediate PHI writing event. *)
Theorem ao_source_trace_phi_probe:
  !ctx fn k s bb p.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK p ==>
    ao_source_trace ctx fn
      [(SUC k,T,s); (k,F,p with vs_inst_idx := phi_prefix_length bb.bb_instructions)]
Proof
  rpt strip_tac >> simp[ao_source_trace_def] >>
  metis_tac[ao_source_step_rules]
QED

(* Re-entry at the same label is a real edge, not the reflexive initial
   node. The phase change still distinguishes pre-PHI from sequential. *)
Theorem ao_source_trace_loop_probe:
  !ctx fn k s bb inst t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ step_inst k ctx inst s = OK t /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb ==>
    ao_source_trace ctx fn [(k,F,s); (k,T,t)]
Proof
  rpt strip_tac >> simp[ao_source_trace_def] >>
  metis_tac[ao_source_step_rules]
QED
