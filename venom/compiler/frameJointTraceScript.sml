Theory frameJointTrace
Ancestors
  frameJointTransition frameOriginHistory list rich_list

Definition joint_chain_def:
  (joint_chain ctx q [] [] r <=> r = q) /\
  (joint_chain ctx q [] (u::us) r <=> F) /\
  (joint_chain ctx q (ev::es) [] r <=> F) /\
  (joint_chain ctx q (ev::es) (u::us) r <=>
    joint_transition ctx q ev u /\ joint_chain ctx u es us r)
End

Definition joint_trace_def:
  joint_trace vs0 ctx q0 es qs q <=>
    joint_initial vs0 ctx q0 /\ joint_chain ctx q0 es qs q
End

Theorem joint_chain_length:
  !es q qs r. joint_chain ctx q es qs r ==> LENGTH es = LENGTH qs
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def] >> metis_tac[]
QED

Theorem joint_chain_append:
  !es q qs r fs rs.
  joint_chain ctx q (es ++ fs) (qs ++ rs) r /\ LENGTH es = LENGTH qs <=>
  LENGTH es = LENGTH qs /\
  ?u. joint_chain ctx q es qs u /\ joint_chain ctx u fs rs r
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def] >> metis_tac[]
QED

Theorem joint_chain_snoc:
  joint_chain ctx q es qs u /\ joint_transition ctx u ev r ==>
  joint_chain ctx q (es ++ [ev]) (qs ++ [r]) r
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_chain_length] >>
  `joint_chain ctx u [ev] [r] r` by simp[joint_chain_def] >>
  metis_tac[joint_chain_append]
QED

Theorem joint_chain_reachable:
  !es q qs r. joint_config_reachable vs0 ctx q /\ joint_chain ctx q es qs r ==>
    joint_config_reachable vs0 ctx r
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def] >>
  metis_tac[joint_transition_reachable]
QED

Theorem joint_trace_reachable:
  joint_trace vs0 ctx q0 es qs q ==> joint_config_reachable vs0 ctx q
Proof
  simp[joint_trace_def] >> metis_tac[joint_initial_reachable, joint_chain_reachable]
QED

Theorem joint_trace_snoc:
  joint_trace vs0 ctx q0 es qs u /\ joint_transition ctx u ev r ==>
  joint_trace vs0 ctx q0 (es ++ [ev]) (qs ++ [r]) r
Proof
  simp[joint_trace_def] >> metis_tac[joint_chain_snoc]
QED

Theorem joint_history_trace:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
    joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
    ?q0 es qs. joint_trace vs0 ctx q0 es qs
      (JointConfig stk PG G tn fn inst s oms om hs h)
Proof
  ho_match_mp_tac joint_origin_history_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac
  >- (simp[joint_trace_def] >>
      qexistsl_tac [`JointConfig [] [] FEMPTY entry_taint fn inst s [] FEMPTY []
        [OriginInitial (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl;
          vs_inst_idx := 0|>); OriginObserve
          (OriginSnapshot fn [] FEMPTY FEMPTY inst s)]`, `[]`, `[]`] >>
      simp[joint_chain_def] >> metis_tac[joint_initial_rules]) >>
  metis_tac[joint_trace_snoc, joint_transition_rules]
QED

Theorem joint_reachable_iff_trace:
  joint_config_reachable vs0 ctx q <=>
  ?q0 es qs. joint_trace vs0 ctx q0 es qs q
Proof
  Cases_on `q` >> eq_tac
  >- (simp[joint_config_reachable_def] >> metis_tac[joint_history_trace]) >>
  metis_tac[joint_trace_reachable]
QED

Theorem joint_chain_split:
  !n es q qs r. joint_chain ctx q es qs r /\ n <= LENGTH es ==>
  ?u. joint_chain ctx q (TAKE n es) (TAKE n qs) u /\
      joint_chain ctx u (DROP n es) (DROP n qs) r
Proof
  Induct >> Cases_on `es` >> Cases_on `qs` >>
  simp[joint_chain_def] >> metis_tac[]
QED

Theorem joint_chain_prefix_reachable:
  !es q qs r. joint_config_reachable vs0 ctx q /\ joint_chain ctx q es qs r ==>
    EVERY (joint_config_reachable vs0 ctx) (q::qs)
Proof
  Induct >> Cases_on `qs` >> simp[joint_chain_def] >>
  rpt strip_tac >>
  `joint_config_reachable vs0 ctx h` by
    metis_tac[joint_transition_reachable] >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem joint_trace_prefix_reachable:
  joint_trace vs0 ctx q0 es qs q ==>
  EVERY (joint_config_reachable vs0 ctx) (q0::qs)
Proof
  rewrite_tac[joint_trace_def] >>
  metis_tac[joint_chain_prefix_reachable, joint_initial_reachable]
QED

(* The numeric index selects an occurrence, not merely a configuration value. *)
Theorem joint_chain_edge_at:
  !n es q qs r. joint_chain ctx q es qs r /\ n < LENGTH es ==>
  joint_transition ctx (EL n (q::qs)) (EL n es) (EL (SUC n) (q::qs))
Proof
  Induct >> Cases_on `es` >> Cases_on `qs` >>
  simp[joint_chain_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`t`,`h'`,`t'`,`r`] mp_tac) >> simp[]
QED

Theorem joint_trace_edge_at:
  joint_trace vs0 ctx q0 es qs q /\ n < LENGTH es ==>
  joint_config_reachable vs0 ctx (EL n (q0::qs)) /\
  joint_transition ctx (EL n (q0::qs)) (EL n es) (EL (SUC n) (q0::qs)) /\
  joint_config_reachable vs0 ctx (EL (SUC n) (q0::qs))
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_chain_length, joint_trace_def] >>
  drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >> strip_tac >>
  conj_tac >- (first_x_assum irule >> simp[]) >>
  conj_tac >- metis_tac[joint_chain_edge_at, joint_trace_def] >>
  first_x_assum irule >> simp[]
QED

(* Composition of occurrence selection and the canonical return inversion.
   The operational return label pins the callee state even after its local
   log is popped.  The successor equation remains the canonical iff boundary
   joint_transition_return, not a separately maintained return semantics. *)
Theorem joint_trace_return_segment:
  joint_trace vs0 ctx q0 es qs q /\ n < LENGTH es /\
  EL n es = SOME (OriginResume fuel fn rinst s ret send post) ==>
  joint_config_reachable vs0 ctx (EL n (q0::qs)) /\
  joint_transition ctx (EL n (q0::qs))
    (SOME (OriginResume fuel fn rinst s ret send post)) (EL (SUC n) (q0::qs)) /\
  ?f stk PG G tn oms om caller_om hs h caller_h.
    EL n (q0::qs) =
      JointConfig (f::stk) PG G tn fn rinst s (caller_om::oms) om (caller_h::hs) h /\
    active_inst fn rinst s /\ step_inst fuel ctx rinst s = IntRet ret send /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state send)) = SOME post
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  rewrite_tac[joint_transition_return] >> metis_tac[]
QED
