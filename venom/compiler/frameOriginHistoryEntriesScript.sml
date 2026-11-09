Theory frameOriginHistoryEntries
Ancestors
  frameOriginHistory frameHistoryCfg venomInstProps list rich_list

(* An entry is tied to an occurrence in this activation's actual log. *)
Definition origin_entry_witness_def:
  origin_entry_witness ctx fn lbl h <=>
    (?e PG G om inst s tail.
      h = e::OriginObserve (OriginSnapshot fn PG G om inst s)::tail /\
      origin_start e (OriginSnapshot fn PG G om inst s) /\
      s.vs_current_bb = lbl) \/
    (?pre PG G om inst s fuel post G' om' inst' t tail.
      h = pre ++ [OriginObserve (OriginSnapshot fn PG G om inst s);
        OriginBlock fuel post; OriginObserve (OriginSnapshot fn PG G' om' inst' t)] ++ tail /\
      origin_edge ctx (OriginSnapshot fn PG G om inst s) (OriginBlock fuel post)
        (OriginSnapshot fn PG G' om' inst' t) /\ t.vs_current_bb = lbl)
End

Theorem origin_entry_witness_append:
  origin_entry_witness ctx fn lbl h ==>
    origin_entry_witness ctx fn lbl (h ++ suffix)
Proof
  simp[origin_entry_witness_def] >> rpt strip_tac >>
  metis_tac[APPEND_ASSOC, APPEND]
QED

Theorem origin_edge_entry_or_same:
  origin_edge ctx (OriginSnapshot fn PG G om inst s) e
    (OriginSnapshot fn' PG' G' om' inst' t) ==>
  fn' = fn /\ PG' = PG /\
  ((?fuel post. e = OriginBlock fuel post) \/ t.vs_current_bb = s.vs_current_bb)
Proof
  Cases_on `e` >> simp[origin_edge_def] >> rpt strip_tac >> gvs[]
  >- metis_tac[step_preserves_control_flow]
  >> metis_tac[return_binding_current_bb]
QED

Theorem origin_log_observation_entries:
  !ctx h. origin_log ctx h ==>
    h <> [] /\
    (!fn PG G om inst s.
      MEM (OriginObserve (OriginSnapshot fn PG G om inst s)) h ==>
      origin_entry_witness ctx fn s.vs_current_bb h)
Proof
  ho_match_mp_tac origin_log_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `a` >> gvs[] >>
      rpt strip_tac >> gvs[]
      >- metis_tac[origin_start_not_observe]
      >> simp[origin_entry_witness_def] >> metis_tac[])
  >> Cases_on `a` >> Cases_on `b` >>
  drule origin_edge_entry_or_same >> strip_tac >> gvs[] >>
  rpt strip_tac >> gvs[]
  >- metis_tac[origin_entry_witness_append]
  >- suspend "block"
  >- metis_tac[origin_entry_witness_append]
  >- metis_tac[origin_edge_not_observe]
  >> suspend "same"
QED

Resume origin_log_observation_entries[block]:
  simp[origin_entry_witness_def] >> disj2_tac >>
  qexists `FRONT h` >>
  metis_tac[APPEND_FRONT_LAST, APPEND_ASSOC, APPEND, APPEND_NIL]
QED

Resume origin_log_observation_entries[same]:
  irule origin_entry_witness_append >>
  `MEM (LAST h) h` by metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM] >>
  metis_tac[]
QED

Finalise origin_log_observation_entries

Theorem origin_log_function:
  !ctx h. origin_log ctx h ==>
    !fn PG G om inst s.
      LAST h = OriginObserve (OriginSnapshot fn PG G om inst s) ==>
      !fn' PG' G' om' inst' s'.
        MEM (OriginObserve (OriginSnapshot fn' PG' G' om' inst' s')) h ==>
        fn' = fn
Proof
  ho_match_mp_tac origin_log_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (Cases_on `a` >> simp[] >> rpt strip_tac >> gvs[] >>
      metis_tac[origin_start_not_observe])
  >> Cases_on `a` >> Cases_on `b` >>
  drule origin_edge_entry_or_same >> strip_tac >>
  simp[NoAsms, LAST_APPEND] >> rpt strip_tac >>
  gvs[NoAsms] >> metis_tac[origin_edge_not_observe]
QED

Theorem history_visit_observation[local]:
  !obs lbl. MEM lbl (history_visits obs) ==>
    ?i s. MEM (i,s) obs /\ s.vs_current_bb = lbl
Proof
  recInduct history_visits_ind >> simp[history_visits_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `is_terminator i.inst_opcode` >> gvs[] >> metis_tac[]
QED

Theorem origin_observations_member[local]:
  !h i s. MEM (i,s) (origin_observations h) ==>
    ?fn PG G om. MEM (OriginObserve (OriginSnapshot fn PG G om i s)) h
Proof
  Induct >> simp[origin_observations_def] >>
  qx_gen_tac `ev` >> Cases_on `ev` >> simp[origin_observations_def] >>
  Cases_on `o'` >>
  simp[origin_observations_def] >> metis_tac[]
QED

Theorem origin_log_visited_entry:
  origin_log ctx h /\
  LAST h = OriginObserve (OriginSnapshot fn PG G om inst s) /\
  MEM lbl (history_visits (origin_observations h)) ==>
    origin_entry_witness ctx fn lbl h
Proof
  rpt strip_tac >> drule history_visit_observation >> strip_tac >>
  drule origin_observations_member >> strip_tac >>
  drule_all origin_log_function >> strip_tac >> gvs[] >>
  metis_tac[origin_log_observation_entries]
QED

Theorem joint_origin_history_visited_entry:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  MEM lbl (history_visits (origin_observations h)) ==>
    origin_entry_witness ctx fn lbl h
Proof
  metis_tac[joint_origin_history_current_log, joint_origin_history_endpoints,
    origin_log_visited_entry]
QED

Theorem joint_origin_history_saved_visited_entry:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  n < LENGTH stk /\ MEM lbl (history_visits (origin_observations (EL n hs))) ==>
    origin_entry_witness ctx (EL n stk).cf_fn lbl (EL n hs)
Proof
  rpt strip_tac >> drule joint_origin_history_endpoints >> strip_tac >>
  drule_all joint_origin_history_saved_log >> strip_tac >>
  irule origin_log_visited_entry >> goal_assum (drule_at Any) >>
  gvs[LIST_REL_EL_EQN, EL_ZIP] >> metis_tac[]
QED

(* Consumers see reset maps or the exact pre-entry maps, never a PHI
   update incorrectly applied to an initial/callee entry. *)
Theorem origin_entry_witness_cases:
  origin_entry_witness ctx fn lbl h ==>
  (?e pre PG inst s tail.
    h = e::OriginObserve (OriginSnapshot fn PG FEMPTY FEMPTY inst s)::tail /\
    (e = OriginInitial pre \/ e = OriginCallee pre) /\
    enters_block fn pre s /\ s.vs_current_bb = lbl) \/
  (?prefix PG G om inst s fuel post inst' t tail.
    h = prefix ++ [OriginObserve (OriginSnapshot fn PG G om inst s);
      OriginBlock fuel post;
      OriginObserve (OriginSnapshot fn PG (entry_prov fn post G)
        (origin_entry fn post om) inst' t)] ++ tail /\
    step_inst fuel ctx inst s = OK post /\ ~post.vs_halted /\
    enters_block fn post t /\ t.vs_current_bb = lbl)
Proof
  simp[origin_entry_witness_def] >> rpt strip_tac
  >- (drule origin_start_cases >> strip_tac >> gvs[origin_start_def] >>
      metis_tac[])
  >> drule origin_edge_block >> strip_tac >> gvs[] >> metis_tac[]
QED
