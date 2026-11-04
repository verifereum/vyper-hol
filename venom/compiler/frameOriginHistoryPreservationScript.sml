Theory frameOriginHistoryPreservation
Ancestors
  frameOriginHistory frameOriginUpdates finite_map list rich_list

Definition origin_phi_writes_def:
  origin_phi_writes [] = {} /\
  origin_phi_writes (i::is) =
    if i.inst_opcode = PHI then set i.inst_outputs UNION origin_phi_writes is
    else {}
End

Definition origin_entry_writes_def:
  origin_entry_writes fn post =
    case lookup_block post.vs_current_bb fn.fn_blocks of
      NONE => {} | SOME bb => origin_phi_writes bb.bb_instructions
End

Definition origin_edge_writes_def:
  origin_edge_writes (OriginSnapshot fn PG G om inst s) e =
    case e of
      OriginOrdinary fuel post => set inst.inst_outputs
    | OriginBlock fuel post => origin_entry_writes fn post
    | OriginResume fuel callee rinst rs ret send post => set inst.inst_outputs
    | _ => {}
End

Theorem origin_phis_outside_writes:
  !is. v NOTIN origin_phi_writes is ==>
    FLOOKUP (origin_phis prev om is) v = FLOOKUP om v
Proof
  Induct >> simp[origin_phi_writes_def, origin_phis_def] >> gen_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[origin_phi_writes_def, origin_phis_def, origin_set_lookup] >>
  rpt strip_tac >> gvs[] >>
  `h.inst_outputs <> [v]` by (strip_tac >> gvs[]) >> simp[]
QED

Theorem origin_entry_outside_writes:
  v NOTIN origin_entry_writes fn post ==>
    FLOOKUP (origin_entry fn post om) v = FLOOKUP om v
Proof
  simp[origin_entry_writes_def, origin_entry_def] >>
  Cases_on `lookup_block post.vs_current_bb fn.fn_blocks` >>
  simp[origin_phis_outside_writes]
QED

Theorem origin_edge_outside_writes:
  origin_edge ctx (OriginSnapshot fn PG G om inst s) e
    (OriginSnapshot fn' PG' G' om' inst' t) /\
  v NOTIN origin_edge_writes (OriginSnapshot fn PG G om inst s) e ==>
    FLOOKUP om' v = FLOOKUP om v
Proof
  Cases_on `e` >> simp[origin_edge_def, origin_edge_writes_def] >>
  rpt strip_tac >> gvs[]
  >- (simp[origin_step_def, origin_set_lookup] >>
      `inst.inst_outputs <> [v]` by (strip_tac >> gvs[]) >> simp[])
  >- metis_tac[origin_entry_outside_writes]
  >> simp[FLOOKUP_DRESTRICT]
QED

(* Alternating edge/observation suffix, with the source snapshot supplied.
   Malformed tails are rejected rather than treated as write-free. *)
Definition origin_suffix_avoids_def:
  origin_suffix_avoids v a [] = T /\
  origin_suffix_avoids v a [e] = F /\
  origin_suffix_avoids v a (e::obs::rest) =
    case obs of OriginObserve b =>
      v NOTIN origin_edge_writes a e /\ origin_suffix_avoids v b rest
    | _ => F
End

Theorem origin_chain_lookup_preserved:
  !ctx a tail. origin_chain ctx a tail ==>
    !v fn PG G om inst s fn' PG' G' om' inst' t.
    a = OriginSnapshot fn PG G om inst s /\
    LAST (OriginObserve a::tail) =
      OriginObserve (OriginSnapshot fn' PG' G' om' inst' t) /\
    origin_suffix_avoids v a tail ==>
    FLOOKUP om' v = FLOOKUP om v
Proof
  ho_match_mp_tac origin_chain_ind >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (rpt strip_tac >> gvs[origin_suffix_avoids_def])
  >> rename1 `origin_edge ctx src ev dst` >>
  Cases_on `src` >> Cases_on `dst` >> rpt strip_tac >>
  gvs[origin_suffix_avoids_def] >>
  drule_all origin_edge_outside_writes >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem origin_chain_suffix:
  !ctx a tail. origin_chain ctx a tail ==>
    !pre b rest.
      OriginObserve a::tail = pre ++ OriginObserve b::rest ==>
      origin_chain ctx b rest
Proof
  ho_match_mp_tac origin_chain_ind >> rpt strip_tac
  >- (Cases_on `pre` >> gvs[] >> metis_tac[origin_chain_rules])
  >> Cases_on `pre`
  >- (gvs[] >> irule origin_chain_cons >> simp[] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[])
  >> gvs[] >> Cases_on `t`
  >- (gvs[] >> metis_tac[origin_edge_not_observe])
  >> gvs[] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem origin_log_suffix:
  origin_log ctx h /\ h = pre ++ OriginObserve a::rest ==>
    origin_chain ctx a rest
Proof
  rpt strip_tac >> drule origin_log_chain >> strip_tac >>
  Cases_on `pre`
  >- (gvs[] >> metis_tac[origin_start_not_observe])
  >> gvs[] >> drule origin_chain_suffix >>
  disch_then irule >> qexists `t` >> simp[]
QED

Theorem origin_log_suffix_lookup_preserved:
  origin_log ctx h /\
  h = pre ++ OriginObserve (OriginSnapshot fn PG G om inst s)::rest /\
  LAST h = OriginObserve (OriginSnapshot fn' PG' G' om' inst' t) /\
  origin_suffix_avoids v (OriginSnapshot fn PG G om inst s) rest ==>
    FLOOKUP om' v = FLOOKUP om v
Proof
  rpt strip_tac >> drule_all origin_log_suffix >> strip_tac >>
  irule origin_chain_lookup_preserved >> goal_assum (drule_at Any) >>
  simp[] >> Cases_on `rest` >> gvs[LAST_APPEND] >>
  Cases_on `t'` >> gvs[LAST_APPEND] >> metis_tac[]
QED
