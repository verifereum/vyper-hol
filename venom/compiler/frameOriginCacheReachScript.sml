Theory frameOriginCacheReach
Ancestors
  frameOriginCache frameOriginReachable frameOriginUpdates ptrDiscipline
  ptrDisciplineEmptyTaint venomExecSemantics venomInst venomState finite_map list

Theorem origin_frame_cache_invariant:
  !vs0 ctx stk PG G tn fn inst s oms om.
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
  local_cache_ok om s /\
  LIST_REL (\f m. local_cache_ok m f.cf_state) stk oms
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt conj_tac
  >- simp[local_cache_ok_def]
  >- suspend "next"
  >- suspend "block"
  >- (simp[local_cache_ok_def] >> metis_tac[])
  >> suspend "ret"
QED

Resume origin_frame_cache_invariant[next]:
  rpt strip_tac >> simp[local_cache_ok_def] >>
  metis_tac[local_cache_ok_step, local_cache_ok_def]
QED

Resume origin_frame_cache_invariant[block]:
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `local_cache_ok om s'` by
    (irule local_cache_ok_transport >> qexists_tac `s` >> simp[] >>
     metis_tac[step_inst_cache_preserved]) >>
  metis_tac[local_cache_ok_entry]
QED

Resume origin_frame_cache_invariant[ret]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule return_bind_cache >> strip_tac >>
  irule local_cache_ok_restrict >>
  irule local_cache_ok_transport >> qexists_tac `f.cf_state` >> simp[]
QED

Finalise origin_frame_cache_invariant

Theorem origin_frame_current_cache:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  FLOOKUP om v = SOME (OriginLocal aid,site) ==>
  FLOOKUP s.vs_allocas aid = SOME site
Proof
  strip_tac >> drule origin_frame_cache_invariant >>
  simp[local_cache_ok_def] >> metis_tac[]
QED

Theorem origin_frame_saved_cache:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  n < LENGTH stk /\ FLOOKUP (EL n oms) v = SOME (OriginLocal aid,site) ==>
  FLOOKUP (EL n stk).cf_state.vs_allocas aid = SOME site
Proof
  strip_tac >> drule origin_frame_cache_invariant >>
  simp[LIST_REL_EL_EQN, local_cache_ok_def] >> metis_tac[]
QED
