Theory concretizeAnalysisOriginReach
Ancestors
  concretizeAnalysisOriginFlow frameOriginReachable frameOriginUpdates
  ptrDiscipline contextCodegenRel venomExecProofs venomInstProps venomWf
  venomInst list finite_map

Theorem origin_frame_flow_invariant:
  !vs0 ctx stk PG G tn fn inst s oms om.
    origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om ==>
    EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions ==>
    MEM fn ctx.ctx_functions /\ origin_local_flow fn om /\
    LIST_REL (\f saved. MEM f.cf_fn ctx.ctx_functions /\
      origin_local_flow f.cf_fn saved) stk oms
Proof
  ho_match_mp_tac origin_frame_reachable_ind >> rpt strip_tac >>
  gvs[]
  >- metis_tac[lookup_function_MEM]
  >- (irule origin_local_flow_step >>
      `MEM inst (fn_insts fn)` by
        (gvs[active_inst_def, fn_insts_def,
          venomWfPropsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[MEM_EL]) >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- metis_tac[origin_local_flow_entry]
  >- metis_tac[lookup_function_MEM] >>
  metis_tac[origin_local_flow_restrict]
QED

Theorem origin_frame_current_flow:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions ==>
  origin_local_flow fn om
Proof
  metis_tac[origin_frame_flow_invariant]
QED

Theorem origin_frame_saved_flow:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  n < LENGTH stk ==>
  origin_local_flow (EL n stk).cf_fn (EL n oms)
Proof
  rpt strip_tac >> drule origin_frame_flow_invariant >> simp[] >>
  simp[LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem origin_frame_current_local_path:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  FLOOKUP om v = SOME (OriginLocal aid,site) ==> bp_flow fn aid v
Proof
  metis_tac[origin_frame_current_flow, origin_local_flow_def]
QED

Theorem origin_frame_saved_local_path:
  origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions /\
  n < LENGTH stk /\ FLOOKUP (EL n oms) v = SOME (OriginLocal aid,site) ==>
  bp_flow (EL n stk).cf_fn aid v
Proof
  metis_tac[origin_frame_saved_flow, origin_local_flow_def]
QED

Theorem frame_reachable_local_flow_witnesses:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY wf_function ctx.ctx_functions ==>
  ?oms om. origin_frame_reachable vs0 ctx stk PG G tn fn inst s oms om /\
    origin_erase om = G /\
    LIST_REL (\f saved. origin_erase saved = f.cf_prov) stk oms /\
    origin_local_flow fn om /\
    LIST_REL (\f saved. origin_local_flow f.cf_fn saved) stk oms
Proof
  rpt strip_tac >> drule frame_reachable_has_origins >> strip_tac >>
  goal_assum (drule_at Any) >>
  drule origin_frame_flow_invariant >> simp[] >>
  drule origin_frame_maps >> rpt strip_tac >> simp[] >>
  gvs[LIST_REL_EL_EQN] >> metis_tac[]
QED
