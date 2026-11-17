Theory fmpStageFmpStepsRetSource
Ancestors
  fmpStageReclaimSound fmpStageOpBase ptrDiscipline list

Theorem fmp_stage_saved_source:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    !pre f rest. stk = pre ++ f::rest ==>
    ?tn0.
      tn0.t_var = f.cf_tvar /\
      frame_reachable vs C rest f.cf_params f.cf_prov tn0
        f.cf_fn f.cf_inst f.cf_state /\
      active_inst f.cf_fn f.cf_inst f.cf_state /\
      f.cf_inst.inst_opcode = INVOKE
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> Cases_on `pre` >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >> first_x_assum irule >>
     qexists_tac `f::pre` >> simp[]
QED

Theorem fmp_stage_saved_facts:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C (pre ++ f::rest) PG G tn fn inst s ==>
  ?tn0.
    tn0.t_var = f.cf_tvar /\
    frame_reachable vs C rest f.cf_params f.cf_prov tn0
      f.cf_fn f.cf_inst f.cf_state /\
    active_inst f.cf_fn f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE /\
    MEM f.cf_fn C.ctx_functions /\ MEM f.cf_inst (fn_insts f.cf_fn) /\
    o1_fn_shape C f.cf_fn /\ ssa_form f.cf_fn /\
    make_ssa_input_ok f.cf_fn /\ f.cf_fn.fn_fmp_signature = NONE /\
    pre_fmp_ops f.cf_fn /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts f.cf_fn) /\
    access_ok eom f.cf_prov f.cf_fn f.cf_inst f.cf_state /\
    taint_ok f.cf_fn tn0 f.cf_inst f.cf_state /\
    (?P. EVERY (fn_static_ptr_ok P) C.ctx_functions) /\
    w2n fmp <= fmp_frame_base (w2n fmp) rest /\
    fmp_frame_base (w2n fmp) rest <= w2n f.cf_state.vs_fmp /\
    EVERY (\g. w2n g.cf_state.vs_fmp <= w2n f.cf_state.vs_fmp) rest /\
    (!v b z. FLOOKUP f.cf_prov v = SOME (b,z) /\ 0 < z ==>
       w2n fmp <= b /\ b + z <= w2n f.cf_state.vs_fmp) /\
    EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==>
      b + z <= fmp_frame_base (w2n fmp) rest) f.cf_params
Proof
  strip_tac >> drule fmp_stage_saved_source >>
  disch_then (qspecl_then [`pre`, `f`, `rest`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `tn0` strip_assume_tac) >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  qexists_tac `tn0` >> simp[] >> metis_tac[]
QED
