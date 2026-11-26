(* The linked Array rounds consume one saved Entry descriptor. *)
Theory bodyForArrayRoundDriverMods
Ancestors
  bodyForArrayEntryMods bodyForRoundsBindMods
  bodyForArrayNilExitMods bodyForArrayBodyLandingMods
  bodyForArrayHeadLandingMods bodyForArrayIncrementMods
  bodyForArraySlotItemMods bodyForArraySnapshotItemMods
  bodyForArraySavedFrameMods bodyForArrayControlMods bodyForArrayRouteMods
  gasOutcomeFullMods gasOutcomeFullPostMods gasContext
  bodyFullPostsMods bodyFullPredsMods loweringPosts
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  compileEnv stmtSimProps stmtSimDefs finite_map list words arithmetic
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem for_array_round_continuation_mods:
  storage_trace_domain cx st0 ee0.storage_trace /\
  ~s0.vs_halted /\
  (!H. valid_horizon cx st0 H ee0.storage_trace ==>
       for_array_entry_mods mods machine cx env st0 outer layout
         H vs ee0 G0 tn0 s0) /\
  gas_admissible (eval_for cx tyv nm body vs) ok ee0 /\
  (!saved.
    (!es s G tn.
      ~s.vs_halted /\ storage_trace_domain cx st0 es.storage_trace /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
         for_array_entry_header_mods mods machine cx env st0 outer layout
           saved H vs [] es G tn s) /\
      gas_admissible (eval_for cx tyv nm body []) ok es ==>
      ?t G1 tn1. !H. valid_horizon cx st0 H es.storage_trace ==>
        gas_origin_ptr_path
          (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
        Done H (es with gas_obs := []) G1 tn1 t) /\
    (!a rs es s G tn.
      ~s.vs_halted /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
         for_array_entry_header_mods mods machine cx env st0 outer layout
           saved H vs (a::rs) es G tn s) /\
      gas_admissible (eval_for cx tyv nm body (a::rs)) ok es ==>
      gas_outcome_full_mods
        (DF,lo,explicit,ctx,func,PG) mods cx st0
        (do v <- read_result cx a;
            push_scope_with_var nm tyv v;
            finally (try (do eval_stmts cx body; return F od)
                         handle_loop_exception) pop_scope od)
        (es,s,G,tn)
        (\H res ee G1 tn1 t.
          ee.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b /\
          (b ==> Done H ee G1 tn1 t) /\
          (~b ==> for_array_entry_header_mods mods machine cx env st0 outer layout
                    saved H vs rs ee G1 tn1 t))
        (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r))) ==>
  gas_outcome_full_mods
    (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_for cx tyv nm body vs) (ee0,s0,G0,tn0)
    (\H res ee G1 tn1 t. res = INL () /\ Done H ee G1 tn1 t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >>
  drule_all_then (qx_choosel_then [`saved`] strip_assume_tac)
    for_array_entry_extract_mods >>
  qabbrev_tac `InvX = \H rs es G tn s.
    for_array_entry_header_mods mods machine cx env st0 outer layout
      saved H vs rs es G tn s` >>
  qabbrev_tac `DoneX = \H ee G tn t. Done H ee G tn t` >>
  qabbrev_tac `RX = \H ex ee gt r. R H ex ee gt r` >>
  qpat_assum `!saved. _` (qspecl_then [`saved`] strip_assume_tac) >>
  irule (Q.INST [`Inv` |-> `InvX`, `Done` |-> `DoneX`, `R` |-> `RX`, `ok` |-> `ok`]
    for_rounds_bind_mods) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`InvX`,`ok`] >>
  conj_tac >-
    (simp[Abbr `InvX`, Abbr `DoneX`, Abbr `RX`] >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[Abbr `InvX`] >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (simp[Abbr `InvX`] >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
