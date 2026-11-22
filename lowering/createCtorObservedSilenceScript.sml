(* A silent execution determines the marks of any observed first arrival. *)
Theory createCtorObservedSilence
Ancestors
  createMarkedPath fragGasOrigin fragExec gasEventsFuel
  venomExecSemantics venomExecProofs venomState list pair relation arithmetic

Theorem ctor_origin_ok_view[local]:
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  gas_origin_edge memory explicit ctx fn s marks (OK t) ==>
  ?fuel bb inst mid.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK mid /\
    marks = MAP (\key. key IN explicit) (gas_events_step fuel ctx fn.fn_name inst s) /\
    t = (mid with vs_inst_idx :=
          if is_terminator inst.inst_opcode then 0 else SUC s.vs_inst_idx)
Proof
  simp[gas_origin_edge_def, exit_result_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `fuel` strip_assume_tac))) >>
  qexists_tac `fuel` >> gvs[] >>
  TRY (qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
       gvs[exit_result_def] >> NO_TAC) >>
  TRY (gvs[jump_to_def] >> NO_TAC) >>
  `phi_prefix_length target.bb_instructions = 0` by
    metis_tac[lookup_block_MEM] >>
  gvs[eval_phis_no_phi]
QED

Theorem ctor_successful_step_fuels[local]:
  step_inst a ctx inst s = OK u /\ step_inst b ctx inst s = OK v ==>
  u = v /\ gas_events_step a ctx owner inst s = gas_events_step b ctx owner inst s
Proof
  strip_tac >>
  Cases_on `a <= b`
  >- (qspecl_then [`a`, `ctx`, `owner`, `inst`, `s`, `b`] mp_tac
        (cj 1 gas_events_fuel_extension) >> simp[]) >>
  `b <= a` by decide_tac >>
  qspecl_then [`b`, `ctx`, `owner`, `inst`, `s`, `a`] mp_tac
    (cj 1 gas_events_fuel_extension) >> simp[] >> metis_tac[]
QED

Theorem ctor_origin_ok_unique[local]:
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  gas_origin_edge memory explicit ctx fn s ms (OK u) /\
  gas_origin_edge memory' explicit ctx fn s ns (OK v) ==>
  u = v /\ ms = ns
Proof
  strip_tac >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ (OK v)` (fn th =>
    drule_all ctor_origin_ok_view >> strip_tac >> assume_tac th) >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ (OK u)` kall_tac >>
  drule_all ctor_origin_ok_view >> strip_tac >>
  gvs[] >>
  `mid = mid' /\
   gas_events_step fuel ctx fn.fn_name inst s =
   gas_events_step fuel' ctx fn.fn_name inst s` by
    metis_tac[ctor_successful_step_fuels] >>
  gvs[]
QED

Theorem ctor_observed_cut_silent_aux[local]:
  !x y. RTC (create_marked_edge
    (\p ms q. (p.vs_current_bb,p.vs_inst_idx) <> cut /\
              gas_origin_edge F explicit ctx fn p ms (OK q))) x y ==>
    (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (t.vs_current_bb,t.vs_inst_idx) = cut /\
    gas_origin_path T explicit ctx fn (FST x) [] (OK t) ==>
    SND y = SND x
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  map_every qx_gen_tac [`x`,`y`,`z`] >>
  map_every PairCases_on [`x`,`y`,`z`] >>
  simp[create_marked_edge_def, PULL_EXISTS] >> rpt strip_tac >>
  qpat_x_assum `gas_origin_path T _ _ _ _ [] (OK _)` mp_tac >>
  simp[Once gas_origin_path_cases, exit_result_def] >> strip_tac
  >- gvs[] >>
  gvs[] >>
  `y0 = mid /\ ms = []` by metis_tac[ctor_origin_ok_unique] >>
  gvs[]
QED

Theorem ctor_observed_cut_silent:
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  RTC (create_marked_edge
    (\p ms q. (p.vs_current_bb,p.vs_inst_idx) <> cut /\
              gas_origin_edge F explicit ctx fn p ms (OK q))) (u,[]) (t,observed) /\
  (t.vs_current_bb,t.vs_inst_idx) = cut /\
  gas_origin_path T explicit ctx fn u [] (OK t) ==>
  observed = []
Proof
  strip_tac >> drule ctor_observed_cut_silent_aux >> simp[] >> metis_tac[]
QED
