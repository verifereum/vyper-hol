(* Physical inspection of the check at the end of the supplied origin path. *)
Theory arrayAbortItinerary
Ancestors
  fragGasOrigin fragGasSeqAbort fragExec instIdxIndep frameGasEvents exprLoweringProps
  venomExecSemantics venomInstProofs venomState venomInst list rich_list arithmetic

Definition array_abort_itinerary_def:
  array_abort_itinerary code func s err raw t <=>
    ?pre check post u bb.
      code = pre ++ check::post /\
      run_inst_seq pre s = OK u /\
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb (s.vs_inst_idx + LENGTH pre) = SOME check /\
      step_inst_base check u = Abort err raw /\
      step_inst_base check (u with vs_inst_idx := s.vs_inst_idx + LENGTH pre) = Abort err t /\
      t = (raw with vs_inst_idx := s.vs_inst_idx + LENGTH pre)
End

Theorem origin_edge_at_array_fetch[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  gas_origin_edge memory E C func s marks r ==>
  marks = [] /\
  r = (case step_inst_base i s of
         OK v => OK (v with vs_inst_idx := SUC s.vs_inst_idx)
       | other => other)
Proof
  simp[gas_origin_edge_def] >> rpt strip_tac >>
  gvs[exit_result_def, step_inst_non_invoke, gas_events_step_plain] >>
  Cases_on `step_inst_base i s` >> gvs[exit_result_def]
QED

Theorem array_seq_keeps_pc[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  (run_inst_seq code s = OK u \/ run_inst_seq code s = Abort err u) ==>
  u.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >>
  qspecl_then [`code`,`s`,`s.vs_inst_idx`] mp_tac run_inst_seq_inst_idx >>
  simp[exec_result_map_def] >>
  disch_then (mp_tac o AP_TERM ``\v:venom_state. v.vs_inst_idx``) >> simp[]
QED

Theorem array_abort_itinerary_prefix[local]:
  ~is_terminator h.inst_opcode /\ step_inst_base h s = OK v /\
  raw.vs_inst_idx = s.vs_inst_idx /\ v.vs_inst_idx = s.vs_inst_idx /\
  v.vs_current_bb = s.vs_current_bb /\
  (!i. MEM i code ==> ~is_terminator i.inst_opcode) /\
  array_abort_itinerary code func (v with vs_inst_idx := SUC s.vs_inst_idx)
    err (raw with vs_inst_idx := SUC s.vs_inst_idx) t ==>
  array_abort_itinerary (h::code) func s err raw t
Proof
  strip_tac >>
  qpat_x_assum `array_abort_itinerary _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [array_abort_itinerary_def]) >>
  disch_then (qx_choosel_then [`apre`,`achk`,`apost`,`au0`,`abb`] strip_assume_tac) >>
  fs[] >> simp[array_abort_itinerary_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) apre /\ ~is_terminator achk.inst_opcode` by
    fs[EVERY_MEM, MEM_APPEND] >>
  qpat_x_assum `run_inst_seq apre _ = OK _` mp_tac >>
  simp[run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq apre v` >> gvs[exec_result_map_def] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  qmatch_asmsub_rename_tac `run_inst_seq apre v = OK au` >>
  `au.vs_inst_idx = s.vs_inst_idx` by metis_tac[array_seq_keeps_pc] >>
  qpat_x_assum `step_inst_base achk (au with vs_inst_idx := SUC _) = Abort _ _` mp_tac >>
  simp[step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base achk au` >> gvs[exec_result_map_def] >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `step_inst_base achk au = Abort err aw` >>
  `aw.vs_inst_idx = s.vs_inst_idx` by
    (`run_inst_seq [achk] au = Abort err aw` by simp[run_inst_seq_def] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) [achk]` by (simp[] >> metis_tac[]) >>
     metis_tac[array_seq_keeps_pc]) >>
  `aw = raw` by
    (qpat_x_assum `(aw with vs_inst_idx := _) = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  qexistsl_tac [`h::apre`, `achk`, `apost`, `au`] >>
  fs[run_inst_seq_def, ADD_CLAUSES]
QED

Theorem run_inst_seq_abort_itinerary:
  !code s raw t bb.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> GAS) code /\
    run_inst_seq code s = Abort err raw /\
    gas_origin_path T E C func s [] (Abort err t) ==>
    array_abort_itinerary code func s err raw t
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >> drule instruction_prefix_cursor >>
  strip_tac >> fs[Once EVERY_DEF] >>
  qpat_x_assum `gas_origin_path T _ _ _ _ [] _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [Once gas_origin_path_cases])
  >- (drule_all origin_edge_at_array_fetch >> strip_tac >>
      Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
      rename1 `step_inst_base h s = OK v` >>
      `v.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      `run_inst_seq code (v with vs_inst_idx := SUC s.vs_inst_idx) =
         Abort err (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      `lookup_block (v with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
         func.fn_blocks = SOME bb` by simp[] >>
      `code ≼ DROP (v with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
         bb.bb_instructions` by simp[] >>
      first_x_assum drule_all >> disch_then assume_tac >>
      `v.vs_inst_idx = s.vs_inst_idx` by
        (`run_inst_seq [h] s = OK v` by simp[run_inst_seq_def] >>
         `EVERY (\i. ~is_terminator i.inst_opcode) [h]` by simp[] >>
         metis_tac[array_seq_keeps_pc]) >>
      `raw.vs_inst_idx = v.vs_inst_idx` by metis_tac[array_seq_keeps_pc] >>
      irule array_abort_itinerary_prefix >> simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all origin_edge_at_array_fetch >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  qmatch_asmsub_rename_tac `step_inst_base h s = Abort aerr raw` >>
  `raw.vs_inst_idx = s.vs_inst_idx` by
    (`run_inst_seq [h] s = Abort aerr raw` by simp[run_inst_seq_def] >>
     `EVERY (\i. ~is_terminator i.inst_opcode) [h]` by simp[] >>
     metis_tac[array_seq_keeps_pc]) >>
  simp[array_abort_itinerary_def] >>
  qexistsl_tac [`[]`,`h`,`code`,`s`] >>
  simp[run_inst_seq_def, venom_state_component_equality]
QED
