(* Initialization boundaries for the selected allocation relation. *)
Theory lowerDloadSafetyEntry
Ancestors
  lowerDloadSafetyRelation lowerDloadSafetyBoundary lowerDloadSafetyKernel
  ptrDiscipline contextCodegenRel
  o1PassContract unitTransformDefs finite_map list venomExecSemantics lowerDloadDefs

Theorem ld_entry_phis:
  s.vs_prev_bb = NONE /\ eval_phis s insts = OK s' ==>
  s' = s /\ phi_prefix_length insts = 0
Proof
  Cases_on `insts` >> simp[eval_phis_def, phi_prefix_length_def] >>
  strip_tac >> Cases_on `h.inst_opcode = PHI` >>
  gvs[eval_one_phi_def, AllCaseEqs()]
QED

Theorem ld_enters_entry:
  s.vs_prev_bb = NONE /\ s.vs_inst_idx = 0 /\ enters_block fn s s' ==>
  s' = s
Proof
  simp[enters_block_def] >> strip_tac >>
  drule_all ld_entry_phis >> strip_tac >> gvs[]
QED

Theorem ld_envelope_entry:
  s.vs_inst_idx = 0 /\ active_inst fn inst s ==>
  ?X. ld_envelope u fn s 0 X 0
Proof
  simp[active_inst_def, MEM_EL] >> strip_tac >>
  simp[ld_envelope_def, lower_dload_insts_supply_def] >>
  metis_tac[]
QED

Theorem ld_sync_entry:
  o1_run_state_ok vs0 /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s /\ EVERY (fn_ptr_ok P) C.ctx_functions ==>
  ?f. f.lf_fn = fn /\ f.lf_supply = u /\ f.lf_Q = [] /\
    ld_sync lo P C vs0 [] [] FEMPTY entry_taint fn inst s s FEMPTY [f] 1 /\
    ld_global lo FEMPTY [f]
Proof
  strip_tac >>
  `s = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (irule ld_enters_entry >> simp[] >> metis_tac[]) >>
  `frame_reachable vs0 C [] [] FEMPTY entry_taint fn inst s` by
    (irule frame_reachable_entry >> metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule lower_dload_initial_allocations >> strip_tac >>
  `s.vs_inst_idx = 0` by simp[] >>
  drule_all ld_envelope_entry >> disch_then (qspec_then `u` strip_assume_tac) >>
  qexists_tac `<|lf_serial := 0; lf_supply := u; lf_fn := fn;
    lf_src := s; lf_tgt := s; lf_H := FEMPTY; lf_Q := [];
    lf_E := {}; lf_tv := entry_taint.t_var|>` >>
  simp[ld_sync_def, ld_global_def, ld_vars_def, ld_maps_def, ld_intervals_def,
       ld_slots_def, ld_sites_def, ld_charge_def, ld_memory_def,
       fmap_eq_flookup, FLOOKUP_o_f] >>
  metis_tac[]
QED

(* The pointer classification is supplied by the frozen source invariant,
   not an additional assumption on a program's entry. *)
Theorem ld_sync_source_entry:
  o1_src_inv D C vs0 /\ o1_run_state_ok vs0 /\
  C.ctx_entry = SOME name /\ lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s /\
  active_inst fn inst s ==>
  ?lo P f. fixed_region_reserved lo C /\
    ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
    f.lf_fn = fn /\ f.lf_supply = u /\ f.lf_Q = [] /\
    ld_sync lo P C vs0 [] [] FEMPTY entry_taint fn inst s s FEMPTY [f] 1 /\
    ld_global lo FEMPTY [f]
Proof
  strip_tac >>
  `?lo. fixed_region_reserved lo C /\ ptr_discipline lo C vs0` by
    (fs[o1_src_inv_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  drule_all ld_sync_entry >> disch_then (qspecl_then [`u`, `lo`] strip_assume_tac) >>
  metis_tac[]
QED
