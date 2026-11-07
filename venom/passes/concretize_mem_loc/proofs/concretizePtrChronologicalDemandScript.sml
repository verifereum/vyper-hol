Theory concretizePtrChronologicalDemand
Ancestors
  concretizePtrCallAncestry concretizePtrSelectedOrigin concretizePtrWriteByteOrigin
  concretizePtrChronologicalHistory concretizePtrProductionCoverage
  concretizePtrRuntimeGeneration concretizePtrActivationSupport
  concretizeAnalysisScanCoverage concretizeMemLocDefs
  ptrDiscipline pointerConfinedDefs basePtrDefs venomWf venomInst
  list rich_list pred_set finite_map words

Definition ptr_activation_seed_def:
  ptr_activation_seed mems site f <=>
    ?aid. FLOOKUP f.cf_state.vs_allocas aid = SOME site /\
      ml_used_gen (Allocation aid)
        (bp_analyze_fuel (concretize_memloc_fuel f.cf_fn)
          (cfg_analyze f.cf_fn) f.cf_fn) mems f.cf_inst
End

Definition ptr_activation_ready_def:
  ptr_activation_ready P site f <=>
    fn_ptr_ok P f.cf_fn /\ ssa_form f.cf_fn /\ wf_function f.cf_fn /\
    all_reachable f.cf_fn /\ EVERY inst_wf (fn_insts f.cf_fn) /\
    MEM f.cf_inst (fn_insts f.cf_fn) /\
    ptr_site_supported
      (pointer_derived_vars f.cf_fn
        (ptr_frame_site_roots f.cf_fn f.cf_state.vs_allocas f.cf_params site))
      f.cf_prov site
End

Theorem ptr_activation_operand_seed:
  ptr_activation_ready P site f /\
  MEM (Var v) f.cf_inst.inst_operands /\ FLOOKUP f.cf_prov v = SOME site ==>
  ptr_activation_seed mems site f \/ MEM (SOME site) f.cf_params
Proof
  simp[ptr_activation_ready_def] >> strip_tac >>
  drule_all ptr_selected_origin >> strip_tac
  >- (disj1_tac >> simp[ptr_activation_seed_def] >>
      qexists `aid` >> simp[] >>
      irule ptr_production_operand_used_seed >> simp[] >>
      metis_tac[bp_scan_production_complete]) >>
  disj2_tac >> metis_tac[MEM_EL]
QED

Theorem ptr_ancestry_operand_seed:
  !stk f v.
  ptr_call_ancestry f.cf_params stk /\ ptr_activation_ready P site f /\
  EVERY (ptr_activation_ready P site) stk /\
  MEM (Var v) f.cf_inst.inst_operands /\ FLOOKUP f.cf_prov v = SOME site ==>
  ptr_activation_seed mems site f \/
  ?n w. n < LENGTH stk /\
    MEM (Var w) (EL n stk).cf_inst.inst_operands /\
    FLOOKUP (EL n stk).cf_prov w = SOME site /\
    ptr_activation_seed mems site (EL n stk)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (drule_all ptr_activation_operand_seed >>
      gvs[ptr_call_ancestry_def]) >>
  drule_all ptr_activation_operand_seed >>
  disch_then (qspec_then `mems` strip_assume_tac) >- simp[] >>
  `?w. MEM (Var w) h.cf_inst.inst_operands /\ FLOOKUP h.cf_prov w = SOME site` by
    metis_tac[ptr_call_ancestry_import] >>
  `ptr_call_ancestry h.cf_params stk` by metis_tac[ptr_call_ancestry_tail] >>
  gvs[listTheory.EVERY_DEF] >>
  first_x_assum (qspecl_then [`h`,`w`] mp_tac) >> simp[] >> strip_tac
  >- (disj2_tac >> qexistsl [`0`,`w`] >> simp[]) >>
  disj2_tac >> qexistsl [`SUC n`,`w'`] >> simp[]
QED

Theorem ptr_frame_operand_instructions:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  MEM inst (fn_insts fn) /\
  EVERY (\f. MEM f.cf_inst (fn_insts f.cf_fn)) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac >> gvs[] >>
  gvs[contextCodegenRelTheory.active_inst_def, fn_insts_def,
    removeUnusedSsaProofsTheory.fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL]
QED

Theorem ptr_frame_operand_seed:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\
  EVERY all_reachable ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  MEM (Var v) inst.inst_operands /\ FLOOKUP G v = SOME site ==>
  (?aid. FLOOKUP s.vs_allocas aid = SOME site /\
    ml_used_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) mems inst) \/
  (?n aid w. n < LENGTH stk /\
    FLOOKUP (EL n stk).cf_state.vs_allocas aid = SOME site /\
    MEM (Var w) (EL n stk).cf_inst.inst_operands /\
    FLOOKUP (EL n stk).cf_prov w = SOME site /\
    ml_used_gen (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel (EL n stk).cf_fn)
        (cfg_analyze (EL n stk).cf_fn) (EL n stk).cf_fn) mems (EL n stk).cf_inst)
Proof
  strip_tac >>
  drule_all ptr_frame_table_support_invariant >> strip_tac >>
  drule ptr_frame_operand_instructions >> strip_tac >>
  drule ptr_frame_call_ancestry >> strip_tac >>
  qspecl_then [`stk`, `<| cf_fn := fn; cf_inst := inst; cf_state := s;
    cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |>`, `v`]
    mp_tac ptr_ancestry_operand_seed >>
  simp[ptr_activation_ready_def, ptr_activation_seed_def] >>
  impl_tac >- (gvs[EVERY_MEM, ptr_activation_ready_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_chrono_initializing_writer_seed:
  ptr_chrono_history vs0 ctx h endpoint /\
  h = pre ++ [a] ++ tail /\ tail <> [] /\
  a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' /\ x NOTIN endpoint.po_taint.t_mem /\
  ptr_discipline lo ctx vs0 /\ lo <= x /\
  EVERY (\obs. ~in_revert_forward obs.po_fn obs.po_state) h /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\
  EVERY all_reachable ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions ==>
  ?k v b sz. LENGTH pre < k /\ k + 1 < LENGTH h /\
    ptr_chrono_write ctx x (EL k h) /\
    ptr_observation_reachable vs0 ctx (EL k h) /\
    inst_write_op (EL k h).po_inst = SOME (Var v) /\
    FLOOKUP (EL k h).po_prov v = SOME (b,sz) /\ b <= x /\ x < b + sz /\
    ((?aid. FLOOKUP (EL k h).po_state.vs_allocas aid = SOME (b,sz) /\
      ml_used_gen (Allocation aid)
        (bp_analyze_fuel (concretize_memloc_fuel (EL k h).po_fn)
          (cfg_analyze (EL k h).po_fn) (EL k h).po_fn) mems (EL k h).po_inst) \/
     (?n aid w. n < LENGTH (EL k h).po_stack /\
      FLOOKUP (EL n (EL k h).po_stack).cf_state.vs_allocas aid = SOME (b,sz) /\
      MEM (Var w) (EL n (EL k h).po_stack).cf_inst.inst_operands /\
      FLOOKUP (EL n (EL k h).po_stack).cf_prov w = SOME (b,sz) /\
      ml_used_gen (Allocation aid)
        (bp_analyze_fuel (concretize_memloc_fuel (EL n (EL k h).po_stack).cf_fn)
          (cfg_analyze (EL n (EL k h).po_stack).cf_fn)
          (EL n (EL k h).po_stack).cf_fn) mems (EL n (EL k h).po_stack).cf_inst))
Proof
  strip_tac >> drule_all ptr_chrono_fresh_write_index >> strip_tac >>
  qpat_x_assum `h = _` kall_tac >>
  `~in_revert_forward (EL k h).po_fn (EL k h).po_state` by
    (`k < LENGTH h` by decide_tac >> fs[EVERY_EL]) >>
  fs[ptr_observation_reachable_def, ptr_discipline_def] >>
  `access_ok lo (EL k h).po_prov (EL k h).po_fn (EL k h).po_inst (EL k h).po_state` by
    metis_tac[] >>
  `x IN range_bytes (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state)` by
    fs[ptr_chrono_write_def] >>
  drule_all ptr_write_byte_selected_site >> strip_tac >>
  qexistsl [`k`,`v`,`b`,`sz`] >> simp[ptr_observation_reachable_def] >>
  `MEM (Var v) (EL k h).po_inst.inst_operands` by
    (drule ptr_write_op_operand >> simp[]) >>
  `EVERY (fn_ptr_ok P) ctx.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  irule ptr_frame_operand_seed >>
  rpt (goal_assum (drule_at Any))
QED

(* An allocating seed is in the writer activation or a suspended ancestor at
   the chronological writer, not necessarily at the endpoint. Numeric byte
   containment does not identify this aid with the earlier fresh allocation.
   Non-revert coverage remains an explicit obligation for future consumers. *)
