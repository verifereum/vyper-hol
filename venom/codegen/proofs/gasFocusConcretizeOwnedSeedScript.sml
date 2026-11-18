Theory gasFocusConcretizeOwnedSeed
Ancestors
  concretizePtrTaggedOrigins concretizePtrTaggedCallOrigins
  concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  concretizePtrOwnerPath concretizePtrOperationalOpcodes concretizePtrReadOrigin
  concretizePtrProductionCoverage concretizeAnalysisScanCoverage
  concretizeAnalysisLivenessTransfer concretizePtrKillIdentity
  concretizeMemLocDefs basePtrDefs allocaFrontierBound
  ptrDiscipline pointerConfinedDefs venomWf venomInst list finite_map pred_set arithmetic

Theorem ptr_source_tag_current_allocation_origin:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  fn_inst_wf a.po_fn /\ FLOOKUP TG v = SOME (HD tokens,aid) ==>
  v IN pointer_derived_vars a.po_fn (ptr_bp_alloc_roots a.po_fn aid)
Proof
  strip_tac >>
  `!idx. idx < LENGTH PT ==> EL idx PT <> SOME (HD tokens,aid)` by
    (rpt strip_tac >>
     `MEM (SOME (HD tokens,aid)) PT` by metis_tac[MEM_EL] >>
     drule_all ptr_source_params_fresh_current >> simp[]) >>
  irule (INST_TYPE [alpha |-> ``:num``] ptr_tag_roots_local_wf) >>
  conj_tac >- simp[] >>
  qexistsl [`PT`,`TG`,`HD tokens`] >> simp[] >>
  metis_tac[ptr_source_tag_roots_current]
QED

(* The owner may be suspended at an INVOKE, even when the current access
   is an ordinary memory instruction. The token selects that actual frame. *)
Theorem ptr_source_owned_operand_origin[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY fn_inst_wf C.ctx_functions /\ d <= LENGTH a.po_stack /\
  EL (LENGTH a.po_stack - d) tokens = token /\
  FLOOKUP TG v = SOME (token,aid) /\ MEM (Var v) a.po_inst.inst_operands ==>
  MEM (ptr_owner_view d a).cf_fn C.ctx_functions /\
  MEM (ptr_owner_view d a).cf_inst (fn_insts (ptr_owner_view d a).cf_fn) /\
  ?u. MEM (Var u) (ptr_owner_view d a).cf_inst.inst_operands /\
    u IN pointer_derived_vars (ptr_owner_view d a).cf_fn
      (ptr_bp_alloc_roots (ptr_owner_view d a).cf_fn aid) /\
    (if d = LENGTH a.po_stack then u = v
     else (ptr_owner_view d a).cf_inst.inst_opcode = INVOKE)
Proof
  strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_sound >> strip_tac >>
  `ptr_observation_reachable vs C a` by
    (drule ptr_chrono_history_reachable >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >>
     `MEM a h` by (Cases_on `h` >> gvs[LAST_EL] >> irule EL_MEM >> decide_tac) >>
     fs[EVERY_MEM]) >>
  fs[ptr_observation_reachable_def] >>
  drule ptr_frame_context_membership >> strip_tac >>
  drule ptr_owner_frame_active >> strip_tac >>
  Cases_on `d = LENGTH a.po_stack`
  >- (gvs[ptr_owner_view_def] >>
      `fn_inst_wf a.po_fn` by fs[EVERY_MEM] >>
      conj_tac >- metis_tac[active_inst_mem_fn_insts] >>
      drule_all ptr_source_tag_current_allocation_origin >> simp[]) >>
  qabbrev_tac `i = LENGTH a.po_stack - d - 1` >>
  `i < LENGTH a.po_stack /\ LENGTH a.po_stack - d = SUC i` by
    (simp[Abbr `i`] >> decide_tac) >>
  `MEM (EL i a.po_stack).cf_fn C.ctx_functions /\
   active_inst (EL i a.po_stack).cf_fn (EL i a.po_stack).cf_inst
     (EL i a.po_stack).cf_state /\ (EL i a.po_stack).cf_inst.inst_opcode = INVOKE` by
    fs[EVERY_EL] >>
  `fn_inst_wf (EL i a.po_stack).cf_fn` by fs[EVERY_MEM] >>
  `EL (SUC i) tokens = token` by metis_tac[] >>
  drule_all ptr_source_tagged_owner_call_operand >> strip_tac >>
  `ptr_owner_view d a = EL i a.po_stack` by simp[ptr_owner_view_def, Abbr `i`] >>
  simp[] >> conj_tac >- metis_tac[active_inst_mem_fn_insts] >>
  qexists_tac `u` >> simp[]
QED

Theorem ptr_source_owned_read_seed:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  d <= LENGTH a.po_stack /\ EL (LENGTH a.po_stack - d) tokens = token /\
  FLOOKUP TG v = SOME (token,aid) /\ MEM (Var v) a.po_inst.inst_operands /\
  (inst_read_op a.po_inst = SOME (Var v) \/ a.po_inst.inst_opcode = INVOKE) ==>
  ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d a).cf_fn)
      (cfg_analyze (ptr_owner_view d a).cf_fn) (ptr_owner_view d a).cf_fn)
    mems (ptr_owner_view d a).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_source_owned_operand_origin >> strip_tac >>
  `(inst_read_op (ptr_owner_view d a).cf_inst = SOME (Var u) \/
    (ptr_owner_view d a).cf_inst.inst_opcode = INVOKE)` by
    (Cases_on `d = LENGTH a.po_stack` >> gvs[ptr_owner_view_def]) >>
  irule ptr_production_selected_read_seed >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_source_owned_use_seed:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  EVERY wf_function C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  d <= LENGTH a.po_stack /\ EL (LENGTH a.po_stack - d) tokens = token /\
  FLOOKUP TG v = SOME (token,aid) /\ MEM (Var v) a.po_inst.inst_operands ==>
  ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d a).cf_fn)
      (cfg_analyze (ptr_owner_view d a).cf_fn) (ptr_owner_view d a).cf_fn)
    mems (ptr_owner_view d a).cf_inst
Proof
  strip_tac >> drule_all ptr_source_owned_operand_origin >> strip_tac >>
  qmatch_asmsub_abbrev_tac `u IN pointer_derived_vars f (ptr_bp_alloc_roots f aid)` >>
  `?off. MEM (Ptr (Allocation aid) off)
      (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel f) (cfg_analyze f) f) u)` by
    (irule ptr_bp_production_coverage >> fs[EVERY_MEM] >>
     metis_tac[bp_scan_production_complete]) >>
  simp[ml_used_gen_def, ml_operand_gen_def] >> disj1_tac >>
  qexists_tac `Var u` >> simp[ptr_find_base_member, Abbr `f`] >> metis_tac[]
QED
