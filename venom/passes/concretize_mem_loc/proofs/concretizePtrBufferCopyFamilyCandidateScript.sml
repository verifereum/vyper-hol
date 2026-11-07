Theory concretizePtrBufferCopyFamilyCandidate
Ancestors
  concretizePtrBufferCopyFamilyForwardProbe concretizeMemLocDefs
  concretizeMemLocTransitionProofs o1PassContract venomPassDispatcher
  venomInst venomState finite_map list words
  ptrDisciplineEmptyTaint concretizePtrOwnerPath unitMemInv ptrOkCheck
  contextRawReachable contextCodegenRel codegenRel ptrDiscipline
  venomExecSemantics allocaFrontierBound unitTransformDefs
  concretizePtrPairedRoot concretizePtrChronologicalHistory
  concretizePtrPairedFields concretizePtrStagePlacements
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrLifetime concretizePtrPairedPrefix concretizePtrActivationBirths

(* The production pass updates metadata even though this body has no alloca. *)
Theorem ptr_buffer_candidate_function_computation:
  fn = mk_raw_function "main"
    [<|bb_label := "entry"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [fn] (SOME "main") ==>
  concretize_function_fuel_in_context (concretize_memloc_fuel fn) C [] fn =
    SOME (fn with fn_eom := SOME 0)
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem ptr_buffer_candidate_entry_label_exclusion:
  fn = mk_raw_function "main"
    [<|bb_label := "entry"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [fn] (SOME "main") ==>
  ~o1_ctx_shape C
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem ptr_buffer_candidate_main_computation:
  fn = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [fn] (SOME "main") ==>
  concretize_function_fuel_in_context (concretize_memloc_fuel fn) C [] fn =
    SOME (fn with fn_eom := SOME 0)
Proof
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem ptr_buffer_candidate_main_forward:
  fn = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  active_inst fn inst s ==>
  in_revert_forward fn s
Proof
  rpt strip_tac >> gvs[active_inst_def, mk_raw_function_def] >>
  `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1` by decide_tac >>
  gvs[in_revert_forward_def, lookup_block_def, FIND_thm,
      revert_forward_at_def] >-
    (qexists_tac `1` >>
     simp[revert_forward_pair_def, get_instruction_def, mk_inst_def,
          same_after_assigns_def, resolve_block_assigns_def]) >>
  qexists_tac `0` >>
  simp[revert_forward_pair_def, get_instruction_def, mk_inst_def,
       same_after_assigns_def, resolve_block_assigns_def]
QED

Theorem ptr_buffer_candidate_main_pointer_shape:
  fn = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] ==>
  fn_ptr_ok (\nm. set []) fn /\
  fn_ptr_ok (\nm. set []) (reachable_fn fn)
Proof
  strip_tac >>
  `reachable_fn fn = fn` by
    (irule unitShapeDefsTheory.reachable_fn_single_block >>
     gvs[mk_raw_function_def] >> simp[mk_inst_def]) >>
  simp[] >> irule (SRULE [] (Q.SPEC `\nm. []` fn_ptr_ok_check_sound)) >>
  gvs[] >> EVAL_TAC
QED

Theorem ptr_buffer_candidate_main_access:
  fn = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  active_inst fn inst s ==>
  access_ok 0 G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  `in_revert_forward fn s` by metis_tac[ptr_buffer_candidate_main_forward] >>
  gvs[active_inst_def, mk_raw_function_def] >>
  `s.vs_inst_idx = 0 \/ s.vs_inst_idx = 1` by decide_tac >>
  gvs[access_ok_def, taint_ok_def, mk_inst_def, op_taint_def,
      about_to_revert_def, active_inst_def, mk_raw_function_def] >>
  Cases_on `op` >> simp[]
QED

Theorem ptr_buffer_candidate_main_discipline:
  fn = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [fn] (SOME "main") /\
  vs.vs_allocas = FEMPTY ==>
  fixed_region_reserved 0 C /\ ptr_discipline 0 C vs
Proof
  strip_tac >>
  `EVERY (\f. EVERY (\i. allocation_free_opcode i.inst_opcode)
       (fn_insts f)) C.ctx_functions` by (gvs[] >> EVAL_TAC) >>
  `~ctx_has_dalloca C` by (gvs[] >> EVAL_TAC) >>
  simp[fixed_region_reserved_def, ptr_discipline_def] >>
  qexists_tac `\nm. set []` >> conj_tac >-
    (drule ptr_buffer_candidate_main_pointer_shape >>
     gvs[mk_venom_context_def]) >>
  rpt strip_tac >>
  drule allocation_free_frame_reachable >>
  (impl_tac >- gvs[]) >> strip_tac >>
  drule ptr_owner_frame_active >> strip_tac >>
  `fn' = fn` by gvs[mk_venom_context_def] >> gvs[] >>
  simp[allocas_from_def] >>
  metis_tac[ptr_buffer_candidate_main_access]
QED

Theorem ptr_buffer_candidate_main_raw_points:
  !vs C fn inst s. raw_reachable vs C fn inst s ==>
  !f. f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [f] (SOME "main") ==>
  fn = f /\ active_inst fn inst s /\
  s.vs_alloca_next = vs.vs_alloca_next
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >-
    (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     gvs[mk_venom_context_def, lookup_function_def, FIND_thm,
         mk_raw_function_def] >>
     drule enters_block_alloca_fields >> simp[]) >-
    (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     gvs[fn_insts_def, fn_insts_blocks_def, mk_raw_function_def,
         mk_inst_def, is_terminator_def] >>
     gvs[step_inst_non_invoke, step_inst_base_def, eval_operand_def,
         AllCaseEqs()]) >>
  (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
   first_x_assum drule_all >> strip_tac >>
   `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
   gvs[fn_insts_def, fn_insts_blocks_def, mk_raw_function_def,
       mk_inst_def, is_terminator_def] >>
   gvs[step_inst_non_invoke, step_inst_base_def, eval_operand_def,
       AllCaseEqs()])
QED

Theorem ptr_buffer_candidate_main_raw_memory:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [f] (SOME "main") /\
  vs.vs_alloca_next < dimword (:256) ==>
  mem_inv raw_mem_ok C vs
Proof
  strip_tac >> rewrite_tac[mem_inv_raw_reachable] >> conj_tac >-
    (gvs[mk_venom_context_def, lookup_function_def, FIND_thm,
         mk_raw_function_def, fn_entry_label_def, entry_block_def]) >>
  rpt strip_tac >>
  drule ptr_buffer_candidate_main_raw_points >>
  disch_then drule_all >> strip_tac >>
  `in_revert_forward fn s` by metis_tac[ptr_buffer_candidate_main_forward] >>
  gvs[raw_mem_ok_def, inst_mem_ok_in_fn_def, in_revert_forward_def]
QED

Theorem ptr_buffer_candidate_main_target_root:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  g = f with fn_eom := SOME 0 /\
  Ct = mk_venom_context [g] (SOME "main") /\
  t = vs with <|vs_prev_bb := NONE; vs_current_bb := "main";
                vs_inst_idx := 0|> /\
  at = ptr_observe [] [] FEMPTY entry_taint g
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t ==>
  ptr_chrono_history vs Ct [at] at
Proof
  strip_tac >> gvs[] >> irule ptr_chrono_history_entry >>
  simp[mk_venom_context_def, lookup_function_def, FIND_thm,
       mk_raw_function_def, fn_entry_label_def, entry_block_def,
       enters_block_def, lookup_block_def, eval_phis_def,
       phi_prefix_length_def, active_inst_def, mk_inst_def]
QED

Theorem ptr_buffer_candidate_main_target_step:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  g = f with fn_eom := SOME 0 /\
  t.vs_current_bb = "main" /\ t.vs_inst_idx = 0 /\
  t.vs_returndata = [7w] /\
  i = mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [] /\
  at = ptr_observe [] [] FEMPTY entry_taint g i t ==>
  ?zt. ptr_chrono_step Ct at zt
Proof
  strip_tac >>
  `?s'. step_inst 0 Ct i t = OK s' /\
        active_inst g (mk_inst 1 REVERT [Lit 0w; Lit 1w] [])
          (s' with vs_inst_idx := SUC t.vs_inst_idx)` by
    (gvs[step_inst_non_invoke, step_inst_base_def, mk_inst_def,
         eval_operand_def, active_inst_def, mk_raw_function_def,
         write_memory_with_expansion_def]) >>
  qexists_tac `ptr_observe [] [] (step_prov [] FEMPTY i s')
    (step_taint i t s' entry_taint) g
    (mk_inst 1 REVERT [Lit 0w; Lit 1w] [])
    (s' with vs_inst_idx := SUC t.vs_inst_idx)` >>
  qpat_x_assum `at = _` SUBST1_TAC >> irule ptr_chrono_step_next >>
  gvs[active_inst_def, mk_raw_function_def, mk_inst_def,
      is_terminator_def] >> metis_tac[]
QED

Theorem ptr_buffer_candidate_main_paired_root:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  g = f with fn_eom := SOME 0 /\
  C = mk_venom_context [f] (SOME "main") /\
  Ct = mk_venom_context [g] (SOME "main") /\
  vs.vs_vars = FEMPTY /\ vs.vs_allocas = FEMPTY /\
  t = vs with <|vs_prev_bb := NONE; vs_current_bb := "main";
                vs_inst_idx := 0|> /\
  at = ptr_observe [] [] FEMPTY entry_taint g
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t ==>
  ?a. a = ptr_observe [] [] FEMPTY entry_taint f
      (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t /\
    ptr_paired_prefix (\f g. g.fn_name = f.fn_name) (\f. FEMPTY) FEMPTY
      0 vs C Ct [a] a [at] at [] [0] (FEMPTY |+ (0,f)) FEMPTY
      [] FEMPTY [] (FEMPTY |+ (0,0))
      [([0],FEMPTY |+ (0,f),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0))] [] []
Proof
  strip_tac >>
  `ptr_chrono_history vs Ct [at] at` by
    metis_tac[ptr_buffer_candidate_main_target_root] >>
  `ptr_paired_code (\f g. g.fn_name = f.fn_name) (\f. FEMPTY)
      (FEMPTY : (allocation,num # num) fmap) f at.po_fn /\
   ptr_stage_placements Ct FEMPTY /\
   at.po_stack = [] /\ C.ctx_entry = SOME "main" /\
   lookup_function "main" C.ctx_functions = SOME f /\
   first_block_no_phi f /\ fn_inst_wf f /\
   (HD f.fn_blocks).bb_instructions <> [] /\
   ALL_DISTINCT (fn_labels at.po_fn) /\
   (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
     IS_SOME (FLOOKUP ((\f. FEMPTY) f : (allocation,num) fmap) (Allocation inst.inst_id)))` by
    (gvs[ptr_paired_code_def, ptr_stage_placements_def, ptr_observe_def] >>
     EVAL_TAC >> rpt conj_tac >> rpt gen_tac >> CCONTR_TAC >> gvs[]) >>
  `?a. ptr_chrono_history vs C [a] a /\ a.po_fn = f /\
    ptr_paired_prefix (\f g. g.fn_name = f.fn_name)
      (\f. (FEMPTY : (allocation,num) fmap)) FEMPTY 0 vs C Ct
      [a] a [at] at [] [0] (FEMPTY |+ (0,f))
      (ptr_birth_lift 0 a.po_state.vs_allocas) [] FEMPTY []
      (FEMPTY |+ (0,0))
      [([0],FEMPTY |+ (0,f),ptr_birth_lift 0 a.po_state.vs_allocas,
        [],FEMPTY,[],FEMPTY |+ (0,0))] [] []` by
    (irule ptr_paired_root >> metis_tac[]) >>
  qpat_assum `ptr_chrono_history vs C [a] a`
    (mp_then Any strip_assume_tac ptr_chrono_root_inversion) >>
  gvs[fn_entry_label_def, entry_block_def, mk_raw_function_def,
      enters_block_def, active_inst_def, mk_inst_def] >>
  gvs[lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def,
      ptr_observe_def, concretizePtrActivationBirthsTheory.ptr_birth_lift_def]
QED

Theorem ptr_buffer_candidate_main_successor:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  t.vs_current_bb = "main" /\ t.vs_inst_idx = 0 /\
  a = ptr_observe [] [] FEMPTY entry_taint f
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t /\
  ptr_chrono_step C a z ==>
  z.po_inst = mk_inst 1 REVERT [Lit 0w; Lit 1w] [] /\
  z.po_state.vs_allocas = t.vs_allocas /\
  0 IN range_bytes (step_writes a.po_inst a.po_state z.po_state) /\
  (!b. ~ptr_chrono_step C z b)
Proof
  strip_tac >>
  qpat_x_assum `ptr_chrono_step C a z` mp_tac >>
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def, mk_inst_def, is_terminator_def,
      step_writes_def, range_bytes_def, source_memory_write_ranges_def,
      sized_source_write_range_def] >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _`
    (mp_tac o CONV_RULE (computeLib.RESTR_EVAL_CONV
      [``write_memory_with_expansion``, ``halt_state``, ``set_returndata``])) >>
  strip_tac >> gvs[eval_operand_def, AllCaseEqs()] >>
  gvs[active_inst_def, mk_raw_function_def,
      write_memory_with_expansion_def, write_memory_def, step_writes_def,
      range_bytes_def, source_memory_write_ranges_def, sized_source_write_range_def] >>
  qpat_x_assum `ptr_chrono_step C _ b` mp_tac >>
  simp[Once ptr_chrono_step_cases, ptr_observe_def] >> rpt strip_tac >>
  gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_def,
      AllCaseEqs()]
QED

Theorem ptr_buffer_candidate_main_no_extension:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  t.vs_current_bb = "main" /\ t.vs_inst_idx = 0 /\
  t.vs_allocas = FEMPTY /\
  a = ptr_observe [] [] FEMPTY entry_taint f
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t /\
  delta <> [] /\
  snap = ([0],FEMPTY |+ (0,f),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0)) ==>
  ~ptr_paired_prefix R lp positions 0 vs C Ct (a::delta) z [at;zt] zt [0]
    tokens registry births PT TG saved entries (snap::snapshots) calls ws
Proof
  strip_tac >> strip_tac >>
  fs[ptr_paired_prefix_def] >>
  `ptr_chrono_history vs C (a::delta) z` by
    metis_tac[ptr_structural_transcript_erasure, ptr_structural_trace_source] >>
  `ptr_chrono_step C a (HD delta)` by
    (drule ptr_chrono_history_adjacent >>
     disch_then (qspec_then `0` mp_tac) >> Cases_on `delta` >> gvs[]) >>
  `((HD delta).po_inst = mk_inst 1 REVERT [Lit 0w; Lit 1w] []) /\
   (HD delta).po_state.vs_allocas = FEMPTY /\
   0 IN range_bytes (step_writes a.po_inst a.po_state (HD delta).po_state) /\
   (!b. ~ptr_chrono_step C (HD delta) b)` by
    metis_tac[ptr_buffer_candidate_main_successor] >>
  `LENGTH snapshots = LENGTH delta` by
    (drule ptr_structural_transcript_endpoint >> simp[]) >>
  drule ptr_structural_transcript_adjacent >>
  disch_then (qspec_then `0` mp_tac) >>
  Cases_on `delta` >> gvs[] >>
  Cases_on `snapshots` >> gvs[ptr_snapshot_step_def] >>
  strip_tac >>
  rename1 `ptr_snapshot_step C _ _ _ _ next` >>
  PairCases_on `next` >>
  gvs[ptr_snapshot_step_def, ptr_birth_overlay_def, ptr_birth_lift_def] >>
  qpat_x_assum `ptr_paired_writes _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[IMP_CLAUSES] >>
  irule ptr_buffer_forward_ledger_obstruction >>
  simp[ptr_observe_def, mk_inst_def, is_terminator_def] >>
  qexists_tac `0` >> gvs[ptr_observe_def, mk_inst_def]
QED

Theorem ptr_buffer_candidate_main_static:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [f] (SOME "main") /\
  Ct = mk_venom_context [f with fn_eom := SOME 0] (SOME "main") ==>
  o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first ["main"] C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME 0 /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (FEMPTY : (allocation,num) fmap) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions
Proof
  strip_tac >>
  `reachable_fn f = f` by
    (irule unitShapeDefsTheory.reachable_fn_single_block >>
     gvs[mk_raw_function_def] >> simp[mk_inst_def]) >>
  gvs[mk_venom_context_def] >>
  simp[o1_ctx_shape_def, o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
       unitShapeDefsTheory.retpc_shape_ok_def] >>
  EVAL_TAC >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  gvs[fn_insts_blocks_def, fcgDefsTheory.get_invoke_targets_def] >>
  rpt conj_tac >> strip_tac >> gvs[]
QED

Theorem ptr_buffer_candidate_main_stage:
  f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>] /\
  C = mk_venom_context [f] (SOME "main") /\
  Ct = mk_venom_context [f with fn_eom := SOME 0] (SOME "main") ==>
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct
Proof
  strip_tac >> simp[ctx_pass_stage_def, mk_venom_context_def] >>
  qexistsl_tac [`ARB with cu_context := C`,
    `irSupply$init_ir_supply (ARB with cu_context := C)`,
    `<|fpo_function := f with fn_eom := SOME 0; fpo_label_map := [];
       fpo_supply := irSupply$init_ir_supply (ARB with cu_context := C)|>`] >>
  simp[fn_pass_step_def, o1_walk_view_def, walk_view_def,
       venomPassDispatcherTheory.execute_configured_fn_pass_def] >>
  gvs[] >> EVAL_TAC >> simp[EVERY_MEM]
QED

Theorem ptr_buffer_candidate_initial_state:
  vs = (ARB : venom_state) with
    <|vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_halted := F;
      vs_memory := []; vs_alloca_next := 0; vs_fmp := 0w;
      vs_initial_fmp := 0w; vs_code := []; vs_data_section := [];
      vs_labels := FEMPTY |+ ("code_end",0w);
      vs_call_ctx := (ARB with cc_static := F); vs_returndata := [7w]|> ==>
  o1_run_state_ok vs /\ vs.vs_alloca_next < dimword (:256) /\
  vs.vs_vars = FEMPTY /\ vs.vs_allocas = FEMPTY /\ vs.vs_returndata = [7w]
Proof
  strip_tac >> gvs[o1_run_state_ok_def, o1_initial_state_ok_def,
    lowerDloadDefsTheory.code_layout_valid_def] >>
  simp[FLOOKUP_UPDATE]
QED

Theorem ptr_buffer_candidate_shared_witness:
  ?rpolicy C Ct vs a at zt.
  EVERY frameRel$retpc_shape_ok C.ctx_functions /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved 0 C /\ ptr_discipline 0 C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first ["main"] C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME 0 /\
  LIST_REL (ptr_paired_code (\f g. g.fn_name = f.fn_name) (\f. FEMPTY)
    (FEMPTY : (allocation,num # num) fmap)) C.ctx_functions Ct.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (FEMPTY : (allocation,num) fmap) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  (!f g. ptr_paired_code (\f g. g.fn_name = f.fn_name) (\f. FEMPTY)
    (FEMPTY : (allocation,num # num) fmap) f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix (\f g. g.fn_name = f.fn_name) (\f. FEMPTY) FEMPTY
    0 vs C Ct [a] a [at] at [] [0] (FEMPTY |+ (0,a.po_fn)) FEMPTY
    [] FEMPTY [] (FEMPTY |+ (0,0))
    [([0],FEMPTY |+ (0,a.po_fn),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0))] [] [] /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions FEMPTY a.po_inst /\
  ptr_chrono_step Ct at zt /\
  MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  ~(?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix (\f g. g.fn_name = f.fn_name) (\f. FEMPTY) FEMPTY
      0 vs C Ct ([a] ++ delta) z ([at] ++ [zt]) zt ([] ++ [LENGTH [a] - 1])
      tokens' registry' births' PT' TG' saved' entries'
      ([([0],FEMPTY |+ (0,a.po_fn),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0))] ++ snapshots)
      calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions FEMPTY z.po_inst)
Proof
  qabbrev_tac `f = mk_raw_function "main"
    [<|bb_label := "main"; bb_instructions :=
      [mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] [];
       mk_inst 1 REVERT [Lit 0w; Lit 1w] []]|>]` >>
  qabbrev_tac `C = mk_venom_context [f] (SOME "main")` >>
  qabbrev_tac `Ct = mk_venom_context [f with fn_eom := SOME 0] (SOME "main")` >>
  qabbrev_tac `vs = (ARB : venom_state) with
    <|vs_vars := FEMPTY; vs_allocas := FEMPTY; vs_halted := F;
      vs_memory := []; vs_alloca_next := 0; vs_fmp := 0w;
      vs_initial_fmp := 0w; vs_code := []; vs_data_section := [];
      vs_labels := FEMPTY |+ ("code_end",0w);
      vs_call_ctx := (ARB with cc_static := F); vs_returndata := [7w]|>` >>
  qabbrev_tac `t = vs with <|vs_prev_bb := NONE; vs_current_bb := "main"; vs_inst_idx := 0|>` >>
  qabbrev_tac `at = ptr_observe [] [] FEMPTY entry_taint (f with fn_eom := SOME 0)
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t` >>
  `o1_run_state_ok vs /\ vs.vs_alloca_next < dimword (:256) /\
   vs.vs_vars = FEMPTY /\ vs.vs_allocas = FEMPTY /\ vs.vs_returndata = [7w]` by
    (irule ptr_buffer_candidate_initial_state >> simp[Abbr `vs`]) >>
  `?a. a = ptr_observe [] [] FEMPTY entry_taint f
    (mk_inst 0 RETURNDATACOPY [Lit 0w; Lit 0w; Lit 1w] []) t /\
    ptr_paired_prefix (\f g. g.fn_name = f.fn_name) (\f. FEMPTY) FEMPTY
      0 vs C Ct [a] a [at] at [] [0] (FEMPTY |+ (0,f)) FEMPTY
      [] FEMPTY [] (FEMPTY |+ (0,0))
      [([0],FEMPTY |+ (0,f),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0))] [] []` by
    (irule ptr_buffer_candidate_main_paired_root >> simp[Abbr `f`, Abbr `C`, Abbr `Ct`, Abbr `t`, Abbr `at`]) >>
  `?zt. ptr_chrono_step Ct at zt` by
    (irule ptr_buffer_candidate_main_target_step >>
     simp[Abbr `f`, Abbr `at`, Abbr `t`] >>
     qexists_tac `vs with <|vs_prev_bb := NONE; vs_current_bb := "main"; vs_inst_idx := 0|>` >> simp[]) >>
  `EVERY frameRel$retpc_shape_ok C.ctx_functions` by
    (simp[Abbr `C`, Abbr `f`, mk_venom_context_def,
      frameRelTheory.retpc_shape_ok_def] >> EVAL_TAC >>
     rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`ARB`, `C`, `Ct`, `vs`, `a`, `at`, `zt`] >>
  `ctx_pass_stage ARB (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view ARB 2) C Ct` by
    (irule ptr_buffer_candidate_main_stage >> simp[Abbr `f`, Abbr `C`, Abbr `Ct`]) >>
  `mem_inv raw_mem_ok C vs` by
    (irule ptr_buffer_candidate_main_raw_memory >> simp[Abbr `f`, Abbr `C`]) >>
  `fixed_region_reserved 0 C /\ ptr_discipline 0 C vs` by
    (irule ptr_buffer_candidate_main_discipline >> simp[Abbr `f`, Abbr `C`]) >>
  mp_tac ptr_buffer_candidate_main_static >>
  (impl_tac >- simp[Abbr `f`, Abbr `C`, Abbr `Ct`]) >> strip_tac >>
  `a.po_fn = f` by simp[ptr_observe_def] >>
  fs[] >>
  conj_tac >- (simp[Abbr `C`, Abbr `Ct`, ptr_paired_code_def] >>
    simp[Abbr `f`] >> EVAL_TAC >> simp[]) >>
  conj_tac >- simp[ptr_paired_code_def] >>
  simp[ptr_observe_def, mk_inst_def, Abbr `at`, concretize_inst_with_positions_def] >>
  conj_tac >- gvs[ptr_observe_def, mk_inst_def] >>
  rpt gen_tac >> rpt disch_tac >>
  Cases_on `delta = []` >- simp[] >> simp[] >> disj1_tac >>
  irule ptr_buffer_candidate_main_no_extension >>
  simp[Abbr `f`, Abbr `t`, ptr_observe_def, mk_inst_def]
QED

Theorem ptr_buffer_candidate_counterexample:
  ?rpolicy C Ct vs a at zt.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved 0 C /\ ptr_discipline 0 C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first ["main"] C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME 0 /\
  LIST_REL (ptr_paired_code (\f g. g.fn_name = f.fn_name) (\f. FEMPTY)
    (FEMPTY : (allocation,num # num) fmap)) C.ctx_functions Ct.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (FEMPTY : (allocation,num) fmap) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) Ct.ctx_functions /\
  (!f g. ptr_paired_code (\f g. g.fn_name = f.fn_name) (\f. FEMPTY)
    (FEMPTY : (allocation,num # num) fmap) f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix (\f g. g.fn_name = f.fn_name) (\f. FEMPTY) FEMPTY
    0 vs C Ct [a] a [at] at [] [0] (FEMPTY |+ (0,a.po_fn)) FEMPTY
    [] FEMPTY [] (FEMPTY |+ (0,0))
    [([0],FEMPTY |+ (0,a.po_fn),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0))] [] [] /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions FEMPTY a.po_inst /\
  ptr_chrono_step Ct at zt /\
  MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] /\
  ~(?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix (\f g. g.fn_name = f.fn_name) (\f. FEMPTY) FEMPTY
      0 vs C Ct ([a] ++ delta) z ([at] ++ [zt]) zt ([] ++ [LENGTH [a] - 1])
      tokens' registry' births' PT' TG' saved' entries'
      ([([0],FEMPTY |+ (0,a.po_fn),FEMPTY,[],FEMPTY,[],FEMPTY |+ (0,0))] ++ snapshots)
      calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions FEMPTY z.po_inst)
Proof
  mp_tac ptr_buffer_candidate_shared_witness >>
  strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `rpolicy` >> simp[]
QED

Theorem ptr_buffer_copy_frozen_obligation_false:
  ~(!rpolicy C C' vs lo names eom R lp positions h a ht at done tokens
      registry births PT TG saved entries H calls ws zt.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst)
Proof
  strip_tac >>
  qpat_x_assum `!rpolicy C C' vs lo names eom R lp positions h a ht at done tokens registry births PT TG saved entries H calls ws zt. _`
    (mp_tac o BETA_RULE o GEN_ALL o
      Q.INST [`R` |-> `\f g. g.fn_name = f.fn_name`,
              `lp` |-> `\f. (FEMPTY : (allocation,num) fmap)`] o SPEC_ALL) >>
  disch_tac >>
  mp_tac ptr_buffer_candidate_counterexample >> strip_tac >>
  qpat_x_assum `!zt ws vs tokens saved rpolicy registry positions names lo ht h eom entries done calls births at a TG PT H C' C. _`
    (drule_all o SPEC_ALL) >> metis_tac[]
QED

(* This is the frameRel-qualified contract as parsed in the family theory. *)
Theorem ptr_buffer_copy_exact_frozen_obligation_false:
  ~(!rpolicy C C' vs lo names eom R lp positions h a ht at done tokens
      registry births PT TG saved entries H calls ws zt.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ frameRel$retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst)
Proof
  strip_tac >>
  qpat_x_assum `!rpolicy C C' vs lo names eom R lp positions h a ht at done tokens registry births PT TG saved entries H calls ws zt. _`
    (mp_tac o BETA_RULE o GEN_ALL o
      Q.INST [`R` |-> `\f g. g.fn_name = f.fn_name`,
              `lp` |-> `\f. (FEMPTY : (allocation,num) fmap)`] o SPEC_ALL) >>
  disch_tac >>
  mp_tac ptr_buffer_candidate_shared_witness >> strip_tac >>
  `EVERY (\f. fn_inst_wf f /\ frameRel$retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (FEMPTY : (allocation,num) fmap) (Allocation i.inst_id)))) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!zt ws vs tokens saved rpolicy registry positions names lo ht h eom entries done calls births at a TG PT H C' C. _`
    (drule_all o SPEC_ALL) >> metis_tac[]
QED
