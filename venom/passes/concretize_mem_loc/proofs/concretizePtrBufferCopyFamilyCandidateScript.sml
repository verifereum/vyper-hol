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
