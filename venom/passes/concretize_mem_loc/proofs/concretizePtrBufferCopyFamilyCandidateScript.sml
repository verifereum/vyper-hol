Theory concretizePtrBufferCopyFamilyCandidate
Ancestors
  concretizePtrBufferCopyFamilyForwardProbe concretizeMemLocDefs
  concretizeMemLocTransitionProofs o1PassContract venomPassDispatcher
  venomInst venomState finite_map list words
  ptrDisciplineEmptyTaint concretizePtrOwnerPath unitMemInv ptrOkCheck
  contextRawReachable contextCodegenRel codegenRel ptrDiscipline
  venomExecSemantics

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
