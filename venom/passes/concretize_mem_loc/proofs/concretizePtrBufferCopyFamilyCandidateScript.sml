Theory concretizePtrBufferCopyFamilyCandidate
Ancestors
  concretizePtrBufferCopyFamilyForwardProbe concretizeMemLocDefs
  concretizeMemLocTransitionProofs o1PassContract venomPassDispatcher
  venomInst venomState finite_map list words

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
