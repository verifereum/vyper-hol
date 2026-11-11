(* Registered, call-free allocation observer: a small route probe. *)
Theory exprSimAbiEncodeObserver
Ancestors
  exprSimAbiEncodeContext allocaSiteResource exprLoweringProps
  abiEncoderObserver venomExecSemantics venomExecProofs venomInst
  fcgDefs relation finite_map list words venomState venomMemDefs

Definition abi_encode_alloc_observer_def:
  abi_encode_alloc_observer fn n =
    fn with fn_blocks :=
      [<|bb_label := "entry"; bb_instructions :=
        [mk_inst 0 ALLOCA [Lit n] ["out"]; mk_inst 1 STOP [] []]|>]
End

Definition abi_encode_observer_context_def:
  abi_encode_observer_context ctx fn n =
    ctx with ctx_functions := [abi_encode_alloc_observer fn n]
End

Theorem abi_encode_alloc_observer_no_calls:
  fn_directly_calls (abi_encode_observer_context ctx fn n) a b <=> F
Proof
  simp[fn_directly_calls_def, abi_encode_observer_context_def,
    abi_encode_alloc_observer_def, lookup_function_def, FIND_thm,
    fn_insts_def, fn_insts_blocks_def, mk_inst_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_encode_alloc_observer_no_reach:
  ~TC (fn_directly_calls (abi_encode_observer_context ctx fn n)) a b
Proof
  simp[Once TC_CASES1, abi_encode_alloc_observer_no_calls]
QED

Theorem abi_encode_alloc_observer_room:
  s.vs_alloca_next + pending_alloca_size (abi_encode_alloc_observer fn n) s
    < dimword (:256) ==>
  alloca_room (abi_encode_observer_context ctx fn n)
    (abi_encode_alloc_observer fn n) s
Proof
  simp[alloca_room_def, abi_encode_alloc_observer_no_reach,
    abi_encode_observer_context_def, abi_encode_alloc_observer_def,
    lookup_function_def, FIND_thm]
QED

Theorem abi_encode_alloca_control[local]:
  exec_alloca (mk_inst id ALLOCA [Lit n] [out]) s n = OK t ==>
  t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb
Proof
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (simp[exec_alloca_def, mk_inst_def, update_var_def] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >>
  simp[exec_alloca_def, mk_inst_def, update_var_def] >> strip_tac >> gvs[]
QED

Theorem abi_encode_alloc_observer_step[local]:
  exec_alloca (mk_inst 0 ALLOCA [Lit n] ["out"]) s n = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 ==>
  abi_observer_step ctx (abi_encode_alloc_observer fn n) ("entry",1)
    s (t with vs_inst_idx := 1)
Proof
  strip_tac >> drule abi_encode_alloca_control >> strip_tac >>
  simp[abi_observer_step_def, abi_encode_alloc_observer_def,
       lookup_block_def, get_instruction_def, FIND_thm] >>
  qexists_tac `t` >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       is_terminator_def] >> fs[mk_inst_def]
QED

Theorem abi_encode_alloc_observer_prefix:
  s.vs_alloca_next + pending_alloca_size (abi_encode_alloc_observer fn n) s
    < dimword (:256) /\ alloca_inv s /\
  (!b sz. FLOOKUP s.vs_allocas 0 = SOME (b,sz) ==> sz = w2n n) /\
  ~s.vs_halted /\ s.vs_current_bb = "entry" /\ s.vs_inst_idx = 0 ==>
  ?t b. local_prefix original_ctx (abi_encode_alloc_observer fn n) ("entry",1) s t /\
    lookup_var "out" t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas 0 = SOME (b,w2n n) /\ alloca_inv t
Proof
  strip_tac >>
  `alloca_room (abi_encode_observer_context ctx fn n)
    (abi_encode_alloc_observer fn n) s` by
    (irule abi_encode_alloc_observer_room >> simp[]) >>
  `MEM (mk_inst 0 ALLOCA [Lit n] ["out"])
    (fn_insts (abi_encode_alloc_observer fn n))` by
    simp[abi_encode_alloc_observer_def, fn_insts_def, fn_insts_blocks_def] >>
  drule alloca_site_execute >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def] >> strip_tac >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (irule abi_encode_alloca_control >>
     qexistsl_tac [`0`, `n`, `"out"`] >> simp[mk_inst_def]) >>
  qexistsl_tac [`t with vs_inst_idx := 1`, `b`] >>
  reverse conj_tac
  >- (fs[lookup_var_def, alloca_inv_def, allocas_non_overlapping_def,
        alloca_next_valid_def] >> metis_tac[]) >>
  irule abi_encode_local_prefix_context >>
  qexists_tac `abi_encode_observer_context ctx fn n` >>
  irule (cj 2 local_prefix_rules) >> qexists_tac `t with vs_inst_idx := 1` >>
  conj_tac
  >- (irule abi_encode_alloc_observer_step >> simp[mk_inst_def]) >>
  irule (cj 1 local_prefix_rules) >> simp[]
QED
