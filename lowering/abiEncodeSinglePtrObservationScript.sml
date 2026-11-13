Theory abiEncodeSinglePtrObservation
Ancestors
  exprSimAbiEncodeStagedObserver exprSimAbiEncodeStateTransport
  exprSimAbiEncodeExecFrame abiDecoderGuards exprLoweringProps
  loweringStateRelDefs loweringPosts abiDecoderReentry
  venomState venomMemDefs finite_map words list

val _ = Parse.hide "body";

Theorem abi_encode_phase_endpoint_observation:
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
  window_strong_result ctx func ready body_end len at av d prepared body /\
  abi_encoder_registered_effect {} [(p,32)] body actual /\
  actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
  (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
    eval_operand op actual = SOME v) /\
  st.cs_next_id <= ready.cs_next_id /\
  st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME(p,outsz)) /\
  32+w <= outsz /\ p <= d /\ d+LENGTH(enc at av) <= p+outsz /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\ d = p+32+m /\
  abi_encode_exec_frame func initial actual /\
  LENGTH initial.vs_memory <= LENGTH actual.vs_memory /\
  stmt_state_rel ctx func cenv cx es actual /\
  pure_frame cenv func es st initial actual /\
  FLOOKUP actual.vs_allocas st.cs_next_id = SOME(p,outsz) /\
  p+outsz <= actual.vs_alloca_next /\ actual.vs_alloca_next < dimword (:256) /\
  eval_operand (FST ops) actual = SOME(n2w p) /\
  mload p actual = n2w (LENGTH(enc at av)+m) /\
  mem_bytes_at d (LENGTH(enc at av)) actual.vs_memory = enc at av /\
  (case method_id of NONE => T | SOME mid =>
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) ==>
  abi_encode_staged_observation ctx func cenv cx es st (FST ops) method_id
    outsz p at av initial actual
Proof
  strip_tac >>
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!aid off sz. FLOOKUP initial.vs_allocas aid = SOME(off,sz) /\ aid < st.cs_next_id ==>
    mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz initial.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_caller_phase_old_rows >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists `aid` >> rpt conj_tac >> asm_rewrite_tac []) >>
  `!z v. not_fresh_at st z /\ lookup_var z initial = SOME v ==>
    lookup_var z actual = SOME v` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var z)` by
       (qpat_assum `not_fresh_at st z` mp_tac >>
        simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          not_fresh_at_def, IN_DEF]) >>
     irule abi_encode_caller_phase_registers >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_exec_frame func initial actual` mp_tac >>
  simp_tac bool_ss [abi_encode_exec_frame_def] >> strip_tac >>
  rewrite_tac [abi_encode_staged_observation_def] >>
  rpt conj_tac >> asm_rewrite_tac [] >>
  qpat_assum `pure_frame cenv func es st initial actual` mp_tac >>
  simp_tac bool_ss [pure_frame_def] >> metis_tac[]
QED
