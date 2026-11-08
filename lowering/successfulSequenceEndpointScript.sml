(* One successful straight-line endpoint, with independent memory pullback. *)
Theory successfulSequenceEndpoint
Ancestors
  abiDecoderReentryPointer fragExecMem fragExec safeSequence rich_list compileEnv emitHelperProps exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Theorem sequence_all_fuel_pullback[local]:
  inst_extends st ready /\ fn_has_code st ready fn /\
  ready.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st ready) /\
  run_inst_seq_mem_ok (emitted_insts st ready) s /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((!fuel. mem_safe_run fuel ctx fn
    (t with vs_inst_idx := LENGTH ready.cs_current_insts)) ==>
   !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX ready.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `?xs. ready.cs_current_insts = st.cs_current_insts ++ xs /\
    emitted_insts st ready = xs` by
    (fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_LENGTH_APPEND]) >>
  strip_tac >> gen_tac >>
  qspecl_then [`xs`, `s`, `fuel`, `ctx`, `fn`, `bb`] mp_tac mem_safe_run_inst_seq >>
  asm_rewrite_tac[] >>
  (impl_tac >- (fs[IS_PREFIX_APPEND] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[])) >>
  disch_then (irule o CONJUNCT1) >> qexists_tac `t` >> gvs[]
QED

Theorem successful_sequence_endpoint:
  inst_extends st ready /\ fn_has_code st ready fn /\
  ready.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st ready) /\
  run_inst_seq_mem_ok (emitted_insts st ready) s /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  P (t with vs_inst_idx := LENGTH ready.cs_current_insts) ==>
  let endpoint = t with vs_inst_idx := LENGTH ready.cs_current_insts in
    P endpoint /\ ~endpoint.vs_halted /\
    endpoint.vs_current_bb = ready.cs_current_bb /\
    endpoint.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ((!fuel. mem_safe_run fuel ctx fn endpoint) ==> !fuel. mem_safe_run fuel ctx fn s) /\
    (!fuel r. run_from fuel ctx fn endpoint = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn endpoint ==> mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `((!fuel. mem_safe_run fuel ctx fn
      (t with vs_inst_idx := LENGTH ready.cs_current_insts)) ==>
    !fuel. mem_safe_run fuel ctx fn s)` by
    (mp_tac (SPEC_ALL sequence_all_fuel_pullback) >> asm_rewrite_tac[]) >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX ready.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `?xs. ready.cs_current_insts = st.cs_current_insts ++ xs /\
    emitted_insts st ready = xs` by
    (fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_LENGTH_APPEND]) >>
  `isPREFIX xs (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  `!fuel. t.vs_current_bb = s.vs_current_bb /\
    exec_block fuel ctx bb s = exec_block fuel ctx bb
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs)` by
    (gen_tac >> qspecl_then [`xs`, `s`, `fuel`, `ctx`, `bb`] mp_tac
      exec_block_run_inst_seq >> gvs[]) >>
  `t.vs_halted = s.vs_halted` by metis_tac[abi_decoder_sequence_halted] >>
  asm_simp_tac (srw_ss()) [] >> rpt strip_tac >>
  qexists_tac `fuel` >> conj_tac
  >- gvs[run_from_def] >>
  qspecl_then [`xs`, `s`, `fuel`, `ctx`, `fn`, `bb`] mp_tac
    mem_safe_run_inst_seq >> gvs[] >> metis_tac[]
QED
