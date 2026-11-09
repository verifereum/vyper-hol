(* Transfer from an explicitly executed initializer to its actual loop header. *)
Theory calldataInitEntry
Ancestors
  calldataInitSequence calldataDynOwned calldataDynInit safeSequence fragExecMem
  emitHelperProps exprLoweringProps abiDecoderLoopEmit venomState

Theorem calldata_executed_init_to_header:
  loop_st.cs_blocks = st.cs_blocks /\
  loop_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st loop_st) /\
  (!pre i post u. emitted_insts st loop_st = pre ++ i::post /\
    run_inst_seq pre initial = OK u ==> inst_mem_below_frontier i u) /\
  run_inst_seq (emitted_insts st loop_st) initial = OK t /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st =
    ((hdr,body_lbl,exit_lbl),end_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st end_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ~t.vs_halted /\
  (!fuel r. run_from fuel ctx fn (jump_to hdr t) = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn initial = r /\
      (mem_safe_run fuel ctx fn (jump_to hdr t) ==>
       mem_safe_run fuel' ctx fn initial))
Proof
  strip_tac >>
  `frag_exec_mem ctx st loop_st (\s. s = initial)
    (\u. u = t with vs_inst_idx := LENGTH loop_st.cs_current_insts) (K F)` by
    (irule safeSequenceTheory.frag_exec_mem_run_inst_seq >>
     asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     disj1_tac >> qexists_tac `t` >> simp[]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >> strip_tac >>
  drule calldata_loop_prefix_entry_safe >> disch_then drule >>
  disch_then (qspecl_then [`t with vs_inst_idx := LENGTH loop_st.cs_current_insts`,
    `ctx`] mp_tac) >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [jump_to_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn
    (t with vs_inst_idx := _) = _ /\ _`
    (qspec_then `fuel` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx fn initial = _ /\ _`
    (qspec_then `fuel'` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexists_tac `fuel''` >> simp[]
QED
