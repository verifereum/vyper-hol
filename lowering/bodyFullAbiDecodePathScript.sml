Theory bodyFullAbiDecodePath
Ancestors
  fragGasCopyLoop fragGasSeqPtr fragExecPtr ptrSafetyTransport instMemFrontier
  venomExecSemantics venomInstProofs fragGasOriginPtrLoop
  exprLoweringProps fragExecMem fragExec emitHelperProps list rich_list
  fragGasSeqAbort instIdxIndep fragGasOriginPtr fragGasOrigin
  fragGasPathPtr gasEvents gasCount ptrSafeRun venomState memSafeRun

Theorem abi_decode_emitted_abort_origin_ptr_path:
  fn_has_code st st' func /\ inst_extends st st' /\
  st'.cs_current_bb = st.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) (emitted_insts st st') /\
  run_inst_seq_mem_ok (emitted_insts st st') s /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts st st') s Gf tnf /\
  run_inst_seq (emitted_insts st st') s = Abort a t ==>
  ?j. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn) []
    (Abort a (t with vs_inst_idx := j), Gf, tnf)
Proof
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def, inst_extends_def] >> metis_tac[]) >>
  `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
          emitted_insts st st' = code` by
    (fs[inst_extends_def, IS_PREFIX_APPEND] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
     rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
  metis_tac[run_inst_seq_abort_origin_ptr_uniform]
QED
