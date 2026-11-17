Theory fragGasStraight
Ancestors
  fragGasSeq abiDecoderReentryPointer exprLoweringProps fragExec
  venomInstProofs venomExecSemantics venomState venomInst rich_list list

Theorem concat_straight_gas_path:
  !ctx func sa sb s t.
    fn_has_code sa sb func /\ ~s.vs_halted /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code _ _ _` mp_tac >>
     simp[fn_has_code_def, IS_PREFIX_APPEND] >> rpt strip_tac >>
     gvs[] >> simp[DROP_APPEND]) >>
  rpt conj_tac
  >- (drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      impl_tac >- simp[] >> simp[])
  >- (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
       run_inst_seq_preserves_field)) >>
      qexists_tac `emitted_insts sa sb` >> simp[] >> rpt strip_tac >>
      fs[EVERY_MEM] >>
      metis_tac[venomInstProofsTheory.step_preserves_control_flow,
                venomExecSemanticsTheory.step_inst_non_invoke]) >>
  drule abi_decoder_sequence_halted >> simp[]
QED
