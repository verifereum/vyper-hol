(*
 * Every instruction but CALL and STATICCALL against the frame's run:
 * the single-context steps (asmEvmStepStarve, asmEvmGasStep) moved into
 * the nested frame (evmStepTransplant), with the frame's trace and
 * run_call carried across the step (frameObsStep).
 *
 * TOP-LEVEL:
 *   asm_frame_local_step
 *)

Theory asmFrameLocalStep
Ancestors
  asmFrameRel frameObsStep evmStepTransplant asmEvmStepStarve asmEvmGasStep
  evmStepSim asmDataSuffixProps codegenRel asmSem asmWf symbolResolve
  callTrace frameOutcome vfmExecution vfmExecutionProp list rich_list vfmOperation alist asmEncodeParse

Theorem frame_rel_singleton[local]:
  asm_evm_rel p a es /\ es.contexts = (c,rb)::rest ==>
  asm_evm_rel p a (es with contexts := [(c,rb)])
Proof
  strip_tac >> gvs[asm_evm_rel_def]
QED

Theorem frame_rel_output_to[local]:
  asm_evm_rel p a es /\ es.contexts = (c,rb)::rest ==>
  !addr. c.msgParams.outputTo <> Code addr
Proof
  strip_tac >> gvs[asm_evm_rel_def]
QED

Theorem frame_local_instruction[local]:
  asm_frame_prog_ok prog /\ i < LENGTH prog /\
  ~is_data_inst (EL i prog) /\
  EL i prog <> AsmOp "CALL" /\ EL i prog <> AsmOp "STATICCALL" ==>
  asm_encoding_wf prog /\
  (!j. j <= i ==> ~is_data_inst (EL j prog)) /\
  (!name. EL i prog = AsmOp name ==> ~is_evm_call_name name)
Proof
  simp[asm_frame_prog_ok_def, is_evm_call_name_def] >> metis_tac[]
QED

Theorem frame_next_opcode[local]:
  asm_frame_prog_ok prog /\
  asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  es.contexts = (c,rb)::rest /\ a.as_pc < LENGTH prog /\
  ~is_data_inst (EL a.as_pc prog) ==>
  ?op. next_opcode c = SOME op /\ wf_opname op /\
    opcode op = encode_inst (SND (compute_label_offsets
      (prog ++ [AsmDataItem data]))) (EL a.as_pc prog)
Proof
  strip_tac >>
  `asm_evm_rel (prog ++ [AsmDataItem data]) a
    (es with contexts := [(c,rb)])` by metis_tac[frame_rel_singleton] >>
  `asm_encoding_wf prog /\
   (!j. j <= a.as_pc ==> ~is_data_inst (EL j prog))` by
    metis_tac[asm_frame_prog_ok_def] >>
  `asm_encoding_wf (prog ++ [AsmDataItem data])` by
    metis_tac[data_suffix_encoding_wf] >>
  `a.as_pc < LENGTH (prog ++ [AsmDataItem data])` by simp[] >>
  `!j. j <= a.as_pc ==>
       ~is_data_inst (EL j (prog ++ [AsmDataItem data]))` by
    (gen_tac >> disch_tac >> `j < LENGTH prog` by decide_tac >>
     simp[EL_APPEND1]) >>
  `LENGTH (es with contexts := [(c,rb)]).contexts = 1` by simp[] >>
  `~is_data_inst (EL a.as_pc (prog ++ [AsmDataItem data]))` by
    simp[EL_APPEND1] >>
  drule_all asm_evm_step_setup >>
  simp[EL_APPEND1] >> strip_tac >> gvs[] >>
  simp[next_opcode_def] >> metis_tac[]
QED

Theorem frame_encode_system[local]:
  ~is_data_inst inst /\
  MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2; Gas] /\
  opcode op = encode_inst offsets inst ==>
  (inst = AsmOp "CALL" /\ op = Call) \/
  (inst = AsmOp "STATICCALL" /\ op = StaticCall) \/
  (inst = AsmOp "DELEGATECALL" /\ op = DelegateCall) \/
  (inst = AsmOp "CREATE" /\ op = Create) \/
  (inst = AsmOp "CREATE2" /\ op = Create2) \/
  (inst = AsmOp "GAS" /\ op = Gas)
Proof
  Cases_on `inst`
  >- (simp[encode_inst_def] >> strip_tac >>
      gvs[opcode_def, AllCaseEqs(), evm_opcode_byte_def] >>
      drule ALOOKUP_MEM >>
      qpat_x_assum `ALOOKUP _ _ = _` kall_tac >>
      simp_tac std_ss [evm_opcode_table_def, MEM, pairTheory.PAIR_EQ,
        wordsTheory.n2w_11, wordsTheory.dimword_8]) >>
  strip_tac >>
  gvs[is_data_inst_def, encode_inst_def, opcode_def,
      AllCaseEqs(), wordsTheory.dimword_8] >>
  Cases_on `l` >> gvs[encode_inst_def, wordsTheory.dimword_8]
QED

Theorem frame_local_opcode[local]:
  asm_frame_prog_ok prog /\
  asm_evm_rel (prog ++ [AsmDataItem data]) a es /\
  es.contexts = (c,rb)::rest /\ a.as_pc < LENGTH prog /\
  ~is_data_inst (EL a.as_pc prog) /\
  EL a.as_pc prog <> AsmOp "CALL" /\
  EL a.as_pc prog <> AsmOp "STATICCALL" ==>
  (!op. next_opcode c = SOME op ==>
     ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  ~observable_call c /\
  (next_opcode c = SOME Gas <=> EL a.as_pc prog = AsmOp "GAS")
Proof
  strip_tac >> drule_all frame_next_opcode >> strip_tac >>
  `~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]` by
    (strip_tac >>
     `MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2; Gas]`
       by gvs[] >>
     drule_all frame_encode_system >>
     gvs[asm_frame_prog_ok_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  conj_tac >- (gvs[observable_call_def] >> metis_tac[]) >>
  simp[] >>
  eq_tac
  >- (strip_tac >>
      `MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2; Gas]`
        by simp[] >>
      drule_all frame_encode_system >> gvs[]) >>
  strip_tac >> gvs[] >>
  `opcode op = opcode Gas` by
    gvs[encode_inst_def, evm_opcode_byte_def, evm_opcode_table_def, opcode_def] >>
  `op = Gas` by (irule opcode_wf_inj >> simp[wf_opname_def]) >> simp[]
QED

Theorem asm_frame_local_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
  EL as.as_pc prog <> AsmOp "CALL" /\ EL as.as_pc prog <> AsmOp "STATICCALL" ==>
  asm_frame_step_ok prog data es0 as es
Proof
  cheat
QED
