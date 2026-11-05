(* Syntactic regional certificates, with retained code outside the region unrestricted. *)
Theory exprSimAbiEncodeControl
Ancestors
  abiEncoderObserver opcodeClass venomStepProps venomInstProps venomExecProofs
  venomState venomExecSemantics venomInst list

Definition encode_region_target_def:
  encode_region_target blocks R lbl <=>
    (lbl,0) IN R /\ ?bb. lookup_block lbl blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0
End

Definition encode_region_certificate_def:
  encode_region_certificate blocks cut R <=>
    (?bb id. lookup_block (FST cut) blocks = SOME bb /\
       get_instruction bb (SND cut) = SOME (mk_inst id STOP [] [])) /\
    (!lbl idx. (lbl,idx) IN R /\ (lbl,idx) <> cut ==>
      ?bb inst. lookup_block lbl blocks = SOME bb /\
        get_instruction bb idx = SOME inst /\
        MEM inst.inst_opcode
          [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; AND; MCOPY; JMP; JNZ]) /\
    (!lbl idx bb inst. (lbl,idx) IN R /\ (lbl,idx) <> cut /\
      lookup_block lbl blocks = SOME bb /\ get_instruction bb idx = SOME inst ==>
      if is_terminator inst.inst_opcode then
        ((?dest. inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
           encode_region_target blocks R dest) \/
         (?v yes no. inst.inst_opcode = JNZ /\
           inst.inst_operands = [v;Label yes;Label no] /\
           encode_region_target blocks R yes /\ encode_region_target blocks R no))
      else (lbl,SUC idx) IN R)
End

Theorem encode_region_inventory:
  encode_region_certificate blocks cut R /\
  (lbl,idx) IN R /\ (lbl,idx) <> cut /\
  lookup_block lbl blocks = SOME bb /\ get_instruction bb idx = SOME inst ==>
  MEM inst.inst_opcode
    [ALLOCA; ADD; MSTORE; MLOAD; MUL; LT; ISZERO; AND; MCOPY; JMP; JNZ]
Proof
  simp[encode_region_certificate_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem encode_region_control:
  encode_region_certificate blocks cut R /\
  (lbl,idx) IN R /\ (lbl,idx) <> cut /\
  lookup_block lbl blocks = SOME bb /\ get_instruction bb idx = SOME inst ==>
  if is_terminator inst.inst_opcode then
    ((?dest. inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
       encode_region_target blocks R dest) \/
     (?v yes no. inst.inst_opcode = JNZ /\
       inst.inst_operands = [v;Label yes;Label no] /\
       encode_region_target blocks R yes /\ encode_region_target blocks R no))
  else (lbl,SUC idx) IN R
Proof
  simp[encode_region_certificate_def]
QED

Theorem encode_region_safe:
  encode_region_certificate fn.fn_blocks cut R ==>
  observer_region_safe fn cut R
Proof
  strip_tac >> rw[observer_region_safe_def]
  >- (gvs[encode_region_certificate_def] >> metis_tac[]) >>
  drule_all encode_region_inventory >> strip_tac >>
  rpt conj_tac
  >- gvs[]
  >- (rpt strip_tac >> spose_not_then assume_tac >>
      drule step_inst_base_halt_opcodes >> gvs[]) >>
  rpt strip_tac >> drule step_inst_base_ok_halted >> simp[]
QED

Theorem encode_region_closed:
  encode_region_certificate fn.fn_blocks cut R ==>
  observer_region_closed ctx fn cut R
Proof
  strip_tac >> rw[observer_region_closed_def, abi_observer_step_def]
  >- (drule_all encode_region_control >> simp[] >> strip_tac >>
      drule step_preserves_control_flow >> simp[] >> strip_tac >> gvs[]) >>
  drule_all encode_region_control >> simp[] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(),
      eval_operand_def, jump_to_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
  metis_tac[encode_region_target_def, optionTheory.SOME_11]
QED
