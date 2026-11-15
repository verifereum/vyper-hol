(* Pure decoding boundary for the cheap instruction complement. *)
Theory asmCheapOpcodeClassify
Ancestors asmEncodeParse asmToBytecodeProofs symbolResolve vfmOperation asmWf vfmExecution

Theorem cheap_asmop_classify:
  wf_opname op /\ opcode op = encode_inst offsets (AsmOp name) /\
  IS_SOME (evm_opcode_byte name) /\
  ~MEM name ["RETURNDATACOPY";"CREATE";"CREATE2";"DELEGATECALL";
    "SELFDESTRUCT";"CALL";"STATICCALL";"SLOAD";"SSTORE";"TLOAD";"TSTORE";
    "MLOAD";"MSTORE";"MSTORE8";"SHA3";"RETURN";"REVERT";"CALLDATACOPY";
    "CODECOPY";"EXTCODECOPY";"MCOPY";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] ==>
  MEM op [Add; Mul; Sub; Div; SDiv; Mod; SMod; AddMod; MulMod;
    SignExtend; LT; GT; SLT; SGT; Eq; IsZero; And; Or; XOr; Not; Byte;
    ShL; ShR; SAR; CLZ] \/
  (op = Pop \/ (?n ws. op = Push n ws) \/ (?n. op = Dup n) \/
    (?n. op = Swap n)) \/
  MEM op [Address; Origin; Caller; CallValue; CallDataSize; CodeSize;
    GasPrice; ReturnDataSize; CoinBase; TimeStamp; Number; PrevRandao;
    GasLimit; ChainId; BaseFee; BlobBaseFee; PC; MSize; Gas] \/
  MEM op [Jump; JumpI; JumpDest; Stop; Invalid] \/
  MEM op [CallDataLoad; BlockHash; BlobHash; SelfBalance] \/
  MEM op [Balance; ExtCodeSize; ExtCodeHash] \/ op = Exp
Proof
  Cases_on `op` >> CONV_TAC (RAND_CONV (SIMP_CONV (srw_ss()) [listTheory.MEM])) >>
  simp[] >> strip_tac >>
  gvs[encode_inst_def, opcode_def, AllCaseEqs()] >>
  fs[evm_opcode_byte_def] >>
  drule alistTheory.ALOOKUP_MEM >>
  all_tac
  >~ [`MEM (name,32w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,55w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,57w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,60w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,62w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,81w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,82w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,83w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,84w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,85w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,92w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,93w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,94w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,240w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,241w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,243w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,244w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,245w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,250w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,253w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8]
  >~ [`MEM (name,255w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8] >>
  all_tac
  >~ [`MEM (name,242w) _ ==> _`] >- simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def, wordsTheory.dimindex_8] >>
  Cases_on `n <= 4` >- (
    `n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4` by decide_tac >>
    gvs[wordsTheory.word_add_n2w] >> simp[evm_opcode_table_def, listTheory.MEM,
      wordsTheory.dimword_def, wordsTheory.dimindex_8]) >> simp[]
QED

Theorem cheap_non_asmop_classify:
  encoding_wf_inst inst offsets /\ ~is_data_inst inst /\
  (!name. inst <> AsmOp name) /\ wf_opname op /\
  opcode op = encode_inst offsets inst ==>
  (?n ws. op = Push n ws) \/ op = JumpDest
Proof
  Cases_on `inst` >> simp[is_data_inst_def] >> strip_tac >>
  gvs[encoding_wf_inst_def, encode_inst_def, AllCaseEqs()] >>
  all_tac
  >~ [`opcode op = encode_inst offsets (AsmPush bytes)`] >- (
    `op = Push (LENGTH bytes) bytes` suffices_by metis_tac[] >>
    irule opcode_wf_inj >> simp[] >>
    Cases_on `bytes` >> gvs[encode_inst_def, opcode_def,
      wordsTheory.word_add_n2w]) >>
  all_tac
  >~ [`opcode op = [91w]`] >- metis_tac[opcode_byte_91_is_jumpdest] >>
  qmatch_asmsub_abbrev_tac `97w::payload` >>
  `LENGTH payload = 2` by (
    unabbrev_all_tac >> simp[symbol_size_def] >>
    irule asmParseProofsTheory.pad_bytes_length >>
    fs[symbol_size_def] >> metis_tac[]) >>
  `op = Push 2 payload` suffices_by metis_tac[] >>
  irule opcode_wf_inj >> simp[opcode_def, wordsTheory.word_add_n2w]
QED

Theorem encoded_call_inst_cases:
  encoding_wf_inst inst offsets /\ ~is_data_inst inst /\ wf_opname op /\
  opcode op = encode_inst offsets inst /\ is_call op ==>
  ?name. inst = AsmOp name /\
    MEM name ["CREATE";"CREATE2";"DELEGATECALL";"CALL";"STATICCALL"]
Proof
  strip_tac >> Cases_on `?name. inst = AsmOp name`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      Cases_on `op` >> gvs[is_call_def] >>
      gvs[encode_inst_def, opcode_def, evm_opcode_byte_def, AllCaseEqs()] >>
      drule alistTheory.ALOOKUP_MEM >>
      simp[evm_opcode_table_def, listTheory.MEM, wordsTheory.dimword_def,
        wordsTheory.dimindex_8] >> metis_tac[]) >>
  drule cheap_non_asmop_classify >> disch_then (qspec_then `op` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >> gvs[is_call_def]
QED
