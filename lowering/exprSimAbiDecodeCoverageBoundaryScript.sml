Theory exprSimAbiDecodeCoverageBoundary
Ancestors
  exprSimAbiDecodeCoverageMutual exprSimAbiDecodeCoverageActions
  exprSimAbiDecodeSuffixWrites exprSimAbiGasBridge abiBuiltinDecodeSetup
  abiBuiltinDecodeCorrect abiDecoderAppend exprSimAbiDecodeSiteCoverage
  builtinAbi abiEncoder exprLoweringProps compileEnv emitHelper context venomInst list rich_list fragExec
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests words arithmetic ASCIInumbers

val writes_simps = [abi_decode_fresh_writes_return, abi_decode_fresh_writes_prims];
val WRITES_BIND_WITH = fn extra => ho_match_mp_tac abi_decode_fresh_writes_bind >> conj_tac
  >- simp (extra @ writes_simps) >> rpt gen_tac;
val WRITES_BIND = WRITES_BIND_WITH [];

Theorem abi_decode_fresh_writes_lower:
  abi_decode_fresh_writes (lower_abi_decode data info mn mx outsz)
Proof
  rewrite_tac[lower_abi_decode_def] >> ntac 2 WRITES_BIND >>
  ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- (IF_CASES_TAC
      >- (WRITES_BIND >> simp writes_simps) >>
      ntac 5 WRITES_BIND >> simp writes_simps) >>
  WRITES_BIND_WITH [abi_decode_fresh_writes_alloc_buffer] >>
  WRITES_BIND >> ho_match_mp_tac abi_decode_fresh_writes_ignore_bind >> conj_tac
  >- simp[abi_decode_fresh_writes_mutual] >> simp writes_simps
QED

Theorem abi_decode_lower_output_writes:
  lower_abi_decode data info mn mx outsz a = (out,b) ==>
  !i x. MEM i (frag_code a b) /\ MEM x i.inst_outputs ==>
    ?n. a.cs_next_var <= n /\ x = STRING #"%" (toString n)
Proof
  mp_tac abi_decode_fresh_writes_lower >>
  simp[abi_decode_fresh_writes_def] >> metis_tac[]
QED

Theorem abi_decode_lower_fresh_interval_instruction:
  lower_abi_decode data info mn mx outsz a = (out,b) /\
  a.cs_next_id <= id /\ id < b.cs_next_id ==>
  ?i. MEM i (frag_code a b) /\ i.inst_id = id /\
      !x. MEM x i.inst_outputs ==>
        ?n. a.cs_next_var <= n /\ x = STRING #"%" (toString n)
Proof
  strip_tac >> drule_all abi_decode_lower_interval_instruction >> strip_tac >>
  qexists_tac `i` >> simp[] >> metis_tac[abi_decode_lower_output_writes]
QED

Theorem abi_decode_setup_output_allocation:
  abi_builtin_decode_setup data mn mx outsz a = (ops,b) ==>
  ?i. MEM i (frag_code a b) /\
      i.inst_id = abi_builtin_decode_output_site a mn mx /\
      i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit (n2w outsz)]
Proof
  Cases_on `mn = mx` >>
  simp[abi_builtin_decode_setup_def, abi_builtin_decode_output_site_def,
    abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[frag_code_def, emitted_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
  >- (qexists_tac `<|inst_id := a.cs_next_id + 4; inst_opcode := ALLOCA;
         inst_operands := [Lit (n2w outsz)];
         inst_outputs := [STRING #"%" (toString (a.cs_next_var + 3))]|>` >> simp[]) >>
  qexists_tac `<|inst_id := a.cs_next_id + 8; inst_opcode := ALLOCA;
         inst_operands := [Lit (n2w outsz)];
         inst_outputs := [STRING #"%" (toString (a.cs_next_var + 7))]|>` >> simp[]
QED

Theorem abi_decode_lower_output_allocation:
  lower_abi_decode data info mn mx outsz a = (out,b) ==>
  ?i. MEM i (frag_code a b) /\
      i.inst_id = abi_builtin_decode_output_site a mn mx /\
      i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit (n2w outsz)]
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  `cs_extends a ready` by
    (drule abi_builtin_decode_setup_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `cs_extends ready b` by metis_tac[cs_extends_abi_decode] >>
  drule abi_decode_setup_output_allocation >> strip_tac >>
  qexists_tac `i` >> simp[] >>
  metis_tac[abi_decode_frag_code_left_inclusion]
QED
