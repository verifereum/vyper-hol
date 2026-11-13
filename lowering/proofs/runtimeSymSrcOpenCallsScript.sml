Theory runtimeSymSrcOpenCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcInternalCalls runtimeSymSrcExternalComplete runtimeSymSrcSimpleCalls
  runtimeSymSrcCreateCalls runtimeSymSrcCallStaging runtimeSymSrcAbiEncode
  runtimeSymSrcContext runtimeSymSrcExternalCalls
  exprLowering compileEnv emitHelper loweringShapeDefs list venomInst stackPlanTypes

Theorem runtime_sym_call_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_acc:
  runtime_sym_lower_value_clause tops ==> runtime_sym_acc_clause tops
Proof
  rewrite_tac[runtime_sym_lower_value_clause_def, runtime_sym_acc_clause_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `item` >> gvs[compile_acc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum (qspecl_then [`cfn`, `ce`, `BaseT AddressT`, `e`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  all_tac
  >~ [`emit_inst INVALID [] [] s = ((),s')`] >-
     (conj_tac >- (irule runtime_sym_emit_inst >>
       goal_assum (drule_at Any) >>
       qexists `s.cs_next_id` >> simp[runtime_sym_inst_def, mk_inst_def]) >>
      simp[is_label_operand_def])
  >~ [`emit_op GT [cs_op; Lit 0w] st2 = (op,s')`] >-
     (dxrule runtime_sym_call_op >> simp[] >> strip_tac >>
      drule runtime_sym_call_op >> simp[is_label_operand_def]) >>
  drule runtime_sym_call_op >> simp[]
QED

Theorem runtime_sym_call:
  runtime_sym_multi_vvs_clause tops /\ runtime_sym_lower_value_clause tops /\
  (!dst src hi info s u s'.
    ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand hi /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_abi_decode_to_buf dst (Lit 0w) MLOAD src hi info s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  runtime_sym_call_clause tops
Proof
  strip_tac >>
  mp_tac runtime_sym_call_internal >>
  (impl_tac >-
    (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
     conj_tac >- (rpt gen_tac >> strip_tac >> drule_all runtime_sym_alloc_buffer >> simp[]) >>
     conj_tac >- MATCH_ACCEPT_TAC runtime_sym_stage_intcall_args >>
     MATCH_ACCEPT_TAC runtime_sym_store_multi_results)) >> disch_tac >>
  mp_tac runtime_sym_call_external >>
  (impl_tac >-
    (conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC runtime_sym_abi_encode_to_buf) >>
     rpt conj_tac >> first_assum MATCH_ACCEPT_TAC)) >> disch_tac >>
  drule runtime_sym_call_send >> disch_tac >>
  rewrite_tac[runtime_sym_call_clause_def] >> rpt gen_tac >>
  Cases_on `target`
  >~ [`Call rt (IntCall _)`] >- first_assum MATCH_ACCEPT_TAC
  >~ [`Call rt (ExtCall _ _ _ _)`] >-
      (PairCases_on `p` >> first_assum MATCH_ACCEPT_TAC)
  >~ [`Call rt (Send _)`] >- first_assum MATCH_ACCEPT_TAC
  >~ [`Call rt RawLog`] >- MATCH_ACCEPT_TAC runtime_sym_call_log
  >~ [`Call rt RawRevert`] >- MATCH_ACCEPT_TAC runtime_sym_call_revert
  >~ [`Call rt SelfDestructTarget`] >- MATCH_ACCEPT_TAC runtime_sym_call_selfdestruct
  >~ [`Call rt (RawCallTarget _)`] >- MATCH_ACCEPT_TAC runtime_sym_call_raw
  >~ [`Call rt (RawCallCalldataTarget _)`] >- MATCH_ACCEPT_TAC runtime_sym_call_raw_calldata
  >> MATCH_ACCEPT_TAC runtime_sym_call_create
QED
