Theory lowerDloadOrdinaryNext
Ancestors
  lowerDloadNormalDispatch lowerDloadNormalData lowerDloadCoverageInvariant
  lowerDloadFrameCertificate lowerDloadPairedBoundary lowerDloadSharedState
  lowerDloadAllocation lowerDloadOwnership ptrDiscipline venomState
  venomExecSemantics list lowerDloadProvenanceSupport

(* Control indices are intentionally independent of the normal data layer. *)
Theorem ld_normal_data_index_update:
  !ns nt. ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f ==>
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un
    (s with vs_inst_idx := ns) (t with vs_inst_idx := nt)
    astk live keys d A suspended gstk f
Proof
  rewrite_tac[ld_normal_data_def, ld_frame_data_def, ld_frame_embedding_def,
       ld_owned_vars_def, ld_shared_state_def, ld_alloc_account_def,
       allocas_from_def, lookup_var_def, read_memory_def,
       venom_state_accfupds]
QED

(* Successor activity remains a configured-control obligation. *)
Theorem ld_normal_ordinary_next_backward:
  !nt.
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ o1_ctx_shape CS /\
  mem_inv dload_headroom_ok CS vs0 /\
  callee_first names CS.ctx_functions /\ ld_stack_origin vs0 CS stk fn s0 /\
  LIST_REL (\A g. FINITE A /\
    CARD A <= LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts g)))
    (A::suspended) (fn::MAP (\f. f.cf_fn) stk) /\
  (!g. MEM g CS.ctx_functions ==> fn_ptr_ok P g) /\ opaque_use_ok fn /\
  U = {v | v IN V /\ ~retpc_var fn v} /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V) /\
  ~in_revert_forward fn s /\
  MEM i.inst_opcode
    [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
     EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SHL; SHR; SAR;
     SIGNEXTEND; BYTE; MLOAD; MSTORE; MSTORE8; MCOPY; SLOAD; SSTORE;
     TLOAD; TSTORE; ILOAD; ISTORE; PARAM; RETPC_PARAM; ASSIGN; NOP;
     INITIAL_FMP; BUMP; CALLER; CALLVALUE; CALLDATALOAD; CALLDATASIZE;
     CALLDATACOPY; ADDRESS; ORIGIN; GASPRICE; GAS; GASLIMIT; COINBASE;
     TIMESTAMP; NUMBER; PREVRANDAO; CHAINID; SELFBALANCE; BALANCE;
     BLOCKHASH; BASEFEE; CODESIZE; CODECOPY; EXTCODESIZE; EXTCODEHASH;
     EXTCODECOPY; RETURNDATASIZE; RETURNDATACOPY; BLOBHASH; BLOBBASEFEE;
     SHA3; LOG; ASSERT; ASSERT_UNREACHABLE; OFFSET] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  step_inst fuel CT i t = OK t' /\
  ~is_terminator i.inst_opcode /\
  (!s'. step_inst fuel CS i s = OK s' ==>
    active_inst fn j (s' with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?s'. step_inst fuel CS i s = OK s' /\
    ld_annotated_reachable vs0 CS astk k L AP (ld_step_prov AP AG L i)
      (step_taint i s s' tn) fn j (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
    ld_normal_data CS fn V U lo E L H AP BP
      (ld_step_prov AP AG L i) (ld_step_prov BP BH H i)
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx) (t' with vs_inst_idx := nt)
      astk live keys d A suspended gstk f
Proof
  gen_tac >> strip_tac >>
  drule_all ld_normal_ordinary_backward >> strip_tac >>
  `i.inst_opcode <> ALLOCA /\ i.inst_opcode <> DALLOCA /\
   i.inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[]) >>
  `ld_erase L = s'.vs_allocas` by
    (drule ld_normal_data_frame >> disch_then (mp_tac o MATCH_MP ld_frame_data_embedding) >>
     simp[ld_frame_embedding_def]) >>
  qexists_tac `s'` >> (conj_tac >- simp[]) >>
  conj_tac
  >- (irule ld_annotated_reachable_next >>
      goal_assum (drule_at Any) >> simp[ld_select_alloca_def] >>
      metis_tac[ld_annotated_active_inst]) >>
  irule ld_normal_data_index_update >> goal_assum (drule_at Any)
QED
