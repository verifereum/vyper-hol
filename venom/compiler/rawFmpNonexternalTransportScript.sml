Theory rawFmpNonexternalTransport
Ancestors
  instIdxIndep unitShapeDefs venomExecSemantics venomState venomInst
  list option pair
Libs
  BasicProvers

(* Only envelope and record equations: arithmetic and memory payloads stay
   opaque throughout the opcode case analysis. *)
val fmp_record_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [venom_state_accfupds, venom_state_fupdcanon,
   venom_state_fupdfupds, venom_state_fupdfupds_comp,
   combinTheory.K_THM, combinTheory.o_DEF, LET_THM,
   exec_result_map_def, update_var_def,
   list_case_def, option_case_def, pair_case_thm, operand_case_def];

val fmp_envelope_ss = fmp_record_ss ++ rewrites
  [exec_pure1_def, exec_pure2_def, exec_pure3_def,
   exec_read0_def, exec_read1_def, exec_write2_def, exec_gas_def,
   exec_alloca_def];

val fmp_state_ss = fmp_record_ss ++ rewrites
  [write_memory_with_expansion_def, read_memory_def,
   mstore_def, mstore8_def, mload_def, mcopy_def, istore_def,
   sload_def, sstore_def, tload_def, tstore_def,
   contract_storage_def, contract_transient_def,
   jump_to_def, halt_state_def, revert_state_def, set_returndata_def];

(* Select the public equation for the known opcode, without rebuilding the
   dispatch or scanning all of its guarded equations in the simplifier. *)
val opcode_equations = map (fn th =>
  (rhs (fst (dest_imp (snd (strip_forall (concl th))))), th))
  (CONJUNCTS step_inst_base_opcode_eqs);

fun rewrite_opcode eq =
  let val (_, th) = valOf (List.find
    (fn (opc, _) => aconv opc (rhs (concl eq))) opcode_equations)
  in pure_once_rewrite_tac [MATCH_MP th eq] end;

Theorem step_inst_base_nonexternal_fmp_update_under_operand:
  (!op s p i e.
    eval_operand op (s with <|vs_fmp := p; vs_initial_fmp := i;
                             vs_call_entry_fmp := e|>) = eval_operand op s) ==>
  !inst s p i e.
    raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA /\
    inst.inst_opcode <> INVOKE /\
    ~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
    step_inst_base inst (s with <|vs_fmp := p; vs_initial_fmp := i;
                                  vs_call_entry_fmp := e|>) =
    exec_result_map
      (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
                    vs_call_entry_fmp := e|>) (step_inst_base inst s)
Proof
  disch_tac >>
  `!ops s p i e.
     eval_operands ops (s with <|vs_fmp := p; vs_initial_fmp := i;
                                vs_call_entry_fmp := e|>) = eval_operands ops s`
    by (Induct >> simp[eval_operands_def]) >>
  rule_assum_tac (SIMP_RULE fmp_record_ss []) >>
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[raw_opcode_ok_def] >>
  qpat_assum `inst.inst_opcode = _` rewrite_opcode >>
  asm_simp_tac fmp_envelope_ss [] >>
  rpt (PURE_TOP_CASE_TAC >> asm_simp_tac fmp_envelope_ss []) >>
  asm_simp_tac fmp_state_ss []
QED
