(*
 * step_inst_base is independent of vs_inst_idx.
 *
 * step_inst_base reads operands (vs_vars), state fields (memory, storage, etc.),
 * but never reads or writes vs_inst_idx. So the result differs from the
 * original only in vs_inst_idx, captured by exec_result_map.
 *
 * Kept separate to isolate the opcode-wide commutation proofs.
 *
 * TOP-LEVEL:
 *   exec_result_map            — map function over state in exec_result
 *   step_inst_inst_idx_indep   — main commutation theorem
 *)

Theory instIdxIndep
Ancestors
  venomExecSemantics venomState venomInst venomCallOracleDefs
Libs
  finite_mapTheory listTheory BasicProvers pairTheory

(* ================================================================
   exec_result_map — exported
   ================================================================ *)

Definition exec_result_map_def:
  (exec_result_map f (OK s) = OK (f s)) /\
  (exec_result_map f (Halt s) = Halt (f s)) /\
  (exec_result_map f (Abort a s) = Abort a (f s)) /\
  (exec_result_map f (IntRet l s) = IntRet l (f s)) /\
  (exec_result_map f (Error e) = Error e)
End

(* ================================================================
   Utility: case-OPTION_MAP fusion
   Pushes OPTION_MAP inside case, avoiding EVERY_CASE_TAC + OPTION_MAP
   issues (L044).
   ================================================================ *)

Theorem option_case_OPTION_MAP[local]:
  !f x n g.
    option_CASE (OPTION_MAP f x) n g = option_CASE x n (g o f)
Proof Cases_on `x` >> simp[]
QED

(* ================================================================
   Basic commutation helpers — all local
   ================================================================ *)

Theorem eval_op_inst_idx:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_ops_inst_idx:
  !ops s n.
    eval_operands ops (s with vs_inst_idx := n) = eval_operands ops s
Proof Induct >> simp[eval_operands_def, eval_op_inst_idx]
QED

Theorem update_var_idx[local]:
  !x v s n.
    update_var x v (s with vs_inst_idx := n) =
    (update_var x v s) with vs_inst_idx := n
Proof simp[update_var_def]
QED

Theorem write_mem_idx[local]:
  !off bytes s n.
    write_memory_with_expansion off bytes (s with vs_inst_idx := n) =
    (write_memory_with_expansion off bytes s) with vs_inst_idx := n
Proof simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem read_mem_idx[local]:
  !off sz s n.
    read_memory off sz (s with vs_inst_idx := n) = read_memory off sz s
Proof simp[read_memory_def]
QED

Theorem jump_to_idx[local]:
  !lbl s n. jump_to lbl (s with vs_inst_idx := n) = jump_to lbl s
Proof simp[jump_to_def, venom_state_component_equality]
QED

Theorem halt_state_idx[local]:
  !s n. halt_state (s with vs_inst_idx := n) =
        (halt_state s) with vs_inst_idx := n
Proof simp[halt_state_def]
QED

Theorem revert_state_idx[local]:
  !s n. revert_state (s with vs_inst_idx := n) =
        (revert_state s) with vs_inst_idx := n
Proof simp[revert_state_def]
QED

Theorem set_returndata_idx[local]:
  !rd s n. set_returndata rd (s with vs_inst_idx := n) =
           (set_returndata rd s) with vs_inst_idx := n
Proof simp[set_returndata_def]
QED

Theorem mstore_idx[local]:
  !off v s n. mstore off v (s with vs_inst_idx := n) =
              (mstore off v s) with vs_inst_idx := n
Proof simp[mstore_def, LET_THM]
QED

Theorem istore_idx[local]:
  !off v s n. istore off v (s with vs_inst_idx := n) =
              (istore off v s) with vs_inst_idx := n
Proof simp[istore_def, mstore_idx]
QED

Theorem mstore8_idx[local]:
  !off v s n. mstore8 off v (s with vs_inst_idx := n) =
              (mstore8 off v s) with vs_inst_idx := n
Proof simp[mstore8_def, LET_THM]
QED

Theorem sstore_idx[local]:
  !k v s n. sstore k v (s with vs_inst_idx := n) =
            (sstore k v s) with vs_inst_idx := n
Proof simp[sstore_def, contract_storage_def, LET_THM]
QED

Theorem tstore_idx[local]:
  !k v s n. tstore k v (s with vs_inst_idx := n) =
            (tstore k v s) with vs_inst_idx := n
Proof simp[tstore_def, contract_transient_def, LET_THM]
QED

Theorem mcopy_idx[local]:
  !dst src sz s n.
    mcopy dst src sz (s with vs_inst_idx := n) =
    (mcopy dst src sz s) with vs_inst_idx := n
Proof simp[mcopy_def, LET_THM, write_memory_with_expansion_def]
QED

Theorem mload_idx[local]:
  !off s n. mload off (s with vs_inst_idx := n) = mload off s
Proof simp[mload_def]
QED

Theorem sload_idx[local]:
  !k s n. sload k (s with vs_inst_idx := n) = sload k s
Proof simp[sload_def, contract_storage_def]
QED

Theorem tload_idx[local]:
  !k s n. tload k (s with vs_inst_idx := n) = tload k s
Proof simp[tload_def, contract_transient_def]
QED

(* ================================================================
   exec_pure/read/write helpers — all local
   ================================================================ *)

(* Only split the exposed envelope/evaluation case, pruning error branches
   immediately.  Do not traverse every nested case or rewrite the context. *)
val idx_case_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [list_case_def, pair_case_thm, pairTheory.UNCURRY,
   pairTheory.FST, pairTheory.SND, optionTheory.option_case_def,
   operand_case_def, venom_state_accfupds, venom_state_fupdcanon,
   venom_state_fupdfupds, combinTheory.K_THM, combinTheory.o_DEF, LET_THM,
   eval_op_inst_idx, update_var_idx, exec_result_map_def];

fun idx_cases_tac ss =
  asm_simp_tac ss [] >>
  REPEAT (PURE_TOP_CASE_TAC >> asm_simp_tac ss []);

val exec_idx_ss = idx_case_ss ++ rewrites
  [exec_pure1_def, exec_pure2_def, exec_pure3_def,
   exec_read0_def, exec_read1_def, exec_write2_def];

val exec_idx_tac = idx_cases_tac exec_idx_ss;

Theorem exec_pure1_idx[local]:
  !f inst s n.
    exec_pure1 f inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (exec_pure1 f inst s)
Proof
  rpt gen_tac >> exec_idx_tac
QED

Theorem exec_pure2_idx[local]:
  !f inst s n.
    exec_pure2 f inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (exec_pure2 f inst s)
Proof
  rpt gen_tac >> exec_idx_tac
QED

Theorem exec_pure3_idx[local]:
  !f inst s n.
    exec_pure3 f inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (exec_pure3 f inst s)
Proof
  rpt gen_tac >> exec_idx_tac
QED

Theorem exec_read0_idx[local]:
  !g inst s n.
    (!s n. g (s with vs_inst_idx := n) = g s) ==>
    exec_read0 g inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (exec_read0 g inst s)
Proof
  rpt strip_tac >> exec_idx_tac
QED

Theorem exec_read1_idx[local]:
  !g inst s n.
    (!v s n. g v (s with vs_inst_idx := n) = g v s) ==>
    exec_read1 g inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (exec_read1 g inst s)
Proof
  rpt strip_tac >> exec_idx_tac
QED

Theorem exec_write2_idx[local]:
  !f inst s n.
    (!v1 v2 s n. f v1 v2 (s with vs_inst_idx := n) =
                 (f v1 v2 s) with vs_inst_idx := n) ==>
    exec_write2 f inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (exec_write2 f inst s)
Proof
  rpt strip_tac >> exec_idx_tac
QED

(* ================================================================
   Allocation helper — local
   ================================================================ *)

val alloca_idx_ss = idx_case_ss ++ rewrites [exec_alloca_def];

Theorem exec_alloca_idx[local]:
  !inst s alloc_size n.
    exec_alloca inst (s with vs_inst_idx := n) alloc_size =
    exec_result_map (\s'. s' with vs_inst_idx := n)
                    (exec_alloca inst s alloc_size)
Proof
  rpt gen_tac >> idx_cases_tac alloca_idx_ss
QED

(* ================================================================
   External call sub-helpers — local
   ================================================================ *)

Theorem venom_to_tx_params_idx[local]:
  !s n. venom_to_tx_params (s with vs_inst_idx := n) = venom_to_tx_params s
Proof simp[venom_to_tx_params_def]
QED

Theorem make_venom_call_state_idx[local]:
  !s target gas value calldata code is_static n.
    make_venom_call_state (s with vs_inst_idx := n) target gas value
      calldata code is_static =
    make_venom_call_state s target gas value calldata code is_static
Proof
  simp[make_venom_call_state_def, LET_THM, venom_to_tx_params_idx]
QED

Theorem make_venom_delegatecall_state_idx[local]:
  !s target gas calldata code is_static n.
    make_venom_delegatecall_state (s with vs_inst_idx := n) target gas
      calldata code is_static =
    make_venom_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, LET_THM, venom_to_tx_params_idx]

QED

Theorem make_venom_create_state_idx[local]:
  !s new_address gas value init_code n.
    make_venom_create_state (s with vs_inst_idx := n) new_address gas
      value init_code =
    make_venom_create_state s new_address gas value init_code
Proof
  simp[make_venom_create_state_def, LET_THM, venom_to_tx_params_idx]

QED

val extract_idx_ss = idx_case_ss ++ rewrites
  [extract_venom_result_def, optionTheory.OPTION_MAP_DEF,
   sumTheory.sum_case_def, write_mem_idx];

Theorem extract_venom_result_idx[local]:
  !s output_val retOff retSize run_result n.
    extract_venom_result (s with vs_inst_idx := n) output_val retOff retSize
      run_result =
    OPTION_MAP (\p. (FST p, (SND p) with vs_inst_idx := n))
               (extract_venom_result s output_val retOff retSize run_result)
Proof
  rpt gen_tac >> idx_cases_tac extract_idx_ss
QED

(* ================================================================
   exec_ext_call / exec_delegatecall / exec_create — local

   Normalize state updates once, then prune exposed envelope cases.
   ================================================================ *)

val ext_call_rw =
  [LET_THM, read_mem_idx, extract_venom_result_idx,
   option_case_OPTION_MAP, update_var_idx];

val ext_call_idx_ss = idx_case_ss ++ rewrites
  (ext_call_rw @ [exec_ext_call_def, venom_call_request_def,
                 consume_call_outcome_eq, write_mem_idx, update_var_def,
                 exec_delegatecall_def, make_venom_delegatecall_state_idx,
                 exec_create_def, make_venom_create_state_idx]);

Theorem exec_ext_call_idx[local]:
  !inst s gas addr value ao as_ ro rs is_static n.
    exec_ext_call inst (s with vs_inst_idx := n) gas addr value ao as_ ro rs
      is_static =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (exec_ext_call inst s gas addr value ao as_ ro rs is_static)
Proof
  rpt gen_tac >> idx_cases_tac ext_call_idx_ss
QED

Theorem exec_delegatecall_idx[local]:
  !inst s gas addr ao as_ ro rs n.
    exec_delegatecall inst (s with vs_inst_idx := n) gas addr ao as_ ro rs =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (exec_delegatecall inst s gas addr ao as_ ro rs)
Proof
  rpt gen_tac >> idx_cases_tac ext_call_idx_ss
QED

Theorem exec_create_idx[local]:
  !inst s value offset sz salt_opt n.
    exec_create inst (s with vs_inst_idx := n) value offset sz salt_opt =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (exec_create inst s value offset sz salt_opt)
Proof
  rpt gen_tac >> idx_cases_tac ext_call_idx_ss
QED

(* ================================================================
   Rewrite sets for the main proof
   ================================================================ *)

val idx_rw = [eval_op_inst_idx, eval_ops_inst_idx, update_var_idx,
              write_mem_idx, read_mem_idx, jump_to_idx,
              halt_state_idx, revert_state_idx, set_returndata_idx,
              mstore_idx, istore_idx, mstore8_idx, sstore_idx, tstore_idx, mcopy_idx, mload_idx,
              sload_idx, tload_idx, exec_result_map_def];

(* Cache guarded equations once; select only the known opcode branch. *)
val step_inst_base_opcode_rewrites = let
  fun key th = let
    val (_, body) = strip_forall (concl th)
    val (guard, _) = dest_imp body
  in rhs guard end
in map (fn th => (key th, th))
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs) end;

fun rewrite_step_inst_base_opcode eq = let
  val (_, rewrite) = valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq)))
    step_inst_base_opcode_rewrites)
in PURE_ONCE_REWRITE_TAC [MATCH_MP rewrite eq] end;

val step_inst_base_opcode_tac =
  qpat_assum `inst.inst_opcode = _` rewrite_step_inst_base_opcode;

val opcode_idx_ss = idx_case_ss ++ rewrites
  (idx_rw @ [exec_pure1_idx, exec_pure2_idx, exec_pure3_idx, exec_alloca_idx,
             exec_ext_call_idx, exec_delegatecall_idx, exec_create_idx]);

(* Direct envelopes do not need the exec_read/exec_write rule probes. *)
val envelope_idx_tac =
  step_inst_base_opcode_tac >> idx_cases_tac opcode_idx_ss;

val opcode_idx_tac =
  step_inst_base_opcode_tac >>
  simp_tac opcode_idx_ss [] >>
  TRY (irule exec_read0_idx >> simp_tac opcode_idx_ss [] >> NO_TAC) >>
  TRY (irule exec_read1_idx >> simp_tac opcode_idx_ss [] >> NO_TAC) >>
  TRY (irule exec_write2_idx >> simp_tac opcode_idx_ss [] >> NO_TAC) >>
  idx_cases_tac opcode_idx_ss;

(* Parameter access only inspects the operand/output envelope.  Keep EL and
   its bounds opaque: the global simpset uses bounds from conditional context
   to rewrite the lookup, although the same lookup occurs on both sides.
   Split only head cases in the conclusion, using cached envelope rewrites
   without arithmetic procedures or conditional-context congruences. *)
val param_idx_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [list_case_def, pair_case_thm, operand_case_def,
   venom_state_accfupds, combinTheory.K_THM, LET_THM,
   update_var_idx, exec_result_map_def];

val param_idx_tac =
  step_inst_base_opcode_tac >>
  simp_tac param_idx_ss [] >>
  REPEAT (PURE_TOP_CASE_TAC >> asm_simp_tac param_idx_ss []);

(* Retain the specialized MUL helper without unfolding opcode dispatch. *)
Theorem step_inst_base_MUL[local]:
  !inst s. inst.inst_opcode = MUL ==>
    step_inst_base inst s = exec_pure2 $* inst s
Proof
  rpt strip_tac >> step_inst_base_opcode_tac >> simp[]
QED

(* ================================================================
   THE MAIN THEOREM — exported
   ================================================================ *)

Theorem step_inst_inst_idx_indep:
  !inst s n. ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n) (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def]
  >- opcode_idx_tac  (* ADD *)
  >- opcode_idx_tac  (* SUB *)
  >- (asm_simp_tac std_ss [step_inst_base_MUL, exec_pure2_idx])  (* MUL *)
  >- opcode_idx_tac  (* Div *)
  >- opcode_idx_tac  (* SDIV *)
  >- opcode_idx_tac  (* Mod *)
  >- opcode_idx_tac  (* SMOD *)
  >- opcode_idx_tac  (* Exp *)
  >- opcode_idx_tac  (* ADDMOD *)
  >- opcode_idx_tac  (* MULMOD *)
  >- opcode_idx_tac  (* EQ *)
  >- opcode_idx_tac  (* LT *)
  >- opcode_idx_tac  (* GT *)
  >- opcode_idx_tac  (* SLT *)
  >- opcode_idx_tac  (* SGT *)
  >- opcode_idx_tac  (* ISZERO *)
  >- opcode_idx_tac  (* AND *)
  >- opcode_idx_tac  (* OR *)
  >- opcode_idx_tac  (* XOR *)
  >- opcode_idx_tac  (* NOT *)
  >- opcode_idx_tac  (* SHL *)
  >- opcode_idx_tac  (* SHR *)
  >- opcode_idx_tac  (* SAR *)
  >- opcode_idx_tac  (* SIGNEXTEND *)
  >- opcode_idx_tac  (* BYTE *)
  >- opcode_idx_tac  (* MLOAD *)
  >- opcode_idx_tac  (* MSTORE *)
  >- opcode_idx_tac  (* MSTORE8 *)
  >- opcode_idx_tac  (* MCOPY *)
  >- opcode_idx_tac  (* MEMTOP *)
  >- opcode_idx_tac  (* SLOAD *)
  >- opcode_idx_tac  (* SSTORE *)
  >- opcode_idx_tac  (* TLOAD *)
  >- opcode_idx_tac  (* TSTORE *)
  >- opcode_idx_tac  (* ILOAD *)
  >- opcode_idx_tac  (* ISTORE *)
  >- opcode_idx_tac  (* PHI *)
  >- param_idx_tac  (* PARAM *)
  >- opcode_idx_tac  (* ASSIGN *)
  >- opcode_idx_tac  (* NOP *)
  >- opcode_idx_tac  (* ALLOCA *)
  >- opcode_idx_tac  (* DALLOCA *)
  >- opcode_idx_tac  (* GETFMP *)
  >- opcode_idx_tac  (* SETFMP *)
  >- opcode_idx_tac  (* INITIAL_FMP *)
  >- opcode_idx_tac  (* BUMP *)
  >- opcode_idx_tac  (* INVOKE *)
  >- param_idx_tac  (* FMP_PARAM *)
  >- param_idx_tac  (* RETPC_PARAM *)
  >- opcode_idx_tac  (* CALLER *)
  >- opcode_idx_tac  (* CALLVALUE *)
  >- opcode_idx_tac  (* CALLDATALOAD *)
  >- opcode_idx_tac  (* CALLDATASIZE *)
  >- opcode_idx_tac  (* CALLDATACOPY *)
  >- opcode_idx_tac  (* ADDRESS *)
  >- opcode_idx_tac  (* ORIGIN *)
  >- opcode_idx_tac  (* GASPRICE *)
  >- opcode_idx_tac  (* GAS *)
  >- opcode_idx_tac  (* GASLIMIT *)
  >- opcode_idx_tac  (* COINBASE *)
  >- opcode_idx_tac  (* TIMESTAMP *)
  >- opcode_idx_tac  (* NUMBER *)
  >- opcode_idx_tac  (* PREVRANDAO *)
  >- opcode_idx_tac  (* CHAINID *)
  >- opcode_idx_tac  (* SELFBALANCE *)
  >- opcode_idx_tac  (* BALANCE *)
  >- opcode_idx_tac  (* BLOCKHASH *)
  >- opcode_idx_tac  (* BASEFEE *)
  >- opcode_idx_tac  (* CODESIZE *)
  >- opcode_idx_tac  (* CODECOPY *)
  >- opcode_idx_tac  (* EXTCODESIZE *)
  >- opcode_idx_tac  (* EXTCODEHASH *)
  >- opcode_idx_tac  (* EXTCODECOPY *)
  >- opcode_idx_tac  (* RETURNDATASIZE *)
  >- opcode_idx_tac  (* RETURNDATACOPY *)
  >- opcode_idx_tac  (* BLOBHASH *)
  >- opcode_idx_tac  (* BLOBBASEFEE *)
  >- opcode_idx_tac  (* SHA3 *)
  >- envelope_idx_tac  (* CALL *)
  >- envelope_idx_tac  (* STATICCALL *)
  >- envelope_idx_tac  (* DELEGATECALL *)
  >- envelope_idx_tac  (* CREATE *)
  >- envelope_idx_tac  (* CREATE2 *)
  >- opcode_idx_tac  (* LOG *)
  >- opcode_idx_tac  (* ASSERT *)
  >- opcode_idx_tac  (* ASSERT_UNREACHABLE *)
  >- opcode_idx_tac  (* DLOAD *)
  >- opcode_idx_tac  (* DLOADBYTES *)
  >- opcode_idx_tac  (* OFFSET *)
QED

(* ================================================================
   DRET packing commutes with instruction-index updates
   ================================================================ *)

Theorem pack_dret_dynamic_inst_idx_update[local]:
  !pairs cursor s ptrs final_cursor s' n.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,s') ==>
    pack_dret_dynamic cursor pairs (s with vs_inst_idx := n) =
      (ptrs,final_cursor,s' with vs_inst_idx := n)
Proof
  Induct
  >- simp[pack_dret_dynamic_def]
  >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >>
  Cases_on `pack_dret_dynamic (cursor + n2w (ceil32 (w2n h1))) pairs
              (mcopy (w2n cursor) (w2n h0) (w2n h1) s)` >>
  Cases_on `r` >>
  gvs[pack_dret_dynamic_def, mcopy_idx] >>
  first_x_assum drule >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[]
QED

(* ================================================================
   TERMINATOR idx-indep: normalizing idx to 0 yields same result
   ================================================================ *)

val terminator_idx_ss = opcode_idx_ss ++ rewrites [combinTheory.K_DEF];

val terminator_idx_tac =
  envelope_idx_tac >> simp_tac terminator_idx_ss [];

Theorem terminator_step_inst_base_idx_norm0:
  !inst s n. is_terminator inst.inst_opcode ==>
    exec_result_map (\s'. s' with vs_inst_idx := 0)
      (step_inst_base inst (s with vs_inst_idx := n)) =
    exec_result_map (\s'. s' with vs_inst_idx := 0)
      (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def]
  >- terminator_idx_tac  (* JMP *)
  >- terminator_idx_tac  (* JNZ *)
  >- terminator_idx_tac  (* DJMP *)
  >- terminator_idx_tac  (* RET *)
  >- terminator_idx_tac  (* RETURN *)
  >- terminator_idx_tac  (* REVERT *)
  >- terminator_idx_tac  (* STOP *)
  >- terminator_idx_tac  (* SINK *)
  >- (step_inst_base_opcode_tac >>
      simp[eval_op_inst_idx, eval_ops_inst_idx,
           jump_to_idx, halt_state_idx, revert_state_idx,
           set_returndata_idx, read_mem_idx, write_mem_idx] >>
      EVERY_CASE_TAC >>
      Cases_on `pack_dret_dynamic s.vs_call_entry_fmp x' s` >>
      Cases_on `r'` >>
      drule pack_dret_dynamic_inst_idx_update >>
      disch_then (fn th => rewrite_tac[th]) >>
      gvs[exec_result_map_def, venom_state_component_equality])  (* DRET *)
  >- terminator_idx_tac  (* RETFMP *)
  >- terminator_idx_tac  (* SELFDESTRUCT *)
  >- terminator_idx_tac  (* INVALID *)
QED

(* OK-producing terminators always set idx=0 (via jump_to) *)
Theorem terminator_OK_inst_idx_0:
  !inst s v. is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK v ==> v.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK v` mp_tac >>
  step_inst_base_opcode_tac >> strip_tac >>
  gvs[AllCaseEqs(), jump_to_def] >>
  Cases_on `pack_dret_dynamic s.vs_call_entry_fmp pairs s` >>
  Cases_on `r` >> gvs[]
QED


