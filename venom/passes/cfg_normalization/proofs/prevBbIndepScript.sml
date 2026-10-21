(*
 * step_inst_base is independent of vs_prev_bb for non-PHI opcodes.
 *
 * Only the PHI case of step_inst_base reads s.vs_prev_bb (via resolve_phi).
 * All other opcodes produce identical results regardless of vs_prev_bb.
 *
 * Built as a separate theory because the 93-opcode case split is expensive.
 *)

Theory prevBbIndep
Ancestors
  venomExecSemantics venomState venomInst venomCallOracleDefs
Libs
  finite_mapTheory listTheory BasicProvers pairTheory

(* ================================================================
   Commutation helpers for vs_prev_bb
   ================================================================ *)

Theorem eval_op_prev_bb[local]:
  !op s p. eval_operand op (s with vs_prev_bb := p) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_ops_prev_bb[local]:
  !ops s p.
    eval_operands ops (s with vs_prev_bb := p) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, eval_op_prev_bb]
QED

Theorem update_var_prev_bb[local]:
  !x v s p.
    update_var x v (s with vs_prev_bb := p) =
    (update_var x v s) with vs_prev_bb := p
Proof
  simp[update_var_def]
QED

Theorem write_mem_prev_bb[local]:
  !off bytes s p.
    write_memory_with_expansion off bytes (s with vs_prev_bb := p) =
    (write_memory_with_expansion off bytes s) with vs_prev_bb := p
Proof
  simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem read_mem_prev_bb[local]:
  !off sz s p. read_memory off sz (s with vs_prev_bb := p) = read_memory off sz s
Proof
  simp[read_memory_def]
QED

Theorem jump_to_prev_bb[local]:
  !lbl s p. jump_to lbl (s with vs_prev_bb := p) = jump_to lbl s
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem halt_state_prev_bb[local]:
  !s p. halt_state (s with vs_prev_bb := p) =
        (halt_state s) with vs_prev_bb := p
Proof
  simp[halt_state_def]
QED

Theorem revert_state_prev_bb[local]:
  !s p. revert_state (s with vs_prev_bb := p) =
        (revert_state s) with vs_prev_bb := p
Proof
  simp[revert_state_def]
QED

Theorem set_returndata_prev_bb[local]:
  !rd s p. set_returndata rd (s with vs_prev_bb := p) =
           (set_returndata rd s) with vs_prev_bb := p
Proof
  simp[set_returndata_def]
QED

Theorem mstore_prev_bb[local]:
  !off v s p. mstore off v (s with vs_prev_bb := p) =
              (mstore off v s) with vs_prev_bb := p
Proof
  simp[mstore_def, LET_THM]
QED

Theorem istore_prev_bb[local]:
  !off v s p. istore off v (s with vs_prev_bb := p) =
              (istore off v s) with vs_prev_bb := p
Proof
  simp[istore_def, mstore_prev_bb]
QED

Theorem mstore8_prev_bb[local]:
  !off v s p. mstore8 off v (s with vs_prev_bb := p) =
              (mstore8 off v s) with vs_prev_bb := p
Proof
  simp[mstore8_def, LET_THM]
QED

Theorem sstore_prev_bb[local]:
  !k v s p. sstore k v (s with vs_prev_bb := p) =
            (sstore k v s) with vs_prev_bb := p
Proof
  simp[sstore_def, contract_storage_def, LET_THM]
QED

Theorem tstore_prev_bb[local]:
  !k v s p. tstore k v (s with vs_prev_bb := p) =
            (tstore k v s) with vs_prev_bb := p
Proof
  simp[tstore_def, contract_transient_def, LET_THM]
QED

Theorem mcopy_prev_bb[local]:
  !dst src sz s p.
    mcopy dst src sz (s with vs_prev_bb := p) =
    (mcopy dst src sz s) with vs_prev_bb := p
Proof
  simp[mcopy_def, LET_THM, write_memory_with_expansion_def]
QED

Theorem mload_prev_bb[local]:
  !off s p. mload off (s with vs_prev_bb := p) = mload off s
Proof
  simp[mload_def]
QED

Theorem sload_prev_bb[local]:
  !k s p. sload k (s with vs_prev_bb := p) = sload k s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem tload_prev_bb[local]:
  !k s p. tload k (s with vs_prev_bb := p) = tload k s
Proof
  simp[tload_def, contract_transient_def]
QED

(* ================================================================
   exec helper commutations
   ================================================================ *)

Definition exec_result_map_prev_bb_def:
  (exec_result_map_prev_bb f (OK s) = OK (f s)) /\
  (exec_result_map_prev_bb f (Halt s) = Halt (f s)) /\
  (exec_result_map_prev_bb f (Abort a s) = Abort a (f s)) /\
  (exec_result_map_prev_bb f (IntRet l s) = IntRet l (f s)) /\
  (exec_result_map_prev_bb f (Error e) = Error e)
End

(* Normalize only state projections and exposed envelope cases.  Keeping
   arithmetic and conditional-context congruences out leaves payloads opaque. *)
val prev_bb_state_rw =
  List.filter (free_in ``vs_prev_bb_fupd`` o concl)
    (CONJUNCTS venom_state_accfupds) @
  [venom_state_fupdcanon, venom_state_fupdfupds];

val prev_bb_case_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  (prev_bb_state_rw @
   [list_case_def, pair_case_thm, pairTheory.UNCURRY,
    pairTheory.FST, pairTheory.SND, optionTheory.option_case_def,
    operand_case_def, combinTheory.K_THM, combinTheory.o_DEF, LET_THM,
    eval_op_prev_bb, update_var_prev_bb, exec_result_map_prev_bb_def]);

fun prev_bb_cases_tac ss =
  asm_simp_tac ss [] >>
  REPEAT (PURE_TOP_CASE_TAC >> asm_simp_tac ss []);

val exec_prev_bb_ss = prev_bb_case_ss ++ rewrites
  [exec_pure1_def, exec_pure2_def, exec_pure3_def,
   exec_read0_def, exec_read1_def, exec_write2_def];

val exec_prev_bb_tac = prev_bb_cases_tac exec_prev_bb_ss;

Theorem exec_pure1_prev_bb[local]:
  !f inst s p.
    exec_pure1 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_pure1 f inst s)
Proof
  rpt gen_tac >> exec_prev_bb_tac
QED

Theorem exec_pure2_prev_bb[local]:
  !f inst s p.
    exec_pure2 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_pure2 f inst s)
Proof
  rpt gen_tac >> exec_prev_bb_tac
QED

Theorem exec_pure3_prev_bb[local]:
  !f inst s p.
    exec_pure3 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_pure3 f inst s)
Proof
  rpt gen_tac >> exec_prev_bb_tac
QED

Theorem exec_read0_prev_bb[local]:
  !g inst s p.
    (!s p. g (s with vs_prev_bb := p) = g s) ==>
    exec_read0 g inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_read0 g inst s)
Proof
  rpt strip_tac >> exec_prev_bb_tac
QED

Theorem exec_read1_prev_bb[local]:
  !g inst s p.
    (!v s p. g v (s with vs_prev_bb := p) = g v s) ==>
    exec_read1 g inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_read1 g inst s)
Proof
  rpt strip_tac >> exec_prev_bb_tac
QED

Theorem exec_write2_prev_bb[local]:
  !f inst s p.
    (!v1 v2 s p. f v1 v2 (s with vs_prev_bb := p) =
                 (f v1 v2 s) with vs_prev_bb := p) ==>
    exec_write2 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_write2 f inst s)
Proof
  rpt strip_tac >> exec_prev_bb_tac
QED

val alloca_prev_bb_ss = prev_bb_case_ss ++ rewrites [exec_alloca_def];

Theorem exec_alloca_prev_bb[local]:
  !inst s alloc_size p.
    exec_alloca inst (s with vs_prev_bb := p) alloc_size =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
                    (exec_alloca inst s alloc_size)
Proof
  rpt gen_tac >> prev_bb_cases_tac alloca_prev_bb_ss
QED

(* ================================================================
   Utility: case-OPTION_MAP fusion
   ================================================================ *)

Theorem option_case_OPTION_MAP_prev_bb[local]:
  !f x n g.
    option_CASE (OPTION_MAP f x) n g = option_CASE x n (g o f)
Proof
  Cases_on `x` >> simp[]
QED

(* ================================================================
   External call helpers
   ================================================================ *)

Theorem venom_to_tx_params_prev_bb[local]:
  !s p. venom_to_tx_params (s with vs_prev_bb := p) = venom_to_tx_params s
Proof
  simp[venom_to_tx_params_def]
QED

Theorem make_venom_call_state_prev_bb[local]:
  !s target gas value calldata code is_static p.
    make_venom_call_state (s with vs_prev_bb := p) target gas value
      calldata code is_static =
    make_venom_call_state s target gas value calldata code is_static
Proof
  simp[make_venom_call_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem make_venom_delegatecall_state_prev_bb[local]:
  !s target gas calldata code is_static p.
    make_venom_delegatecall_state (s with vs_prev_bb := p) target gas
      calldata code is_static =
    make_venom_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem make_venom_create_state_prev_bb[local]:
  !s new_address gas value init_code p.
    make_venom_create_state (s with vs_prev_bb := p) new_address gas
      value init_code =
    make_venom_create_state s new_address gas value init_code
Proof
  simp[make_venom_create_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

val extract_prev_bb_ss = prev_bb_case_ss ++ rewrites
  [extract_venom_result_def, optionTheory.OPTION_MAP_DEF,
   sumTheory.sum_case_def, write_mem_prev_bb];

Theorem extract_venom_result_prev_bb[local]:
  !s output_val retOff retSize run_result p.
    extract_venom_result (s with vs_prev_bb := p) output_val retOff retSize
      run_result =
    OPTION_MAP (\q. (FST q, (SND q) with vs_prev_bb := p))
               (extract_venom_result s output_val retOff retSize run_result)
Proof
  rpt gen_tac >> prev_bb_cases_tac extract_prev_bb_ss
QED

val ext_call_rw_prev_bb =
  [LET_THM, read_mem_prev_bb, extract_venom_result_prev_bb,
   option_case_OPTION_MAP_prev_bb, update_var_prev_bb];

val ext_call_prev_bb_ss = prev_bb_case_ss ++ rewrites
  (ext_call_rw_prev_bb @
   [exec_ext_call_def, venom_call_request_def, consume_call_outcome_eq,
    write_mem_prev_bb, update_var_def, venom_state_accfupds,
    exec_delegatecall_def,
    make_venom_delegatecall_state_prev_bb, exec_create_def,
    make_venom_create_state_prev_bb]);

Theorem exec_ext_call_prev_bb[local]:
  !inst s gas addr value ao as_ ro rs is_static p.
    exec_ext_call inst (s with vs_prev_bb := p) gas addr value ao as_ ro rs
      is_static =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (exec_ext_call inst s gas addr value ao as_ ro rs is_static)
Proof
  rpt gen_tac >> prev_bb_cases_tac ext_call_prev_bb_ss
QED

Theorem exec_delegatecall_prev_bb[local]:
  !inst s gas addr ao as_ ro rs p.
    exec_delegatecall inst (s with vs_prev_bb := p) gas addr ao as_ ro rs =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (exec_delegatecall inst s gas addr ao as_ ro rs)
Proof
  rpt gen_tac >> prev_bb_cases_tac ext_call_prev_bb_ss
QED

Theorem exec_create_prev_bb[local]:
  !inst s value offset sz salt_opt p.
    exec_create inst (s with vs_prev_bb := p) value offset sz salt_opt =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (exec_create inst s value offset sz salt_opt)
Proof
  rpt gen_tac >> prev_bb_cases_tac ext_call_prev_bb_ss
QED

(* ================================================================
   Rewrite sets for the main proof
   ================================================================ *)

val prev_bb_rw = [eval_op_prev_bb, eval_ops_prev_bb, update_var_prev_bb,
              write_mem_prev_bb, read_mem_prev_bb, jump_to_prev_bb,
              halt_state_prev_bb, revert_state_prev_bb, set_returndata_prev_bb,
              mstore_prev_bb, istore_prev_bb, mstore8_prev_bb,
              sstore_prev_bb, tstore_prev_bb, mcopy_prev_bb,
              mload_prev_bb, sload_prev_bb, tload_prev_bb,
              exec_result_map_prev_bb_def];

(* ================================================================
   MAIN THEOREM 1: For non-PHI, non-terminator opcodes,
   step_inst_base commutes with vs_prev_bb update.
   ================================================================ *)

(* Cache guarded equations, then rewrite only the selected opcode branch. *)
val prev_bb_opcode_rewrites = let
  fun key th = let
    val (_, body) = strip_forall (concl th)
    val (guard, _) = dest_imp body
  in rhs guard end
in map (fn th => (key th, th))
  (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs) end;

fun rewrite_prev_bb_opcode eq = let
  val (_, rewrite) = valOf (List.find
    (fn (key, _) => aconv key (rhs (concl eq))) prev_bb_opcode_rewrites)
in PURE_ONCE_REWRITE_TAC [MATCH_MP rewrite eq] end;

(* The opcode equation has served its purpose after dispatch.  Do not feed
   it to every subsequent envelope-case simplification. *)
val prev_bb_dispatch_tac =
  qpat_x_assum `inst.inst_opcode = _` rewrite_prev_bb_opcode;

val opcode_prev_bb_ss = prev_bb_case_ss ++ rewrites
  (prev_bb_rw @ [exec_pure1_prev_bb, exec_pure2_prev_bb,
                exec_pure3_prev_bb, exec_alloca_prev_bb,
                exec_ext_call_prev_bb, exec_delegatecall_prev_bb,
                exec_create_prev_bb]);

(* Direct envelopes need no exec_read/exec_write rule probes. *)
val envelope_prev_bb_ss = prev_bb_case_ss ++ rewrites
  [eval_ops_prev_bb, jump_to_prev_bb, exec_ext_call_prev_bb,
   exec_delegatecall_prev_bb, exec_create_prev_bb];

val prev_bb_envelope_tac =
  prev_bb_dispatch_tac >> prev_bb_cases_tac envelope_prev_bb_ss;

(* Probe only the helper actually exposed by the selected opcode. *)
fun prev_bb_exec_tac (goal as (_, w)) = let
  val head = fst (strip_comb (lhs w))
  val rule = List.find (fn (c, _) => same_const c head)
    [(``exec_read0``, exec_read0_prev_bb),
     (``exec_read1``, exec_read1_prev_bb),
     (``exec_write2``, exec_write2_prev_bb)]
in
  (case rule of
     SOME (_, th) => irule th >> simp_tac opcode_prev_bb_ss []
   | NONE => prev_bb_cases_tac opcode_prev_bb_ss) goal
end;

val prev_bb_opcode_tac =
  prev_bb_dispatch_tac >>
  simp_tac opcode_prev_bb_ss [] >> prev_bb_exec_tac;

(* Keep EL, its bounds, and conditional payloads opaque in parameter access. *)
val param_prev_bb_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  (prev_bb_state_rw @
   [list_case_def, pair_case_thm, operand_case_def,
    combinTheory.K_THM, LET_THM, update_var_prev_bb,
    exec_result_map_prev_bb_def]);

val prev_bb_param_tac =
  prev_bb_dispatch_tac >>
  simp_tac param_prev_bb_ss [] >>
  REPEAT (PURE_TOP_CASE_TAC >> asm_simp_tac param_prev_bb_ss []);

(* Cache classification once per constructor; only the implication guard is
   rewritten at proof time, leaving the execution equality opaque. *)
val prev_bb_classifications = map (fn (opcode, _) =>
  SIMP_CONV (srw_ss()) [is_terminator_def]
    (subst [``op:opcode`` |-> opcode]
      ``op <> PHI /\ ~is_terminator op``)) prev_bb_opcode_rewrites;

val prev_bb_classify_conv = PURE_REWRITE_CONV prev_bb_classifications;

val prev_bb_classify_tac =
  qpat_assum `inst.inst_opcode = _` (fn eq =>
    CONV_TAC (LAND_CONV
      (PURE_REWRITE_CONV [eq] THENC prev_bb_classify_conv))) >>
  PURE_REWRITE_TAC [boolTheory.IMP_CLAUSES];

Theorem step_inst_base_prev_bb_indep:
  !inst s p.
    inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  prev_bb_classify_tac
  >- prev_bb_opcode_tac (* ADD *)
  >- prev_bb_opcode_tac (* SUB *)
  >- prev_bb_opcode_tac (* MUL *)
  >- prev_bb_opcode_tac (* Div *)
  >- prev_bb_opcode_tac (* SDIV *)
  >- prev_bb_opcode_tac (* Mod *)
  >- prev_bb_opcode_tac (* SMOD *)
  >- prev_bb_opcode_tac (* Exp *)
  >- prev_bb_opcode_tac (* ADDMOD *)
  >- prev_bb_opcode_tac (* MULMOD *)
  >- prev_bb_opcode_tac (* EQ *)
  >- prev_bb_opcode_tac (* LT *)
  >- prev_bb_opcode_tac (* GT *)
  >- prev_bb_opcode_tac (* SLT *)
  >- prev_bb_opcode_tac (* SGT *)
  >- prev_bb_opcode_tac (* ISZERO *)
  >- prev_bb_opcode_tac (* AND *)
  >- prev_bb_opcode_tac (* OR *)
  >- prev_bb_opcode_tac (* XOR *)
  >- prev_bb_opcode_tac (* NOT *)
  >- prev_bb_opcode_tac (* SHL *)
  >- prev_bb_opcode_tac (* SHR *)
  >- prev_bb_opcode_tac (* SAR *)
  >- prev_bb_opcode_tac (* SIGNEXTEND *)
  >- prev_bb_opcode_tac (* BYTE *)
  >- prev_bb_opcode_tac (* MLOAD *)
  >- prev_bb_opcode_tac (* MSTORE *)
  >- prev_bb_opcode_tac (* MSTORE8 *)
  >- prev_bb_opcode_tac (* MCOPY *)
  >- prev_bb_opcode_tac (* MEMTOP *)
  >- prev_bb_opcode_tac (* SLOAD *)
  >- prev_bb_opcode_tac (* SSTORE *)
  >- prev_bb_opcode_tac (* TLOAD *)
  >- prev_bb_opcode_tac (* TSTORE *)
  >- prev_bb_opcode_tac (* ILOAD *)
  >- prev_bb_opcode_tac (* ISTORE *)
  >- prev_bb_param_tac (* PARAM *)
  >- prev_bb_opcode_tac (* ASSIGN *)
  >- prev_bb_opcode_tac (* NOP *)
  >- prev_bb_opcode_tac (* ALLOCA *)
  >- prev_bb_opcode_tac (* DALLOCA *)
  >- prev_bb_opcode_tac (* GETFMP *)
  >- prev_bb_opcode_tac (* SETFMP *)
  >- prev_bb_opcode_tac (* INITIAL_FMP *)
  >- prev_bb_opcode_tac (* BUMP *)
  >- prev_bb_opcode_tac (* INVOKE *)
  >- prev_bb_param_tac (* FMP_PARAM *)
  >- prev_bb_param_tac (* RETPC_PARAM *)
  >- prev_bb_opcode_tac (* CALLER *)
  >- prev_bb_opcode_tac (* CALLVALUE *)
  >- prev_bb_opcode_tac (* CALLDATALOAD *)
  >- prev_bb_opcode_tac (* CALLDATASIZE *)
  >- prev_bb_opcode_tac (* CALLDATACOPY *)
  >- prev_bb_opcode_tac (* ADDRESS *)
  >- prev_bb_opcode_tac (* ORIGIN *)
  >- prev_bb_opcode_tac (* GASPRICE *)
  >- prev_bb_opcode_tac (* GAS *)
  >- prev_bb_opcode_tac (* GASLIMIT *)
  >- prev_bb_opcode_tac (* COINBASE *)
  >- prev_bb_opcode_tac (* TIMESTAMP *)
  >- prev_bb_opcode_tac (* NUMBER *)
  >- prev_bb_opcode_tac (* PREVRANDAO *)
  >- prev_bb_opcode_tac (* CHAINID *)
  >- prev_bb_opcode_tac (* SELFBALANCE *)
  >- prev_bb_opcode_tac (* BALANCE *)
  >- prev_bb_opcode_tac (* BLOCKHASH *)
  >- prev_bb_opcode_tac (* BASEFEE *)
  >- prev_bb_opcode_tac (* CODESIZE *)
  >- prev_bb_opcode_tac (* CODECOPY *)
  >- prev_bb_opcode_tac (* EXTCODESIZE *)
  >- prev_bb_opcode_tac (* EXTCODEHASH *)
  >- prev_bb_opcode_tac (* EXTCODECOPY *)
  >- prev_bb_opcode_tac (* RETURNDATASIZE *)
  >- prev_bb_opcode_tac (* RETURNDATACOPY *)
  >- prev_bb_opcode_tac (* BLOBHASH *)
  >- prev_bb_opcode_tac (* BLOBBASEFEE *)
  >- prev_bb_opcode_tac (* SHA3 *)
  >- prev_bb_envelope_tac (* CALL *)
  >- prev_bb_envelope_tac (* STATICCALL *)
  >- prev_bb_envelope_tac (* DELEGATECALL *)
  >- prev_bb_envelope_tac (* CREATE *)
  >- prev_bb_envelope_tac (* CREATE2 *)
  >- prev_bb_opcode_tac (* LOG *)
  >- prev_bb_opcode_tac (* ASSERT *)
  >- prev_bb_opcode_tac (* ASSERT_UNREACHABLE *)
  >- prev_bb_opcode_tac (* DLOAD *)
  >- prev_bb_opcode_tac (* DLOADBYTES *)
  >- prev_bb_opcode_tac (* OFFSET *)
QED

(* ================================================================
   JUMP TERMINATORS: step_inst_base ignores vs_prev_bb entirely
   (plain equality). jump_to sets vs_prev_bb from vs_current_bb.
   ================================================================ *)

Theorem step_inst_base_jump_prev_bb:
  !inst s p.
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    step_inst_base inst s
Proof
  rpt strip_tac >> prev_bb_envelope_tac
QED

