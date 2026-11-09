Theory deadStoreElimOpcodeCoverage
Ancestors
  deadStoreElimPureSteps deadStoreElimFrameReadSteps basePtrDefs
  venomInst venomEffects memLocDefs

(* This is static coverage only, not a residual simulation theorem. *)
Theorem dse_opcode_coverage:
  dse_pure_opcode opc \/ dse_frame_read_opcode opc \/
  opc IN {MLOAD; MSTORE; MSTORE8; SLOAD; SSTORE; TLOAD; TSTORE;
    MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY} \/
  opc IN {OFFSET; ASSIGN; NOP; PARAM; FMP_PARAM; RETPC_PARAM;
    INITIAL_FMP; BUMP; ALLOCA} \/
  opc IN {GETFMP; SETFMP; DALLOCA; JMP; JNZ; DJMP; RET; RETFMP; DRET;
    STOP; SINK; RETURN; REVERT; INVALID; SELFDESTRUCT; ASSERT;
    ASSERT_UNREACHABLE; PHI; BALANCE; SELFBALANCE; EXTCODESIZE;
    EXTCODEHASH; MEMTOP; SHA3; LOG; ILOAD; ISTORE; INVOKE;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2}
Proof
  Cases_on `opc` >> simp[dse_pure_opcode_def, dse_frame_read_opcode_def]
QED

(* Only these selected spaces are mutated by the public pass. Calls have
   unconditional undefined reads in key spaces, but not in Memory. *)
Theorem dse_key_barrier_read_location:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; INVOKE; CREATE;
    CREATE2; RETURN; STOP; SINK; SELFDESTRUCT; RET; DRET; RETFMP} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} ==>
  bp_get_read_location bp inst sp = ml_undefined
Proof
  simp[] >> strip_tac >>
  simp[bp_get_read_location_def]
QED

Theorem dse_memory_barrier_read_location:
  inst.inst_opcode IN {ILOAD; INVOKE; RET; DRET; RETFMP; MEMTOP} ==>
  bp_get_read_location bp inst AddrSp_Memory = ml_undefined
Proof
  simp[] >> strip_tac >>
  simp[bp_get_read_location_def, is_raw_fmp_opcode_def, read_effects_def,
       mem_read_ops_def]
QED

Theorem dse_raw_frame_read_location:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA} ==>
  bp_get_read_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >> Cases_on `sp` >>
  simp[bp_get_read_location_def, is_raw_fmp_opcode_def,
       read_effects_def, empty_effects_def]
QED

Theorem dse_precise_memory_read_location:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
    RETURN; REVERT; SHA3; LOG} ==>
  bp_get_read_location bp inst AddrSp_Memory =
    case mem_read_ops inst of
      NONE => ml_undefined
    | SOME ops => bp_segment_from_ops bp ops
Proof
  simp[] >> strip_tac >>
  simp[bp_get_read_location_def, is_raw_fmp_opcode_def, read_effects_def,
       all_effects_def]
QED

Theorem dse_residual_empty_read_location:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA; JMP; JNZ; DJMP; STOP;
    SINK; INVALID; SELFDESTRUCT; ASSERT; ASSERT_UNREACHABLE; PHI;
    BALANCE; SELFBALANCE; EXTCODESIZE; EXTCODEHASH; ISTORE} ==>
  bp_get_read_location bp inst AddrSp_Memory = ml_empty
Proof
  simp[] >> strip_tac >>
  simp[bp_get_read_location_def, is_raw_fmp_opcode_def,
       read_effects_def, empty_effects_def]
QED

Theorem dse_residual_key_read_location:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA; JMP; JNZ; DJMP; REVERT;
    INVALID; ASSERT; ASSERT_UNREACHABLE; PHI; BALANCE; SELFBALANCE;
    EXTCODESIZE; EXTCODEHASH; MEMTOP; SHA3; LOG; ILOAD; ISTORE} /\
  sp IN {AddrSp_Storage; AddrSp_Transient} ==>
  bp_get_read_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >> simp[bp_get_read_location_def]
QED

Theorem dse_residual_other_read_location:
  inst.inst_opcode IN {GETFMP; SETFMP; DALLOCA; JMP; JNZ; DJMP; RET;
    RETFMP; DRET; STOP; SINK; RETURN; REVERT; INVALID; SELFDESTRUCT;
    ASSERT; ASSERT_UNREACHABLE; PHI; BALANCE; SELFBALANCE; EXTCODESIZE;
    EXTCODEHASH; MEMTOP; SHA3; LOG; ILOAD; ISTORE; INVOKE;
    CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2} /\
  sp NOTIN {AddrSp_Memory; AddrSp_Storage; AddrSp_Transient} ==>
  bp_get_read_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >> Cases_on `sp` >>
  gvs[bp_get_read_location_def]
QED

(* Residual semantic interface report (classification, NOT simulation proofs).
 * Every family below also admits Error for malformed/undefined operands
 * unless stated otherwise. Continuing interfaces must preserve strong local
 * agreement, never merely terminal dse_equiv.
 *
 * GETFMP/SETFMP/DALLOCA: retained, no selected-space write effects. OK/Error.
 * Equal FMP and operands give common variable/FMP updates; allocas unchanged.
 * Their Memory reads are EMPTY, not undefined (checked above).
 *
 * JMP/JNZ/DJMP: retained terminators. OK/Error, common jump_to selected label.
 * Need suffix-dead successor transport, not sequential SUC-index transport.
 * RET/RETFMP/DRET: retained terminators. IntRet/Error. All three selected
 * spaces have undefined reads, so pending-at forces exact input states.
 * DRET packs dynamic memory and changes FMP, but equal inputs suffice.
 *
 * STOP/SINK: retained terminators, Halt only. SELFDESTRUCT: retained
 * terminator, Halt/Error with account balance transfer. Storage/Transient
 * barriers force equality; Memory needs coarse terminal projection plus
 * common account/returndata/halt transformations, not memory-length equality.
 * RETURN: retained terminator, Halt/Error. REVERT: retained terminator,
 * Abort/Error. Memory uses precise read bytes (or undefined fallback);
 * RETURN has key barriers, whereas REVERT has empty key reads.
 * INVALID: retained, Abort only. ASSERT/ASSERT_UNREACHABLE: retained,
 * OK/Abort/Error; identity on OK and common terminal-state operation on Abort.
 * PHI: retained, Error only when reached by step_inst; prefix eval separate.
 *
 * BALANCE/SELFBALANCE/EXTCODESIZE/EXTCODEHASH: retained (no selected-space
 * write). OK/Error, common read update needs equal account observations.
 * EXTCODEHASH needs account_empty, not just code equality; its projection
 * boundary must be checked before implementing that simulation.
 * MEMTOP: retained (no write), OK/Error. Memory undefined-read barrier
 * forces equal memory length. In key spaces memory is already equal.
 * SHA3: retained, OK/Error, equal precise input bytes then common output.
 * LOG: not a memory-definition opcode, OK/Error, equal precise bytes and
 * topics then common log append. Both need SUC-index pending continuation.
 * ILOAD: retained (no write), OK/Error, Memory undefined-read shortcut;
 * key spaces already agree on Memory. ISTORE: effects_in_space must exclude
 * selection because of Eff_IMMUTABLES; OK/Error common mstore-like write
 * plus immutable bookkeeping needs its own pending overwrite interface.
 *
 * INVOKE: cannot satisfy effects_in_space (all effects), OK/Halt/Abort/Error,
 * never propagates IntRet directly (binds return values). Undefined reads
 * in all selected spaces force equal inputs; do not unfold recursive runs.
 * CALL/STATICCALL/DELEGATECALL: selection excluded by effects_in_space or
 * successful single-output requirement. OK/Error. Key spaces force exact
 * inputs; Memory is precise and needs equality of call request/input bytes,
 * matched outcomes, return writes and pending expansion/overwrite transport.
 * DELEGATECALL executes an EVM state: its observation boundary needs checking.
 * CREATE/CREATE2: selection excluded by effects or successful outputs.
 * OK/Abort/Error (oversized initcode aborts). Key spaces force exact inputs;
 * Memory needs precise initcode equality and matched outcome continuation.
 *
 * Other address spaces have EMPTY reads for every residual (checked above),
 * so they do NOT justify the undefined-read shortcut. The public pass uses
 * only Memory/Storage/Transient, but the frozen space theorem is quantified
 * over all address spaces; its identity-transform cases must be discharged.
 *)
