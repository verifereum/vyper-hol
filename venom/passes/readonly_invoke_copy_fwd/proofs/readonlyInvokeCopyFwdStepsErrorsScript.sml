Theory readonlyInvokeCopyFwdStepsErrors
Ancestors
  readonlyInvokeCopyFwdStepsControl
  readonlyInvokeCopyFwdStepsDirectErrors
  readonlyInvokeCopyFwdStepsExternalErrors
  venomExecSemantics venomInst

(* Error/control publication interface for StepsOrdinary.

   This is a union of adapters, NOT an unconditional all-opcode simulation.
   The caller must discharge the premises of the selected adapter.  In
   particular, availability means member-local equality of the NONE tests;
   it does not mean equality of relocated pointer values.

   Audit against step_inst_base_def and the closed opcode datatype:

   Opcodes                                      Error adapter / equation
   -----------------------------------------------------------------------
   ISZERO, NOT                                  ricf_pure1_error
   ADD SUB MUL Div Mod SDIV SMOD Exp EQ LT GT
   SLT SGT AND OR XOR SHL SHR SAR SIGNEXTEND
   BYTE OFFSET                                  ricf_pure2_error
   ADDMOD MULMOD                                ricf_pure3_error
   CALLER ADDRESS CALLVALUE ORIGIN GASPRICE
   CHAINID COINBASE TIMESTAMP NUMBER PREVRANDAO
   GASLIMIT BASEFEE BLOBBASEFEE SELFBALANCE
   CALLDATASIZE RETURNDATASIZE MEMTOP CODESIZE    ricf_read0_error
   MLOAD ILOAD SLOAD TLOAD BLOCKHASH BLOBHASH
   BALANCE CALLDATALOAD EXTCODESIZE EXTCODEHASH
   DLOAD                                        ricf_read1_error
   MSTORE MSTORE8                               ricf_write2_error
   ASSIGN ALLOCA GETFMP INITIAL_FMP RETPC_PARAM
   SETFMP DALLOCA BUMP PARAM FMP_PARAM MCOPY
   CALLDATACOPY RETURNDATACOPY DLOADBYTES
   CODECOPY EXTCODECOPY ISTORE SHA3 DRET
   SSTORE TSTORE SELFDESTRUCT LOG RET RETFMP
   RETURN REVERT GAS                            ricf_<opcode>_error
   CALL STATICCALL CREATE CREATE2               ricf_<opcode>_error
   DELEGATECALL                                 ricf_delegatecall_dispatch_error
   JMP JNZ DJMP                                 ricf_cert_jmp/jnz/djmp
   ASSERT ASSERT_UNREACHABLE PHI                 ricf_cert_assert
   NOP INVALID                                  ricf_cert_assert (no Error)
   STOP SINK                                    ricf_cert_stop/sink (no Error)
   INVOKE (base dispatch only)                   ricf_base_invoke_unknown

   Helper rows are reached with step_inst_base_opcode_eqs; the helpers do
   not inspect the numerical results of pure arithmetic or memory reads.
   Error extraction from a control adapter uses ricf_control_result_def.
   JMP needs no operand comparison; JNZ, DJMP and assertions currently use
   the Control interface's equality of member operand evaluations.  DJMP
   includes its index-out-of-range Error, not just failed evaluation.
   PARAM/FMP_PARAM require equal parameter-list lengths.  Static-sensitive
   direct adapters require equal cc_static.  CALL also requires matching
   zero-value tests.  DELEGATECALL additionally requires agreement of the
   concrete extraction NONE tests; availability alone is NOT sufficient.
   Its helper-internal invalid/non-terminating and output-envelope errors
   are covered by ricf_delegatecall_error_iff.  Other external/create helper
   Error cases are exactly the single-output envelope failures, exposed by
   ricf_ext_call_error_iff and ricf_create_error_iff.

   There are no constructors beyond this table.  The only default arm of
   base dispatch is INVOKE; its real semantics is deliberately NOT this
   default arm.  For non-INVOKE instructions the existing theorem
   step_inst_non_invoke rewrites the fuel/context wrapper to base dispatch,
   so it adds no new Error cases (including at zero fuel).  The INVOKE
   wrapper's lookup, fuel, callee execution and return-binding failures
   belong to Calls, outside this ordinary non-call consumer envelope.

   Successful control/terminal transport is published by Control, including
   return-boundary reconstruction and RETURN's explicit equal-byte slice
   premise.  This Error audit does not discharge successful external-call,
   memory mutation, copy activation or caller restoration obligations.
*)

Theorem ricf_base_invoke_unknown:
  inst.inst_opcode = INVOKE ==>
  step_inst_base inst s = Error "unknown opcode"
Proof
  simp[step_inst_base_opcode_eqs]
QED
