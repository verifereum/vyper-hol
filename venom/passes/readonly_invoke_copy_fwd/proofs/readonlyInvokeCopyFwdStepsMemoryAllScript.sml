Theory readonlyInvokeCopyFwdStepsMemoryAll
Ancestors
  readonlyInvokeCopyFwdStepsMemory
  readonlyInvokeCopyFwdStepsMemoryData
  readonlyInvokeCopyFwdStepsAllocation

(* Direct memory publication / coverage boundary.

   Successful step_inst_base branches published through these ancestors:
     MSTORE          ricf_cert_mstore
     MSTORE8         ricf_cert_mstore8
     MCOPY           ricf_cert_mcopy (ordinary copy, not activation)
     CALLDATACOPY    ricf_cert_data_copy
     DLOADBYTES      ricf_cert_data_copy
     CODECOPY        ricf_cert_data_copy
     RETURNDATACOPY  ricf_cert_returndatacopy (in-bounds guard required)
     EXTCODECOPY     ricf_cert_extcodecopy
     ISTORE          ricf_cert_istore
     ALLOCA          ricf_cert_alloca_cached / ricf_cert_alloca_fresh

   These are operational certificate rules, not unconditional simulation:
   operand agreement, write exclusion, raw taint and fresh-allocation bounds
   remain explicit in their respective statements.  ricf_cert_write_memory
   is the common byte-write boundary; allocation uses its separate frame.

   This umbrella does NOT establish all memory-changing non-INVOKE cases.
   Responsibility outside this publication (PLAN component references):
     CALL / STATICCALL, CREATE / CREATE2 success: C1.6.4.1.7,
       StepsExternalOracle (publication pending at this audit).
     DELEGATECALL success and extraction-NONE discharge: C1.6.4.1.8,
       StepsDelegate (publication pending at this audit).
     DRET pack_dret_dynamic writes and IntRet: C1.6.4.1.9,
       StepsDret (publication pending at this audit).
   StepsEffects already exports non-memory SSTORE/TSTORE, returndata and
   GAS framing; those do not establish the external memory effects above.
   StepsControl exports jumps, Ret/Abort/Halt rules and wrapper errors;
   direct and external Error extensions are joined by C1.6.4.1.5.3.
   In particular RETURNDATACOPY's out-of-bounds outcome is not covered by
   its successful direct-copy adapter here.  INVOKE/caller restoration and
   erased-MCOPY activation remain separate Calls/CopySteps obligations.

   C1.6.4.1.6 is the final ordinary-operation coverage join: it must consume
   the external and DRET publications as well as MemoryAll and Errors.
   No external-success or exhaustive ordinary-coverage claim follows from
   building this umbrella.  No duplicate theorem aliases are needed:
   the imported exported interfaces retain their original names.
*)
