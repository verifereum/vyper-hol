(* Concrete checks of the lowering and the compiler, as one build root:
   interface contracts on concrete inputs, compiled creation code, and
   regressions of the compiler's allocation and evaluation order. Bytecode
   parity with the pinned Python compiler is the native runner's job
   (bytecode/native/). *)
Theory loweringChecks
Ancestors
  (* allocation limits, conversions, concat buffers, shared callee memory *)
  compilerLoweringTest
  (* fixed-program regressions: ranges, allocation budget, immutables,
     assignment order, the O1 source-stage unit shape *)
  evalCompilerRange evalCompilerAllocationBudget evalCompilerInternalImmutables
  evalAssignmentOrder evalCompilerSourceShape
  (* branch_opt's output checker on the parity fixtures' compiled functions;
     scalar_arith_pow_base, scalar_convert_decimal and
     scalar_convert_int_to_decimal are left out: evaluating them in the
     kernel exceeds a 12 GB heap *)
  branchOptCheckCorpusA branchOptCheckCorpusB branchOptCheckCorpusC
  branchOptCheckCorpusD branchOptCheckCorpusE branchOptCheckCorpusF
  branchOptCheckCorpusG branchOptCheckCorpusH branchOptCheckCorpusJ
  (* contracts of the lowering's interfaces on concrete inputs *)
  targetPlaceTest
  abiEncodeSnapshotTest
  (* oracle-admission audit of the CREATE boundary theories *)
  createOracleClosureAudit
  (* compiled creation code *)
  vyperCtorAliasTest createImmutableBytecodeTest createCompletionProbe
