(* Concrete checks of the lowering and the compiler, as one build root:
   bytecode parity with the pinned Python compiler on fixed fixtures,
   membership in the supported subset, interface contracts on concrete
   inputs, and oracle-admission audits. The pinned-Python witnesses have
   their own root, evalCompilerWitnesses, so CI can shard them. *)
Theory loweringChecks
Ancestors
  (* bytecode parity with the pinned Python compiler, evaluated in the kernel *)
  evalCompilerBytecodeExternalEntries evalCompilerBytecodePragmaPure
  evalCompilerBytecodeDefaultEntries evalCompilerBytecodeDefaultMulti
  evalCompilerBytecodeDefaultSender evalCompilerBytecodeDefaultOnly
  evalCompilerBytecodeDefaultConstant evalCompilerBytecodeDefaultNamedConstant
  evalCompilerBytecodeDefaultPayable evalCompilerBytecodeDefaultBalance
  evalCompilerBytecodeDefaultInternalFull
  evalCompilerBytecodeNonreentrantMulti evalCompilerBytecodeNonreentrantInternal
  evalCompilerBytecodeNonreentrantPragma evalCompilerBytecodeNonreentrantPayable
  evalCompilerBytecodeNonreentrantView evalCompilerBytecodeNonreentrantNoStorage
  evalCompilerBytecodeNonreentrantTransient
  evalCompilerBytecodeNonreentrantEarlyReturn
  evalCompilerBytecodeNonreentrantFallback
  evalCompilerBytecodeNonreentrantPragmaFallback
  evalCompilerBytecodeNonreentrantPragmaInit
  evalCompilerBytecodeNonreentrantInternalView
  evalCompilerBytecodeNonreentrantPragmaReentrant
  evalCompilerBytecodeNonreentrantInternalEarlyReturn
  evalCompilerBytecodeNonreentrantInternalReturn
  evalCompilerBytecodeNonreentrantFallbackEarlyReturn
  evalCompilerAbiCodegen evalCompilerAbiTupleString
  (* the same parity with the final assembly optimizer on *)
  evalCompilerBytecodeAsmOpt
  (* each fixture lowers to a unit of the shape the O1 source stage promises *)
  evalCompilerSourceShape
  (* tests of the evaluation libraries those checks use *)
  evalCompilerBytecodeLibTest evalCompilerBaseDftLibTest
  evalCompilerPlanCacheLibTest
  (* the supported subset: per-construct contracts, fixture membership *)
  supportedTypeProps supportedNameProps supportedDeclProps
  supportedExprFormProps supportedExprProps supportedStmtProps
  supportedStmtTraverseProps supportedProgramProps
  supportedFixturesCore supportedFixturesControl supportedFixturesControlDeploy
  supportedFixturesState supportedFixturesMultiple supportedFixturesBuiltins
  supportedFixturesAbiBuiltinsEvents supportedFixturesAbiCalls
  supportedFixturesAbiExternal
  supportedFixturesScalarArithmetic supportedFixturesScalarBounds
  supportedFixturesScalarConversions supportedFixturesScalarOperators
  supportedFixturesScalarWidthsLiterals
  supportedEvalTest vyperMembershipMatrixTest
  (* contracts of the lowering's interfaces on concrete inputs *)
  e2eBoundaryTest e2eEntryChecks e2eProducerChecks groupedDispatchProps
  targetPlaceTest
  (* compiled creation code and events *)
  vyperCreateMemoryTest vyperCtorAliasTest createImmutableBytecodeTest
  vyperEventForwardStruct
  (* admission audits: listed theorems use only the oracle tags each allows *)
  createLoweringAudit createOracleClosureAudit conversionProofAudit
  eventEndpointAudit
