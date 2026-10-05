(* Opt-in rollup of all 101 exact pinned-Python bytecode comparisons.
   Each public parity theorem is proved by plain EVAL_TAC. *)
Theory evalCompilerBytecodeParity
Ancestors
  evalCompilerRange
  evalCompilerAllocationBudget
  evalCompilerAllocationBudgetCost
  evalCompilerBytecode
  evalCompilerBytecodeControl
  evalCompilerBytecodeState
  evalCompilerBytecodeAbiExternalStatic
  evalCompilerBytecodeAbiExternalArrays
  evalCompilerBytecodeAbiExternalDynamic
  evalCompilerBytecodeAbiEvents
  evalCompilerBytecodeAbiInternalCalls
  evalCompilerBytecodeAbiExternalCalls
  evalCompilerBytecodeAbiStatic
  evalCompilerBytecodeAbiDynamic
  evalCompilerBytecodeFunctionModes
  evalCompilerBytecodeAssertRaise
  evalCompilerBytecodeAssertReason
  evalCompilerBytecodeRaiseBare
  evalCompilerBytecodeRaiseReason
  evalCompilerBytecodeLoops
  evalCompilerBytecodeScalarWidths
  evalCompilerBytecodeScalarLiterals
  evalCompilerBytecodeScalarLiteralsBytes
  evalCompilerBytecodeScalarArithmetic
  evalCompilerBytecodeScalarIntegerMin
  evalCompilerBytecodeScalarDecimalMinPipeline
  evalCompilerBytecodeScalarConvertDecimal
  evalCompilerBytecodeScalarConvertIntToDecimal
  evalCompilerBytecodeScalarConvertBytes32ToDecimal
  evalCompilerBytecodeScalarOperators
  evalCompilerBytecodeScalarTypeBuiltins
  evalCompilerBytecodeScalarWeiModular
  evalCompilerBytecodeBuiltinsEnvCore
  evalCompilerBytecodeBuiltinsEnvBlock
  evalCompilerBytecodeBuiltinsAccountHash
  evalCompilerBytecodeBuiltinsEc

(* Audit exported theorem tags, including cached/checkpointed theorems.
   DISK_THM is HOL's ordinary theory-storage marker, not a proof admission.
   Existing definition-termination hypotheses are reported, not asserted
   closed: this rollup does not claim to solve unrelated compiler proof debt. *)
val parity_theorems = List.filter
  (fn (name, th) =>
    String.isSuffix "_matches_python_oracle" name andalso
    boolSyntax.is_eq (concl th) andalso
    same_const (#1 (strip_comb (lhs (concl th)))) ``compile_vyper``)
  (List.concat (map DB.theorems (Theory.ancestry "-")))
val () = if length parity_theorems = 101 then ()
         else raise Fail "expected exactly 101 bytecode parity theorems"
val () = List.app
  (fn (name, th) =>
    if Tag.isEmpty (tag th) orelse Tag.isDisk (tag th) then
      print ("PARITY_KERNEL_OK " ^ name ^
        " inherited_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n")
    else raise Fail ("admitted parity theorem: " ^ name ^
      " oracles=" ^ String.concatWith "," (#1 (Tag.dest_tag (tag th))) ^
      " axioms=" ^ String.concatWith "," (#2 (Tag.dest_tag (tag th)))))
  parity_theorems
