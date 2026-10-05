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

(* Audit saved objects, including cached/checkpointed theorems. TASK063's E
   package is never allowed. Pending TASK064's C package is allowed only on
   its two existing internal-call fixtures, alpha-identical to the C owner.
   DISK_THM is the ordinary storage marker, not a proof admission. *)
val parity_theorems = List.filter
  (fn (name, th) =>
    String.isSuffix "_matches_python_oracle" name andalso
    boolSyntax.is_eq (concl th) andalso
    same_const (#1 (strip_comb (lhs (concl th)))) ``compile_vyper``)
  (List.concat (map DB.theorems (Theory.ancestry "-")))
val () = if length parity_theorems = 101 then ()
         else raise Fail "expected exactly 101 bytecode parity theorems"
val c_hypotheses = hyp contextTheory.compile_store_memory_typed_def
fun same_hypothesis_set xs ys =
  length xs = length ys andalso
  List.all (fn x => List.exists (aconv x) ys) xs
fun c_fixture name =
  String.isSuffix "internal_tuple_call_matches_python_oracle" name orelse
  String.isSuffix "internal_bytes_call_matches_python_oracle" name
val () = List.app
  (fn (name, th) =>
    if not (Tag.isEmpty (tag th) orelse Tag.isDisk (tag th)) then
      raise Fail ("admitted parity theorem: " ^ name)
    else if null (hyp th) orelse
            (c_fixture name andalso same_hypothesis_set (hyp th) c_hypotheses) then
      print ("PARITY_KERNEL_E_FREE " ^ name ^
        " C_hypotheses=" ^ Int.toString (length (hyp th)) ^ "\n")
    else raise Fail ("unexpected kernel hypotheses in parity theorem: " ^ name))
  parity_theorems
