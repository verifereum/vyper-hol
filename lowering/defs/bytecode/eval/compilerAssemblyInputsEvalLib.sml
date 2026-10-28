(* TOP-LEVEL: warm_slice. Check assembly inputs once, then reuse that exact
   equation while the existing evaluator prepares captured children. *)
structure compilerAssemblyInputsEvalLib = struct
  open HolKernel boolLib
  val active = ref (NONE : term option)
  val inputs = ref (NONE : thm option)

  fun warm_step (goal as (_,proposition)) = let
    val root = rand proposition
    val () = if Option.isSome (!active) andalso aconv (valOf (!active)) root
      then () else (active := SOME root; inputs := NONE)
    val operator = fst (strip_comb root)
    fun prepare () = let
      val arguments = snd (strip_comb root)
      val numbered = List.tabulate (length arguments,fn index =>
        (index + 1,List.nth (arguments,index)))
      val equation = List.foldl (fn ((position,argument),result) =>
        MK_COMB (result,compilerContextPlannerEvalLib.checked_argument
          operator position argument)) (REFL operator) numbered
      val () = inputs := SOME equation
      val () = compilerPlannerEvalLib.active := SOME root
      val () = compilerPlannerEvalLib.pending := [rhs (concl equation)]
    in Tactical.ALL_TAC goal end
    fun finish equation = let
      val normalized = rhs (concl equation)
      val result = case List.find
          (fn theorem => aconv normalized (lhs (concl theorem)))
          (!evalCompilerBytecodeLib.compiler_certificates) of
        SOME theorem => theorem
      | NONE => raise Fail "assembly root has no checked equation"
      val evaluated = TRANS equation result
      val value = rhs (concl evaluated)
      val () = if optionSyntax.is_some value then ()
        else raise Fail "assembly root did not return SOME"
      val boundary = EQT_ELIM (TRANS (AP_TERM (rator proposition) evaluated)
        (Rewrite.PURE_REWRITE_CONV [optionTheory.IS_SOME_DEF]
          (mk_comb (rator proposition,value))))
      val () = evalCompilerBytecodeLib.cache_named_results evaluated
    in Tactic.ACCEPT_TAC boundary goal end
  in case !inputs of
    NONE => (prepare () handle compilerInstructionPlannerEvalLib.InputsPrepared =>
      Tactical.ALL_TAC goal)
  | SOME equation => if null (!compilerPlannerEvalLib.pending) then finish equation
      else compilerAssemblyEvalLib.warm_step goal
  end

  fun warm_slice goal = let
    val started = Time.now ()
    fun advance remaining goal =
      if remaining = 0 orelse
          Time.- (Time.now (),started) >= Time.fromReal 0.005 then
        Tactical.ALL_TAC goal
      else Tactical.THEN (warm_step,advance (remaining - 1)) goal
  in advance 8 goal end
end
