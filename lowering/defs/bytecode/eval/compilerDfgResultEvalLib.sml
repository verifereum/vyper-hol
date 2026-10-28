(* Compose original DFG outer equations from checked recursive results.
   The completed graph remains opaque during these two wrapper steps. *)
structure compilerDfgResultEvalLib = struct
  open HolKernel boolLib

  (* Name the checked graph using transitivity, without applying a conversion
     to an equality whose right side contains the whole completed graph. *)
  fun cache_checkpoint (goal as (_,proposition)) = let
    val alias = rhs proposition
    val (head,_) = strip_comb alias
    val {Thy,Name,...} = dest_thy_const head
    val () = if Thy = "evalCompilerBytecodeStages" andalso Name = "parity_plan_dfg"
      then () else raise Fail "expected the original DFG stage alias"
    fun timed label work = evalCompilerBytecodeLib.timed_evaluation head label work
    val definition = Conv.REWR_CONV (DB.fetch Thy (Name ^ "_def")) alias
    val inputs = timed "DFG stage inputs" (fn () =>
      evalCompilerBytecodeLib.normalize_call (rhs (concl definition)))
    val child = compilerDfgBuildEvalLib.checked (rhs (concl inputs))
    val evaluated = TRANS inputs child
    val named = TRANS definition evaluated
    val alias_inputs = timed "DFG alias inputs" (fn () =>
      evalCompilerBytecodeLib.normalize_call alias)
    val normalized_alias = TRANS (SYM alias_inputs) named
    val () = evalCompilerBytecodeLib.register_compile_eval normalized_alias
    val () = evalCompilerBytecodeLib.pending_stage_values :=
      (SOME named,child) :: (NONE,normalized_alias) ::
        !evalCompilerBytecodeLib.pending_stage_values
  in timed "DFG checked alias" (fn () =>
       Tactic.ACCEPT_TAC (TRANS evaluated (SYM named)) goal) end

  fun finish current rest goal = let
    val {Name,...} = dest_thy_const (fst (strip_comb current))
    val unfolded = Conv.REWR_CONV (DB.fetch "dfgDefs" (Name ^ "_def")) current
    val inputs = evalCompilerBytecodeLib.normalize_call (rhs (concl unfolded))
    val child = compilerDfgBuildEvalLib.checked (rhs (concl inputs))
    val certificate = TRANS unfolded (TRANS inputs child)
    val () = evalCompilerBytecodeLib.register_compile_eval certificate
    val () = compilerDfgBuildEvalLib.equations := Redblackmap.insert
      (!compilerDfgBuildEvalLib.equations,current,certificate)
    val () = evalCompilerBytecodeLib.pending_stage_values :=
      (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
    val () = compilerDfgBuildEvalLib.pending := rest
  in Tactical.ALL_TAC goal end

  fun warm_call call goal =
    (if Option.isSome (!compilerDfgBuildEvalLib.active) andalso
        aconv (valOf (!compilerDfgBuildEvalLib.active)) call then
      (case !compilerDfgBuildEvalLib.pending of
          current::rest => let
            val {Thy,Name,...} = dest_thy_const (fst (strip_comb current))
          in if Thy = "dfgDefs" andalso
              (Name = "dfg_build_insts" orelse Name = "dfg_build_function") then
            finish current rest goal
          else compilerDfgBuildEvalLib.warm_call call goal end
        | [] => compilerDfgBuildEvalLib.warm_call call goal)
    else compilerDfgBuildEvalLib.warm_call call goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerDfgBuildEvalLib.pending := child :: !compilerDfgBuildEvalLib.pending;
       Tactical.ALL_TAC goal)
end
