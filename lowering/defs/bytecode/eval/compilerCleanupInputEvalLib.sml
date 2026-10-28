(* TOP-LEVEL: warm_slice. Prepare cleanup input observations before the
   generic planner normalizes their arguments. Analysis records stay opaque. *)
structure compilerCleanupInputEvalLib = struct
  open HolKernel boolLib

  fun head theory name = prim_mk_const {Thy=theory,Name=name}
  val apply_head = head "stackPlanCleanupCases" "planner_cleanup_apply"
  val single_head = head "stackPlanCleanupCases" "planner_cleanup_single"
  val input_head = head "livenessDefs" "input_vars_from"
  val live_head = head "livenessDefs" "live_vars_at"
  val safety_head = head "stackPlanGen" "cleanup_elision_safe"
  val block_type = Type.mk_thy_type {Thy="venomInst",Tyop="basic_block",Args=[]}

  fun application operator equations =
    List.foldl (fn (equation,result) => MK_COMB (result,equation))
      (REFL operator) equations

  fun project expression =
    compilerPassEffectsEvalLib.observe [block_type] expression

  fun small expression = let
    val projected = project expression
  in TRANS projected (computeLib.EVAL_CONV (rhs (concl projected))) end

  fun live_result current = let
    val (operator,arguments) = strip_comb current
    val [analysis,label,index] = arguments
    val () = if same_const operator live_head then ()
      else raise Fail "expected cleanup liveness observation"
    val inputs = application operator [REFL analysis,small label,small index]
    val result = compilerContextPlannerEvalLib.live_query (rhs (concl inputs))
  in TRANS inputs result end

  fun input_result current = let
    val (operator,arguments) = strip_comb current
  in if same_const operator live_head then live_result current
    else if same_const operator input_head then let
      val [label,instructions,liveness] = arguments
      val live = if same_const (fst (strip_comb liveness)) live_head
        then live_result liveness else small liveness
      val inputs = application operator [small label,project instructions,live]
      val result = computeLib.EVAL_CONV (rhs (concl inputs))
    in TRANS inputs result end
    else small current
  end

  fun safety_result current = let
    val [cfg,func,bb] = snd (strip_comb current)
    val bound = computeLib.EVAL_CONV
      ``LENGTH (planner_cleanup_candidates ^func) + cleanup_max_transient ^func <= 1024``
  in if aconv (rhs (concl bound)) F then
      compilerCleanupEvalLib.compute_safety current
    else let
      val selected = compilerCleanupEvalLib.apply_case
        (DB.fetch "stackPlanCleanupCases" "planner_cleanup_safety_frame_bound")
        current (EQT_ELIM bound)
      val projected = compilerPassEffectsEvalLib.observe
        [block_type,type_of func,type_of cfg] (rhs (concl selected))
      val expression = rhs (concl projected)
      val (parameters,membership) = boolSyntax.dest_conj expression
      val parameter_eq = computeLib.EVAL_CONV parameters
      val labels = compilerContextPlannerEvalLib.checked_call (rand membership)
      val replaced = Conv.RAND_CONV (fn _ => labels) membership
      val member_eq = TRANS replaced (computeLib.EVAL_CONV (rhs (concl replaced)))
      val joined = MK_COMB (AP_TERM (rator (rator expression)) parameter_eq,member_eq)
      val result = TRANS joined (computeLib.EVAL_CONV (rhs (concl joined)))
    in TRANS selected (TRANS projected result) end
  end

  fun checked_cleanup current =
    if same_const (fst (strip_comb current)) apply_head then let
      val arguments = snd (strip_comb current)
      val observations = [List.nth (arguments,1),List.nth (arguments,2)]
    in case List.find (not o compilerPlanMetadataEvalLib.cached) observations of
      SOME expression => let
        val equation = evalCompilerBytecodeLib.timed_evaluation apply_head
          "cleanup input observation" (fn () => input_result expression)
        val () = compilerPlanMetadataEvalLib.remember expression equation
      in raise compilerInstructionPlannerEvalLib.InputsPrepared end
    | NONE => compilerContextPlannerEvalLib.checked_call current
    end
    else compilerContextPlannerEvalLib.checked_call current

  fun single_result current = compilerPlanCleanupEvalLib.single_result
    checked_cleanup (compilerContextPlannerEvalLib.checked_argument single_head 1)
    current

  fun warm_step goal =
    case !compilerPlannerEvalLib.pending of
      current::_ =>
        if same_const (fst (strip_comb current)) safety_head then
          compilerExternalPlannerEvalLib.composed_step safety_result current goal
        else if same_const (fst (strip_comb current)) single_head then
          compilerExternalPlannerEvalLib.composed_step single_result current goal
        else compilerContextPlannerEvalLib.warm_step goal
    | [] => compilerContextPlannerEvalLib.warm_step goal

  fun warm_slice goal = let
    val started = Time.now ()
    fun advance remaining goal =
      if remaining = 0 orelse
          Time.- (Time.now (),started) >= Time.fromReal 0.005 then
        Tactical.ALL_TAC goal
      else Tactical.THEN (warm_step,advance (remaining - 1)) goal
  in advance 8 goal end
end
