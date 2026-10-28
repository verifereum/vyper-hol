(* Compose the original code generator one native stack operation at a time. *)
structure compilerAssemblyEvalLib = struct
  open HolKernel boolLib
  fun head theory name = prim_mk_const {Thy=theory,Name=name}
  val execute_head = head "planExec" "execute_plan"
  val operation_head = head "planExec" "exec_stack_op"
  val assembly_head = head "codegen" "codegen_assembly"
  val finalize_head = head "codegen" "finalize_codegen"
  val assemble_head = head "symbolResolve" "assemble"
  val encode_head = head "asmIR" "encode_num_bytes_fuel"

  fun metadata () =
    [(head "venomPolicyTypes" "target_capabilities_wf",1),
     (head "venomTargetSafety" "context_target_safe",2),
     (head "stackPlanGen" "context_plan_ops",1),
     (head "asmIR" "data_segment_asm",1),
     (head "asmTargetSafety" "assembly_target_safe",2)]

  fun configure () = app
    (fn (operator,arity) => evalCompilerBytecodeLib.ensure_certificate_head operator arity)
    ((execute_head,2) :: (operation_head,2) :: (encode_head,2) ::
     (assemble_head,1) :: metadata ())

  fun captures operator =
    if same_const operator assembly_head then execute_head :: map #1 (metadata ())
    else if same_const operator finalize_head then [assemble_head]
    else if same_const operator operation_head then [encode_head]
    else []

  fun execute_result current = let
    val [initial_fmp,operations] = snd (strip_comb current)
  in if listSyntax.is_nil operations then
      Conv.REWR_CONV (DB.fetch "planExecEval" "execute_plan_nil") current
    else let
      val (operation,rest) = listSyntax.dest_cons operations
      (* These are constructor values taken directly from the normalized input. *)
      val () = app (compilerTraversalPlannerEvalLib.remember o REFL)
        [initial_fmp,operation,rest]
      val emitted = compilerContextPlannerEvalLib.checked_call
        (boolSyntax.list_mk_icomb (operation_head,[initial_fmp,operation]))
      val suffix = compilerContextPlannerEvalLib.checked_call
        (boolSyntax.list_mk_icomb (execute_head,[initial_fmp,rest]))
      val unfolded = Conv.REWR_CONV
        (DB.fetch "planExecEval" "execute_plan_cons") current
      val substituted = Conv.COMB2_CONV
        (Conv.RAND_CONV (fn _ => emitted),fn _ => suffix) (rhs (concl unfolded))
      val joined = computeLib.EVAL_CONV (rhs (concl substituted))
    in TRANS unfolded (TRANS substituted joined) end
  end

  fun safety_result current = let
    val unfolded = Conv.REWR_CONV
      (DB.fetch "asmTargetSafety" "assembly_target_safe_def") current
    val [predicate,items] = snd (strip_comb (rhs (concl unfolded)))
    val cache = ref (Redblackmap.mkDict Term.compare)
    fun check item = case Redblackmap.peek (!cache,item) of
        SOME theorem => theorem
      | NONE => let
          val theorem = computeLib.EVAL_CONV (mk_comb (predicate,item))
          val () = cache := Redblackmap.insert (!cache,item,theorem)
        in theorem end
    val facts = map check (#1 (listSyntax.dest_list items))
  in if List.all (fn theorem => aconv (rhs (concl theorem)) T) facts then
      TRANS unfolded (EQT_INTRO (listLib.join_EVERY predicate (map EQT_ELIM facts)))
    else computeLib.EVAL_CONV current
  end

  fun warm_step goal =
    case !compilerPlannerEvalLib.pending of
      current::_ => if same_const (fst (strip_comb current)) execute_head then
          compilerExternalPlannerEvalLib.composed_step execute_result current goal
        else if same_const (fst (strip_comb current))
            (head "asmTargetSafety" "assembly_target_safe") then
          compilerExternalPlannerEvalLib.composed_step safety_result current goal
        else compilerPlannerEvalLib.warm_step_with captures goal
    | [] => compilerPlannerEvalLib.warm_step_with captures goal

  fun warm_slice goal = let
    val started = Time.now ()
    fun advance remaining goal =
      if remaining = 0 orelse
          Time.- (Time.now (),started) >= Time.fromReal 0.005 then
        Tactical.ALL_TAC goal
      else Tactical.THEN (warm_step,advance (remaining - 1)) goal
  in advance 8 goal end

  fun finish goal =
    if null (!compilerPlannerEvalLib.pending) then warm_step goal
    else raise Fail "assembly preparation incomplete"
end
