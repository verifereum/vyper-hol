(* Prepare large planner inputs once, then reuse the existing checked cases. *)
structure compilerExternalPlannerEvalLib = struct
  open HolKernel boolLib
  val active = ref (NONE : term option)
  val inputs = ref (NONE : thm option)

  fun regular_head name = prim_mk_const {Thy="stackPlanRegularCases",Name=name}
  fun regular_queries () = map (fn (name,arity) => (regular_head name,arity))
    [("planner_regular_join",6),("planner_regular_reorder",4),
     ("planner_regular_stack",3),("planner_regular_finish",6)]

  fun configure () =
    (compilerModularPlannerEvalLib.configure ();
     app (fn (head,arity) => evalCompilerBytecodeLib.ensure_certificate_head head arity)
       (regular_queries ()))

  fun captures head =
    if same_const head (regular_head "planner_regular_join") then
      [prim_mk_const {Thy="stackPlanOps",Name="reorder_plan"},
       compilerBlockPlannerEvalLib.lookup_head]
    else if same_const head (regular_head "planner_regular_reorder") then
      [prim_mk_const {Thy="stackPlanOps",Name="reorder_plan"}]
    else if same_const head (regular_head "planner_regular_finish") then
      map (fn name => prim_mk_const
        {Thy=if name = "release_dead_spills" orelse name = "popmany_plan"
          then "stackPlanOps" else "stackPlanGen",Name=name})
        ["popmany_plan","optimistic_swap_plan","release_dead_spills"]
    else if same_const head (regular_head "planner_regular_stack") then []
    else compilerModularPlannerEvalLib.capture_heads head

  fun regular_result current = let
    val [liveness,dfg,cfg,func,inst,next_live,halting,next_term,label,ps] =
      snd (strip_comb current)
    val operand_eq = computeLib.EVAL_CONV ``compute_operands ^inst``
    val opcode_eq = computeLib.EVAL_CONV ``(^inst).inst_opcode``
    val operand = rhs (concl operand_eq)
    val opcode = rhs (concl opcode_eq)
    fun checked head arguments = compilerInstructionPlannerEvalLib.checked_call
      (boolSyntax.list_mk_icomb (head,arguments))
    fun plan_head name = prim_mk_const {Thy="stackPlanGen",Name=name}
    fun pair_result theorem = pairSyntax.dest_pair (rhs (concl theorem))
    fun application head equations = let
      val call = boolSyntax.list_mk_icomb
        (head,map (lhs o concl) equations)
    in List.foldl (fn (equation,result) => MK_COMB (result,equation))
      (REFL (fst (strip_comb call))) equations end
    val input = checked (plan_head "emit_input_plan") [opcode,operand,next_live,ps]
    val input_original = TRANS (application (plan_head "emit_input_plan")
      [opcode_eq,operand_eq,REFL next_live,REFL ps]) input
    val (input_ops,ps1) = pair_result input
    val join = checked (regular_head "planner_regular_join")
      [liveness,dfg,func,inst,label,ps1]
    val (join_ops,ps2) = pair_result join
    val reorder = checked (regular_head "planner_regular_reorder")
      [dfg,opcode,operand,ps2]
    val reorder_original = TRANS (application (regular_head "planner_regular_reorder")
      [REFL dfg,opcode_eq,operand_eq,REFL ps2]) reorder
    val (reorder_ops,ps4) = pair_result reorder
    val stack = boolSyntax.list_mk_icomb (regular_head "planner_regular_stack",
      [operand,``(^inst).inst_outputs``,ps4])
    val topics = ``case (^inst).inst_opcode of LOG =>
      (case HD (^inst).inst_operands of Lit value => w2n value | _ => 0)
      | _ => 0``
    val emit = checked (plan_head "generate_emit_ops") [inst,topics,stack]
    val stack_original = application (regular_head "planner_regular_stack")
      [operand_eq,REFL ``(^inst).inst_outputs``,REFL ps4]
    val emit_original = TRANS (application (plan_head "generate_emit_ops")
      [REFL inst,REFL topics,stack_original]) emit
    val (emit_ops,ps7) = pair_result emit
    val finish = checked (regular_head "planner_regular_finish")
      [dfg,inst,next_live,halting,next_term,ps7]
    val (post_ops,ps10) = pair_result finish
    val generic = DB.fetch "stackPlanRegularCases" "generate_regular_inst_plan_parts"
    val (_,formula) = strip_forall (concl generic)
    val schema_head = fst (strip_comb (lhs (snd (dest_imp formula))))
    val theorem = INST_TYPE (Type.match_type (type_of schema_head)
      (type_of (fst (strip_comb current)))) generic
    val (variables,_) = strip_forall (concl theorem)
    val arguments = [liveness,dfg,cfg,func,inst,next_live,halting,next_term,label,ps,
      input_ops,ps1,join_ops,ps2,reorder_ops,ps4,emit_ops,ps7,post_ops,ps10]
    val schema = INST (ListPair.map (fn (variable,value) => variable |-> value)
      (variables,arguments)) (SPECL variables theorem)
    val premises = LIST_CONJ [input_original,join,reorder_original,emit_original,finish]
    val result = MP schema premises
  in Conv.CONV_RULE (Conv.RAND_CONV computeLib.EVAL_CONV) result end

  (* Select the opcode branch before inserting large analysis records. *)
  fun instruction_result current = let
    val (head,arguments) = strip_comb current
    val inst = List.nth (arguments,4)
    val symbolic = List.tabulate (length arguments,fn index =>
      if index = 4 then inst else genvar (type_of (List.nth (arguments,index))))
    val call = boolSyntax.list_mk_icomb (head,symbolic)
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanGen" "generate_inst_plan_def") call
    val conditions = map computeLib.EVAL_CONV
      [``is_pre_codegen_opcode (^inst).inst_opcode``,
       ``(^inst).inst_opcode = INVOKE /\ ~invoke_operands_wf ^inst``,
       ``(^inst).inst_opcode = PHI``, ``(^inst).inst_opcode = OFFSET``,
       ``is_param_opcode (^inst).inst_opcode``, ``(^inst).inst_opcode = NOP``]
    val selected = TRANS unfolded
      (simpLib.SIMP_CONV boolSimps.bool_ss conditions (rhs (concl unfolded)))
    val () = if optionSyntax.is_some (rhs (concl selected)) orelse
        optionSyntax.is_none (rhs (concl selected)) then ()
      else raise Fail ("instruction dispatch remained symbolic: " ^
        term_to_string (rhs (concl selected)))
    val replacements = List.filter (fn (variable,_) => is_var variable)
      (ListPair.zip (symbolic,arguments))
    val concrete = INST (map (fn (variable,value) => variable |-> value)
      replacements) selected
    val value = rhs (concl concrete)
  in if optionSyntax.is_none value then concrete
    else let
      val child = optionSyntax.dest_some value
    in if pairSyntax.is_pair child then concrete
      else TRANS concrete (AP_TERM (rator value)
        (compilerInstructionPlannerEvalLib.checked_call child))
    end
  end

  fun composed_step compute current goal =
    let
      val certificate = evalCompilerBytecodeLib.timed_evaluation
        (fst (strip_comb current)) "planner phase composition"
        (fn () => compute current)
      val () = evalCompilerBytecodeLib.register_compile_eval certificate
      val () = evalCompilerBytecodeLib.pending_stage_values :=
        (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
      val () = compilerPlannerEvalLib.pending := tl (!compilerPlannerEvalLib.pending)
    in Tactical.ALL_TAC goal end
    handle compilerInstructionPlannerEvalLib.InputsPrepared => Tactical.ALL_TAC goal
      | evalCompilerBytecodeLib.PlannerBoundary child =>
          (compilerPlannerEvalLib.pending := child :: !compilerPlannerEvalLib.pending;
           Tactical.ALL_TAC goal)

  fun warm_step (goal as (_,proposition)) = let
    val root = rand proposition
    val () = if Option.isSome (!active) andalso aconv (valOf (!active)) root
      then () else (active := SOME root; inputs := NONE)
    val head = fst (strip_comb root)
    fun prepare () = let
      val (operator,arguments) = strip_comb root
      val certificate = List.foldl (fn (argument,equation) =>
        MK_COMB (equation,
          evalCompilerBytecodeLib.timed_evaluation head "planner input argument"
            (fn () => compilerInstructionPlannerEvalLib.checked_argument argument)))
        (REFL operator) arguments
      val () = inputs := SOME certificate
      val () = compilerPlannerEvalLib.active := SOME root
      val () = compilerPlannerEvalLib.pending := [rhs (concl certificate)]
    in Tactical.ALL_TAC goal end
    fun finish certificate = let
      val normalized = rhs (concl certificate)
      val result = case List.find
          (fn theorem => aconv normalized (lhs (concl theorem)))
          (!evalCompilerBytecodeLib.compiler_certificates) of
        SOME theorem => theorem
      | NONE => raise Fail "completed planner root has no checked equation"
      val evaluated = TRANS certificate result
      val value = rhs (concl evaluated)
      val () = if optionSyntax.is_some value then ()
        else raise Fail "planner root did not return SOME"
      val boundary = EQT_ELIM (TRANS (AP_TERM (rator proposition) evaluated)
        (Rewrite.PURE_REWRITE_CONV [optionTheory.IS_SOME_DEF]
          (mk_comb (rator proposition,value))))
      val () = evalCompilerBytecodeLib.cache_named_results evaluated
    in Tactic.ACCEPT_TAC boundary goal end
  in case !inputs of
    NONE => (prepare () handle compilerInstructionPlannerEvalLib.InputsPrepared =>
      Tactical.ALL_TAC goal)
  | SOME certificate => if null (!compilerPlannerEvalLib.pending)
      then finish certificate
      else let
        val current = hd (!compilerPlannerEvalLib.pending)
        val head = fst (strip_comb current)
      in if same_const head compilerBlockPlannerEvalLib.regular_head then
          composed_step regular_result current goal
        else if same_const head compilerPlannerEvalLib.inst_head then
          composed_step instruction_result current goal
        else if List.exists (fn (query,_) => same_const head query)
            (regular_queries ()) then
          compilerPlannerEvalLib.warm_step_with captures goal
        else compilerModularPlannerEvalLib.warm_step goal
      end
  end
end
