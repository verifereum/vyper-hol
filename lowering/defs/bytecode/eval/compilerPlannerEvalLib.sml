(* One semantic discovery or completed instruction/block per proof fragment. *)
structure compilerPlannerEvalLib = struct
  open HolKernel boolLib stackPlanCleanupCasesTheory
  val block_head = evalCompilerBytecodeLib.planner_block_head
  val inst_head = evalCompilerBytecodeLib.planner_inst_head
  val insts_head = prim_mk_const {Thy="stackPlanGen",Name="generate_block_insts_plan"}
  val function_head = prim_mk_const {Thy="stackPlanGen",Name="generate_fn_plan"}
  val traversal_head = prim_mk_const {Thy="stackPlanGen",Name="generate_fn_plan_aux"}
  val successors_head = prim_mk_const {Thy="stackPlanGen",Name="generate_succs_plan"}
  val cleanup_head = prim_mk_const {Thy="stackPlanGen",Name="clean_stack_plan"}
  val params_head = prim_mk_const {Thy="stackPlanGen",Name="prepare_params_plan"}
  val safety_head = prim_mk_const {Thy="stackPlanGen",Name="cleanup_elision_safe"}
  val cleanup_queries = map (fn name =>
    prim_mk_const {Thy="stackPlanGen",Name=name})
    ["must_halt_labels","cleanup_frame_vars","cleanup_max_transient"]
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  datatype attempt = Complete of thm * thm | Captured of term | Prepared
  val cleanup_configured = ref false

  fun configure () =
    (evalCompilerBytecodeLib.ensure_certificate_head block_head 6;
     evalCompilerBytecodeLib.ensure_certificate_head inst_head 10;
     evalCompilerBytecodeLib.ensure_certificate_head params_head 3;
     evalCompilerBytecodeLib.ensure_certificate_head safety_head 3;
     app (fn (head,arity) => evalCompilerBytecodeLib.ensure_certificate_head head arity)
       (ListPair.zip(cleanup_queries,[2,1,1]));
     if !cleanup_configured then () else let
       val cleanup = cleanup_head
       val tail = prim_mk_const {Thy="stackPlanCleanupCases",Name="planner_cleanup_tail"}
       (* Removing functions also removes their dispatch cells. Install only
          the proved equations, then rebuild memo cells and their callers. *)
       val () = computeLib.del_consts [cleanup,tail]
       val () = computeLib.add_funs [planner_cleanup_case,
         planner_cleanup_singleton,planner_cleanup_nonempty]
       val () = evalCompilerBytecodeLib.certificate_heads := List.filter
         (fn head => not(same_const head cleanup orelse same_const head tail))
         (!evalCompilerBytecodeLib.certificate_heads)
       val () = evalCompilerBytecodeLib.ensure_certificate_head cleanup 5
       val () = evalCompilerBytecodeLib.ensure_certificate_head tail 7
     in cleanup_configured := true end)

  fun capture_heads head =
    if same_const head block_head then [params_head,cleanup_head,inst_head]
    else if same_const head cleanup_head then [safety_head]
    else if same_const head safety_head then cleanup_queries
    else if List.exists (same_const head)
      ([inst_head,params_head] @ cleanup_queries)
      then [] else [block_head]

  fun warm_step_with captures_for (goal as (_,proposition)) = let
    val root = rand proposition
    val () = if Option.isSome (!active) andalso aconv (valOf(!active)) root
      then () else (active := SOME root; pending := [])
    val () = configure ()
    val is_root = null (!pending)
    val current = if is_root then root else hd(!pending)
    val head = fst(strip_comb current)
    val captures = captures_for head
    fun evaluate () = if is_root andalso not(List.exists (same_const head) captures)
        then evalCompilerBytecodeLib.evaluate_call current
      else let
        val inputs = if is_root then evalCompilerBytecodeLib.normalize_call current
          else REFL current
        val normalized = rhs(concl inputs)
        val certificate = evalCompilerBytecodeLib.timed_evaluation head "planner fragment"
          (fn () => if same_const head cleanup_head then
             compilerCleanupEvalLib.compute normalized
           else if same_const head safety_head then
             compilerCleanupEvalLib.compute_safety normalized
           else if same_const head block_head andalso
               List.exists (same_const insts_head) captures then
             compilerBlockCaseEvalLib.compute normalized
           else if same_const head successors_head andalso
               List.exists (same_const traversal_head) captures andalso
               listSyntax.is_cons (List.nth(snd(strip_comb normalized),6)) then
             compilerTraversalCaseEvalLib.compute normalized
           else if same_const head traversal_head andalso
               List.exists (same_const block_head) captures andalso
               (case total listSyntax.dest_cons (List.nth(snd(strip_comb normalized),4)) of
                  SOME (_,rest) => listSyntax.is_nil rest | NONE => false) then
             compilerTraversalCaseEvalLib.compute_function normalized
           else if same_const head insts_head andalso
               listSyntax.is_cons (List.nth(snd(strip_comb normalized),9)) then
             compilerInstructionPlannerEvalLib.compute normalized
           else if List.exists (same_const head)
               [insts_head,traversal_head,successors_head] then let
             (* Expose one equation before capturing recursive suffix calls. *)
             val (name,list_arg,base) =
               if same_const head insts_head then ("generate_block_insts_plan_def",9,0)
               else if same_const head traversal_head then ("generate_fn_plan_aux_def",4,0)
               else ("generate_fn_plan_aux_def",6,2)
             val items = List.nth(snd(strip_comb normalized),list_arg)
             val index = base + (if listSyntax.is_nil items then 0
               else if listSyntax.is_cons items then 1
               else raise Fail "planner suffix was not normalized")
             val equation = if same_const head insts_head andalso index = 1 then
                 DB.fetch "stackPlanInstructionCases" "generate_block_insts_plan_cons"
               else List.nth(CONJUNCTS(SPEC_ALL(DB.fetch "stackPlanGen" name)),index)
             val unfolded = evalCompilerBytecodeLib.timed_evaluation head "planner unfold"
               (fn () => Conv.REWR_CONV equation normalized)
             val evaluated = evalCompilerBytecodeLib.timed_evaluation head "planner body"
               (fn () => computeLib.EVAL_CONV(rhs(concl unfolded)))
           in TRANS unfolded evaluated end
           else computeLib.EVAL_CONV normalized)
      in (TRANS inputs certificate,certificate) end
    val result =
      (Complete (Lib.with_flag (evalCompilerBytecodeLib.planner_capture_heads,captures)
         evaluate ())
       handle evalCompilerBytecodeLib.PlannerBoundary child => Captured child
            | compilerInstructionPlannerEvalLib.InputsPrepared => Prepared)
  in case result of
    Prepared => Tactical.ALL_TAC goal
  | Captured child =>
      (if evalCompilerBytecodeLib.profile_evaluation then
         print ("PLANNER_CAPTURE " ^ #Name(dest_thy_const(fst(strip_comb child))) ^ "\n")
       else ();
       pending := child :: !pending; Tactical.ALL_TAC goal)
  | Complete (evaluated,normalized) => let
      val value = rhs(concl evaluated)
      val optional = is_root orelse List.exists (same_const head)
        [block_head,inst_head,insts_head,function_head,traversal_head,successors_head]
      val () = if not optional orelse optionSyntax.is_some value then ()
        else raise Fail "planner call did not return SOME"
      val () = evalCompilerBytecodeLib.register_compile_eval normalized
      val () = evalCompilerBytecodeLib.pending_stage_values :=
        (NONE,normalized) :: !evalCompilerBytecodeLib.pending_stage_values
    in if not is_root then
        (pending := tl(!pending); Tactical.ALL_TAC goal)
      else let
        val boundary = EQT_ELIM (TRANS (AP_TERM (rator proposition) evaluated)
          (Rewrite.PURE_REWRITE_CONV [optionTheory.IS_SOME_DEF]
            (mk_comb(rator proposition,value))))
      in Tactic.ACCEPT_TAC boundary goal end
    end
  end

  fun warm_step goal = warm_step_with capture_heads goal
end
