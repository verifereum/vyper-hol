(* One actual DFT worklist step per instrumented preparation fragment. *)
structure compilerDftEvalLib = struct
  open HolKernel boolLib
  val step_head = prim_mk_const {Thy="dftDefs",Name="dft_loop_step"}
  val loop_head = prim_mk_const {Thy="dftDefs",Name="dft_loop_run_fuel"}
  val process_head = prim_mk_const {Thy="dftDefs",Name="dft_process_one"}
  val analyze_head = prim_mk_const {Thy="stackOrderInternalDefs",Name="so_analyze_block"}
  val order_head = prim_mk_const {Thy="stackOrderDefs",Name="so_get_stack"}
  val block_head = prim_mk_const {Thy="dftDefs",Name="dft_block"}
  val completed = ref ([] : term list)
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  datatype attempt = Complete of thm | Pending of term

  fun warm_call call goal =
    if List.exists (aconv call) (!completed) then Tactical.ALL_TAC goal else let
      val () = if Option.isSome (!active) andalso aconv (valOf(!active)) call
        then () else (active := SOME call; pending := [])
      val () = evalCompilerBytecodeLib.ensure_certificate_head step_head 4
      val () = evalCompilerBytecodeLib.ensure_certificate_head loop_head 3
      val () = app (fn (head,arity) =>
          evalCompilerBytecodeLib.ensure_certificate_head head arity)
        [(process_head,5),(analyze_head,5),(order_head,5),(block_head,2)]
      fun remember certificate =
        (evalCompilerBytecodeLib.register_compile_eval certificate;
         evalCompilerBytecodeLib.pending_stage_values :=
           (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values)
      val is_root = null (!pending)
      val current = if is_root then call else hd(!pending)
      val head = fst(strip_comb current)
      val captures = if same_const head loop_head then [step_head,loop_head]
        else if same_const head step_head then [process_head]
        else if same_const head process_head then [analyze_head,order_head,block_head]
        else if List.exists (same_const head) [analyze_head,order_head,block_head]
          then [] else [loop_head]
      fun evaluate () = if is_root then
          snd(evalCompilerBytecodeLib.evaluate_call current)
        else let
          val unfolded = if same_const head loop_head then
            Conv.REWR_CONV (DB.fetch "venomDftEval" "dft_loop_run_fuel_unfold") current
            else REFL current
          val result = evalCompilerBytecodeLib.timed_evaluation head "DFT fragment"
            (fn () => computeLib.EVAL_CONV(rhs(concl unfolded)))
        in TRANS unfolded result end
      val result =
        (Complete (Lib.with_flag (evalCompilerBytecodeLib.planner_capture_heads,captures)
           evaluate ())
         handle evalCompilerBytecodeLib.PlannerBoundary child => Pending child)
      val () = case result of
        Pending child => pending := child :: !pending
      | Complete certificate =>
          (remember certificate;
           if is_root then completed := call :: !completed else pending := tl(!pending))
    in Tactical.ALL_TAC goal end
end
