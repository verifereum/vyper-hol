(* Compose the original memory-allocation queries from checked children. *)
structure compilerMemoryFrameEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="concretizeMemLocDefs",Name=name}
  fun frame_head () = head "call_frame_reservations"
  fun allocation_head () = head "compute_alloc_map_fuel_in_context"
  fun configure () = app compilerPassEvalLib.install_indexed_head
    [(frame_head (),3),(allocation_head (),7)]
  val allocation_work = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)

  fun checked call = case Redblackmap.peek (!compilerPassEvalLib.equations,call) of
      SOME certificate => certificate
    | NONE => raise evalCompilerBytecodeLib.PlannerBoundary call

  fun value call =
    if is_const (fst (strip_comb call)) andalso
       List.exists (same_const (fst (strip_comb call))) (!compilerPassEvalLib.phase_heads)
    then checked call else computeLib.EVAL_CONV call

  fun remember current certificate goal = let
    val () = evalCompilerBytecodeLib.register_compile_eval certificate
    val () = compilerPassEvalLib.equations := Redblackmap.insert
      (!compilerPassEvalLib.equations,current,certificate)
    val () = evalCompilerBytecodeLib.pending_stage_values :=
      (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
    val () = compilerPassEvalLib.pending := tl (!compilerPassEvalLib.pending)
  in Tactical.ALL_TAC goal end

  fun frame_result current = let
    val unfolded = Conv.REWR_CONV
      (DB.fetch "concretizeMemLocDefs" "call_frame_reservations_def") current
    val mapped = Conv.RAND_CONV (listLib.MAP_CONV checked) (rhs (concl unfolded))
    val flattened = computeLib.EVAL_CONV (rhs (concl mapped))
  in TRANS unfolded (TRANS mapped flattened) end

  fun allocation_step current goal =
    case Redblackmap.peek (!allocation_work,current) of
      NONE => let
        val unfolded = Conv.REWR_CONV
          (DB.fetch "concretizeMemLocDefs" "compute_alloc_map_fuel_in_context_def") current
        val () = allocation_work := Redblackmap.insert
          (!allocation_work,current,unfolded)
      in Tactical.ALL_TAC goal end
    | SOME prefix => let
        val body = rhs (concl prefix)
        val (operator,arguments) = strip_comb body
      in if same_const operator ``LET`` then let
          val argument = List.nth (arguments,1)
          val evaluated = evalCompilerBytecodeLib.timed_evaluation
            (allocation_head ()) "allocation binding" (fn () => value argument)
          val projected = Conv.RAND_CONV (fn _ => evaluated) body
          val unfolded = Conv.REWR_CONV boolTheory.LET_THM (rhs (concl projected))
          val reduced = BETA_CONV (rhs (concl unfolded))
          val result = TRANS prefix (TRANS projected (TRANS unfolded reduced))
          val () = allocation_work := Redblackmap.insert
            (!allocation_work,current,result)
        in Tactical.ALL_TAC goal end
        else remember current (TRANS prefix (checked body)) goal
      end

  fun warm_step goal =
    (case !compilerPassEvalLib.pending of
        current::_ => let val operator = fst (strip_comb current)
          in if same_const operator (frame_head ()) then
              remember current
                (evalCompilerBytecodeLib.timed_evaluation (frame_head ())
                  "checked reservation map" (fn () => frame_result current)) goal
            else if same_const operator (allocation_head ()) then allocation_step current goal
            else compilerSingleUseEvalLib.warm_step goal
          end
      | [] => compilerSingleUseEvalLib.warm_step goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerPassEvalLib.pending := child :: !compilerPassEvalLib.pending;
       Tactical.ALL_TAC goal)
end

