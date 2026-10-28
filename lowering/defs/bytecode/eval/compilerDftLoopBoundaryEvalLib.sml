(* Compose exact outer worklist cases without revisiting large analyses. *)
structure compilerDftLoopBoundaryEvalLib = struct
  open HolKernel boolLib
  val step_head = compilerDftEvalLib.step_head

  fun step_result current = let
    val arguments = snd (strip_comb current)
    val analyses = List.take (arguments,3)
    val (state,tail) = pairSyntax.dest_pair (List.nth (arguments,3))
    val (work,done) = pairSyntax.dest_pair tail
    fun law name values = ISPECL values (DB.fetch "venomDftLoopCases" name)
  in if aconv done T then
      law "dft_loop_step_done_tuple" (analyses @ [state,work])
    else if not (aconv done F) then raise Fail "DFT done flag is not a Boolean value"
    else if listSyntax.is_nil work then
      law "dft_loop_step_empty" (analyses @ [state])
    else let
      val (label,rest) = listSyntax.dest_cons work
      val child = compilerDftBoundaryEvalLib.checked
        (boolSyntax.list_mk_icomb (compilerDftEvalLib.process_head,
          analyses @ [state,label]))
      val (next,result) = pairSyntax.dest_pair (rhs (concl child))
      val (converged,preds) = pairSyntax.dest_pair result
      val certificate = MP
        (law "dft_loop_step_cons_result"
          (analyses @ [state,label,rest,next,converged,preds])) child
      val body = rhs (concl certificate)
      val tested = compilerDftWorklistEvalLib.argument 1 computeLib.EVAL_CONV body
      val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
        (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl tested))
      val labels = Conv.RAND_CONV (Conv.RATOR_CONV (Conv.RAND_CONV
        computeLib.EVAL_CONV)) (rhs (concl selected))
    in TRANS certificate (TRANS tested (TRANS selected labels)) end
  end

  fun warm_call call goal =
    (case !compilerDftWorklistEvalLib.pending of
        current::_ =>
          if Option.isSome (!compilerDftWorklistEvalLib.active) andalso
              aconv (valOf (!compilerDftWorklistEvalLib.active)) call andalso
              same_const (fst (strip_comb current)) step_head then let
            val certificate = evalCompilerBytecodeLib.timed_evaluation step_head
              "checked outer worklist case" (fn () => step_result current)
            val () = if aconv (lhs (concl certificate)) current then ()
              else raise Fail "DFT loop case changed its original call"
            val () = evalCompilerBytecodeLib.register_compile_eval certificate
            val () = compilerDftWorklistEvalLib.equations := Redblackmap.insert
              (!compilerDftWorklistEvalLib.equations,current,certificate)
            val () = evalCompilerBytecodeLib.pending_stage_values :=
              (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
            val () = compilerDftWorklistEvalLib.pending :=
              tl (!compilerDftWorklistEvalLib.pending)
          in Tactical.ALL_TAC goal end
          else compilerDftBoundaryEvalLib.warm_call call goal
      | [] => compilerDftBoundaryEvalLib.warm_call call goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerDftWorklistEvalLib.pending :=
        child :: !compilerDftWorklistEvalLib.pending;
       Tactical.ALL_TAC goal)
end

