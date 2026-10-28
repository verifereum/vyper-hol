(* Discharge the actual instruction-result case before its large continuation. *)
structure compilerInstructionPlannerEvalLib = struct
  open HolKernel boolLib
  exception InputsPrepared
  val normalization_certificates = ref ([] : thm list)
  val argument_certificates = ref ([] : thm list)

  fun checked_argument argument =
    case List.find (fn th => aconv argument (lhs(concl th)))
        (!argument_certificates) of
      SOME certificate => certificate
    | NONE => let
        val certificate = computeLib.EVAL_CONV argument
        val () = argument_certificates := certificate :: !argument_certificates
      in raise InputsPrepared end

  fun checked_call call = let
    val inputs = case List.find (fn th => aconv call (lhs(concl th)))
        (!normalization_certificates) of
      SOME certificate => certificate
    | NONE => let
        val (head,args) = strip_comb call
        val certificate = evalCompilerBytecodeLib.timed_evaluation head
          "planner call inputs" (fn () =>
            List.foldl (fn (argument,equation) =>
                MK_COMB(equation,checked_argument argument)) (REFL head) args)
        val () = normalization_certificates := certificate :: !normalization_certificates
      in raise InputsPrepared end
    val normalized = rhs(concl inputs)
  in case List.find (fn th => aconv normalized (lhs(concl th)))
      (!evalCompilerBytecodeLib.compiler_certificates) of
    SOME certificate => TRANS inputs certificate
  | NONE => raise evalCompilerBytecodeLib.PlannerBoundary normalized
  end

  fun finish_case selected = let
    val continuation = rhs(concl selected)
    val (case_head,args) = strip_comb continuation
    val tail = checked_call (hd args)
    val substituted = List.foldl (fn (arg,th) => AP_THM th arg)
      (AP_TERM case_head tail) (tl args)
    val evaluated = computeLib.EVAL_CONV(rhs(concl substituted))
  in TRANS selected (TRANS substituted evaluated) end

  fun compute call = let
    val [liveness,dfg,cfg,func,label,halting,nparams,block_len,index,insts,ps] =
      snd(strip_comb call)
    val (inst,rest) = listSyntax.dest_cons insts
    val next_live =
      ``if ^rest = [] then live_vars_at ^liveness ^label ^block_len
        else live_vars_at ^liveness ^label (^index + ^nparams + 1)``
    val next_term =
      ``case ^rest of [] => F | next_i::_ => is_terminator next_i.inst_opcode``
    val instruction = boolSyntax.list_mk_icomb(evalCompilerBytecodeLib.planner_inst_head,
      [liveness,dfg,cfg,func,inst,next_live,halting,next_term,label,ps])
    val evidence = checked_call instruction
    val result = rhs(concl evidence)
    val name = if optionSyntax.is_some result then "generate_block_insts_plan_some"
      else if optionSyntax.is_none result then "generate_block_insts_plan_none"
      else raise Fail "instruction result was not a concrete option"
    val selected = evalCompilerBytecodeLib.timed_evaluation
      (fst(strip_comb call)) "instruction result case" (fn () =>
        PART_MATCH lhs
          (MATCH_MP (SPEC_ALL(DB.fetch "stackPlanInstructionCases" name)) evidence) call)
  in if optionSyntax.is_none result then selected else finish_case selected
  end
end
