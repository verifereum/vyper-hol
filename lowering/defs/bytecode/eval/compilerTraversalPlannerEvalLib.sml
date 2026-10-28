(* Reuse exported named analyses before evaluating planner input projections. *)
structure compilerTraversalPlannerEvalLib = struct
  open HolKernel boolLib
  val named : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  val rewritten = ref (NONE : thm option)

  fun configure () =
    (compilerExternalPlannerEvalLib.configure ();
     app (fn theory => app (fn (name,theorem) =>
       if String.isPrefix "parity_stage_value_" name then
         named := Redblackmap.insert (!named,lhs (concl theorem),theorem)
       else ()) (DB.thms theory))
       ["evalCompilerBytecodeAbiExternalCallsLowering",
        "evalCompilerBytecodeAbiExternalCallsMemory",
        "evalCompilerBytecodeAbiExternalCallsSingleUse",
        "evalCompilerBytecodeAbiExternalCallsDft",
        "evalCompilerBytecodeAbiExternalCallsPipeline",
        "evalCompilerBytecodeAbiExternalCallsAnalysis",
        "evalCompilerBytecodeAbiExternalCallsEntry"])

  (* Stop at a named value: its potentially large result remains opaque here. *)
  fun replace_named term =
    case Redblackmap.peek (!named,term) of
      SOME theorem => theorem
    | NONE => if is_comb term then let
        val (operator,argument) = dest_comb term
      in MK_COMB (replace_named operator,replace_named argument) end
      else if is_abs term then let
        val (variable,body) = dest_abs term
      in ABS variable (replace_named body) end
      else REFL term

  fun remember theorem =
    compilerInstructionPlannerEvalLib.argument_certificates :=
      theorem :: !compilerInstructionPlannerEvalLib.argument_certificates

  fun reorder_result current = let
    val [dfg,opcode,operands,ps] = snd (strip_comb current)
    val dfg_variable = genvar (type_of dfg)
    val ps_variable = genvar (type_of ps)
    val reorder_head = prim_mk_const {Thy="stackPlanOps",Name="reorder_plan"}
    val symbolic = boolSyntax.list_mk_icomb
      (compilerExternalPlannerEvalLib.regular_head "planner_regular_reorder",
       [dfg_variable,opcode,operands,ps_variable])
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanRegularCases" "planner_regular_reorder_def") symbolic
    val condition = computeLib.EVAL_CONV
      ``is_commutative ^opcode /\ LENGTH ^operands >= 2``
    val replacements = [dfg_variable |-> dfg,ps_variable |-> ps]
    fun checked operands = compilerInstructionPlannerEvalLib.checked_call
      (boolSyntax.list_mk_icomb (reorder_head,[dfg,operands,ps]))
  in if aconv (rhs (concl condition)) F then let
      val selected = TRANS unfolded (simpLib.SIMP_CONV boolSimps.bool_ss
        [condition] (rhs (concl unfolded)))
      val concrete = INST replacements selected
    in TRANS concrete (checked operands) end
    else let
      val swapped = computeLib.EVAL_CONV
        ``TAKE (LENGTH ^operands - 2) ^operands ++
          [EL (LENGTH ^operands - 1) ^operands;
           EL (LENGTH ^operands - 2) ^operands]``
      val first = checked operands
      val second = checked (rhs (concl swapped))
      fun premise operands result = mk_eq
        (boolSyntax.list_mk_icomb
          (reorder_head,[dfg_variable,operands,ps_variable]),result)
      val first_premise = premise operands (rhs (concl first))
      val second_premise = premise (rhs (concl swapped)) (rhs (concl second))
      val selected = TRANS unfolded (simpLib.SIMP_CONV (bossLib.srw_ss())
        [condition,swapped,boolTheory.LET_THM,
         ASSUME first_premise,ASSUME second_premise] (rhs (concl unfolded)))
      val schema = INST replacements
        (DISCH first_premise (DISCH second_premise selected))
      val result = MP (MP schema first) second
    in Conv.CONV_RULE (Conv.RAND_CONV computeLib.EVAL_CONV) result end
  end

  fun warm_step (goal as (_,proposition)) = let
    val root = rand proposition
    val head = fst (strip_comb root)
    val () = if Option.isSome (!active) andalso aconv (valOf (!active)) root
      then () else (active := SOME root; pending := snd (strip_comb root);
                    rewritten := NONE)
    fun advance () = (pending := tl (!pending); rewritten := NONE)
  in case !pending of
    [] => (case !compilerPlannerEvalLib.pending of
        current::_ => if same_const (fst (strip_comb current))
            (compilerExternalPlannerEvalLib.regular_head "planner_regular_reorder") then
          compilerExternalPlannerEvalLib.composed_step reorder_result current goal
        else compilerExternalPlannerEvalLib.warm_step goal
      | [] => compilerExternalPlannerEvalLib.warm_step goal)
  | argument::_ =>
      if List.exists (fn theorem => aconv argument (lhs (concl theorem)))
          (!compilerInstructionPlannerEvalLib.argument_certificates) then
        (advance (); Tactical.ALL_TAC goal)
      else case Redblackmap.peek (!named,argument) of
        SOME theorem => (remember theorem; advance (); Tactical.ALL_TAC goal)
      | NONE => (case !rewritten of
          NONE =>
            (rewritten := SOME (evalCompilerBytecodeLib.timed_evaluation head
               "planner named input" (fn () => replace_named argument));
             Tactical.ALL_TAC goal)
        | SOME certificate => let
            val result = evalCompilerBytecodeLib.timed_evaluation head
              "planner input projection"
              (fn () => computeLib.EVAL_CONV (rhs (concl certificate)))
            val () = remember (TRANS certificate result)
            val () = advance ()
          in Tactical.ALL_TAC goal end)
  end
end
