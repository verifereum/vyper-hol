(* TOP-LEVEL: configure. Observe guarded-fold metadata without walking
   opaque runner, policy or pass-list arguments. All six guards remain checked. *)
structure compilerFnFoldEvalLib = struct
  open HolKernel boolLib
  fun result current = let
    val [runner,rpolicy,passes,unit,supply,func,labels] = snd (strip_comb current)
    val (pass,_) = listSyntax.dest_cons passes
    val observed_eq = compilerPassEffectsEvalLib.checked
      (list_mk_comb (prim_mk_const
        {Thy="venomFnScheduleRunner",Name="unit_with_current_fn"},[unit,func]))
    val observed = optionSyntax.dest_some (rhs (concl observed_eq))
    val output_eq = compilerPassEffectsEvalLib.checked
      (list_mk_comb (runner,[rpolicy,pass,observed,supply,func]))
    val out = optionSyntax.dest_some (rhs (concl output_eq))
    val constructor = PART_MATCH (lhs o snd o dest_imp)
      (MATCH_MP (DB.fetch "venomFnScheduleCases"
        "run_configured_fn_pass_fold_cons_result") (CONJ observed_eq output_eq)) current
    val types = map type_of [runner,rpolicy,passes,unit,supply,func,labels,out]
    val record_types = map type_of [unit,supply,func,out]
    val getters = List.concat (map
      (#1 o compilerPassEffectsEvalLib.record_rules) record_types)
    val k = prim_mk_const {Thy="combin",Name="K"}
    fun observe term = let val operator = fst (strip_comb term)
      in if is_const operator andalso
          (same_const operator k orelse List.exists (same_const operator) getters) then
        compilerPassEffectsEvalLib.observe record_types term
      else if List.exists (fn typ => type_of term = typ) types then REFL term
      else if is_comb term then MK_COMB (observe (rator term),observe (rand term))
      else if is_abs term then let val (variable,body) = dest_abs term
        in ABS variable (observe body) end
      else REFL term end
    val head = fst (strip_comb current)
    val projected = evalCompilerBytecodeLib.timed_evaluation head
      "guard metadata projection" (fn () => observe
        (fst (dest_imp (concl constructor))))
    fun certify atom =
      if is_const (fst (strip_comb atom)) andalso
          List.exists (same_const (fst (strip_comb atom)))
            (compilerPassEffectsEvalLib.head "fn_pass_effects_hold" ::
             compilerPassEffectsEvalLib.head "introduces_no_invoke_edges" ::
             compilerSupplyBoundaryEvalLib.guards ()) then
        compilerPassEffectsEvalLib.checked atom
      else computeLib.EVAL_CONV atom
    val facts = evalCompilerBytecodeLib.timed_evaluation head
      "six checked guards" (fn () => LIST_CONJ (map (EQT_ELIM o certify)
        (strip_conj (rhs (concl projected)))))
    val composed = MP constructor (EQ_MP (SYM projected) facts)
    val tail = evalCompilerBytecodeLib.timed_evaluation head
      "continuation metadata projection" (fn () => observe (rhs (concl composed)))
  in TRANS composed tail end

  fun complete current = let
    val prefix = Conv.FIRST_CONV [result,Conv.REWR_CONV
      (hd (CONJUNCTS (SPEC_ALL (DB.fetch "venomFnScheduleRunner"
        "run_configured_fn_pass_fold_def"))))] current
    val body = rhs (concl prefix)
  in if same_const (fst (strip_comb body)) compilerPassEvalLib.fold_head then let
      val labels = compilerSingleUseEvalLib.argument 7 computeLib.EVAL_CONV body
      val remaining = compilerPassEffectsEvalLib.checked (rhs (concl labels))
    in TRANS prefix (TRANS labels remaining) end
    else prefix
  end

  fun warm_step next goal =
    (case !compilerPassEvalLib.pending of
      current::_ => if same_const (fst (strip_comb current))
          compilerPassEvalLib.fold_head then let
        val certificate = evalCompilerBytecodeLib.timed_evaluation
          compilerPassEvalLib.fold_head "checked full fold composition"
          (fn () => complete current)
        val () = if aconv (lhs (concl certificate)) current then ()
          else raise Fail "function fold changed its original call"
        val () = evalCompilerBytecodeLib.register_compile_eval certificate
        val () = compilerPassEvalLib.equations := Redblackmap.insert
          (!compilerPassEvalLib.equations,current,certificate)
        val () = evalCompilerBytecodeLib.pending_stage_values :=
          (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
        val () = compilerPassEvalLib.pending := tl (!compilerPassEvalLib.pending)
      in Tactical.ALL_TAC goal end
      else next goal
    | [] => next goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerPassEvalLib.pending := child :: !compilerPassEvalLib.pending;
       Tactical.ALL_TAC goal)

  fun effects_result current = let
    val head = fst (strip_comb current)
    val prefix = evalCompilerBytecodeLib.timed_evaluation head
      "effect metadata projection" (fn () => compilerPassEffectsEvalLib.effects_step current)
    fun reduce term =
      if boolSyntax.is_eq term andalso aconv (lhs term) (rhs term) then
        EQT_INTRO (REFL (lhs term))
      else if boolSyntax.is_conj term then let
        val (left,right) = boolSyntax.dest_conj term
        val joined = MK_COMB
          (AP_TERM (rator (rator term)) (reduce left),reduce right)
      in TRANS joined (computeLib.EVAL_CONV (rhs (concl joined))) end
      else computeLib.EVAL_CONV term
    val checked = evalCompilerBytecodeLib.timed_evaluation head
      "reflexive metadata comparisons" (fn () => reduce (rhs (concl prefix)))
  in TRANS prefix checked end

  fun configure () = compilerPassEvalLib.extend_phases []
    [(compilerPassEvalLib.fold_head,Conv.FIRST_CONV [result,Conv.REWR_CONV
      (hd (CONJUNCTS (SPEC_ALL (DB.fetch "venomFnScheduleRunner"
        "run_configured_fn_pass_fold_def"))))]),
     (compilerPassEffectsEvalLib.head "fn_pass_effects_hold",effects_result)] []
end
