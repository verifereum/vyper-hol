(* Compose the already certified analyses before traversing a whole function. *)
structure compilerContextPlannerEvalLib = struct
  open HolKernel boolLib
  fun head name = prim_mk_const {Thy="stackPlanGen",Name=name}
  val analyzed_head = head "generate_fn_plan_analyzed"
  val reorder_head = prim_mk_const {Thy="stackPlanOps",Name="reorder_plan"}
  val reorder_one_head = prim_mk_const {Thy="stackPlanOps",Name="reorder_one"}
  fun reorder_fold_head () = prim_mk_const
    {Thy="stackPlanReorderEval",Name="planner_reorder_fold"}
  fun cleanup_case_head name = prim_mk_const {Thy="stackPlanCleanupCases",Name=name}
  val analysis_boundaries = ref ([] : thm list)
  val rewritten_analysis = ref (NONE : thm option)
  fun add_analysis theorem = analysis_boundaries := theorem :: !analysis_boundaries

  fun lookup_result current = let
    val (state,_) = finite_mapSyntax.dest_flookup current
  in if finite_mapSyntax.is_fempty state then
      Conv.REWR_CONV finite_mapTheory.FLOOKUP_EMPTY current
    else if finite_mapSyntax.is_fupdate state then let
      val unfolded = Conv.REWR_CONV finite_mapTheory.FLOOKUP_UPDATE current
      val condition = Conv.RATOR_CONV (Conv.RATOR_CONV
        (Conv.RAND_CONV computeLib.EVAL_CONV)) (rhs (concl unfolded))
      val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
        (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl condition))
      val prefix = TRANS unfolded (TRANS condition selected)
      val next = rhs (concl prefix)
    in if finite_mapSyntax.is_flookup next then TRANS prefix (lookup_result next)
      else prefix end
    else if same_const (fst (strip_comb state))
        (prim_mk_const {Thy="finite_map",Name="FUNION"}) then let
      val unfolded = Conv.REWR_CONV
        (DB.fetch "dfAnalyzeDefs" "df_flookup_funion") current
      val left = compilerSingleUseEvalLib.argument 1 lookup_result
        (rhs (concl unfolded))
      val selected = Rewrite.PURE_REWRITE_CONV [optionTheory.option_case_def]
        (rhs (concl left))
      val prefix = TRANS unfolded (TRANS left selected)
      val next = rhs (concl prefix)
    in if finite_mapSyntax.is_flookup next then TRANS prefix (lookup_result next)
      else prefix end
    else computeLib.EVAL_CONV current
  end

  fun live_query current = let
    fun timed phase run = evalCompilerBytecodeLib.timed_evaluation
      (fst (strip_comb current)) phase run
    val state = hd (snd (strip_comb current))
    val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of (type_of state)))
    val select = Rewrite.PURE_REWRITE_CONV
      (DB.fetch "dfAnalyzeDefs" "df_state_accfupds" ::
       DB.fetch "combin" "K_THM" :: fields)
    val expanded = Conv.REWR_CONV
      (DB.fetch "livenessDefs" "live_vars_at_def") current
    val unfolded = Conv.REWR_CONV
      (DB.fetch "dfAnalyzeDefs" "df_at_def") (rhs (concl expanded))
    val projected = timed "state projection" (fn () =>
      compilerSingleUseEvalLib.argument 1
        (compilerSingleUseEvalLib.argument 1 select) (rhs (concl unfolded)))
    val looked = timed "map lookup" (fn () =>
      compilerSingleUseEvalLib.argument 1 lookup_result (rhs (concl projected)))
    val result = timed "lookup result" (fn () =>
      computeLib.EVAL_CONV (rhs (concl looked)))
  in TRANS expanded (TRANS unfolded (TRANS projected (TRANS looked result))) end

  fun normalize_query current = let
    val [dfg,visited,operand] = snd (strip_comb current)
    val constructors = TypeBase.constructors_of (type_of operand)
    val is_constructor = List.exists
      (same_const (fst (strip_comb operand))) constructors
  in if not is_constructor then let
      val value = computeLib.EVAL_CONV operand
      val () = if aconv operand (rhs (concl value)) then raise Conv.UNCHANGED else ()
      val inputs = MK_COMB (REFL (rator current),value)
    in TRANS inputs (normalize_query (rhs (concl inputs))) end
    else let
      val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV (CONJUNCTS (SPEC_ALL
        (DB.fetch "dfgDefs" "normalize_operand_def")))) current
    in if #Name (dest_thy_const (fst (strip_comb operand))) <> "Var" then unfolded
      else let
        val condition = Conv.RATOR_CONV (Conv.RATOR_CONV
          (Conv.RAND_CONV computeLib.EVAL_CONV)) (rhs (concl unfolded))
        val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
          (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl condition))
        val prefix = TRANS unfolded (TRANS condition selected)
        val body = rhs (concl prefix)
      in if #Name (dest_thy_const (fst (strip_comb body))) = "Var" then prefix
        else let
          val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
            (TypeBase.accessors_of (type_of dfg)))
          val select = Rewrite.PURE_REWRITE_CONV
            (DB.fetch "dfgDefs" "dfg_analysis_accfupds" ::
             DB.fetch "combin" "K_THM" :: fields)
          val projected = compilerSingleUseEvalLib.argument 1
            (compilerSingleUseEvalLib.argument 1 select) body
          val looked = compilerSingleUseEvalLib.argument 1 lookup_result
            (rhs (concl projected))
          val opaque = genvar (type_of dfg)
          val normalize = prim_mk_const {Thy="dfgDefs",Name="normalize_operand"}
          val recursive = genvar (type_of normalize)
          val body = Term.subst [dfg |-> opaque,normalize |-> recursive]
            (rhs (concl looked))
          val selected = computeLib.EVAL_CONV body
          val concrete = INST [opaque |-> dfg,recursive |-> normalize] selected
          val () = if aconv (lhs (concl concrete)) (rhs (concl looked)) then ()
            else raise Fail "operand continuation did not recover its DFG input"
          val next = rhs (concl concrete)
          val result = if same_const (fst (strip_comb next)) normalize then
              TRANS concrete (normalize_query next)
            else if List.exists (same_const (fst (strip_comb next))) constructors then
              concrete
            else raise Fail "operand continuation did not select a constructor or recursive call"
        in TRANS prefix (TRANS projected (TRANS looked result)) end
      end
    end
  end

  fun equivalent_query current = let
    fun timed phase run = evalCompilerBytecodeLib.timed_evaluation
      (fst (strip_comb current)) phase run
    val unfolded = Conv.REWR_CONV
      (DB.fetch "dfgDefs" "operand_equiv_def") current
    val left = timed "left normalization" (fn () =>
      Conv.LAND_CONV normalize_query (rhs (concl unfolded)))
    val right = timed "right normalization" (fn () =>
      Conv.RAND_CONV normalize_query (rhs (concl left)))
    val result = computeLib.EVAL_CONV (rhs (concl right))
  in TRANS unfolded (TRANS left (TRANS right result)) end

  val query_equations : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)

  fun configure_query query_head arity evaluate = let
    val rules = evalCompilerBytecodeLib.unique_rules (List.concat (List.concat (map
      (fn (_,entries) => map
        (fn clauses.RRules theorems => theorems | clauses.Conversion _ => []) entries)
      (computeLib.listItems (computeLib.the_compset ())))))
    fun headed theorem = same_const query_head
      (fst (strip_comb (lhs (#2 (strip_forall (concl theorem))))))
      handle HOL_ERR _ => false
    val originals = List.filter headed rules
    val callers = List.filter (fn theorem => not (headed theorem) andalso
      HOLset.member (evalCompilerBytecodeLib.dependencies theorem,
        evalCompilerBytecodeLib.constant_key query_head)) rules
    fun convert current =
      case Redblackmap.peek (!query_equations,current) of
        SOME theorem => theorem
      | NONE => if null (free_vars current) then let
          val theorem = evaluate current
          val () = evalCompilerBytecodeLib.register_compile_eval theorem
          val () = query_equations := Redblackmap.insert (!query_equations,current,theorem)
        in theorem end else raise Conv.UNCHANGED
    val () = computeLib.del_consts [query_head]
    val () = computeLib.add_convs [(query_head,arity,convert)]
  in computeLib.add_funs (rev originals @ callers) end

  fun configure () =
    (compilerTraversalPlannerEvalLib.configure ();
     evalCompilerBytecodeLib.ensure_certificate_head analyzed_head 6;
     evalCompilerBytecodeLib.ensure_certificate_head (reorder_fold_head ()) 4;
     evalCompilerBytecodeLib.ensure_certificate_head reorder_one_head 5;
     evalCompilerBytecodeLib.ensure_certificate_head
       (cleanup_case_head "planner_cleanup_single") 6;
     evalCompilerBytecodeLib.ensure_certificate_head
       (cleanup_case_head "planner_cleanup_apply") 4;
     evalCompilerBytecodeLib.ensure_certificate_head
       (prim_mk_const {Thy="livenessDefs",Name="live_vars_at"}) 3;
     evalCompilerBytecodeLib.ensure_certificate_head
       (prim_mk_const {Thy="dfgDefs",Name="normalize_operand"}) 3;
     evalCompilerBytecodeLib.ensure_certificate_head
       (prim_mk_const {Thy="dfgDefs",Name="operand_equiv"}) 3;
     app (fn (theory,name) => evalCompilerBytecodeLib.ensure_certificate_head
       (prim_mk_const {Thy=theory,Name=name}) 1)
       [("livenessDefs","liveness_analyze"),
        ("dfgDefs","dfg_build_function"),("cfgDefs","cfg_analyze")];
     configure_query (prim_mk_const {Thy="livenessDefs",Name="live_vars_at"}) 3 live_query;
     configure_query (prim_mk_const {Thy="dfgDefs",Name="normalize_operand"}) 3 normalize_query;
     configure_query (prim_mk_const {Thy="dfgDefs",Name="operand_equiv"}) 3 equivalent_query)

  fun checked_argument head position argument = let
    fun timed phase run = evalCompilerBytecodeLib.timed_evaluation head
      ("argument " ^ Int.toString position ^ " " ^ phase) run
    val cached = timed "cache" (fn () => List.find
      (fn theorem => aconv argument (lhs (concl theorem)))
      (!compilerInstructionPlannerEvalLib.argument_certificates))
  in case cached of SOME theorem => theorem
    | NONE => let
        val theorem = timed "evaluation" (fn () => computeLib.EVAL_CONV argument)
        val () = compilerInstructionPlannerEvalLib.argument_certificates :=
          theorem :: !compilerInstructionPlannerEvalLib.argument_certificates
      in raise compilerInstructionPlannerEvalLib.InputsPrepared end
  end

  fun checked_call call = let
    val (head,arguments) = strip_comb call
    val cached = evalCompilerBytecodeLib.timed_evaluation head "input call cache"
      (fn () => List.find (fn theorem => aconv call (lhs (concl theorem)))
        (!compilerInstructionPlannerEvalLib.normalization_certificates))
    val inputs = case cached of SOME theorem => theorem
      | NONE => let
          val numbered = List.tabulate (length arguments,fn index =>
            (index + 1,List.nth (arguments,index)))
          val theorem = List.foldl (fn ((position,argument),result) =>
            MK_COMB (result,checked_argument head position argument))
            (REFL head) numbered
          val () = compilerInstructionPlannerEvalLib.normalization_certificates :=
            theorem :: !compilerInstructionPlannerEvalLib.normalization_certificates
        in raise compilerInstructionPlannerEvalLib.InputsPrepared end
    val normalized = rhs (concl inputs)
    val completed = evalCompilerBytecodeLib.timed_evaluation head "completed call cache"
      (fn () => List.find (fn theorem => aconv normalized (lhs (concl theorem)))
        (!evalCompilerBytecodeLib.compiler_certificates))
  in case completed of
    SOME theorem => TRANS inputs theorem
  | NONE => raise evalCompilerBytecodeLib.PlannerBoundary normalized
  end

  fun function_result current = let
    val [func,spill_base,labels] = snd (strip_comb current)
    fun analysis theory name = checked_call
      (boolSyntax.list_mk_icomb (prim_mk_const {Thy=theory,Name=name},[func]))
    val liveness = analysis "livenessDefs" "liveness_analyze"
    val dfg = analysis "dfgDefs" "dfg_build_function"
    val cfg = analysis "cfgDefs" "cfg_analyze"
    val () = app (fn theorem => let val value = rhs (concl theorem)
      in if List.exists (fn certificate => aconv value (lhs (concl certificate)))
          (!compilerInstructionPlannerEvalLib.argument_certificates) then ()
        else compilerTraversalPlannerEvalLib.remember (REFL value)
      end) [liveness,dfg,cfg]
    val equations = [liveness,dfg,cfg,REFL func,REFL spill_base,REFL labels]
    val call = boolSyntax.list_mk_icomb (analyzed_head,map (lhs o concl) equations)
    val inputs = List.foldl (fn (equation,result) => MK_COMB (result,equation))
      (REFL (fst (strip_comb call))) equations
    val child = checked_call (rhs (concl inputs))
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanGen" "generate_fn_plan_def") current
  in TRANS unfolded (TRANS inputs child) end

  val analyzed_cases : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)

  fun analyzed_result current = let
    fun prepare () = let
      val arguments = snd (strip_comb current)
      val [liveness,dfg,cfg,func,spill_base,labels] = arguments
      val symbolic = map (genvar o type_of) arguments
      val [_,_,_,func_variable,spill_variable,labels_variable] = symbolic
      val call = boolSyntax.list_mk_icomb (analyzed_head,symbolic)
      fun timed phase run = evalCompilerBytecodeLib.timed_evaluation
        analyzed_head phase run
      val unfolded = timed "analyzed unfold" (fn () => Conv.REWR_CONV
        (DB.fetch "stackPlanGen" "generate_fn_plan_analyzed_def") call)
      val prepared = map (fn term => timed "analyzed metadata"
        (fn () => compilerInstructionPlannerEvalLib.checked_argument term))
        [``canonical_param_prefix ^func``, ``fn_entry_label ^func``,
         ``(init_plan_state ^spill_base) with ps_label_counter := ^labels``]
      val queries =
        [``canonical_param_prefix ^func_variable``,
         ``fn_entry_label ^func_variable``,
         ``(init_plan_state ^spill_variable) with
             ps_label_counter := ^labels_variable``]
      val premises = ListPair.map (fn (query,theorem) =>
        mk_eq (query,rhs (concl theorem))) (queries,prepared)
      val selected = timed "analyzed entry case" (fn () => TRANS unfolded
        (simpLib.SIMP_CONV boolSimps.bool_ss
          (boolTheory.LET_THM :: optionTheory.option_case_def :: map ASSUME premises)
          (rhs (concl unfolded))))
      val schema = List.foldr (fn (premise,theorem) => DISCH premise theorem)
        selected premises
      val concrete = timed "analyzed instantiate" (fn () => INST
        (ListPair.map (fn (variable,value) => variable |-> value)
          (symbolic,arguments)) schema)
      val checked = List.foldl (fn (premise,theorem) => MP theorem premise)
        concrete prepared
      val () = analyzed_cases := Redblackmap.insert (!analyzed_cases,current,checked)
    in raise compilerInstructionPlannerEvalLib.InputsPrepared end
  in case Redblackmap.peek (!analyzed_cases,current) of
    NONE => prepare ()
  | SOME concrete => let val value = rhs (concl concrete)
    in if optionSyntax.is_none value orelse optionSyntax.is_some value then concrete
      else evalCompilerBytecodeLib.timed_evaluation analyzed_head "analyzed continuation"
        (fn () => compilerInstructionPlannerEvalLib.finish_case concrete)
    end
  end

  fun join_result current = let
    val [liveness,dfg,func,inst,label,ps] = snd (strip_comb current)
    val variables = map (genvar o type_of) [liveness,dfg,func,ps]
    val [live_variable,dfg_variable,func_variable,ps_variable] = variables
    val replacements = ListPair.map (fn (variable,value) => variable |-> value)
      (variables,[liveness,dfg,func,ps])
    val symbolic = boolSyntax.list_mk_icomb
      (compilerExternalPlannerEvalLib.regular_head "planner_regular_join",
       [live_variable,dfg_variable,func_variable,inst,label,ps_variable])
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanRegularCases" "planner_regular_join_def") symbolic
    val opcode = computeLib.EVAL_CONV ``(^inst).inst_opcode``
    val operands = computeLib.EVAL_CONV ``(^inst).inst_operands``
    val selected = TRANS unfolded (simpLib.SIMP_CONV (bossLib.srw_ss())
      [opcode,operands,boolTheory.LET_THM] (rhs (concl unfolded)))
    fun checked head arguments = checked_call
      (boolSyntax.list_mk_icomb (head,arguments))
    fun finish theorem = let
      val result = rhs (concl theorem)
    in if pairSyntax.is_pair result then theorem
      else TRANS theorem (checked_call result)
    end
  in if pairSyntax.is_pair (rhs (concl selected)) then INST replacements selected
    else let
      val ([operand],_) = listSyntax.dest_list (rhs (concl operands))
      val target = rand operand
      val lookup_head = prim_mk_const {Thy="venomInst",Name="lookup_block"}
      val lookup = checked lookup_head [target,``(^func).fn_blocks``]
      val lookup_premise = mk_eq
        (boolSyntax.list_mk_icomb (lookup_head,
          [target,``(^func_variable).fn_blocks``]),rhs (concl lookup))
      val found = TRANS selected (simpLib.SIMP_CONV (bossLib.srw_ss())
        [ASSUME lookup_premise,boolTheory.LET_THM] (rhs (concl selected)))
    in if optionSyntax.is_none (rhs (concl lookup)) then
        MP (INST replacements (DISCH lookup_premise found)) lookup
      else let
        val live_head = prim_mk_const {Thy="livenessDefs",Name="live_vars_at"}
        val live = checked live_head [liveness,target,``0:num``]
        val live_premise = mk_eq
          (boolSyntax.list_mk_icomb (live_head,[live_variable,target,``0:num``]),
           rhs (concl live))
        val stack = TRANS found (simpLib.SIMP_CONV (bossLib.srw_ss())
          [ASSUME live_premise,boolTheory.LET_THM] (rhs (concl found)))
        val (operator,arguments) = strip_comb (rhs (concl stack))
        val operands_eq = computeLib.EVAL_CONV (List.nth (arguments,1))
        val prepared = List.foldl (fn (equation,result) => MK_COMB (result,equation))
          (REFL operator) [REFL dfg_variable,operands_eq,REFL ps_variable]
        val schema = INST replacements (DISCH lookup_premise
          (DISCH live_premise (TRANS stack prepared)))
      in finish (MP (MP schema lookup) live) end
    end
  end

  fun reorder_plan_result current = let
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanReorderEval" "reorder_plan_fold") current
    val (operator,arguments) = strip_comb (rhs (concl unfolded))
    val equations = List.tabulate (length arguments,fn index =>
      if index = 2 then computeLib.EVAL_CONV (List.nth (arguments,index))
      else REFL (List.nth (arguments,index)))
    val inputs = List.foldl (fn (equation,result) => MK_COMB (result,equation))
      (REFL operator) equations
    val result = checked_call (rhs (concl inputs))
  in TRANS unfolded (TRANS inputs result) end

  fun reorder_fold_result current = let
    val [dfg,targets,items,accumulator] = snd (strip_comb current)
  in if listSyntax.is_nil items then
      Conv.REWR_CONV (hd (CONJUNCTS (SPEC_ALL
        (DB.fetch "stackPlanReorderEval" "planner_reorder_fold_def")))) current
    else let
      val (item,rest) = listSyntax.dest_cons items
      val (index,operand) = pairSyntax.dest_pair item
      val (ops,ps) = pairSyntax.dest_pair accumulator
      val step = checked_call
        (boolSyntax.list_mk_icomb (reorder_one_head,[dfg,targets,index,operand,ps]))
      val (step_ops,next_ps) = pairSyntax.dest_pair (rhs (concl step))
      val theorem = DB.fetch "stackPlanReorderEval" "planner_reorder_fold_cons_result"
      val (variables,_) = strip_forall (concl theorem)
      val arguments = [dfg,targets,index,operand,rest,ops,ps,step_ops,next_ps]
      val schema = INST (ListPair.map (fn (variable,value) => variable |-> value)
        (variables,arguments)) (SPECL variables theorem)
      val selected = MP schema step
      val result = checked_call (rhs (concl selected))
    in TRANS selected result end
  end

  fun predicate_result worker_name bridge_name current = let
    val (current_head,arguments) = strip_comb current
    val dfg = hd arguments
    val equivalent = mk_comb
      (prim_mk_const {Thy="dfgDefs",Name="operand_equiv"},dfg)
    val predicate = genvar (type_of equivalent)
    val worker = prim_mk_const
      {Thy="stackPlanReorderEval",Name=worker_name}
    val call = boolSyntax.list_mk_icomb (worker,predicate :: tl arguments)
    val evaluated = evalCompilerBytecodeLib.timed_evaluation current_head
      "symbolic stack operations" (fn () => computeLib.EVAL_CONV call)
    val concrete = INST [predicate |-> equivalent] evaluated
    val bridge = Conv.REWR_CONV
      (DB.fetch "stackPlanReorderEval" bridge_name) current
    val selected = TRANS bridge concrete
    (* Stop at each query before traversing its large DFG argument. *)
    fun predicates term = let
      val (operator,operands) = strip_comb term
    in if is_const operator andalso same_const operator
          (prim_mk_const {Thy="dfgDefs",Name="operand_equiv"}) then
        if length operands = 3 andalso null (free_vars term) then
          equivalent_query term
        else REFL term
      else if is_comb term then Conv.COMB2_CONV (predicates,predicates) term
      else if is_abs term then Conv.ABS_CONV predicates term
      else REFL term
    end
    val queries = evalCompilerBytecodeLib.timed_evaluation current_head
      "direct operand queries" (fn () => predicates (rhs (concl selected)))
    val result = evalCompilerBytecodeLib.timed_evaluation current_head
      "concrete operand decisions" (fn () => computeLib.EVAL_CONV (rhs (concl queries)))
  in TRANS selected (TRANS queries result) end

  fun conditional_pair_result definition guard current = let
    val (operator,arguments) = strip_comb current
    val symbolic = map (genvar o type_of) arguments
    val evidence = checked_argument operator 1 (guard arguments)
    val value = rhs (concl evidence)
    val () = if aconv value T orelse aconv value F then ()
      else raise Fail "block prefix guard was not concrete"
    val premise = mk_eq (guard symbolic,value)
    val call = boolSyntax.list_mk_icomb (operator,symbolic)
    val unfolded = Conv.REWR_CONV (DB.fetch "stackPlanBlockCases" definition) call
    val selected = TRANS unfolded (simpLib.SIMP_CONV boolSimps.bool_ss
      [ASSUME premise] (rhs (concl unfolded)))
    val schema = INST (ListPair.map (fn (variable,value) => variable |-> value)
      (symbolic,arguments)) (DISCH premise selected)
    val concrete = MP schema evidence
  in if pairSyntax.is_pair (rhs (concl concrete)) then concrete
    else TRANS concrete (checked_call (rhs (concl concrete)))
  end

  fun block_entry_result current = conditional_pair_result "planner_block_entry_def"
    (fn [_,func,bb,_] => ``^bb = HD (^func).fn_blocks``
      | _ => raise Fail "invalid block entry arguments") current

  fun block_cleanup_result current = conditional_pair_result "planner_block_cleanup_def"
    (fn [_,cfg,_,bb,_] => ``LENGTH (cfg_preds_of ^cfg (^bb).bb_label) = 1``
      | _ => raise Fail "invalid block cleanup arguments") current

  fun instructions_result current = let
    val (current_head,arguments) = strip_comb current
    fun timed phase run = evalCompilerBytecodeLib.timed_evaluation
      current_head phase run
    val (inst,rest) = listSyntax.dest_cons (List.nth (arguments,9))
    fun prepare name = let
      val generic = SPEC_ALL (DB.fetch "stackPlanInstructionCases" name)
      fun conclusion theorem = snd (dest_imp (concl theorem))
      val generic_head = fst (strip_comb (lhs (conclusion generic)))
      val typed = INST_TYPE (Type.match_type (type_of generic_head)
        (type_of current_head)) generic
      val variables = snd (strip_comb (lhs (conclusion typed)))
      val (inst_variable,rest_variable) = listSyntax.dest_cons (List.nth (variables,9))
      val ordinary = List.tabulate (length arguments,fn position =>
        (List.nth (variables,position),List.nth (arguments,position)))
      val replacements = List.filter (is_var o fst) ordinary @
        [(inst_variable,inst),(rest_variable,rest)]
    in (typed,replacements) end
    val (some_schema,some_replacements) = timed "suffix template"
      (fn () => prepare "generate_block_insts_plan_some")
    val instruction = timed "instruction term substitution" (fn () =>
      Term.subst (map (fn (variable,value) => variable |-> value) some_replacements)
        (lhs (fst (dest_imp (concl some_schema)))))
    val instruction_arguments = snd (strip_comb instruction)
    val () = timed "liveness input proof" (fn () =>
      compilerPlanMetadataEvalLib.prepare_liveness checked_call
        (List.nth (instruction_arguments,5)) rest)
    val () = timed "terminator input proof" (fn () =>
      compilerPlanMetadataEvalLib.prepare_terminator
        (List.nth (instruction_arguments,7)) rest)
    val evidence = checked_call instruction
    val value = rhs (concl evidence)
    val (typed,replacements,outputs) =
      if optionSyntax.is_none value then let
        val (schema,replacements) = prepare "generate_block_insts_plan_none"
      in (schema,replacements,[]) end
      else if optionSyntax.is_some value then let
        val expected = rhs (fst (dest_imp (concl some_schema)))
        val (ops_variable,ps_variable) = pairSyntax.dest_pair (optionSyntax.dest_some expected)
        val (ops,next_ps) = pairSyntax.dest_pair (optionSyntax.dest_some value)
      in (some_schema,some_replacements,[(ops_variable,ops),(ps_variable,next_ps)]) end
      else raise Fail "instruction result was not a concrete option"
    val schema = timed "suffix instantiate" (fn () => INST
      (map (fn (variable,value) => variable |-> value) (replacements @ outputs)) typed)
    val selected = timed "suffix premise" (fn () => MP schema evidence)
  in if optionSyntax.is_none value then selected
    else timed "suffix continuation"
      (fn () => compilerInstructionPlannerEvalLib.finish_case selected)
  end

  fun plan_step goal =
    case !compilerPlannerEvalLib.pending of
      current::_ => let val current_head = fst (strip_comb current)
        in if same_const current_head compilerPlannerEvalLib.function_head then
            compilerExternalPlannerEvalLib.composed_step function_result current goal
          else if same_const current_head analyzed_head then
            compilerExternalPlannerEvalLib.composed_step analyzed_result current goal
          else if same_const current_head
              (compilerExternalPlannerEvalLib.regular_head "planner_regular_join") then
            compilerExternalPlannerEvalLib.composed_step join_result current goal
          else if same_const current_head (compilerBlockPlannerEvalLib.entry_head ()) then
            compilerExternalPlannerEvalLib.composed_step block_entry_result current goal
          else if same_const current_head (compilerBlockPlannerEvalLib.cleanup_head ()) then
            compilerExternalPlannerEvalLib.composed_step block_cleanup_result current goal
          else if same_const current_head compilerPlannerEvalLib.cleanup_head then
            compilerExternalPlannerEvalLib.composed_step
              (compilerPlanCleanupEvalLib.clean_result checked_call
                (checked_argument current_head 1)) current goal
          else if same_const current_head (cleanup_case_head "planner_cleanup_single") then
            compilerExternalPlannerEvalLib.composed_step
              (compilerPlanCleanupEvalLib.single_result checked_call
                (checked_argument current_head 1)) current goal
          else if same_const current_head reorder_head then
            compilerExternalPlannerEvalLib.composed_step reorder_plan_result current goal
          else if same_const current_head
              (prim_mk_const {Thy="livenessDefs",Name="live_vars_at"}) then
            compilerExternalPlannerEvalLib.composed_step live_query current goal
          else if same_const current_head (reorder_fold_head ()) then
            compilerExternalPlannerEvalLib.composed_step reorder_fold_result current goal
          else if same_const current_head reorder_one_head then
            compilerExternalPlannerEvalLib.composed_step
              (predicate_result "planner_reorder_one" "reorder_one_planner") current goal
          else if same_const current_head (head "optimistic_swap_plan") then
            compilerExternalPlannerEvalLib.composed_step
              (predicate_result "planner_optimistic_swap" "optimistic_swap_planner") current goal
          else if same_const current_head compilerPlannerEvalLib.insts_head andalso
              listSyntax.is_cons (List.nth (snd (strip_comb current),9)) then
            compilerExternalPlannerEvalLib.composed_step instructions_result current goal
          else if same_const current_head
              (compilerExternalPlannerEvalLib.regular_head "planner_regular_finish") then
            compilerExternalPlannerEvalLib.composed_step
              (compilerPlanFinishEvalLib.compute checked_call) current goal
          else compilerTraversalPlannerEvalLib.warm_step goal
        end
    | [] => compilerTraversalPlannerEvalLib.warm_step goal

  fun finish goal =
    if null (!compilerPlannerEvalLib.pending) then
      compilerExternalPlannerEvalLib.warm_step goal
    else let
      val current = hd (!compilerPlannerEvalLib.pending)
      val operator = fst (strip_comb current)
      val name = if is_const operator then #Name (dest_thy_const operator) else "unknown"
    in raise Fail ("planner preparation incomplete: " ^
      Int.toString (length (!compilerPlannerEvalLib.pending)) ^
      " pending calls; next " ^ name) end

  fun warm_step goal =
    case !analysis_boundaries of
      [] => plan_step goal
    | boundary::_ => (case !rewritten_analysis of
        NONE => let
          val alias = rhs (concl boundary)
          val named = Redblackmap.find (!compilerTraversalPlannerEvalLib.named,alias)
          val certificate = TRANS boundary named
          val call = lhs (concl certificate)
          val projected = AP_TERM (rator call)
            (compilerTraversalPlannerEvalLib.replace_named (rand call))
          val () = rewritten_analysis := SOME (TRANS (SYM projected) certificate)
        in Tactical.ALL_TAC goal end
      | SOME certificate => let
          val normalized = evalCompilerBytecodeLib.normalize_compile_eval certificate
          val () = evalCompilerBytecodeLib.register_compile_eval normalized
          val () = evalCompilerBytecodeLib.pending_stage_values :=
            (NONE,normalized) :: !evalCompilerBytecodeLib.pending_stage_values
          val () = analysis_boundaries := tl (!analysis_boundaries)
          val () = rewritten_analysis := NONE
        in Tactical.ALL_TAC goal end)

  (* Keep proof-history growth bounded while yielding between native steps.
     holbuild still applies its normal timeout to each complete slice. *)
  fun warm_slice goal = let
    val started = Time.now ()
    fun advance remaining goal =
      if remaining = 0 orelse
          Time.- (Time.now (),started) >= Time.fromReal 0.005 then
        Tactical.ALL_TAC goal
      else Tactical.THEN (warm_step,advance (remaining - 1)) goal
  in advance 8 goal end
end
