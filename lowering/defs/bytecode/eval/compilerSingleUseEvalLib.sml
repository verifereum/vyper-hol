(* Exact constructor boundaries for the existing supply-aware SUE traversal. *)
structure compilerSingleUseEvalLib = struct
  open HolKernel boolLib

  fun argument position conversion current = let
    fun descend 0 = Conv.RAND_CONV conversion
      | descend n = Conv.RATOR_CONV (descend (n - 1))
  in descend (length (snd (strip_comb current)) - position) current end

  fun uses_step current = let
    val dfg = hd (snd (strip_comb current))
    val accessors = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of (type_of dfg)))
    val select_field = Rewrite.PURE_REWRITE_CONV
      (DB.fetch "dfgDefs" "dfg_empty_def" ::
       DB.fetch "dfgDefs" "dfg_analysis_accfupds" ::
       DB.fetch "combin" "K_THM" :: accessors)
    val step = Conv.REWR_CONV (DB.fetch "dfgDefs" "dfg_get_uses_def") current
    val projected = argument 1 (argument 1 select_field) (rhs (concl step))
    val lookup = argument 1 compilerPassEvalLib.evaluate_flookup (rhs (concl projected))
    val result = computeLib.EVAL_CONV (rhs (concl lookup))
  in TRANS step (TRANS projected (TRANS lookup result)) end

  fun guard_observation current =
    if boolSyntax.is_conj current then let
      val left = Conv.RATOR_CONV (Conv.RAND_CONV guard_observation) current
      val right = Conv.RAND_CONV guard_observation (rhs (concl left))
      val result = computeLib.EVAL_CONV (rhs (concl right))
    in TRANS left (TRANS right result) end
    else if same_const (fst (strip_comb current))
        (prim_mk_const {Thy="venomFnScheduleRunner",Name="list_subset"}) then
      compilerPassEvalLib.checked_call current
    else if same_const (fst (strip_comb current))
        (prim_mk_const {Thy="list",Name="EVERY"}) then let
      val predicate = argument 1 (Conv.ABS_CONV computeLib.EVAL_CONV) current
      val result = computeLib.EVAL_CONV (rhs (concl predicate))
    in TRANS predicate result end
    else computeLib.EVAL_CONV current

  fun supply_guard name current = let
    val head = fst (strip_comb current)
    val supply = hd (snd (strip_comb current))
    val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of (type_of supply)))
    val step = evalCompilerBytecodeLib.timed_evaluation head "supply unfold"
      (fn () => Conv.REWR_CONV
        (DB.fetch "venomFnScheduleRunner" (name ^ "_def")) current)
    val projected = evalCompilerBytecodeLib.timed_evaluation head "supply fields"
      (fn () => let val body = rhs (concl step)
        in Rewrite.PURE_REWRITE_CONV fields body
           handle Conv.UNCHANGED => REFL body end)
    val result = guard_observation (rhs (concl projected))
  in TRANS step (TRANS projected result) end

  fun needs_step current =
    Conv.REWR_CONV (DB.fetch "singleUseExpansionDefs" "sue_needs_assign_def") current

  fun finish_step current = let
    val step = Conv.REWR_CONV
      (DB.fetch "venomSingleUseEval" "sue_finish_operand_direct") current
    val test = argument 1 computeLib.EVAL_CONV (rhs (concl step))
    val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl test))
    val prefix = TRANS step (TRANS test selected)
    val body = rhs (concl prefix)
  in if same_const (fst (strip_comb body))
        (prim_mk_const {Thy="venomSingleUseEval",Name="sue_prepend_assignment"}) then let
      val assigned = Conv.RAND_CONV compilerPassEvalLib.checked_call body
      val result = Conv.REWR_CONV
        (DB.fetch "venomSingleUseEval" "sue_prepend_assignment_def")
        (rhs (concl assigned))
    in TRANS prefix (TRANS assigned result) end
    else prefix
  end

  fun operand_step current = let
    val step = Conv.REWR_CONV
      (DB.fetch "venomSingleUseEval" "sue_expand_ops_supply_step") current
    val needs = argument 2 compilerPassEvalLib.checked_call (rhs (concl step))
    val remaining = argument 3 computeLib.EVAL_CONV (rhs (concl needs))
    val uses = argument 4 compilerPassEvalLib.checked_call (rhs (concl remaining))
    fun tail_result call = let
      val index = Conv.RAND_CONV computeLib.EVAL_CONV call
      val result = compilerPassEvalLib.checked_call (rhs (concl index))
    in TRANS index result end
    val tail = argument 5 tail_result (rhs (concl uses))
    val result = compilerPassEvalLib.checked_call (rhs (concl tail))
  in TRANS step (TRANS needs (TRANS remaining (TRANS uses (TRANS tail result)))) end

  fun constructor_step first_name rest_name theorem_name current = let
    val args = snd (strip_comb current)
    val dfg = List.nth (args,0)
    val supply = List.nth (args,1)
    val (item,rest) = listSyntax.dest_cons (List.nth (args,2))
    fun head name = prim_mk_const {Thy="singleUseExpansionDefs",Name=name}
    val first = compilerPassEvalLib.checked_call
      (list_mk_comb (head first_name,[dfg,supply,item]))
    val (_,supply1) = pairSyntax.dest_pair (rhs (concl first))
    val tail = compilerPassEvalLib.checked_call
      (list_mk_comb (head rest_name,[dfg,supply1,rest]))
    val result = MATCH_MP (DB.fetch "venomSingleUseEval" theorem_name) (CONJ first tail)
    val () = if aconv (lhs (concl result)) current then ()
      else raise Fail "SUE constructor equation has the wrong input"
  in result
  end

  val insts_step = constructor_step "sue_expand_inst_supply"
    "sue_expand_insts_supply" "sue_expand_insts_supply_cons_result"
  val blocks_step = constructor_step "sue_expand_block_supply"
    "sue_expand_blocks_supply" "sue_expand_blocks_supply_cons_result"

  fun block_step current = let
    val args = snd (strip_comb current)
    val block = List.nth (args,2)
    val instructions = Parse.Term [QUOTE "(",ANTIQUOTE block,QUOTE ").bb_instructions"]
    val call = list_mk_comb
      (prim_mk_const {Thy="singleUseExpansionDefs",Name="sue_expand_insts_supply"},
       [List.nth(args,0),List.nth(args,1),instructions])
    val projected = Conv.RAND_CONV computeLib.EVAL_CONV call
    val result = compilerPassEvalLib.checked_call (rhs (concl projected))
  in MATCH_MP (DB.fetch "venomSingleUseEval" "sue_expand_block_supply_result")
       (TRANS projected result) end

  fun warm_step goal =
    case !compilerPassEvalLib.pending of [] => compilerPassEvalLib.warm_step goal
    | call::_ =>
      if same_const (fst (strip_comb call))
          (prim_mk_const {Thy="venomFnScheduleRunner",Name="list_subset"}) then
        (case !compilerGuardEvalLib.subset_pending of
          SOME (saved,_,_,[],_) =>
            if aconv saved call then compilerPassEvalLib.warm_step goal
            else compilerGuardEvalLib.warm_subset call goal
        | _ => compilerGuardEvalLib.warm_subset call goal)
      else compilerPassEvalLib.warm_step goal

  fun configure () = let
    fun head name = prim_mk_const {Thy="singleUseExpansionDefs",Name=name}
    fun eval_head name = prim_mk_const {Thy="venomSingleUseEval",Name=name}
    val entries =
      [(head "sue_expand_function_supply",2),
       (head "sue_expand_blocks_supply",3),
       (head "sue_expand_block_supply",3),
       (head "sue_expand_insts_supply",3),
       (head "sue_expand_inst_supply",3),
       (head "sue_expand_ops_supply",5),
       (head "sue_needs_assign",3),
       (head "sue_alloc_assign_supply",2),
       (eval_head "sue_finish_operand",5),
       (eval_head "sue_operand_use_count",2),
       (prim_mk_const {Thy="dfgDefs",Name="dfg_get_uses"},2),
       (prim_mk_const {Thy="dfgDefs",Name="dfg_build_function"},1)]
    fun runner name = prim_mk_const {Thy="venomFnScheduleRunner",Name=name}
    val guards =
      [(runner "ir_supply_extends",2),(runner "ir_supply_covers_fn",2),
       (runner "ir_supply_covers_unit",2),(runner "list_subset",2),
       (prim_mk_const {Thy="venomPassDispatcher",Name="fn_pass_effects_hold"},3),
       (prim_mk_const {Thy="venomPassDispatcher",Name="introduces_no_invoke_edges"},2)]
    fun unfold name = (head name,Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL (DB.fetch "singleUseExpansionDefs" (name ^ "_def"))))))
    val unfolds =
      [(head "sue_expand_blocks_supply",Conv.FIRST_CONV
        [blocks_step,#2 (unfold "sue_expand_blocks_supply")]),
       (head "sue_expand_insts_supply",Conv.FIRST_CONV
        [insts_step,#2 (unfold "sue_expand_insts_supply")])] @
      [(head "sue_expand_ops_supply",Conv.FIRST_CONV
        [operand_step,#2 (unfold "sue_expand_ops_supply")]),
       (eval_head "sue_finish_operand",finish_step),
       (head "sue_needs_assign",needs_step),
       (head "sue_expand_block_supply",block_step),
       (prim_mk_const {Thy="dfgDefs",Name="dfg_get_uses"},uses_step)] @
      map (fn name => (runner name,supply_guard name))
        ["ir_supply_extends","ir_supply_covers_fn","ir_supply_covers_unit"]
    val captures =
      [(evalCompilerBytecodeLib.scheduled_fold_head,
          evalCompilerBytecodeLib.scheduled_pass_head :: map #1 guards),
       (evalCompilerBytecodeLib.scheduled_function_head,
          evalCompilerBytecodeLib.scheduled_fold_head :: map #1 guards),
       (head "sue_expand_blocks_supply",
          [head "sue_expand_block_supply",head "sue_expand_blocks_supply"]),
       (head "sue_expand_insts_supply",
          [head "sue_expand_inst_supply",head "sue_expand_insts_supply"]),
       (head "sue_expand_ops_supply",
          [head "sue_expand_ops_supply",head "sue_needs_assign",
           head "sue_alloc_assign_supply",
           eval_head "sue_finish_operand",eval_head "sue_operand_use_count",
           prim_mk_const {Thy="dfgDefs",Name="dfg_get_uses"}])]
  in compilerPassEvalLib.extend_phases (entries @ guards) unfolds captures;
     app compilerPassEvalLib.install_indexed_head entries
  end
end
