(* Keep large analyses outside stack branches and cost comparisons. *)
structure compilerDftBoundaryEvalLib = struct
  open HolKernel boolLib
  val step_head = prim_mk_const {Thy="stackOrderInternalDefs",Name="so_step"}
  val sort_head = prim_mk_const {Thy="dftDefs",Name="sort_children"}
  val cost_head = prim_mk_const {Thy="dftDefs",Name="dft_cost"}
  val dfs_head = prim_mk_const {Thy="dftDefs",Name="dfs_step"}
  val deps_head = prim_mk_const {Thy="dftDefs",Name="inst_all_deps"}

  fun checked query =
    case Redblackmap.peek (!compilerDftWorklistEvalLib.equations,query) of
      SOME certificate => certificate
    | NONE => raise evalCompilerBytecodeLib.PlannerBoundary query

  fun step_result current = let
    val arguments = snd (strip_comb current)
    val symbolic = List.tabulate (length arguments,fn index =>
      if index < 3 then genvar (type_of (List.nth (arguments,index)))
      else List.nth (arguments,index))
    val call = boolSyntax.list_mk_icomb (step_head,symbolic)
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackOrderInternalDefs" "so_step_def") call
    val selected = evalCompilerBytecodeLib.timed_evaluation step_head
      "symbolic instruction branch" (fn () => computeLib.EVAL_CONV (rhs (concl unfolded)))
    val replacements = List.tabulate (3,fn index =>
      List.nth (symbolic,index) |-> List.nth (arguments,index))
    val concrete = INST replacements (TRANS unfolded selected)
    val () = if aconv (lhs (concl concrete)) current then ()
      else raise Fail "stack-order branch did not recover its original inputs"
    val result = evalCompilerBytecodeLib.timed_evaluation step_head
      "selected analysis queries" (fn () => computeLib.EVAL_CONV (rhs (concl concrete)))
  in TRANS concrete result end

  fun indexed_lists term = let
    val operator = fst (strip_comb term)
  in if is_const operator andalso #Name (dest_thy_const operator) = "MAPi" then
      computeLib.EVAL_CONV term
    else if is_comb term then Conv.COMB2_CONV (indexed_lists,indexed_lists) term
    else if is_abs term then Conv.ABS_CONV indexed_lists term
    else REFL term
  end

  fun sort_result current = let
    val arguments = snd (strip_comb current)
    val children = List.nth (arguments,5)
    val values = #1 (listSyntax.dest_list children)
    fun cost child = let
      val query = boolSyntax.list_mk_icomb
        (cost_head,List.take (arguments,5) @ [child])
    in case Redblackmap.peek (!compilerDftWorklistEvalLib.equations,query) of
        SOME certificate => certificate
      | NONE => raise evalCompilerBytecodeLib.PlannerBoundary query
    end
    val costs = map cost values
    val symbolic = map (genvar o type_of) (List.take (arguments,5))
    val premises = ListPair.map (fn (child,certificate) => mk_eq
      (boolSyntax.list_mk_icomb (cost_head,symbolic @ [child]),
       rhs (concl certificate))) (values,costs)
    val call = boolSyntax.list_mk_icomb (sort_head,symbolic @ [children])
    val unfolded = Conv.REWR_CONV (DB.fetch "dftDefs" "sort_children_def") call
    val indexed = Conv.CONV_RULE (Conv.RAND_CONV indexed_lists) unfolded
    val selected = evalCompilerBytecodeLib.timed_evaluation sort_head
      "numeric cost ordering" (fn () => simpLib.SIMP_CONV (bossLib.srw_ss())
        (DB.fetch "sorting" "QSORT_DEF" :: DB.fetch "sorting" "PARTITION_DEF" ::
         DB.fetch "sorting" "PART_DEF" ::
         pairTheory.pair_case_thm :: boolTheory.LET_THM :: map ASSUME premises)
        (rhs (concl indexed)))
    val () = if listSyntax.is_list (rhs (concl selected)) then ()
      else raise Fail "child ordering remained symbolic after its cost premises"
    val schema = List.foldr (fn (premise,theorem) => DISCH premise theorem)
      (TRANS indexed selected) premises
    val replacements = ListPair.map (fn (variable,value) => variable |-> value)
      (symbolic,List.take (arguments,5))
    val concrete = INST replacements schema
    val result = List.foldl (fn (certificate,theorem) => MP theorem certificate)
      concrete costs
    val () = if aconv (lhs (concl result)) current then ()
      else raise Fail "child ordering did not recover its original inputs"
  in result end

  fun state_projection expression state = let
    val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
      (TypeBase.accessors_of (type_of state)))
    val selected = Rewrite.PURE_REWRITE_CONV
      (DB.fetch "dftDefs" "dfs_state_accfupds" ::
       DB.fetch "combin" "K_THM" :: fields) expression
  in TRANS selected (computeLib.EVAL_CONV (rhs (concl selected))) end

  fun dfs_result current = let
    val arguments = snd (strip_comb current)
    val state = List.nth (arguments,5)
    val stack = evalCompilerBytecodeLib.timed_evaluation dfs_head
      "work-stack projection" (fn () =>
        state_projection ``(^state).ds_stack`` state)
    fun apply name extra facts = let
      val generic = DB.fetch "venomDfsCases" name
      val (_,formula) = strip_forall (concl generic)
      val schema_head = fst (strip_comb (lhs (snd (dest_imp formula))))
      val theorem = INST_TYPE (Type.match_type (type_of schema_head)
        (type_of (fst (strip_comb current)))) generic
      val (variables,_) = strip_forall (concl theorem)
      val schema = INST (ListPair.map (fn (variable,value) => variable |-> value)
        (variables,arguments @ extra)) (SPECL variables theorem)
      val premise = if length facts = 1 then hd facts else LIST_CONJ facts
      val result = MP schema premise
    in evalCompilerBytecodeLib.timed_evaluation dfs_head
      "known work-item update" (fn () =>
        Conv.CONV_RULE (Conv.RAND_CONV computeLib.EVAL_CONV) result) end
    val items = rhs (concl stack)
  in if listSyntax.is_nil items then apply "dfs_step_empty" [] [stack]
    else let
      val (item,rest) = listSyntax.dest_cons items
      val (operator,values) = strip_comb item
      val inst = hd values
    in if #Name (dest_thy_const operator) = "DfsEmit" then
        apply "dfs_step_emit" [inst,rest] [stack]
      else if #Name (dest_thy_const operator) <> "DfsProcess" then
        raise Fail "unrecognized native DFS work item"
      else let
        val visited = state_projection ``(^state).ds_visited`` state
        val identifier = computeLib.EVAL_CONV ``(^inst).inst_id``
        val member_call = ``MEM (^inst).inst_id (^state).ds_visited``
        val inputs = Rewrite.PURE_REWRITE_CONV [identifier,visited] member_call
        val membership = TRANS inputs (computeLib.EVAL_CONV (rhs (concl inputs)))
      in if aconv (rhs (concl membership)) T then
          apply "dfs_step_visited" [inst,rest] [stack,EQT_ELIM membership]
        else let
          val pseudo = computeLib.EVAL_CONV ``is_pseudo (^inst).inst_opcode``
          val fresh = EQF_ELIM membership
        in if aconv (rhs (concl pseudo)) T then
            apply "dfs_step_pseudo" [inst,rest] [stack,fresh,EQT_ELIM pseudo]
          else let
            val dependencies = checked (boolSyntax.list_mk_icomb
              (deps_head,List.take (arguments,3) @ [inst]))
            val children = rhs (concl dependencies)
            val ordered = checked (boolSyntax.list_mk_icomb
              (sort_head,List.take (arguments,4) @ [inst,children]))
            val sorted = rhs (concl ordered)
          in apply "dfs_step_process" [inst,rest,children,sorted]
            [stack,fresh,EQF_ELIM pseudo,dependencies,ordered] end
        end
      end
    end
  end

  fun warm_call call goal =
    case !compilerDftWorklistEvalLib.pending of
      current::_ =>
        if Option.isSome (!compilerDftWorklistEvalLib.active) andalso
            aconv (valOf (!compilerDftWorklistEvalLib.active)) call andalso
            List.exists (same_const (fst (strip_comb current)))
              [step_head,sort_head,dfs_head] then let
          val certificate = if same_const (fst (strip_comb current)) step_head then
            step_result current
            else if same_const (fst (strip_comb current)) sort_head then
              sort_result current else dfs_result current
          val () = evalCompilerBytecodeLib.register_compile_eval certificate
          val () = compilerDftWorklistEvalLib.equations := Redblackmap.insert
            (!compilerDftWorklistEvalLib.equations,current,certificate)
          val () = evalCompilerBytecodeLib.pending_stage_values :=
            (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
          val () = compilerDftWorklistEvalLib.pending :=
            tl (!compilerDftWorklistEvalLib.pending)
        in Tactical.ALL_TAC goal end
        handle evalCompilerBytecodeLib.PlannerBoundary child =>
          (compilerDftWorklistEvalLib.pending :=
             child :: !compilerDftWorklistEvalLib.pending;
           Tactical.ALL_TAC goal)
        else compilerDftWorklistEvalLib.warm_call call goal
    | [] => compilerDftWorklistEvalLib.warm_call call goal
end
