(* Exact recursive composition for the existing bounded DFT worklist.
   Other corpus evaluators continue using compilerDftEvalLib unchanged. *)
structure compilerDftWorklistEvalLib = struct
  open HolKernel boolLib
  val step_head = compilerDftEvalLib.step_head
  val loop_head = compilerDftEvalLib.loop_head
  val process_head = compilerDftEvalLib.process_head
  val analyze_head = compilerDftEvalLib.analyze_head
  val order_head = compilerDftEvalLib.order_head
  val block_head = compilerDftEvalLib.block_head
  val fold_head = prim_mk_const {Thy="list",Name="FOLDL"}
  val equations = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)
  val completed = ref ([] : term list)
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  datatype attempt = Complete of thm | Pending of term

  fun block_phases () = map (fn (name,arity) =>
    (prim_mk_const {Thy="dftDefs",Name=name},arity))
    [("build_eda",1),("build_offspring_map",2),("entry_instructions",3),
     ("schedule_from_entries",5)]

  fun dfs_phases () = map (fn (name,arity) =>
    (prim_mk_const {Thy="dftDefs",Name=name},arity))
    [("dfs_run_fuel",3),("dfs_step",6),("inst_all_deps",4),
     ("sort_children",6),("dft_cost",6)]

  fun analysis_phases () =
    [(prim_mk_const {Thy="cfgDefs",Name="cfg_analyze"},1),
     (prim_mk_const {Thy="livenessDefs",Name="liveness_analyze"},1),
     (prim_mk_const {Thy="livenessDefs",Name="liveness_block"},4),
     (prim_mk_const {Thy="livenessDefs",Name="liveness_changed"},4),
     (prim_mk_const {Thy="worklistDefs",Name="wl_iterate"},5),
     (prim_mk_const {Thy="worklistDefs",Name="wl_step"},4)]

  fun stack_phases () = map (fn (name,arity) =>
    (prim_mk_const {Thy="stackOrderInternalDefs",Name=name},arity))
    [("so_analyze_succ",5),("so_record_from_to",4),("so_step",6)]

  fun argument position conversion current = let
    fun descend 0 = Conv.RAND_CONV conversion
      | descend n = Conv.RATOR_CONV (descend (n - 1))
  in descend (length (snd (strip_comb current)) - position) current end

  fun checked_call current =
    case Redblackmap.peek (!equations,current) of SOME theorem => theorem
    | NONE => raise evalCompilerBytecodeLib.PlannerBoundary current

  fun condition facts current = let
    val projected = Rewrite.PURE_REWRITE_CONV facts current
      handle Conv.UNCHANGED => REFL current
  in TRANS projected (computeLib.EVAL_CONV (rhs (concl projected))) end

  fun loop_result loop unfold facts current = let
    val unfolded = unfold current
  in if not (boolSyntax.is_cond (rhs (concl unfolded))) then unfolded else let
    val test = argument 1 (condition facts) (rhs (concl unfolded))
    val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl test))
    val prefix = TRANS unfolded (TRANS test selected)
    val body = rhs (concl prefix)
  in if not (same_const (fst (strip_comb body)) loop) then prefix
    else let
      val fuel = argument 2 computeLib.EVAL_CONV body
      val step = argument 3 checked_call (rhs (concl fuel))
      val tail = checked_call (rhs (concl step))
    in TRANS prefix (TRANS fuel (TRANS step tail)) end
  end end

  fun unfold_dfs current = let
    val fuel = List.nth (snd (strip_comb current),1)
    val exposed = if numSyntax.int_of_term fuel = 0 then REFL current
      else argument 2 numLib.num_CONV current
    val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL (DB.fetch "dftDefs" "dfs_run_fuel_def"))))
      (rhs (concl exposed))
  in TRANS exposed unfolded end

  fun iterate_result current = let
    val unfolded = Conv.REWR_CONV (DB.fetch "worklistDefs" "wl_iterate_def") current
  in TRANS unfolded (checked_call (rhs (concl unfolded))) end

  fun fold_result current = let
    val unfolded = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL listTheory.FOLDL))) current
    val body = rhs (concl unfolded)
  in if not (same_const (fst (strip_comb body)) fold_head) then unfolded
    else let
      val step = argument 2 checked_call body
      val tail = checked_call (rhs (concl step))
    in TRANS unfolded (TRANS step tail) end
  end

  fun analyze_result current = let
    val law = ISPECL (snd (strip_comb current))
      (DB.fetch "venomStackOrderEval" "so_analyze_block_result")
    val premise = fst (dest_imp (concl (SPEC_ALL law)))
    val call = lhs premise
    val initial = argument 2 computeLib.EVAL_CONV call
    val folded = TRANS initial (checked_call (rhs (concl initial)))
    val result = MATCH_MP law folded
    val observed = computeLib.EVAL_CONV (rhs (concl result))
  in TRANS result observed end

  fun work_step_result current = let
    val [changed,process,deps,pair] = snd (strip_comb current)
    val (worklist,state) = pairSyntax.dest_pair pair
    val (label,rest) = listSyntax.dest_cons worklist
    val processed = checked_call (list_mk_comb (process,[label,state]))
    val next = rhs (concl processed)
    val change = checked_call (list_mk_comb (changed,[label,state,next]))
    val law = ISPECL [changed,process,deps,label,rest,state,next,rhs (concl change)]
      (DB.fetch "venomWorklistEval" "wl_step_cons_result")
    val result = MATCH_MP law (CONJ processed change)
    val labels = Conv.RATOR_CONV (Conv.RAND_CONV computeLib.EVAL_CONV)
      (rhs (concl result))
  in TRANS result labels end

  fun while_result current = let
    val unfolded = Conv.REWR_CONV (DB.fetch "While" "WHILE") current
    fun test term = let
      val beta = if is_comb term andalso is_abs (rator term)
        then Thm.BETA_CONV term else REFL term
      val result = condition [pairTheory.FST,pairTheory.SND] (rhs (concl beta))
    in TRANS beta result end
    val tested = argument 1 test (rhs (concl unfolded))
    val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl tested))
    val prefix = TRANS unfolded (TRANS tested selected)
    val body = rhs (concl prefix)
  in if not (same_const (fst (strip_comb body)) (fst (strip_comb current))) then prefix
    else let
      val step = argument 3 checked_call body
      val tail = checked_call (rhs (concl step))
    in TRANS prefix (TRANS step tail) end
  end

  fun configure () = let
    val entries = [(fold_head,3),(step_head,4),(loop_head,3),(process_head,5),
      (analyze_head,5),(order_head,5),(block_head,2)] @
      block_phases () @ dfs_phases () @ analysis_phases () @ stack_phases ()
    val () = app (fn (head,arity) =>
      evalCompilerBytecodeLib.ensure_certificate_head head arity) entries
  in app (compilerSsaEvalLib.install_indexed_head equations) entries end

  fun require_complete call goal =
    if List.exists (aconv call) (!completed) then Tactical.ALL_TAC goal
    else raise Fail ("DFT preparation incomplete: " ^
      Int.toString (length (!pending)) ^ " pending calls")

  fun warm_call call goal =
    if List.exists (aconv call) (!completed) then Tactical.ALL_TAC goal else let
      val () = if Option.isSome (!active) andalso aconv (valOf (!active)) call
        then () else (active := SOME call; pending := [])
      val is_root = null (!pending)
      val current = if is_root then call else hd (!pending)
      val head = fst (strip_comb current)
      val block_children = map #1 (block_phases ())
      val [dfs_loop,dfs_step,all_deps,sort,cost] = map #1 (dfs_phases ())
      val [cfg,live,live_block,live_changed,iterate,work_step] =
        map #1 (analysis_phases ())
      val while_head = prim_mk_const {Thy="While",Name="WHILE"}
      val [successor,record,stack_step] = map #1 (stack_phases ())
      val schedule = #1 (List.last (block_phases ()))
      val captures = if same_const head live then [cfg,iterate]
        else if same_const head work_step then [live_block,live_changed]
        else if List.exists (same_const head) [cfg,live_block,live_changed] then []
        else if same_const head order_head then [fold_head]
        else if same_const head successor then [analyze_head,record]
        else if same_const head analyze_head then [fold_head]
        else if same_const head fold_head then []
        else if List.exists (same_const head) [record,stack_step] then []
        else if same_const head dfs_loop then [dfs_step,dfs_loop]
        else if same_const head dfs_step then [all_deps,sort]
        else if same_const head sort then [cost]
        else if List.exists (same_const head) [all_deps,cost] then []
        else if same_const head schedule then [dfs_loop]
        else if same_const head loop_head then [step_head,loop_head]
        else if same_const head step_head then [process_head]
        else if same_const head process_head then [analyze_head,order_head,block_head]
        else if same_const head block_head then block_children
        else if List.exists (same_const head) block_children then
          List.filter (fn child => not (same_const head child)) block_children
        else if List.exists (same_const head) [analyze_head,order_head]
          then [] else [cfg,live,loop_head]
      fun evaluate () = if is_root then
          snd (evalCompilerBytecodeLib.evaluate_call current)
        else evalCompilerBytecodeLib.timed_evaluation head "DFT worklist"
          (fn () => if same_const head loop_head then
              loop_result loop_head (Conv.REWR_CONV
                (DB.fetch "venomDftEval" "dft_loop_run_fuel_unfold"))
                [pairTheory.SND] current
            else if same_const head dfs_loop then let
              val state = List.nth (snd (strip_comb current),2)
              val fields = List.concat (map (CONJUNCTS o SPEC_ALL)
                (TypeBase.accessors_of (type_of state)))
            in loop_result dfs_loop unfold_dfs fields current end
            else if same_const head iterate then iterate_result current
            else if same_const head fold_head then fold_result current
            else if same_const head analyze_head then analyze_result current
            else if same_const head work_step then work_step_result current
            else if same_const head while_head then while_result current
            else if same_const head schedule then let
              val unfolded = Conv.REWR_CONV
                (DB.fetch "dftDefs" "schedule_from_entries_compute") current
              val result = computeLib.EVAL_CONV (rhs (concl unfolded))
            in TRANS unfolded result end
            else computeLib.EVAL_CONV current)
      val result = (Complete (Lib.with_flag
        (evalCompilerBytecodeLib.planner_capture_heads,captures) evaluate ())
        handle evalCompilerBytecodeLib.PlannerBoundary child => Pending child)
      val () = case result of Pending child => pending := child :: !pending
      | Complete certificate =>
          (evalCompilerBytecodeLib.timed_evaluation head "DFT register"
             (fn () => evalCompilerBytecodeLib.register_compile_eval certificate);
           evalCompilerBytecodeLib.timed_evaluation head "DFT memo"
             (fn () => equations := Redblackmap.insert
               (!equations,lhs (concl certificate),certificate));
           evalCompilerBytecodeLib.pending_stage_values :=
             (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values;
           if is_root then completed := call :: !completed
           else pending := tl (!pending))
    in Tactical.ALL_TAC goal end
end
