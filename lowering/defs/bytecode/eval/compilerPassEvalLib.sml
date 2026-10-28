(* TOP-LEVEL: configure installs dispatch metadata; warm_step certifies one
   transition of an actual optional schedule call per instrumented tactic.
   Reuses evalCompilerBytecodeLib certificates and its capture boundaries.
   A captured child is deferred to the next tactic, as in compilerDftEvalLib. *)
structure compilerPassEvalLib = struct
  open HolKernel boolLib
  val function_head = evalCompilerBytecodeLib.scheduled_function_head
  val fold_head = evalCompilerBytecodeLib.scheduled_fold_head
  val pass_head = evalCompilerBytecodeLib.scheduled_pass_head
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  val completed = ref ([] : term list)
  val phase_heads = ref ([] : term list)
  val memory_set_heads = ref ([] : term list)
  val unfold_extensions : (term * conv) list ref = ref []
  val capture_extensions : (term * term list) list ref = ref []
  val equations : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)
  val loop_prefixes : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)
  datatype attempt = Complete of thm * thm | Pending of term

  val install_indexed_head = compilerSsaEvalLib.install_indexed_head equations

  (* Additional passes supply only dispatch metadata here. Their semantic
     reductions still run inside individually instrumented warm_step calls. *)
  fun extend_phases entries unfolds captures =
    (app (fn (head,arity) =>
       evalCompilerBytecodeLib.ensure_certificate_head head arity) entries;
     phase_heads := !phase_heads @ List.filter
       (fn head => not (List.exists (same_const head) (!phase_heads)))
       (map #1 entries);
     unfold_extensions := unfolds @ !unfold_extensions;
     capture_extensions := captures @ !capture_extensions)

  (* Pure evaluator configuration: no compiler call is evaluated here. *)
  fun configure () = let
    (* Resolve model constants after the script's ancestors are loaded. *)
    val phases =
      compilerSsaEvalLib.phases () @
      [(prim_mk_const {Thy="concretizeMemLocDefs",Name="concretize_function_fuel_in_context"},4),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="compute_function_layout_fuel_in_context"},4),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="compute_function_layout_eval"},2),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="compute_alloc_map_fuel_in_context"},7),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="bp_analyze_fuel"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="mem_liveness_analyze_fuel"},7),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="static_alloca_items"},1),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="forced_candidate_positions"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="complete_alloc_positions_with_items"},5),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="apply_concretize_layout"},2),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_iterate_fuel"},9),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_one_pass"},8),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_one_pass_liveat"},7),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_one_pass_used"},7),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_liveat_block"},6),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_used_block"},7),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_compute_livesets"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_mark_stores_live"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="bp_iterate_fuel"},4),
       (prim_mk_const {Thy="basePtrDefs",Name="bp_one_pass"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_livesets_insts"},5),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_mark_stores_insts"},4),
       (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_livesets_blocks"},4),
       (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_mark_stores_blocks"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="alloc_liveset_items"},2),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="sort_alloc_liveset_items"},1),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="get_alloca_size"},2),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="allocate_with_livesets_in_context"},6),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="allocate_one"},2),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="call_frame_reservations"},3),
       (prim_mk_const {Thy="concretizeMemLocDefs",Name="call_frame_at_addr"},3)]
    val () = phase_heads := map #1 phases
    val sets = [(prim_mk_const {Thy="enumeral",Name="smerge"},3),
                (prim_mk_const {Thy="enumeral",Name="sinter"},3),
                (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_add_live_addr"},3),
                (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_add_live_addrs"},3),
                (prim_mk_const {Thy="concretizeMemLocDefs",Name="ml_lookup"},2)]
    val () = memory_set_heads := map #1 sets
    val indexed = compilerSsaEvalLib.phases () @ sets @
      List.filter (fn (head,_) =>
        let val {Name,...} = dest_thy_const head in
          Name = "ml_livesets_insts" orelse Name = "ml_mark_stores_insts" orelse
          Name = "ml_livesets_blocks" orelse Name = "ml_mark_stores_blocks"
        end) phases
  in app (fn (head,arity) =>
       evalCompilerBytecodeLib.ensure_certificate_head head arity)
       ([(function_head,6),(fold_head,7),(pass_head,5)] @ phases @ sets);
     app install_indexed_head indexed
  end

  fun ssa_head name = prim_mk_const {Thy="makeSsaCurrentDefs",Name=name}
  fun memory_head name = prim_mk_const {Thy="concretizeMemLocDefs",Name=name}
  fun memory_eval_head name = prim_mk_const {Thy="venomMemLivenessEval",Name=name}

  fun is_memory_loop head =
    same_const head (memory_head "ml_livesets_insts") orelse
    same_const head (memory_head "ml_mark_stores_insts") orelse
    same_const head (memory_eval_head "ml_livesets_blocks") orelse
    same_const head (memory_eval_head "ml_mark_stores_blocks") orelse
    same_const head
      (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_add_live_addrs"})

  (* Expose one recursive constructor before capturing recursive children.
     Each equation is instantiated from the existing model definition. *)
  fun unfold_current current =
    case List.find (fn (head,_) => same_const head (fst (strip_comb current)))
        (!unfold_extensions) of
      SOME (_,conversion) => conversion current
    | NONE => let
    val {Thy,Name,...} = dest_thy_const (fst (strip_comb current))
    val definition = if Thy = "concretizeMemLocDefs" andalso
        (Name = "ml_one_pass_liveat" orelse Name = "ml_one_pass_used" orelse
         Name = "ml_livesets_insts" orelse Name = "ml_mark_stores_insts") then
        SOME (Thy,Name ^ "_def")
      else if Thy = "concretizeMemLocDefs" andalso
          Name = "allocate_with_livesets_in_context" then SOME (Thy,Name ^ "_def")
      else if Thy <> "makeSsaCurrentDefs" then NONE
      else if Name = "rename_current_blocks" orelse
              Name = "rename_current_children" then SOME (Thy,"rename_current_blocks_def")
      else if Name = "rename_current_block_insts" then
        SOME (Thy,"rename_current_block_insts_def") else NONE
  in if Thy = "venomMemLivenessEval" andalso
      (Name = "ml_livesets_blocks" orelse Name = "ml_mark_stores_blocks") then
    Conv.FIRST_CONV (map Conv.REWR_CONV
      [DB.fetch Thy (Name ^ "_cons"),DB.fetch Thy (Name ^ "_nil")]) current
  else if Thy = "concretizeMemLocDefs" andalso
      (Name = "ml_compute_livesets" orelse Name = "ml_mark_stores_live") then
    Conv.REWR_CONV (DB.fetch "venomMemLivenessEval"
      (if Name = "ml_compute_livesets" then "ml_compute_livesets_blocks"
       else "ml_mark_stores_live_blocks")) current
  else if Thy = "venomMemLivenessEval" andalso Name = "ml_add_live_addr" then
    Conv.REWR_CONV (DB.fetch Thy "ml_add_live_addr_step") current
  else if Thy = "venomMemLivenessEval" andalso Name = "ml_add_live_addrs" then
    Conv.FIRST_CONV (map Conv.REWR_CONV
      [DB.fetch Thy "ml_add_live_addrs_cons",
       DB.fetch Thy "ml_add_live_addrs_nil"]) current
  else if Thy = "concretizeMemLocDefs" andalso Name = "ml_iterate_fuel" then
    Conv.REWR_CONV (DB.fetch "venomMemLivenessEval" "ml_iterate_fuel_unfold") current
  else if Thy = "concretizeMemLocDefs" andalso Name = "bp_iterate_fuel" then
    Conv.REWR_CONV (DB.fetch "venomMemLivenessEval" "bp_iterate_fuel_unfold") current
  else if Thy = "concretizeMemLocDefs" andalso
      (Name = "ml_livesets_insts" orelse Name = "ml_mark_stores_insts") then
    Conv.FIRST_CONV (map Conv.REWR_CONV
      (DB.fetch "venomMemLivenessEval" (Name ^ "_step_fold") ::
       CONJUNCTS (SPEC_ALL (DB.fetch Thy (Name ^ "_def"))))) current
  else case definition of
    NONE => REFL current
  | SOME (theory,name) => Conv.FIRST_CONV (map Conv.REWR_CONV
      (CONJUNCTS (SPEC_ALL (DB.fetch theory name)))) current
  end

  (* The direct step has only its live-map argument to compute. Retain that
     equation while the recursive child is proved, then compose exact
     equations instead of beta-reducing the whole continuation again. *)
  fun checked_call current =
    case Redblackmap.peek (!equations,current) of
      SOME theorem => theorem
    | NONE => raise evalCompilerBytecodeLib.PlannerBoundary current

  fun allocation_set_conv current =
    if same_const (fst (strip_comb current))
        (prim_mk_const {Thy="enumeral",Name="sinter"}) then let
      val left = Conv.RATOR_CONV (Conv.RAND_CONV checked_call) current
      val right = Conv.RAND_CONV checked_call (rhs (concl left))
      val result = computeLib.EVAL_CONV (rhs (concl right))
    in TRANS left (TRANS right result) end
    else computeLib.EVAL_CONV current

  fun live_argument_conv head current =
    if same_const head (memory_eval_head "ml_livesets_blocks") orelse
        same_const head (memory_eval_head "ml_mark_stores_blocks") then let
      val label_conv = if same_const head (memory_eval_head "ml_livesets_blocks") then
          Conv.RATOR_CONV (Conv.RATOR_CONV (Conv.RATOR_CONV
            (Conv.RATOR_CONV (Conv.RAND_CONV computeLib.EVAL_CONV))))
        else Conv.RATOR_CONV (Conv.RATOR_CONV (Conv.RAND_CONV computeLib.EVAL_CONV))
      val label = label_conv current
      val insts = Conv.RAND_CONV computeLib.EVAL_CONV (rhs (concl label))
      val result = checked_call (rhs (concl insts))
    in TRANS label (TRANS insts result) end
    else if same_const head
        (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_add_live_addrs"}) then
      checked_call current
    else let
      val allocs = Conv.RAND_CONV allocation_set_conv current
      val result = checked_call (rhs (concl allocs))
    in TRANS allocs result end

  fun evaluate_memory_loop current = let
    val head = fst (strip_comb current)
    val prefix = case Redblackmap.peek (!loop_prefixes,current) of
        SOME theorem => theorem
      | NONE => let
          val unfolded = evalCompilerBytecodeLib.timed_evaluation head "unfold"
            (fn () => unfold_current current)
          val body = rhs (concl unfolded)
          val recursive = same_const head (fst (strip_comb body))
          val evaluated = if recursive then
              evalCompilerBytecodeLib.timed_evaluation head "live argument"
                (fn () => Conv.RATOR_CONV
                  (Conv.RAND_CONV (live_argument_conv head)) body)
            else REFL body
          val theorem = TRANS unfolded evaluated
          val () = loop_prefixes :=
            Redblackmap.insert (!loop_prefixes,current,theorem)
        in theorem end
    val next = rhs (concl prefix)
  in if not (same_const head (fst (strip_comb next))) then prefix
    else case Redblackmap.peek (!equations,next) of
      SOME child => TRANS prefix child
    | NONE => raise evalCompilerBytecodeLib.PlannerBoundary next
  end

  (* Select a lookup branch using only the small address equality. The map
     and value arguments stay opaque throughout this exact kernel reduction. *)
  fun evaluate_memory_lookup current = let
    val head = fst (strip_comb current)
    val state = hd (snd (strip_comb current))
  in if finite_mapSyntax.is_fempty state then
      Conv.REWR_CONV (DB.fetch "venomMemLivenessEval" "ml_lookup_empty") current
    else if finite_mapSyntax.is_fupdate state then let
      val unfolded = Conv.REWR_CONV
        (DB.fetch "venomMemLivenessEval" "ml_lookup_update") current
      val condition = Conv.RATOR_CONV (Conv.RATOR_CONV
        (Conv.RAND_CONV computeLib.EVAL_CONV)) (rhs (concl unfolded))
      val selected = Conv.FIRST_CONV (map Conv.REWR_CONV
        (CONJUNCTS (SPEC_ALL boolTheory.COND_CLAUSES))) (rhs (concl condition))
      val prefix = TRANS unfolded (TRANS condition selected)
      val next = rhs (concl prefix)
    in if same_const head (fst (strip_comb next)) then
        TRANS prefix (evaluate_memory_lookup next)
      else prefix
    end else evalCompilerBytecodeLib.timed_evaluation head "lookup map fallback"
      (fn () => computeLib.EVAL_CONV current)
  end

  fun evaluate_flookup current = let
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
    in if finite_mapSyntax.is_flookup next then
        TRANS prefix (evaluate_flookup next) else prefix
    end else computeLib.EVAL_CONV current
  end

  fun evaluate_memory_update current = let
    val unfolded = unfold_current current
    val lookup = Conv.RAND_CONV (Conv.RAND_CONV (Conv.RAND_CONV
      (Conv.RATOR_CONV (Conv.RATOR_CONV (Conv.RAND_CONV evaluate_flookup)))))
      (rhs (concl unfolded))
    val addresses = Conv.RAND_CONV (Conv.RAND_CONV
      (Conv.RAND_CONV computeLib.EVAL_CONV)) (rhs (concl lookup))
    val merged = Conv.RAND_CONV (Conv.RAND_CONV computeLib.EVAL_CONV)
      (rhs (concl addresses))
  in TRANS unfolded (TRANS lookup (TRANS addresses merged)) end

  fun warm_step (goal as (_,proposition)) = let
    val root = rand proposition
  in if List.exists (aconv root) (!completed) then Tactical.ALL_TAC goal else let
    val () = if Option.isSome (!active) andalso aconv (valOf (!active)) root
      then () else (active := SOME root; pending := [])
    val is_root = null (!pending)
    val current = if is_root then root else hd (!pending)
    val head = fst (strip_comb current)
    val captures = case List.find (fn (key,_) => same_const head key)
        (!capture_extensions) of SOME (_,children) => children
      | NONE => if same_const head function_head then [fold_head]
      else if same_const head fold_head then [pass_head]
      else if same_const head pass_head then !phase_heads
      else if same_const head (hd (!phase_heads)) then tl (!phase_heads)
      else if same_const head (ssa_head "rename_current_blocks") then
        [ssa_head "rename_current_block_insts",ssa_head "rename_current_children"]
      else if same_const head (ssa_head "rename_current_children") then
        [ssa_head "rename_current_blocks",ssa_head "rename_current_children"]
      else if same_const head (ssa_head "rename_current_block_insts") then
        [ssa_head "rename_current_inst",ssa_head "rename_current_block_insts"]
      else if same_const head (memory_head "ml_iterate_fuel") then
        [memory_head "ml_one_pass",memory_head "ml_iterate_fuel"]
      else if same_const head (memory_head "bp_iterate_fuel") then
        [prim_mk_const {Thy="basePtrDefs",Name="bp_one_pass"},
         memory_head "bp_iterate_fuel"]
      else if same_const head (memory_head "ml_one_pass_liveat") then
        [memory_head "ml_liveat_block",memory_head "ml_one_pass_liveat"]
      else if same_const head (memory_head "ml_one_pass_used") then
        [memory_head "ml_used_block",memory_head "ml_one_pass_used"]
      else if same_const head (memory_head "allocate_with_livesets_in_context") then
        !phase_heads
      else if same_const head (memory_head "ml_livesets_insts") then
        [memory_head "ml_livesets_insts"] @ !memory_set_heads
      else if same_const head (memory_head "ml_mark_stores_insts") then
        [memory_head "ml_mark_stores_insts"] @ !memory_set_heads
      else if List.exists (same_const head) (!memory_set_heads) then
        List.filter (fn child => not (same_const head child)) (!memory_set_heads)
      else if List.exists (same_const head) (!phase_heads) then
        List.filter (fn child => not (same_const head child)) (!phase_heads)
      else [function_head,fold_head]
    fun evaluate () = if is_root then
        evalCompilerBytecodeLib.evaluate_call current
      else let
        val result = if same_const head
              (prim_mk_const {Thy="venomMemLivenessEval",Name="ml_add_live_addr"}) then
            evalCompilerBytecodeLib.timed_evaluation head "exact update"
              (fn () => evaluate_memory_update current)
          else if same_const head (memory_head "ml_lookup") then
            evalCompilerBytecodeLib.timed_evaluation head "exact lookup"
              (fn () => evaluate_memory_lookup current)
          else if is_memory_loop head then
            evalCompilerBytecodeLib.timed_evaluation head "exact loop step"
              (fn () => evaluate_memory_loop current)
          else let
            val unfolded = unfold_current current
            val equation = evalCompilerBytecodeLib.timed_evaluation head "pass boundary"
              (fn () => computeLib.EVAL_CONV (rhs (concl unfolded)))
          in TRANS unfolded equation end
      in (result,result) end
    val result =
      (Complete (Lib.with_flag
        (evalCompilerBytecodeLib.planner_capture_heads,captures) evaluate ())
       handle evalCompilerBytecodeLib.PlannerBoundary child => Pending child)
    val () = case result of
      Pending child => pending := child :: !pending
    | Complete (equation,normalized) =>
        if is_root andalso
           not (optionSyntax.is_some (rhs (concl equation))) then
          raise Fail "configured pass stage did not return SOME"
        else
          (evalCompilerBytecodeLib.register_compile_eval normalized;
           equations := Redblackmap.insert
             (!equations,lhs (concl normalized),normalized);
           evalCompilerBytecodeLib.pending_stage_values :=
             (NONE,normalized) :: !evalCompilerBytecodeLib.pending_stage_values;
           if is_root then completed := root :: !completed
           else pending := tl (!pending))
  in Tactical.ALL_TAC goal end end
end
