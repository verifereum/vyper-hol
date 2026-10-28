(* Exact SSA/front-end pass certificates. Independent of memory-evaluation
   helpers, so later concretization proof edits preserve this build frontier. *)
structure compilerSsaEvalLib = struct
  open HolKernel boolLib
  val function_head = evalCompilerBytecodeLib.scheduled_function_head
  val fold_head = evalCompilerBytecodeLib.scheduled_fold_head
  val pass_head = evalCompilerBytecodeLib.scheduled_pass_head
  val active = ref (NONE : term option)
  val pending = ref ([] : term list)
  val completed = ref ([] : term list)
  val phase_heads = ref ([] : term list)
  val equations : (term,thm) Redblackmap.dict ref =
    ref (Redblackmap.mkDict Term.compare)
  datatype attempt = Complete of thm * thm | Pending of term

  (* Same checked certificate/capture interface as the shared library, indexed
     by exact term for memory operations with many large, similar arguments. *)
  fun install_indexed_head equations (head,arity) = let
    fun cached tm = case Redblackmap.peek (!equations,tm) of
        SOME theorem => theorem
      | NONE =>
        if List.exists (same_const head)
            (!evalCompilerBytecodeLib.planner_capture_heads) andalso
            null (free_vars tm) then
          (* CBV has already supplied the arguments. Preserve this exact call;
             the child proof, including all needed reductions, certifies it.
             Re-evaluating a growing map here was redundant and expensive. *)
          raise evalCompilerBytecodeLib.PlannerBoundary tm
        else raise Conv.UNCHANGED
    val rules = evalCompilerBytecodeLib.unique_rules
      (List.concat (List.concat (map
        (fn (_,xs) => map
          (fn clauses.RRules theorems => theorems | clauses.Conversion _ => []) xs)
        (computeLib.listItems (computeLib.the_compset ())))))
    fun headed theorem = same_const head
      (fst (strip_comb (lhs (#2 (strip_forall (concl theorem))))))
      handle HOL_ERR _ => false
    val originals = List.filter headed rules
    val callers = List.filter (fn theorem => not (headed theorem) andalso
      HOLset.member (evalCompilerBytecodeLib.dependencies theorem,
        evalCompilerBytecodeLib.constant_key head)
      handle HOL_ERR _ => false) rules
    val () = computeLib.del_consts [head]
    val () = computeLib.add_convs [(head,arity,cached)]
  in computeLib.add_funs (rev originals @ callers) end


  fun phases () =
    [(prim_mk_const {Thy="makeSsaCurrentDefs",Name="make_ssa_current_fn"},2),
       (prim_mk_const {Thy="cfgDefs",Name="cfg_analyze"},1),
       (prim_mk_const {Thy="dominatorDefs",Name="dom_analyze"},2),
       (prim_mk_const {Thy="livenessDefs",Name="liveness_analyze"},1),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="add_phi_nodes_supply"},6),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="rename_current_blocks"},5),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="rename_current_children"},6),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="rename_current_block_insts"},3),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="rename_current_inst"},3),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="current_query_map"},2),
       (prim_mk_const {Thy="makeSsaDefs",Name="compute_defs"},1),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="init_current_rename_state"},1),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="select_current_live_in"},3),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="current_dom_tree_aux"},3),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="dom_tree_postorder"},1),
       (prim_mk_const {Thy="makeSsaCurrentDefs",Name="simplify_current_phis_if"},2)]

  fun configure () = let
    val entries = phases ()
    val () = phase_heads := map #1 entries
    val () = app (fn (head,arity) =>
      evalCompilerBytecodeLib.ensure_certificate_head head arity)
      ([(function_head,6),(fold_head,7),(pass_head,5)] @ entries)
  in app (install_indexed_head equations) entries end

  fun ssa_head name = prim_mk_const {Thy="makeSsaCurrentDefs",Name=name}

  fun unfold_current current = let
    val {Thy,Name,...} = dest_thy_const (fst (strip_comb current))
    val definition = if Thy <> "makeSsaCurrentDefs" then NONE
      else if Name = "rename_current_blocks" orelse
              Name = "rename_current_children" then SOME "rename_current_blocks_def"
      else if Name = "rename_current_block_insts" then
        SOME "rename_current_block_insts_def" else NONE
  in case definition of NONE => REFL current
    | SOME name => Conv.FIRST_CONV (map Conv.REWR_CONV
        (CONJUNCTS (SPEC_ALL (DB.fetch Thy name)))) current
  end

  fun warm_step (goal as (_,proposition)) = let
    val root = rand proposition
  in if List.exists (aconv root) (!completed) then Tactical.ALL_TAC goal else let
    val () = if Option.isSome (!active) andalso aconv (valOf (!active)) root
      then () else (active := SOME root; pending := [])
    val is_root = null (!pending)
    val current = if is_root then root else hd (!pending)
    val head = fst (strip_comb current)
    val captures = if same_const head function_head then [fold_head]
      else if same_const head fold_head then [pass_head]
      else if same_const head pass_head then !phase_heads
      else if same_const head (ssa_head "rename_current_blocks") then
        [ssa_head "rename_current_block_insts",ssa_head "rename_current_children"]
      else if same_const head (ssa_head "rename_current_children") then
        [ssa_head "rename_current_blocks",ssa_head "rename_current_children"]
      else if same_const head (ssa_head "rename_current_block_insts") then
        [ssa_head "rename_current_inst",ssa_head "rename_current_block_insts"]
      else List.filter (fn child => not (same_const head child)) (!phase_heads)
    fun evaluate () = if is_root then
        evalCompilerBytecodeLib.evaluate_call current
      else let
        val unfolded = unfold_current current
        val equation = evalCompilerBytecodeLib.timed_evaluation head "SSA boundary"
          (fn () => computeLib.EVAL_CONV (rhs (concl unfolded)))
        val result = TRANS unfolded equation
      in (result,result) end
    val result = (Complete (Lib.with_flag
        (evalCompilerBytecodeLib.planner_capture_heads,captures) evaluate ())
      handle evalCompilerBytecodeLib.PlannerBoundary child => Pending child)
    val () = case result of Pending child => pending := child :: !pending
      | Complete (equation,normalized) =>
        if is_root andalso not (optionSyntax.is_some (rhs (concl equation))) then
          raise Fail "SSA prefix stage did not return SOME"
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
