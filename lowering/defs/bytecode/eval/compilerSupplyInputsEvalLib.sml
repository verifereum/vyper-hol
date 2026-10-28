(* TOP-LEVEL: warm_step. Reuse literal supply lists without re-evaluating
   their elements; the original subset predicate is still checked in chunks. *)
structure compilerSupplyInputsEvalLib = struct
  open HolKernel boolLib
  val subset_head = compilerSupplyBoundaryEvalLib.head "list_subset"

  fun list_input term =
    if can listSyntax.dest_list term then REFL term
    else if listSyntax.is_cons term then Conv.RAND_CONV list_input term
    else if listSyntax.is_append term then let
      val arguments = Conv.COMB2_CONV
        (Conv.RAND_CONV list_input,list_input) term
      val appended = listLib.APPEND_CONV (rhs (concl arguments))
    in TRANS arguments appended end
    else if is_const (fst (strip_comb term)) andalso
        List.exists (same_const (fst (strip_comb term)))
          (compilerSupplyBoundaryEvalLib.collections ()) then
      compilerPassEvalLib.checked_call term
    else let
      val () = if evalCompilerBytecodeLib.profile_evaluation then
        print ("SUPPLY_LIST_INPUT_HEAD " ^ term_to_string (fst (strip_comb term)) ^ "\n")
        else ()
    in computeLib.EVAL_CONV term end

  fun subset_inputs atom = Conv.COMB2_CONV
    (Conv.RAND_CONV list_input,list_input) atom

  fun seed_subset call =
    case !compilerGuardEvalLib.subset_pending of
      SOME (saved,_,_,_,_) => if aconv saved call then () else initialize call
    | NONE => initialize call
  and initialize call = let
    val (head,args) = strip_comb call
    val (xs,ty) = listSyntax.dest_list (hd args)
    val _ = listSyntax.dest_list (List.nth (args,1))
    val () = if null (free_vars call) andalso null (type_vars_in_term call)
      then () else raise Fail "expected closed supply subset inputs"
  in compilerGuardEvalLib.subset_pending := SOME
    (call,head,List.nth (args,1),compilerGuardEvalLib.subset_chunks xs ty,[]) end

  fun warm_atom current prefix atom rest facts goal = let
    val supply_types = map type_of (snd (strip_comb current))
    val projected = compilerPassEffectsEvalLib.observe supply_types atom
    val reduced = evalCompilerBytecodeLib.timed_evaluation subset_head
      "literal supply inputs" (fn () => Lib.with_flag
      (evalCompilerBytecodeLib.planner_capture_heads,
       compilerSupplyBoundaryEvalLib.collections ()) subset_inputs
         (rhs (concl projected)))
    val inputs = TRANS projected reduced
    val checked = compilerPassEvalLib.checked_call (rhs (concl inputs))
    val certificate = TRANS inputs checked
    val () = compilerSupplyBoundaryEvalLib.work := Redblackmap.insert
      (!compilerSupplyBoundaryEvalLib.work,current,
       (prefix,rest,certificate::facts))
  in Tactical.ALL_TAC goal end

  fun warm_step goal =
    (case !compilerPassEvalLib.pending of
      [] => compilerSupplyBoundaryEvalLib.warm_step goal
    | current::_ => let val head = fst (strip_comb current)
      in if same_const head subset_head then
        (seed_subset current; compilerSupplyBoundaryEvalLib.warm_step goal)
      else if List.exists (same_const head)
          (compilerSupplyBoundaryEvalLib.guards ()) then
        (case Redblackmap.peek (!compilerSupplyBoundaryEvalLib.work,current) of
          SOME (prefix,atom::rest,facts) =>
            if same_const (fst (strip_comb atom)) subset_head then
              warm_atom current prefix atom rest facts goal
            else compilerSupplyBoundaryEvalLib.warm_step goal
        | _ => compilerSupplyBoundaryEvalLib.warm_step goal)
      else compilerSupplyBoundaryEvalLib.warm_step goal end)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerPassEvalLib.pending := child :: !compilerPassEvalLib.pending;
       Tactical.ALL_TAC goal)
end
