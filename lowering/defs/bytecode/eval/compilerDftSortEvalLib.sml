(* Certify the original stable cost order with instruction payloads opaque. *)
structure compilerDftSortEvalLib = struct
  open HolKernel boolLib
  val sort_head = compilerDftBoundaryEvalLib.sort_head
  val cost_head = compilerDftBoundaryEvalLib.cost_head

  fun sort_result current = let
    val arguments = snd (strip_comb current)
    val children = List.nth (arguments,5)
    val (values,child_type) = listSyntax.dest_list children
    fun cost child = compilerDftBoundaryEvalLib.checked
      (boolSyntax.list_mk_icomb (cost_head,List.take (arguments,5) @ [child]))
    val costs = map cost values
    val analyses = map (genvar o type_of) (List.take (arguments,5))
    val payloads = map (genvar o type_of) values
    val symbolic_children = listSyntax.mk_list (payloads,child_type)
    val premises = ListPair.map (fn (child,certificate) => mk_eq
      (boolSyntax.list_mk_icomb (cost_head,analyses @ [child]),
       rhs (concl certificate))) (payloads,costs)
    val call = boolSyntax.list_mk_icomb
      (sort_head,analyses @ [symbolic_children])
    val unfolded = Conv.REWR_CONV (DB.fetch "dftDefs" "sort_children_def") call
    val indexed = Conv.CONV_RULE
      (Conv.RAND_CONV compilerDftBoundaryEvalLib.indexed_lists) unfolded
    val selected = evalCompilerBytecodeLib.timed_evaluation sort_head
      "opaque-payload numeric ordering" (fn () =>
        simpLib.SIMP_CONV (bossLib.srw_ss ())
          (DB.fetch "sorting" "QSORT_DEF" ::
           DB.fetch "sorting" "PARTITION_DEF" ::
           DB.fetch "sorting" "PART_DEF" ::
           pairTheory.pair_case_thm :: boolTheory.LET_THM :: map ASSUME premises)
          (rhs (concl indexed)))
    val () = if listSyntax.is_list (rhs (concl selected)) then ()
      else raise Fail "symbolic child ordering did not reduce to a list"
    val schema = List.foldr (fn (premise,theorem) => DISCH premise theorem)
      (TRANS indexed selected) premises
    val replacements = ListPair.map (fn (variable,value) => variable |-> value)
      (analyses @ payloads,List.take (arguments,5) @ values)
    val concrete = INST replacements schema
    val result = List.foldl (fn (certificate,theorem) => MP theorem certificate)
      concrete costs
    val () = if aconv (lhs (concl result)) current then ()
      else raise Fail "numeric sorting did not recover the original call"
  in result end

  fun warm_call call goal =
    (case !compilerDftWorklistEvalLib.pending of
       current::_ =>
         if Option.isSome (!compilerDftWorklistEvalLib.active) andalso
             aconv (valOf (!compilerDftWorklistEvalLib.active)) call andalso
             same_const (fst (strip_comb current)) sort_head then let
           val certificate = sort_result current
           val () = evalCompilerBytecodeLib.register_compile_eval certificate
           val () = compilerDftWorklistEvalLib.equations := Redblackmap.insert
             (!compilerDftWorklistEvalLib.equations,current,certificate)
           val () = evalCompilerBytecodeLib.pending_stage_values :=
             (NONE,certificate) :: !evalCompilerBytecodeLib.pending_stage_values
           val () = compilerDftWorklistEvalLib.pending :=
             tl (!compilerDftWorklistEvalLib.pending)
         in Tactical.ALL_TAC goal end
         else compilerDftLoopBoundaryEvalLib.warm_call call goal
     | [] => compilerDftLoopBoundaryEvalLib.warm_call call goal)
    handle evalCompilerBytecodeLib.PlannerBoundary child =>
      (compilerDftWorklistEvalLib.pending :=
         child :: !compilerDftWorklistEvalLib.pending;
       Tactical.ALL_TAC goal)
end
