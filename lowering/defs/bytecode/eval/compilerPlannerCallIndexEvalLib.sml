(* Index exact checked planner calls after CBV has prepared their arguments.
   Captured misses yield directly instead of normalizing large graphs again. *)
structure compilerPlannerCallIndexEvalLib = struct
  open HolKernel boolLib
  val equations = ref (Redblackmap.mkDict Term.compare : (term,thm) Redblackmap.dict)

  fun install (head,arity) = let
    fun cached current =
      case Redblackmap.peek (!equations,current) of
        SOME theorem => theorem
      | NONE => (case List.find (fn theorem => aconv current (lhs (concl theorem)))
            (!evalCompilerBytecodeLib.compiler_certificates) of
          SOME theorem =>
            (equations := Redblackmap.insert (!equations,current,theorem); theorem)
        | NONE =>
            if List.exists (same_const head)
                (!evalCompilerBytecodeLib.planner_capture_heads) andalso
                null (free_vars current) then
              raise evalCompilerBytecodeLib.PlannerBoundary current
            else raise Conv.UNCHANGED)
    val rules = evalCompilerBytecodeLib.unique_rules
      (List.concat (List.concat (map
        (fn (_,entries) => map
          (fn clauses.RRules theorems => theorems | clauses.Conversion _ => []) entries)
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

  fun configure () = app install
    [(prim_mk_const {Thy="stackPlanOps",Name="reorder_plan"},3),
     (prim_mk_const {Thy="stackPlanRegularCases",Name="planner_regular_join"},6)]
end
