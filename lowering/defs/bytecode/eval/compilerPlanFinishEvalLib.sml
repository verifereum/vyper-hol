(* Compose the original post-instruction operations with opaque planner inputs. *)
structure compilerPlanFinishEvalLib = struct
  open HolKernel boolLib

  fun compute checked current = let
    val arguments = snd (strip_comb current)
    val [dfg,inst,next_live,halting,next_term,ps] = arguments
    val symbolic = map (genvar o type_of) arguments
    val [dfg_variable,inst_variable,live_variable,halt_variable,term_variable,ps_variable] =
      symbolic
    val actual_queries =
      [``(^inst).inst_outputs = []``, ``~^halting``,
       ``MAP Var (FILTER (\out. ~MEM out ^next_live) (^inst).inst_outputs)``,
       ``FILTER (\out. MEM out ^next_live) (^inst).inst_outputs = []``]
    val queries =
      [``(^inst_variable).inst_outputs = []``, ``~^halt_variable``,
       ``MAP Var (FILTER (\out. ~MEM out ^live_variable) (^inst_variable).inst_outputs)``,
       ``FILTER (\out. MEM out ^live_variable) (^inst_variable).inst_outputs = []``]
    val metadata = map compilerInstructionPlannerEvalLib.checked_argument actual_queries
    val facts = ListPair.map (fn (query,theorem) =>
      (mk_eq (query,rhs (concl theorem)),theorem)) (queries,metadata)
    fun value index = rhs (concl (List.nth (metadata,index)))
    val empty_outputs = aconv (value 0) T
    val pop_needed = not empty_outputs andalso aconv (value 1) T
    val opt_needed = not empty_outputs andalso aconv (value 3) F
    fun operation theory name = prim_mk_const {Thy=theory,Name=name}
    fun phase head arguments = checked (boolSyntax.list_mk_icomb (head,arguments))
    fun premise head arguments theorem =
      (mk_eq (boolSyntax.list_mk_icomb (head,arguments),rhs (concl theorem)),theorem)
    val (ps8,symbolic_ps8,pop_facts) = if not pop_needed then
        (ps,ps_variable,[])
      else let
        val head = operation "stackPlanOps" "popmany_plan"
        val theorem = phase head [value 2,ps]
        val (_,next_ps) = pairSyntax.dest_pair (rhs (concl theorem))
      in (next_ps,next_ps,[premise head [value 2,ps_variable] theorem]) end
    val (ps9,symbolic_ps9,opt_facts) = if not opt_needed then
        (ps8,symbolic_ps8,[])
      else let
        val head = operation "stackPlanGen" "optimistic_swap_plan"
        val theorem = phase head [dfg,inst,next_live,next_term,ps8]
        val (_,next_ps) = pairSyntax.dest_pair (rhs (concl theorem))
      in (next_ps,next_ps,
        [premise head [dfg_variable,inst_variable,live_variable,term_variable,
          symbolic_ps8] theorem]) end
    val release_head = operation "stackPlanOps" "release_dead_spills"
    val released = phase release_head [next_live,ps9]
    val all_facts = facts @ pop_facts @ opt_facts @
      [premise release_head [live_variable,symbolic_ps9] released]
    val call = boolSyntax.list_mk_icomb
      (compilerExternalPlannerEvalLib.regular_head "planner_regular_finish",symbolic)
    val unfolded = Conv.REWR_CONV
      (DB.fetch "stackPlanRegularCases" "planner_regular_finish_def") call
    val selected = TRANS unfolded (simpLib.SIMP_CONV (bossLib.srw_ss())
      (boolTheory.LET_THM :: map (ASSUME o fst) all_facts) (rhs (concl unfolded)))
    val () = if null (free_vars (rhs (concl selected))) then ()
      else raise Fail ("instruction cleanup did not compose: " ^
        term_to_string (rhs (concl selected)))
    val schema = List.foldr (fn ((condition,_),theorem) => DISCH condition theorem)
      selected all_facts
    val concrete = INST (ListPair.map (fn (variable,value) => variable |-> value)
      (symbolic,arguments)) schema
    val result = List.foldl (fn ((_,premise),theorem) => MP theorem premise)
      concrete all_facts
  in Conv.CONV_RULE (Conv.RAND_CONV computeLib.EVAL_CONV) result end
end
