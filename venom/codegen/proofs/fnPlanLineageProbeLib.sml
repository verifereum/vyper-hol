(* Evaluate closed applications of one definition once per invocation, then
   rewrite every occurrence with the kernel-checked result.  Finding the next
   application avoids conversion traversal/congruence through large, already
   computed analysis records. No theorem is admitted or registered here. *)
structure fnPlanLineageProbeLib : sig
  val eval_def_occurrences : Thm.thm -> Abbrev.conv
  val eval_def_innermost : Thm.thm -> Abbrev.conv
  val cache_context : Thm.thm -> Thm.thm -> Abbrev.conv
  val trace_prepare : Abbrev.conv
  val trace_step : Thm.thm -> Abbrev.conv
end =
struct
  open HolKernel boolLib
  fun eval_def_occurrences def =
    let
      val (_, equation) = strip_forall (concl def)
      val (lhs, _) = dest_eq equation
      val (head, args) = strip_comb lhs
      val arity = length args
      fun matches tm =
        let val (h, xs) = strip_comb tm
        in aconv h head andalso length xs = arity end
      fun step tm =
        let
          val instance = find_term matches tm
          val equation = (REWR_CONV def THENC computeLib.EVAL_CONV) instance
        in (PURE_REWRITE_CONV [equation] THENC TRY_CONV step) tm end
    in step end

  fun eval_def_innermost def tm =
    let
      val (_, equation) = strip_forall (concl def)
      val (lhs, _) = dest_eq equation
      val (head, args) = strip_comb lhs
      fun matches t =
        let val (h, xs) = strip_comb t
        in aconv h head andalso length xs = length args end
      fun deepest t =
        let val candidate = find_term matches t
            val (_, xs) = strip_comb candidate
        in case List.find (can (find_term matches)) xs of
             NONE => candidate
           | SOME x => deepest x
        end
      val instance = deepest tm
      val result = (REWR_CONV def THENC computeLib.EVAL_CONV) instance
    in PURE_REWRITE_CONV [result] tm end

  fun def_head def =
    let val (_, eq) = strip_forall (concl def)
    in #1 (strip_comb (#1 (dest_eq eq))) end

  (* Only checked reductions enter the evaluator's cache.  Nothing is unfolded
     throughout the proof goal.  Each cache call is a separate tactic step. *)
  fun cache_context context_def def tm =
    let
      val context_head = def_head context_def
      val context = find_term (fn t =>
        let val (h,args) = strip_comb t
        in aconv h context_head andalso length args = 4 end) tm
      val args = List.take (#2 (strip_comb context), 3)
      val equation = computeLib.EVAL_CONV (list_mk_comb (def_head def, args))
      val _ = computeLib.add_funs [equation]
    in REFL tm end

  fun fold_term tm = find_term (fn t =>
    let val (h,args) = strip_comb t
    in same_const h (def_head (Drule.cj 2 listTheory.FOLDL)) andalso length args = 3 end) tm

  fun trace_prepare tm =
    let val fold = fold_term tm
        val equation = (RAND_CONV computeLib.EVAL_CONV THENC
          RATOR_CONV (RAND_CONV computeLib.EVAL_CONV)) fold
    in PURE_REWRITE_CONV [equation] tm end

  fun trace_step inst_def tm =
    let
      val fold = fold_term tm
      val inst_head = def_head inst_def
      fun reduce_acc acc =
        let
          val expose = computeLib.RESTR_EVAL_CONV [inst_head] acc
          val exposed = rhs (concl expose)
          val call = find_term (fn t =>
            let val (h,args) = strip_comb t
            in aconv h inst_head andalso length args = 5 end) exposed
          val equation = computeLib.EVAL_CONV call
          val _ = computeLib.add_funs [equation]
        in TRANS expose (computeLib.EVAL_CONV exposed) end
      val equation =
        if listSyntax.is_nil (last (#2 (strip_comb fold))) then
          REWR_CONV (Drule.cj 1 listTheory.FOLDL) fold
        else (REWR_CONV (Drule.cj 2 listTheory.FOLDL) THENC
          RATOR_CONV (RAND_CONV reduce_acc)) fold
    in PURE_REWRITE_CONV [equation] tm end
end
