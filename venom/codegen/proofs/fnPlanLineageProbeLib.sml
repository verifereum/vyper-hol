(* Evaluate closed applications of one definition once per invocation, then
   rewrite every occurrence with the kernel-checked result.  Finding the next
   application avoids conversion traversal/congruence through large, already
   computed analysis records. No theorem is admitted or registered here. *)
structure fnPlanLineageProbeLib : sig
  val eval_def_occurrences : Thm.thm -> Abbrev.conv
  val eval_def_innermost : Thm.thm -> Abbrev.conv
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
end
