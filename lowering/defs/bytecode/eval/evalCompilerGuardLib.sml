(* Positive literal-subset certificates. EVERY_MEM proves that each element
   of the carrier belongs to it. Extract those proved memberships once,
   then assemble the requested EVERY without string-inequality proofs. *)
structure evalCompilerGuardLib = struct
open HolKernel Parse boolLib bossLib

exception Missing_literal_member
fun entry_literal_subset_proof tm = let
  fun fallback () = computeLib.WEAK_CBV_CONV (computeLib.the_compset()) tm
  val (_,args) = strip_comb tm
  val xs = List.nth(args,0)
  val ys = List.nth(args,1)
in if not (can listSyntax.dest_list xs andalso can listSyntax.dest_list ys)
   then fallback ()
   else let
      val (_,element_type) = listSyntax.dest_list ys
      val element = mk_var ("subset_element",element_type)
      val predicate = mk_abs (element,listSyntax.mk_mem(element,ys))
      fun index proved = let
        val carrier = List.nth(snd(strip_comb(concl proved)),1)
      in if listSyntax.is_nil carrier then [] else let
        val parts = EQ_MP (REWR_CONV (cj 2 listTheory.EVERY_DEF) (concl proved)) proved
        val head = CONV_RULE (TRY_CONV BETA_CONV) (CONJUNCT1 parts)
        val (x,_) = listSyntax.dest_mem (concl head)
      in (x,head) :: index (CONJUNCT2 parts) end end
      fun all_members () = let
        val premise = listSyntax.mk_mem(element,ys)
        val reflexive = GEN element (DISCH premise (ASSUME premise))
        val equation = REWR_CONV listTheory.EVERY_MEM
          (listSyntax.mk_every (predicate,ys))
        val normalized = CONV_RULE
          (RAND_CONV (BINDER_CONV (RAND_CONV (TRY_CONV BETA_CONV)))) equation
      in EQ_MP (SYM normalized) reflexive end
      val memberships = if listSyntax.is_nil xs then [] else index (all_members ())
     fun cached_member q = let
        val (x,_) = listSyntax.dest_mem q
      in case List.find (fn (y,_) => aconv x y) memberships of
         SOME (_,th) => th
        | NONE => raise Missing_literal_member
     end
     fun every q = let
       val carrier = List.nth(snd(strip_comb q),1)
     in if listSyntax.is_nil carrier then
          EQT_ELIM (REWR_CONV (cj 1 listTheory.EVERY_DEF) q)
        else let
          val eq = REWR_CONV (cj 2 listTheory.EVERY_DEF) q
          val (head,tail) = boolSyntax.dest_conj (rhs (concl eq))
          val beta = (BETA_CONV head
            handle HOL_ERR _ => REFL head | UNCHANGED => REFL head)
          val head_proof = EQ_MP (SYM beta) (cached_member (rhs (concl beta)))
        in EQ_MP (SYM eq) (CONJ head_proof (every tail)) end
     end
     val opened = REWR_CONV venomFnScheduleRunnerTheory.list_subset_def tm
   in EQT_INTRO (EQ_MP (SYM opened) (every (rhs (concl opened)))) end
   handle Missing_literal_member => fallback ()
end

(* Pass validation repeats identical literal guards. Reuse their proved
   equations; keep the cache finite across unrelated compiler evaluations. *)
val literal_subset_certificates = ref ([] : (term * thm) list)
fun entry_literal_subset_conv tm =
  case List.find (fn (t,_) => aconv t tm) (!literal_subset_certificates) of
    SOME (_,th) => th
  | NONE => let
      val literalize = computeLib.EVAL_CONV
      val prepared = (RATOR_CONV (RAND_CONV literalize) THENC
        RAND_CONV literalize) tm
      val th = TRANS prepared
        (entry_literal_subset_proof (rhs (concl prepared)))
      val previous = !literal_subset_certificates
      val () = if aconv (rhs (concl th)) boolSyntax.T then
        literal_subset_certificates := (tm,th) ::
          List.take (previous,Int.min (63,List.length previous))
        else ()
    in th end
end
