(* Structural induction for proved first-order presentations of existing
   recursive functions.  The temporary definition supplies only induction;
   execution always uses equations proved about the original constants. *)
structure jsonToVyperCVLib =
struct
  open HolKernel boolLib bossLib
  fun domains ty =
    case total dom_rng ty of NONE => [] | SOME (a,b) => a :: domains b

  (* Primitive datatype induction omits the functions' fixed parameters.
     Quantify those parameters inside each predicate, then commute them to
     the API argument order expected by the CV precondition prover. *)
  fun lift_primitive_induction originals induction = let
    val predicates = fst (strip_forall (concl induction))
    fun lift (i,predicate) = let
      val node_ty = fst (dom_rng (type_of predicate))
      val original = valOf (List.find
        (fn c => List.last (domains (type_of c)) = node_ty) originals)
      val args = map (fn (j,ty) => mk_var
        ("ind_arg" ^ Int.toString j,ty))
        (Lib.enumerate 0 (domains (type_of original)))
      val full = mk_var ("ind_pred" ^ Int.toString i,
        List.foldr (fn (a,b) => a --> b) bool (map type_of args))
      val applied = list_mk_comb (full,args)
      val fixed = List.take (args,length args-1)
    in (full,mk_abs (List.last args,list_mk_forall (fixed,applied))) end
    val lifted = map lift (Lib.enumerate 0 predicates)
    val specialized = CONV_RULE (DEPTH_CONV BETA_CONV)
      (ISPECL (map #2 lifted) induction)
    val premise = fst (dest_imp (concl specialized))
    val conclusions = CONJUNCTS (MP specialized (ASSUME premise))
    fun reorder theorem = let
      val args = fst (strip_forall (concl theorem))
      val body = SPECL args theorem
    in GENL (tl args @ [hd args]) body end
  in GENL (map #1 lifted)
       (DISCH premise (LIST_CONJ (map reorder conclusions))) end

  fun register_first_order_induction stem equations termination = let
    val clauses = map SPEC_ALL (CONJUNCTS (SPEC_ALL equations))
    fun head th = fst (strip_comb (lhs (concl th)))
    fun add (c, cs) = if List.exists (aconv c) cs then cs else cs @ [c]
    val originals = List.foldl add [] (map head clauses)
    val temporaries = map (fn (i,c) =>
      mk_var (stem ^ "_" ^ Int.toString i, type_of c))
      (Lib.enumerate 0 originals)
    val replacements = ListPair.map (fn (c,v) => c |-> v)
      (originals, temporaries)
    val formula = subst replacements (list_mk_conj (map concl clauses))
    val definition = Defn.mk_defn stem formula
    val induction =
      if null (Defn.tcs_of definition) then
        lift_primitive_induction originals (valOf (Defn.ind_of definition))
      else #2 (Defn.tprove0 (definition, termination))
    val keys = map (fn c => let val {Thy,Name,...} = dest_thy_const c
                           in {Thy=Thy,Name=Name} end) originals
    val _ = DefnBase.register_indn (induction, keys)
    val _ = List.app (Theory.delete_const o fst o dest_var) temporaries
  in
    induction
  end
end
