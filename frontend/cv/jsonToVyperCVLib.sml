(* Structural induction for proved first-order presentations of existing
   recursive functions.  The temporary definition supplies only induction;
   execution always uses equations proved about the original constants. *)
structure jsonToVyperCVLib :> jsonToVyperCVLib =
struct
  open HolKernel boolLib bossLib

  (* Generated preconditions are relations with quantified representation
     premises, not ordinary CV functions. Unfold only closed instances: feeding
     all recursive cases to simp also unfolds predicates on bound variables.
     Each round evaluates source computations and simplifies those premises
     before another layer of concrete recursion is exposed. *)
  fun condition_conv tm = let
    val case_theorems = List.map #2
      (List.filter (String.isSuffix "_pre_cases" o #1)
        (DB.thms "jsonToVyperExprCV" @ DB.thms "jsonToVyperCV"))
    val cases = List.map (fn th =>
      (fst (strip_comb (lhs (concl (SPEC_ALL th)))), th))
      (List.concat (List.map (CONJUNCTS o SPEC_ALL) case_theorems))
    fun unfold_closed tm = let
      val head = fst (strip_comb tm)
    in
      case List.find (fn (c, _) => is_const head andalso same_const c head) cases of
        NONE => NO_CONV tm
      | SOME (_, th) =>
          if type_of tm = bool andalso null (free_vars tm)
          then REWR_CONV th tm else NO_CONV tm
    end
    val proved = List.map (fn name => DB.fetch "jsonToVyperCV" name)
      ["canonical_default_pre", "json_expr_size_pre", "initialized_chains_pre",
       "resolve_json_expr_pre", "resolve_json_stmt_pre"]
    val datatype_rules = List.concat (List.map
      (fn info => TypeBasePure.gen_std_rewrs info @
        #rewrs (TypeBasePure.simpls_of info))
      (List.concat (List.map
        (fn thy => TypeBase.thy_updates {thyname = thy})
        ["jsonAST", "vyperAST", "list", "option", "pair", "num", "cv"])))
    (* Follow vyperState's root-first logical cleanup. Semantic expressions
       stay opaque until EVAL; never run a generic simplifier over their bodies. *)
    val cleanup_rules = Rewrite.add_rewrites Rewrite.bool_rewrites
      (GSYM AND_IMP_INTRO ::
       datatype_rules @ #rewrs (TypeBase.simpls_of numSyntax.num) @ proved)
    fun suc_numeral tm =
      if is_eq tm then let
        val (l, r) = dest_eq tm
        fun positive t = numSyntax.is_numeral t andalso
          numSyntax.dest_numeral t <> Arbnum.zero
      in
        if numSyntax.is_suc l andalso positive r then
          RAND_CONV numLib.num_CONV tm
        else if numSyntax.is_suc r andalso positive l then
          LAND_CONV numLib.num_CONV tm
        else NO_CONV tm
      end else NO_CONV tm
    val root = FIRST_CONV
      [CHANGED_CONV (Rewrite.REWRITES_CONV cleanup_rules),
       CHANGED_CONV suc_numeral,
       CHANGED_CONV Unwind.UNWIND_FORALL_CONV]
    (* Imperative theorem composition must turn UNCHANGED into reflexivity;
       otherwise an unchanged child would discard earlier conversion progress. *)
    fun simplify tm = let
      val normalized = QCONV (TRY_CONV root) tm
      val current = rhs (concl normalized)
    in
      if not (aconv current tm) then TRANS normalized (simplify current)
      else if is_forall current then finish (QCONV (QUANT_CONV simplify) current)
      else if is_neg current then finish (QCONV (RAND_CONV simplify) current)
      else if is_imp_only current orelse is_conj current orelse is_disj current then let
        val left = QCONV (RATOR_CONV (RAND_CONV simplify)) current
        val middle = rhs (concl left)
        val normalized = QCONV (TRY_CONV root) middle
        val current = rhs (concl normalized)
      in
        if not (aconv current middle) then
          TRANS left (TRANS normalized (simplify current))
        else if is_imp_only current orelse is_conj current orelse is_disj current then
          finish (TRANS left (QCONV (RAND_CONV simplify) current))
        else TRANS left normalized
      end
      else normalized
    end
    and finish th = let
      val previous = rhs (concl th)
      val normalized = QCONV (TRY_CONV root) previous
      val after = rhs (concl normalized)
    in
      if aconv previous after then TRANS th normalized
      else TRANS th (TRANS normalized (simplify after))
    end
    (* Unlike DEPTH_CONV, visit each existing node once and never descend into
       an unfolded RHS before constructor/representation premises simplify. *)
    fun layer tm = (SUB_CONV layer THENC TRY_CONV unfold_closed) tm
    (* A quantified formula is closed as a whole, but its semantic bodies can
       still be open. Never ask EVAL to expand those bodies symbolically. *)
    fun eval_closed tm =
      if is_forall tm orelse is_exists tm then QUANT_CONV eval_closed tm
      else if is_imp_only tm orelse is_conj tm orelse is_disj tm then
        (LAND_CONV eval_closed THENC RAND_CONV eval_closed) tm
      else if is_neg tm then RAND_CONV eval_closed tm
      else if is_abs tm then ABS_CONV eval_closed tm
      else if null (free_vars tm) then EVAL tm
      else SUB_CONV eval_closed tm
    val step = layer THENC simplify THENC eval_closed THENC simplify
    fun reduce tm = let
      val th = QCONV step tm
      val result = rhs (concl th)
    in
      if aconv result tm then th else TRANS th (reduce result)
    end
  in reduce tm end

  (* The actual translation always uses CV. Only its defined-input antecedents
     use the kernel condition prover above; false or stuck conditions fail. *)
  fun eval tm = let
    fun discharge th =
      if is_imp_only (concl th) then let
        val condition = fst (dest_imp (concl th))
        val checked = condition_conv condition
        val () = if aconv (rhs (concl checked)) T then () else
          raise Fail ("frontend CV condition is false or unreduced: " ^
                      term_to_string (rhs (concl checked)))
        val proof = EQT_ELIM checked
      in discharge (MP th proof) end
      else th
    val th = discharge (cv_transLib.cv_eval tm)
    val () = if null (hyp th) andalso aconv (lhs (concl th)) tm then ()
             else raise Fail "frontend CV evaluation is not unconditional"
  in th end
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
