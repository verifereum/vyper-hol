(*
 * Walking a goal about an evaluator computation through its monadic body
 *
 * A walk proves a property of a computation M by reducing M's combinators
 * with structural rules (bind, try, finally), rewriting the case and let
 * redexes at M's head, splitting the case it exposes, and closing what is
 * left with a primitive's lemma or an induction hypothesis.  The property
 * supplies the rules and leaves (walk_net), where M sits in the goal (the
 * conversion `at` of STEP), the definitions to unfold, and its own
 * introductions and fallbacks.  vyperEvalFrame and vyperExprNoControl walk
 * the evaluator this way; vyperEvalOutcomeSuffix uses head_conv and
 * HEAD_CASE_TAC.
 *)
structure evalWalkLib =
struct

open HolKernel boolLib bossLib
open pairTheory vyperASTTheory vyperInterpreterTheory

(* Rewrite only the exposed head: case and let redexes, beta, UNCURRY. *)
val head_conv =
  let
    val case_rules = List.concat (List.map
      (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
      (LET_THM :: COND_CLAUSES ::
       List.mapPartial (total TypeBasePure.case_def_of) (TypeBase.elts ())))
    val cases = List.foldl (fn (th,net) =>
      Net.insert (lhs (concl th), REWR_CONV th) net) Net.empty case_rules
    fun root tm = FIRST_CONV (Net.match tm cases) tm
    fun head tm = (BETA_CONV ORELSEC root ORELSEC
      REWR_CONV UNCURRY ORELSEC RATOR_CONV head) tm
  in head end;

(* Split the exposed case, not one buried in a continuation.  Guarded IHs
   are kept verbatim; only the branch's fresh equations simplify the goal. *)
fun HEAD_CASE_TAC (g as (old,_)) =
  let fun simplify (asl,w) =
    let val fresh = List.filter (fn a => not (is_forall a) andalso
      not (List.exists (aconv a) old)) asl
    in simp_tac bool_ss (map ASSUME fresh) (asl,w) end
  in (BasicProvers.PURE_TOP_CASE_TAC >> simplify) g end;

(* Close the goal with an induction hypothesis, discharging its guards from
   the bind results in the assumptions.  An implication for which stop holds
   is the property itself, not a guard; normalise is applied to the
   hypotheses and the facts before matching. *)
fun IH_TAC {stop, normalise} (asl,w) =
  let
    fun terminal tm =
      if is_forall tm then terminal (snd (dest_forall tm))
      else if is_imp tm andalso not (stop tm) then terminal (snd (dest_imp tm))
      else tm
    val candidates = List.mapPartial
      (total (fn a => PART_MATCH terminal (ASSUME a) w)) asl
    val facts = List.concat (map (CONJUNCTS o normalise o ASSUME)
      (List.filter (not o is_forall) asl))
    fun discharge raw =
      let val th = normalise raw
          val body = snd (strip_forall (concl th)) in
        if not (is_imp body) orelse stop body then th else
        let val guard = fst (dest_imp body)
            fun refl side = MATCH_MP th (REFL (side guard))
        in discharge (tryfind (MATCH_MP th) facts handle HOL_ERR _ =>
             refl lhs handle HOL_ERR _ => refl rhs) end
      end
    fun close candidate g = MATCH_ACCEPT_TAC (discharge
      (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (normalise candidate))) g
  in FIRST (map close candidates) (asl,w) end;

(* Hypotheses guarded by a CreateTarget kind, and IntCall's tuple
   projections, need normalising before ih applies. *)
fun NORMALISE_IH_TAC ih =
  RULE_ASSUM_TAC (REWRITE_RULE [create_kind_11, create_kind_distinct,
    GSYM create_kind_distinct, COND_CLAUSES]) >>
  simp_tac bool_ss [FST, SND] >>
  FIRST [first_assum ACCEPT_TAC, ih];

(* Structural rules  premises ==> P (comb ...)  are indexed by their
   conclusion and applied with MATCH_MP_TAC; leaves come with their own key
   and closing tactic. *)
fun walk_net rules (leaves : (term * tactic) list) =
  List.foldl (fn ((key,tac),net) => Net.insert (key, tac) net)
    (List.foldl (fn (th,net) => Net.insert (snd (dest_imp (concl th)),
       MATCH_MP_TAC th >> rpt conj_tac) net) Net.empty rules)
    leaves;

(* Unfold one of ths at the head of the computation. *)
fun unfold_conv ths =
  let
    val c = FIRST_CONV (map REWR_CONV
      (List.concat (map (CONJUNCTS o SPEC_ALL) ths)))
    fun spine tm = (c ORELSEC RATOR_CONV spine) tm
  in spine end;

(* One walk step on a goal whose computation the conversion at reaches. *)
fun STEP {net, at, unfolds, intros, fallbacks} =
  let val unfold = unfold_conv unfolds in
    FIRST ([first_assum MATCH_ACCEPT_TAC,
      (fn g as (_,w) => FIRST (Net.match w net) g),
      CONV_TAC (at unfold), CONV_TAC (at (CHANGED_CONV head_conv))] @
      intros @ [HEAD_CASE_TAC] @ fallbacks)
  end;

(* Unfold one evaluator equation and walk its body. *)
fun EVAL_CASE intro step =
  intro >>
  simp_tac bool_ss [Once evaluate_def, lock_if_nr_def, unlock_if_nr_def] >>
  rpt step;

end
