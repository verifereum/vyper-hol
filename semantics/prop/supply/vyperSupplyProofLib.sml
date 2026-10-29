(* Shared indexed tactics for supply-preservation proofs. *)
structure vyperSupplyProofLib =
struct

open HolKernel Parse boolLib bossLib;

(* Index only exposed action heads; do not search inside continuations. *)
fun fact_net facts rules =
  List.foldl (fn (th,net) =>
    Net.insert (concl th, MATCH_ACCEPT_TAC th) net)
    (List.foldl (fn (th,net) =>
      Net.insert (snd (dest_imp (concl th)), MATCH_MP_TAC th >> TRY conj_tac) net)
      Net.empty (map SPEC_ALL rules)) (map SPEC_ALL facts);

fun solve net (goal as (_,w)) = FIRST (Net.match w net) goal;

val head_conv =
  let
    val rules = List.concat (map (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
      (LET_THM :: COND_CLAUSES ::
       List.mapPartial (total TypeBasePure.case_def_of) (TypeBase.elts ())));
    val cases = List.foldl (fn (th,net) =>
      Net.insert (lhs (concl th), REWR_CONV th) net) Net.empty rules;
    fun root tm = FIRST_CONV (Net.match tm cases) tm;
    fun head tm = (BETA_CONV ORELSEC root ORELSEC
      REWR_CONV pairTheory.UNCURRY ORELSEC RATOR_CONV head) tm;
  in head end;

(* Preserve guarded IHs; simplify only with fresh branch equations. *)
fun case_tac (goal as (old,_)) =
  let
    fun simplify (asl,w) =
      let val fresh = List.filter (fn a => not (is_forall a) andalso
            not (List.exists (aconv a) old)) asl
      in simp_tac bool_ss (map ASSUME fresh) (asl,w) end;
  in (BasicProvers.PURE_TOP_CASE_TAC >> simplify) goal end;

fun step net = FIRST [
  CONV_TAC (HO_REWR_CONV pairTheory.FORALL_PROD), gen_tac,
  first_assum ACCEPT_TAC, solve net,
  CONV_TAC (RAND_CONV (CHANGED_CONV head_conv)),
  strip_tac, conj_tac, case_tac];

(* Discharge a guarded recursive IH using atomic success equations only.
   Normalising the whole IH context expands nested evaluator continuations. *)
fun finish_goal (goal as (asl,w)) =
  let
    fun key tm = #Name (dest_thy_const (fst (strip_comb (rand tm))));
    val atomic = List.concat (map (CONJUNCTS o ASSUME)
      (List.filter (not o is_forall) asl));
    val base = SIMP_RULE (bool_ss ++ numSimps.ARITH_ss)
      [vyperStateTheory.ignore_bind_def, oneTheory.one,
       pairTheory.FST, pairTheory.SND, arithmeticTheory.SUB_RIGHT_LESS_EQ];
    val atomic = map (base o BETA_RULE) atomic;
    val branch = List.filter (fn th => is_eq (concl th) andalso
      not (pairSyntax.is_pair (rhs (concl th)))) atomic;
    val normalise = SIMP_RULE (bool_ss ++ numSimps.ARITH_ss)
      (vyperStateTheory.ignore_bind_def :: oneTheory.one ::
       pairTheory.FST :: pairTheory.SND :: branch);
    val facts = map normalise atomic @ atomic;
    val candidates = rev (List.filter (fn tm => is_forall tm andalso
      total (key o snd o strip_imp o snd o strip_forall) tm = total key w) asl);
    fun guard_conv tm =
      if is_forall tm then BINDER_CONV guard_conv tm
      else LAND_CONV (SIMP_CONV (bool_ss ++ numSimps.ARITH_ss)
        [vyperStateTheory.ignore_bind_def, oneTheory.one,
         pairTheory.FST, pairTheory.SND, arithmeticTheory.SUB_RIGHT_LESS_EQ]) tm;
    fun discharge th =
      if is_imp (snd (strip_forall (concl th))) then
        discharge (tryfind (MATCH_MP (CONV_RULE guard_conv th)) (TRUTH :: facts))
      else base th;
    fun finish tm g =
      MATCH_ACCEPT_TAC (discharge
        (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (normalise (ASSUME tm)))) g;
  in FIRST (first_assum ACCEPT_TAC ::
       map (fn tm => fn g => finish tm g) candidates) goal end;

end
