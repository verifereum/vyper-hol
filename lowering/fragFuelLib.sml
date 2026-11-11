(*
 * Tactics for fuel_ok goals (lowering run-bound proofs).
 *
 * fuel_step takes one structural step of a goal
 *   fuel_ok Wv L E m
 * by the shape of m: a fresh_var bind, a bind or sequence whose first part
 * has no entry labels, an if, a let, or a return.
 *
 * fuel_auto ths repeats fuel_step and closes the leaves with the fuel_ok
 * lemmas ths (and the assumptions), leaving their side conditions.
 *)
structure fragFuelLib =
struct

open HolKernel boolLib bossLib fragFuelTheory

val fuel_step =
  FIRST [
    match_mp_tac fuel_ok_fresh_var >> gen_tac >> BETA_TAC,
    match_mp_tac fuel_ok_ignore_bind0 >> conj_tac,
    match_mp_tac fuel_ok_bind0 >> conj_tac,
    match_mp_tac fuel_ok_if >> conj_tac >> strip_tac,
    CHANGED_TAC (PURE_REWRITE_TAC [LET_THM]) >> BETA_TAC,
    gen_tac >> BETA_TAC,
    MATCH_ACCEPT_TAC fuel_ok_return,
    MATCH_ACCEPT_TAC (CONJUNCT1 fuel_ok_prims),
    MATCH_ACCEPT_TAC (CONJUNCT1 (CONJUNCT2 fuel_ok_prims)),
    MATCH_ACCEPT_TAC (CONJUNCT2 (CONJUNCT2 fuel_ok_prims))
  ]

fun leaf_tac th =
  if is_imp (snd (strip_forall (concl th))) then match_mp_tac th
  else MATCH_ACCEPT_TAC th

fun leaf_thms ths =
  List.concat (map (map (GEN_ALL o SPEC_ALL) o CONJUNCTS o SPEC_ALL) ths)

fun fuel_auto ths =
  rpt (FIRST (fuel_step :: map leaf_tac (leaf_thms ths) @
              [first_assum MATCH_ACCEPT_TAC]))

end
