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

(* The labels of the blocks a computation starts (new_block l), for the
   labels free in the goal. *)
val new_block_tm = prim_mk_const {Thy = "compileEnv", Name = "new_block"}

fun nb_labels gfvs t =
  let
    val ls = find_terms (fn x => is_comb x andalso
                                 same_const (rator x) new_block_tm) t
             |> map rand
             |> List.filter (fn l => List.all (fn v => tmem v gfvs)
                                              (free_vars l))
  in
    op_mk_set aconv ls
  end

fun label_set ls = pred_setSyntax.mk_set ls
  handle HOL_ERR _ => pred_setSyntax.mk_empty stringSyntax.string_ty

(* A sequence or bind m then f where f starts blocks m may jump to. *)
fun fwd_tac rule (g as (asl, w)) =
  let
    val (_, args) = strip_comb w
    val m_f = List.last args
    val (_, mf) = strip_comb m_f
    val (m, f) = case mf of [m, f] => (m, f)
                          | _ => raise mk_HOL_ERR "fragFuelLib" "fwd_tac" ""
    val gfvs = free_varsl (w :: asl)
    val lf = nb_labels gfvs f
    val lm = nb_labels gfvs m
  in
    if null lf andalso null lm then NO_TAC g
    else (match_mp_tac (ISPECL [label_set lm, label_set lf] rule) >>
          rpt conj_tac) g
  end

fun subset_tac (g as (_, w)) =
  if pred_setSyntax.is_subset w then
    (simp_tac (srw_ss()) [pred_setTheory.SUBSET_DEF] >> NO_TAC) g
  else NO_TAC g

val fuel_step =
  FIRST [
    match_mp_tac fuel_ok_fresh_var >> gen_tac >> BETA_TAC,
    fwd_tac fuel_ok_seq_fwd,
    fwd_tac fuel_ok_bind_fwd,
    subset_tac,
    match_mp_tac fuel_ok_ignore_bind0 >> conj_tac,
    match_mp_tac fuel_ok_bind0 >> conj_tac,
    match_mp_tac fuel_ok_if >> conj_tac >> strip_tac,
    CHANGED_TAC (PURE_REWRITE_TAC [LET_THM]) >> BETA_TAC,
    CHANGED_TAC (Ho_Rewrite.PURE_REWRITE_TAC [uncurry_comp_bind, comp_return_eta]),
    gen_tac >> BETA_TAC,
    MATCH_ACCEPT_TAC fuel_ok_return,
    MATCH_ACCEPT_TAC fuel_ok_new_block,
    MATCH_ACCEPT_TAC (CONJUNCT1 fuel_ok_prims),
    MATCH_ACCEPT_TAC (CONJUNCT1 (CONJUNCT2 fuel_ok_prims)),
    MATCH_ACCEPT_TAC (CONJUNCT2 (CONJUNCT2 fuel_ok_prims))
  ]

(* A definition `!xs st. f xs st = rhs` as `!xs. f xs = \st. rhs`, so it
   rewrites the unapplied action. *)
fun eta_def th =
  LIST_CONJ (map (fn c =>
    let
      val c1 = SPEC_ALL c
      val st = rand (lhs (concl c1))
    in
      GEN_ALL (CONV_RULE (LAND_CONV ETA_CONV) (ABS st c1))
    end) (CONJUNCTS (SPEC_ALL th)))

fun leaf_tac th =
  if is_imp (snd (strip_forall (concl th))) then match_mp_tac th
  else MATCH_ACCEPT_TAC th

fun leaf_thms ths =
  List.concat (map (map (GEN_ALL o SPEC_ALL) o CONJUNCTS o SPEC_ALL) ths)

fun fuel_auto ths =
  rpt (FIRST (fuel_step :: map leaf_tac (leaf_thms ths) @
              [first_assum MATCH_ACCEPT_TAC]))

end
