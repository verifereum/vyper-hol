structure memSSAProofsLib = struct

open HolKernel boolLib bossLib;

(* Tactic to apply a universally-quantified inductive hypothesis.
   Matches the IH conclusion against the goal, specializes, and
   discharges the premise from assumptions.

   Two modes:
   1. Direct: IH premise conjuncts are exactly in assumptions (NONE/MnPhi cases)
   2. Simp: IH premise conjuncts can be proved by simp from assumptions (MnDef/MnUse)
*)
fun apply_forall_ih_tac (asl, g) =
  let
    fun try_ih tm =
      let
        val (vs, body) = strip_forall tm
        val _ = if null vs then raise Match else ()
        val (prem, ih_concl) = dest_imp body
        val (tm_subst, ty_subst) = match_term ih_concl g
        val ih_thm = ASSUME tm
        val spec_vals = map (fn v => subst tm_subst (inst ty_subst v)) vs
        val specialized = SPECL spec_vals ih_thm
        val spec_prem = fst (dest_imp (Thm.concl specialized))
        val conjs = strip_conj spec_prem
        fun find_asm c =
          case List.find (fn a => aconv a c) asl of
            SOME a => ASSUME a
          | NONE => raise mk_HOL_ERR "memSSAProofsLib" "try_ih"
                      ("No matching assumption for: " ^ term_to_string c)
        val prem_thms = map find_asm conjs
        val prem_thm = LIST_CONJ prem_thms
        val result = MP specialized prem_thm
      in
        SOME result
      end
      handle _ => NONE

    val results = List.mapPartial (fn a => try_ih a) asl
  in
    if not (null results)
    then ACCEPT_TAC (hd results) (asl, g)
    else raise mk_HOL_ERR "memSSAProofsLib" "apply_forall_ih_tac"
              "No IH found that matches the goal"
  end

(* Variant: match IH conclusion, then leave IH premise as subgoal *)
fun match_forall_ih_tac (asl, g) =
  let
    fun try_ih tm =
      let
        val (vs, body) = strip_forall tm
        val _ = if null vs then raise Match else ()
        val (prem, ih_concl) = dest_imp body
        val (tm_subst, ty_subst) = match_term ih_concl g
        val ih_thm = ASSUME tm
        val spec_vals = map (fn v => subst tm_subst (inst ty_subst v)) vs
        val specialized = SPECL spec_vals ih_thm
      in
        SOME specialized
      end
      handle _ => NONE

    val results = List.mapPartial (fn a => try_ih a) asl
    val _ = if null results then
              raise mk_HOL_ERR "memSSAProofsLib" "match_forall_ih_tac"
                "No IH found that matches the goal"
            else ()
    val result = hd results
    (* Use MATCH_MP_TAC to apply: leaves premise as subgoal *)
  in
    MATCH_MP_TAC result (asl, g)
  end

(* After applying a build-level lemma (which expands ms to mem_ssa_build ...),
   re-abbreviate: rewrite all expanded-form assumptions back to use ms.
   Usage: reabbrev_tac `ms` — looks for Abbrev(ms = ...), uses GSYM to
   rewrite (mem_ssa_build ...) back to ms in all assumptions. *)
fun reabbrev_tac q : tactic = fn (asl, g) =>
  let
    val target = Parse.parse_in_context (free_varsl (g :: asl)) q
    val ab_tm = List.find (fn a =>
      can (match_term ``Abbrev (x = y)``) a andalso
      aconv (fst (dest_eq (rand a))) target) asl
  in
    case ab_tm of
      NONE => raise mk_HOL_ERR "memSSAProofsLib" "reabbrev_tac"
                ("No Abbrev for " ^ term_to_string target)
    | SOME ab =>
        let val eq = REWRITE_RULE [markerTheory.Abbrev_def] (ASSUME ab)
            val geq = GSYM eq
        in (RULE_ASSUM_TAC (REWRITE_RULE [geq]) >>
            assume_tac (REWRITE_RULE [markerTheory.Abbrev_def |> GSYM] eq))
           (asl, g)
        end
  end

(* Wrap a plain equality 'x = ...' in assumptions as Abbrev(x = ...).
   Protects it from gvs[] substitution. Usage: wrap_abbrev `ms` *)
fun wrap_abbrev q =
  qpat_x_assum q
    (ASSUME_TAC o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])

(* Wrap the standard 4 build abbreviations: ms, dom, cfg, dfs_pre.
   Use after rpt strip_tac in build-level trivialities. *)
val wrap_build_abbrevs =
  wrap_abbrev `ms = _` >>
  wrap_abbrev `dom = _` >>
  wrap_abbrev `cfg = _` >>
  wrap_abbrev `dfs_pre = cfg.cfg_dfs_pre`

(* Apply a build-level lemma (with let ms = mem_ssa_build ...) to the current goal.
   Handles the BETA_RULE / PURE_REWRITE_RULE [LET_THM] boilerplate,
   specializes with given terms, discharges the impl_tac with gvs[],
   and strips the conclusion into assumptions.
   Usage: use_build_lemma build_reaching_same_block [`bp`, `fn`, ...] *)
fun use_build_lemma thm specs =
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] thm)) >>
  disch_then (qspecl_then specs mp_tac) >>
  (impl_tac >- (rpt conj_tac >> gvs[])) >> strip_tac

(* Like use_build_lemma but gives back two impl_tac stages
   (for lemmas with two-stage quantification like build_same_block_reaching_closest) *)
fun use_build_lemma2 thm specs1 specs2 =
  mp_tac (BETA_RULE (PURE_REWRITE_RULE [LET_THM] thm)) >>
  disch_then (qspecl_then specs1 mp_tac) >>
  (impl_tac >- (rpt conj_tac >> gvs[])) >>
  disch_then (qspecl_then specs2 mp_tac) >>
  (impl_tac >- (rpt conj_tac >> gvs[])) >> strip_tac

end;
