(*
 * Safe Arithmetic Properties
 *
 * TOP-LEVEL:
 *   compile_safe_add_correct — add with overflow check
 *   compile_safe_add_overflow — an overflowing unsigned 256-bit add reverts
 *   compile_safe_add_overflow_signed_256 — likewise a signed one
 *   compile_safe_add_unsigned_256_shape — its code stays in the block
 *   compile_safe_sub_correct — sub with underflow check
 *   compile_safe_sub_overflow_256 — an overflowing 256-bit sub reverts
 *   compile_safe_mul_correct — mul with overflow check (includes int256 MIN_INT)
 *   compile_safe_div_correct — div with division-by-zero check
 *   compile_safe_mod_correct — mod with division-by-zero check
 *   compile_compare_correct  — comparison with signed/unsigned dispatch
 *   compile_clamp_correct    — value clamping to type range
 *   compile_clamp_out_of_range, clamp_and_return_out_of_range
 *                            — an out-of-range value reverts
 *   compile_safe_add_out_of_range, compile_safe_sub_out_of_range,
 *   compile_safe_mul_overflow — an out-of-range result reverts
 *   compile_safe_div_ok      — div with no zero divisor or INT_MIN / -1
 *   sdiv_in_type_range       — the signed quotient stays in the type, but
 *                              for INT_MIN / -1
 *   compile_safe_div_overflow — signed INT_MIN / -1 reverts
 *   compile_safe_decimal_mul_run, compile_safe_decimal_div_run
 *                            — decimal mul and div, both outcomes
 *
 * Source: arithmetic.py (safe_add/sub/mul/div/mod/pow)
 * Lowering: exprLoweringScript.sml (compile_safe_*, compile_compare, compile_clamp)
 *
 * Proof strategy: Each compile_safe_* is a sequence of emit_op/emit_void.
 *   1. Unfold the definition (do-notation desugars to comp_bind chains)
 *   2. Use emitted_insts_append / run_inst_seq_append to split the sequence
 *   3. Prove each step via emit_op_*_correct or step_* from emitHelperProps
 *   4. For ASSERT: use assert_ok / assert_revert for the disjunction
 *   5. fresh_vars_wrt advances with each emit_op (emit_op_extends + fresh_var_distinct)
 *)

Theory arithmeticProps
Ancestors
  exprLoweringProps emitHelperProps
  exprLowering compileEnv
  venomExecSemantics venomState venomInst
  valueEncoding

(* ===== Reusable Tactics ===== *)

(* elim_lit n th: For emit_op_X_correct theorems, specialize the n-th operand
   (1-indexed) to be a Lit, eliminating its eval_operand conjunct.
   This allows drule_all to work without needing eval_operand (Lit w) ss
   as an explicit assumption.
   Example: elim_lit 2 emit_op_SLT_correct — SLT with Lit second arg *)
fun elim_lit n th =
  let
    val (vars, _) = strip_forall (concl th)
    val op_var = List.nth (vars, n-1)
    val v_var = List.nth (vars, n+1)
    val lit_const = prim_mk_const{Name="Lit",Thy="venomState"}
  in
    th |> SPEC_ALL
       |> INST [op_var |-> mk_comb(lit_const, v_var)]
       |> SIMP_RULE (srw_ss()) [eval_operand_lit]
       |> GENL (List.filter (fn v => not (aconv v op_var)) vars)
  end;

(* forward_all_evals: For each preservation fact
     ∀op w. eval_operand op ss_old = SOME w ⇒ eval_operand op ss_new = SOME w
   in the assumptions (from oldest to newest), apply it to all matching
   eval_operand facts and add the forwarded versions. Multiple passes
   ensure transitive forwarding through chains of states. *)
fun forward_all_evals (asl, g) : Context.t -> goal list * validation =
  let
    fun is_pres t =
      (let val (vs, body) = strip_forall t
       in length vs = 2 andalso is_imp body andalso
          let val (ant, _) = dest_imp body
              val (lhs_t, _) = dest_eq ant
              val (f, _) = strip_comb lhs_t
          in fst (dest_const f) = "eval_operand"
          end
       end) handle _ => false
    fun is_eval t =
      (not (is_forall t) andalso
       let val (lhs_t, rhs_t) = dest_eq t
           val (f, _) = strip_comb lhs_t
           val (some_c, _) = dest_comb rhs_t
       in fst (dest_const f) = "eval_operand" andalso
          fst (dest_const some_c) = "SOME"
       end) handle _ => false
    (* Process oldest preservation facts first for transitive forwarding *)
    val pres_list = rev (List.filter is_pres asl)
    fun apply_one_pres pres_t (asl', g') =
      let val pres_th = ASSUME pres_t
          val evals = List.filter is_eval asl'
          fun forward_one eval_t (asl'', g'') =
            (let val new_th = MATCH_MP (SPEC_ALL pres_th) (ASSUME eval_t)
                 val new_concl = concl new_th
             in if List.exists (aconv new_concl) asl''
                then ALL_TAC (asl'', g'')
                else assume_tac new_th (asl'', g'')
             end handle _ => ALL_TAC (asl'', g''))
      in EVERY (map forward_one evals) (asl', g')
      end
  in
    EVERY (map apply_one_pres pres_list) (asl, g)
  end;

(* collapse_run: given thm `A = B`, find assumption `B = OK s`, produce `A = OK s` *)
fun collapse_run (eq_th : thm) : tactic = fn (asl, g) =>
  let val rhs_tm = rhs (concl eq_th)
      fun matches_rhs a =
        (aconv (lhs (concl (ASSUME a))) rhs_tm) handle _ => false
  in case List.find matches_rhs asl of
       SOME a_str => assume_tac (TRANS eq_th (ASSUME a_str)) (asl, g)
     | NONE => raise mk_HOL_ERR "collapse_run" "collapse_run" "no matching run"
  end;

(* chain_step th: Forward all eval_operand preservation facts, apply an
   emit_op_*_correct theorem via drule_all, then chain with existing
   run_inst_seq prefix via imp_res_tac emit_op_extends + run_inst_seq_chain.
   Uses collapse_run instead of asm_rewrite_tac[] to avoid APPEND looping. *)
fun chain_step th : tactic =
  forward_all_evals >>
  drule_all th >> strip_tac >>
  TRY (imp_res_tac emit_op_extends >>
       drule_all run_inst_seq_chain >> strip_tac >>
       qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run);

(* Support for the final ASSERT step. ASSERT is a no-op (v≠0w) or
   reverts (v=0w). The tactic itself is defined below assert_chain so it can
   refer to the theorem directly, without mutable forward-reference state. *)
(* chain_assert_solve_run: solve a run_inst_seq goal using assumptions.
   Tries direct assumption match first (fast), then targeted chaining.
   AVOIDS: asm_rewrite_tac[] (loops on APPEND), imp_res_tac emitted_insts_append (O(N²)). *)
val chain_assert_solve_run : tactic =
  first_assum ACCEPT_TAC ORELSE
  (drule_all run_inst_seq_chain >> strip_tac >>
   first_assum ACCEPT_TAC) ORELSE
  asm_rewrite_tac[];

(* compose_eval_pres: solve ∀op w. eval op ss0 = SOME w ⇒ eval op ssN = SOME w
   by composing pres facts from assumptions. O(N) — no search.
   Handles identity (ss0=ssN) and multi-step chains. *)
fun compose_eval_pres (asl, gl) =
  let
    val (_, body) = strip_forall gl
    val (ant, con) = dest_imp body
    val ss0 = el 2 (#2 (strip_comb (lhs ant)))
    val ssN = el 2 (#2 (strip_comb (lhs con)))
  in
    if aconv ss0 ssN then
      (rpt strip_tac >> first_assum ACCEPT_TAC) (asl, gl)
    else
    let
      fun get_pres t =
        let val (vs, b) = strip_forall t
        in if length vs <> 2 then NONE
           else let val (a, c) = dest_imp b
                    val s1 = el 2 (#2 (strip_comb (lhs a)))
                    val s2 = el 2 (#2 (strip_comb (lhs c)))
                in if is_var s1 andalso is_var s2
                      andalso fst (dest_const (fst (strip_comb (lhs a)))) = "eval_operand"
                   then SOME (s1, s2, ASSUME t)
                   else NONE
                end
        end handle _ => NONE
      val pres_facts = List.mapPartial get_pres asl
      fun find_next s = List.find (fn (s1, _, _) => aconv s s1) pres_facts
      fun build_chain s acc =
        if aconv s ssN then SOME (rev acc)
        else case find_next s of
               SOME (_, s2, th) => build_chain s2 ((s, s2, th) :: acc)
             | NONE => NONE
      fun compose_chain [] = raise Fail "empty chain"
        | compose_chain [(_, _, th)] = th
        | compose_chain ((_, _, th1) :: rest) =
            let val composed_rest = compose_chain rest
                val th1s = SPEC_ALL th1
                val u1 = UNDISCH th1s
                val rest_s = SPEC_ALL composed_rest
                val result = MATCH_MP rest_s u1
                val ant_tm = fst (dest_imp (concl th1s))
                val disched = DISCH ant_tm result
                val (fv1, fv2) = let val vs = fst (strip_forall (concl th1))
                                 in (el 1 vs, el 2 vs) end
            in GENL [fv1, fv2] disched
            end
    in
      case build_chain ss0 [] of
        SOME chain =>
          let val composed = compose_chain chain
          in (rpt strip_tac >>
              first_assum (fn eval_assum =>
                assume_tac (MATCH_MP (SPEC_ALL composed) eval_assum) >>
                first_assum ACCEPT_TAC)) (asl, gl)
          end
      | NONE => raise mk_HOL_ERR "compose_eval_pres" "compose_eval_pres"
                      ("no chain from " ^ term_to_string ss0 ^ " to " ^ term_to_string ssN)
    end
  end;

(* solve_ci: solve ci extension goal
     fin.ci = pre.ci ++ ei pre fin
   by finding chain of ci facts in assumptions and composing via
   emitted_insts_append + APPEND associativity. O(N). *)
fun solve_ci (asl, gl) : Context.t -> goal list * validation =
  let
    (* Parse goal: fin.ci = pre.ci ++ ei pre fin *)
    val (lhs_tm, rhs_tm) = dest_eq gl
    (* LHS: acc(fin_state), RHS: acc(pre_state) ++ ei(pre_state, fin_state) *)
    val (acc_fn, fin_state) = dest_comb lhs_tm
    val [pre_ci_tm, _] = snd (strip_comb rhs_tm)
    val (_, pre_state) = dest_comb pre_ci_tm
    (* Parse ci fact: st2.ci = st1.ci ++ ei st1 st2 — returns (st1, st2, thm) *)
    fun parse_ci t =
      (let val (l, r) = dest_eq t
           val (a, st2) = dest_comb l
       in if aconv a acc_fn then
            let val [base, _] = snd (strip_comb r)
                val (_, st1) = dest_comb base
            in SOME (st1, st2, ASSUME t) end
          else NONE
       end) handle _ => NONE
    val ci_facts = List.mapPartial parse_ci asl
    (* Build chain from pre to fin using ci step facts.
       We want facts where st1 chains forward from pre_state to fin_state.
       Prefer the LONGEST step from pre_state (i.e. accumulated ci). *)
    fun find_step_from st =
      List.find (fn (s1, _, _) => aconv s1 st) ci_facts
    fun build_chain st =
      if aconv st fin_state then []
      else case find_step_from st of
             SOME (_, s2, th) => (s2, th) :: build_chain s2
           | NONE => raise mk_HOL_ERR "solve_ci" "solve_ci"
                       ("no ci step from " ^ term_to_string st)
    val chain = build_chain pre_state
  in
    case chain of
      [] => raise mk_HOL_ERR "solve_ci" "solve_ci" "empty chain"
    | [(_, th)] =>
        (* Single step: the assumption IS the goal *)
        ACCEPT_TAC th (asl, gl)
    | _ =>
      let
        val eia = emitted_insts_append
        fun compose_two (ci_prev, ci_next) =
          let
            val eia_inst = MATCH_MP eia (CONJ ci_prev ci_next)
            val step1 = CONV_RULE (RAND_CONV (RATOR_CONV (RAND_CONV
                          (REWR_CONV ci_prev)))) ci_next
            val step2 = CONV_RULE (RAND_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) step1
            val step3 = CONV_RULE (RAND_CONV (RAND_CONV
                          (REWR_CONV (GSYM eia_inst)))) step2
          in step3 end
        val ci_ths = map snd chain
        val first_ci = hd ci_ths
        val composed = List.foldl (fn (next, acc) => compose_two (acc, next))
                                  first_ci (tl ci_ths)
      in
        ACCEPT_TAC composed (asl, gl)
      end
  end;

(* solve_same_blocks: solve `same_blocks pre fin` by chaining
   step-wise same_blocks facts from assumptions. O(N). *)
fun solve_same_blocks (asl, gl) : Context.t -> goal list * validation =
  let
    val sb_def = same_blocks_def
    val (sb_fn, [pre_st, fin_st]) = strip_comb gl
    (* Parse same_blocks facts from assumptions *)
    fun parse_sb t =
      (let val (f, [s1, s2]) = strip_comb t
       in if aconv f sb_fn then SOME (s1, s2, ASSUME t) else NONE
       end) handle _ => NONE
    val sb_facts = List.mapPartial parse_sb asl
    fun find_step_from st =
      List.find (fn (s1, _, _) => aconv s1 st) sb_facts
    fun build_chain st =
      if aconv st fin_st then []
      else case find_step_from st of
             SOME (_, s2, th) => (s2, th) :: build_chain s2
           | NONE => raise mk_HOL_ERR "solve_same_blocks" "solve_same_blocks"
                       ("no same_blocks step from " ^ term_to_string st)
    val chain = build_chain pre_st
    (* Compose: unfold each to field equalities, TRANS chain, refold *)
    fun compose_two (sb_prev, sb_next) =
      let
        val [b1, bb1] = CONJUNCTS (REWRITE_RULE [sb_def] sb_prev)
        val [b2, bb2] = CONJUNCTS (REWRITE_RULE [sb_def] sb_next)
        val b = TRANS b2 b1
        val bb = TRANS bb2 bb1
      in REWRITE_RULE [GSYM sb_def] (CONJ b bb) end
    val ths = map snd chain
  in
    case ths of
      [] => raise mk_HOL_ERR "solve_same_blocks" "" "empty chain"
    | [th] => ACCEPT_TAC th (asl, gl)
    | _ =>
      let val composed = List.foldl (fn (next, acc) => compose_two (acc, next))
                                    (hd ths) (tl ths)
      in ACCEPT_TAC composed (asl, gl) end
  end;

(* chain_assert_branch: solve one subgoal from assert_chain.
   Dispatches to OK or Abort handling based on assumptions.
   AVOIDS: res_tac (O(N²) on 60+ assumptions), gvs[] (loops on APPEND). *)
fun chain_assert_branch (asl, gl) : Context.t -> goal list * validation =
  let
    val ok_pat = ``run_inst_seq _ _ = OK s``
    val abort_pat = ``run_inst_seq _ _ = Abort _ s``
    fun find_match pat =
      List.find (fn a =>
        can (match_term pat) a andalso not (is_forall a)) asl
    (* Dispatch each conjunct goal by shape *)
    fun solve_conjunct (asl2, g2) =
      let val head = fst (strip_comb g2) handle _ => g2
          val head_name = fst (dest_const head) handle _ => ""
      in
        if head_name = "fresh_vars_wrt" then
          (* Goal: fresh_vars_wrt fin ss. Find fresh_vars_wrt cs ss and
             emit_void _ _ cs = ((), fin) in assumptions, compose via MP. *)
          let
            val [_, ss_tm] = snd (strip_comb g2)
            val fv_emit = SRULE [] fresh_vars_wrt_emit_void
            (* Find a fresh_vars_wrt assumption whose ss matches the goal's ss *)
            fun is_fv_match a =
              (let val (f, [_, s]) = strip_comb a
               in fst (dest_const f) = "fresh_vars_wrt" andalso aconv s ss_tm
               end) handle _ => false
            val fv_asm = valOf (List.find is_fv_match asl2)
            val fv_th = ASSUME fv_asm
            (* Find emit_void assumption matching the state from fv_asm *)
            val [cs_tm, _] = snd (strip_comb fv_asm)
            fun is_ev_match a =
              (let val (l, r) = dest_eq a
                   val (f, args) = strip_comb l
               in fst (dest_const f) = "emit_void" andalso
                  aconv (last args) cs_tm
               end) handle _ => false
            val ev_asm = valOf (List.find is_ev_match asl2)
            val ev_th = ASSUME ev_asm
            val result = MATCH_MP fv_emit (CONJ fv_th ev_th)
          in ACCEPT_TAC result (asl2, g2) end
        else if head_name = "same_blocks" then
          solve_same_blocks (asl2, g2)
        else if is_eq g2 andalso
                (let val (l,_) = dest_eq g2
                     val (a,_) = dest_comb l
                 in fst (dest_const a) = "recordtype.compile_state.seldef.cs_current_insts"
                 end handle _ => false) then
          solve_ci (asl2, g2)
        else if is_forall g2 then
          compose_eval_pres (asl2, g2)
        else
          first_assum ACCEPT_TAC (asl2, g2)
      end
  in
    case find_match abort_pat of
      SOME t =>
        let val witness = rand (rhs t)
        in (EXISTS_TAC witness >> disj2_tac >> chain_assert_solve_run)
             (asl, gl) end
    | NONE =>
      (case find_match ok_pat of
         SOME t =>
           let val witness = rand (rhs t)
           in (EXISTS_TAC witness >> disj1_tac >>
               conj_tac >- (first_assum ACCEPT_TAC ORELSE chain_assert_solve_run) >>
               rpt conj_tac >> solve_conjunct)
               (asl, gl) end
       | NONE => raise mk_HOL_ERR "chain_assert" "chain_assert_branch"
                       "no run_inst_seq fact found")
  end;

(* chain_last th: Like chain_step but for the final emit_op.
   Chains and closes the goal with gvs + metis_tac. *)
fun chain_last th : tactic =
  chain_step th >>
  TRY (gvs[] >> metis_tac[]);

(* Unfold compile monad for one nesting level *)
val monad_unfold =
  [comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM];

(* ===== Type-Appropriate Integer Interpretation ===== *)

Definition math_val_def:
  math_val ty (w:bytes32) : int =
    if is_signed_type ty then w2i w else &(w2n w)
End

Definition in_type_range_def:
  in_type_range ty (v:int) =
    let bits = type_bits ty in
    if is_signed_type ty then
      -&(2 ** (bits - 1)) ≤ v ∧ v ≤ &(2 ** (bits - 1) - 1)
    else
      0 ≤ v ∧ v < &(2 ** bits)
End

(* Signed bounds roundtrip independently of the compiler/evaluation context. *)
Theorem w2i_i2w_neg_pow2:
  ∀bits. bits ≤ 255 ⇒
    w2i (i2w (-&(2 ** bits)) : bytes32) = -&(2 ** bits)
Proof
  rpt strip_tac >>
  `2 ** bits ≤ 2 ** 255` by simp[bitTheory.TWOEXP_MONO2] >>
  irule integer_wordTheory.w2i_i2w_neg >>
  simp[wordsTheory.INT_MIN_def]
QED

Theorem w2i_i2w_pow2_sub1:
  ∀bits. bits ≤ 255 ⇒
    w2i (i2w (&(2 ** bits - 1)) : bytes32) = &(2 ** bits - 1)
Proof
  rpt strip_tac >>
  `2 ** bits ≤ 2 ** 255` by simp[bitTheory.TWOEXP_MONO2] >>
  irule integer_wordTheory.w2i_i2w_pos >>
  simp[wordsTheory.INT_MIN_def, integer_wordTheory.INT_MAX_def]
QED

Theorem unsigned_in_range_not_gt_hi[local]:
  ∀ty v lo hi.
    in_type_range ty (math_val ty v) ∧
    type_bits ty ≤ 256 ∧
    type_bounds ty = (lo, hi) ∧
    ¬is_signed_type ty ⇒
    ¬(w2n v > w2n hi)
Proof
  rw[type_bounds_def, in_type_range_def, math_val_def, LET_THM] >>
  `2 ** type_bits ty ≤ 2 ** 256` by simp[bitTheory.TWOEXP_MONO2] >>
  `2 ** type_bits ty − 1 < dimword (:256)` by
    simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  simp[wordsTheory.w2n_n2w]
QED

(* bool_to_word simplification *)
Theorem bool_to_word_T[simp]:
  bool_to_word T = 1w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_F[simp]:
  bool_to_word F = 0w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_iszero[simp]:
  bool_to_word (bool_to_word b = 0w) = bool_to_word (¬b)
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_eq_0w[simp]:
  (bool_to_word b = 0w) ⇔ ¬b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_neq_0w[simp]:
  (bool_to_word b ≠ 0w) ⇔ b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_and[simp]:
  bool_to_word a && bool_to_word b = bool_to_word (a ∧ b) : bytes32
Proof
  Cases_on `a` >> Cases_on `b` >> simp[bool_to_word_def] >>
  blastLib.BBLAST_TAC
QED

(* ===== Zero-Check Helpers ===== *)

Theorem zero_check_reverts:
  ∀ y st0 yz st1 ynz st2 st3 ss.
    emit_op ISZERO [y] st0 = (yz, st1) ∧
    emit_op ISZERO [yz] st1 = (ynz, st2) ∧
    emit_void ASSERT [ynz] st2 = ((), st3) ∧
    eval_operand y ss = SOME 0w ∧
    fresh_vars_wrt st0 ss
    ⇒
    (∃ ss'. run_inst_seq (emitted_insts st0 st3) ss = Abort Revert_abort ss') ∧
    st3.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st3
Proof
  rpt strip_tac
  >- (drule_all emit_op_ISZERO_correct >> strip_tac >>
      imp_res_tac emit_op_extends >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      imp_res_tac emit_op_extends >>
      drule_all run_inst_seq_chain >> strip_tac >>
      `run_inst_seq (emitted_insts st0 st2) ss = OK ss''` by gvs[] >>
      `eval_operand ynz ss'' = SOME 0w` by gvs[] >>
      drule_all emit_void_ASSERT_revert >> strip_tac >>
      imp_res_tac emit_void_extends >>
      drule_all run_inst_seq_chain >> strip_tac >> gvs[] >> metis_tac[])
  >> imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     `emitted_insts st0 st2 = emitted_insts st0 st1 ++ emitted_insts st1 st2`
       by (irule emitted_insts_append >> gvs[]) >>
     `emitted_insts st0 st3 = emitted_insts st0 st2 ++ emitted_insts st2 st3`
       by (irule emitted_insts_append >> gvs[]) >>
     gvs[]
QED

Theorem zero_check_passes:
  ∀ y st0 yz st1 ynz st2 st3 ss b.
    emit_op ISZERO [y] st0 = (yz, st1) ∧
    emit_op ISZERO [yz] st1 = (ynz, st2) ∧
    emit_void ASSERT [ynz] st2 = ((), st3) ∧
    eval_operand y ss = SOME b ∧ b ≠ 0w ∧
    fresh_vars_wrt st0 ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st0 st3) ss = OK ss' ∧
      fresh_vars_wrt st3 ss' ∧
      st3.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st3 ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      same_blocks st0 st3
Proof
  rpt strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st0 st2) ss = OK ss''` by gvs[] >>
  `eval_operand ynz ss'' = SOME 1w` by gvs[] >>
  `(1w:bytes32) ≠ 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok >> strip_tac >>
  imp_res_tac emit_void_extends >>
  imp_res_tac fresh_vars_wrt_emit_void >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[] >>
  metis_tac[same_blocks_def]
QED

Theorem abort_propagates:
  ∀ st st_mid st' ss.
    st_mid.cs_current_insts = st.cs_current_insts ++ emitted_insts st st_mid ∧
    (∃ L. st'.cs_current_insts = st_mid.cs_current_insts ++ L) ∧
    (∀s. run_inst_seq (emitted_insts st st_mid) ss ≠ OK s)
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      run_inst_seq (emitted_insts st st_mid) ss
Proof
  rw[] >>
  `st'.cs_current_insts = st_mid.cs_current_insts ++ emitted_insts st_mid st'`
    by gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all run_inst_seq_chain_err >> rw[]
QED

(* ===== Clamping ===== *)

(* Transitivity of extends: if state chains through intermediate states,
   the overall emitted_insts is the concatenation. *)
Theorem extends_trans:
  ∀ st st1 st'.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st' ∧
    same_blocks st st1 ∧ same_blocks st1 st'
    ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rpt strip_tac
  >- (`emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
        by (irule emitted_insts_append >> gvs[]) >>
      gvs[])
  >> gvs[same_blocks_def]
QED

(* chain_extends_tac: prove ci ∧ same_blocks for composed state extension
   by chaining individual ci + same_blocks facts from assumptions via
   extends_trans. Solves goals of the form:
     st'.ci = st.ci ++ ei st st' ∧ same_blocks st st'
   where intermediate ci/same_blocks facts are in assumptions. O(N). *)
fun chain_extends_tac (asl, gl) : Context.t -> goal list * validation =
  let
    val (ci_goal, sb_goal) = dest_conj gl
    val (lhs_ci, _) = dest_eq ci_goal
    val (acc_fn, fin_st) = dest_comb lhs_ci
    val (sb_fn, [pre_st, _]) = strip_comb sb_goal
    fun parse_ci t =
      (let val (l, r) = dest_eq t
           val (a, s2) = dest_comb l
       in if aconv a acc_fn then
            let val (_, s1) = dest_comb (hd (snd (strip_comb r)))
            in SOME (s1, s2) end else NONE
       end) handle _ => NONE
    fun parse_sb t =
      (let val (f, [s1, s2]) = strip_comb t
       in if aconv f sb_fn then SOME (s1, s2) else NONE end) handle _ => NONE
    fun find_ci_from st =
      List.find (fn a => case parse_ci a of SOME (s1, _) => aconv s1 st | _ => false) asl
    fun build_chain st =
      if aconv st fin_st then []
      else case find_ci_from st of
             SOME a => let val SOME (_, s2) = parse_ci a in a :: build_chain s2 end
           | NONE => raise mk_HOL_ERR "chain_extends_tac" "" ("no ci from " ^ term_to_string st)
    val chain = build_chain pre_st
    fun find_sb s1 s2 =
      valOf (List.find (fn a =>
        case parse_sb a of SOME (a1, a2) => aconv a1 s1 andalso aconv a2 s2 | _ => false) asl)
    val et = extends_trans
    fun fold_chain [] = raise Fail "empty"
      | fold_chain [ci] =
          let val SOME (s1, s2) = parse_ci ci
          in LIST_CONJ [ASSUME ci, ASSUME (find_sb s1 s2)] end
      | fold_chain (ci :: rest) =
          let val rest_th = fold_chain rest
              val SOME (s1, s2) = parse_ci ci
              val conj4 = LIST_CONJ [ASSUME ci, CONJUNCT1 rest_th,
                                     ASSUME (find_sb s1 s2), CONJUNCT2 rest_th]
          in MATCH_MP et conj4 end
    val composed = fold_chain chain
  in
    (conj_tac >- ACCEPT_TAC (CONJUNCT1 composed)
              >> ACCEPT_TAC (CONJUNCT2 composed)) (asl, gl)
  end;

(* Bridge: chain prefix run from st→mid with suffix run from mid→fin.
   Requires the emitted_insts decomposition as a hypothesis (since
   deriving it from ci equations needs same_blocks transitivity). *)
Theorem run_inst_seq_bridge:
  ∀ st mid fin ss ss_mid.
    run_inst_seq (emitted_insts st mid) ss = OK ss_mid ∧
    emitted_insts st fin = emitted_insts st mid ++ emitted_insts mid fin ⇒
    run_inst_seq (emitted_insts st fin) ss =
    run_inst_seq (emitted_insts mid fin) ss_mid
Proof
  rpt strip_tac >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `emitted_insts mid fin` mp_tac) >>
  asm_rewrite_tac[]
QED

(* Derive emitted_insts split: if mid.ci = st.ci ++ ... and fin.ci = mid.ci ++ ...,
   then emitted_insts st fin = emitted_insts st mid ++ emitted_insts mid fin.
   Weaker than emitted_insts_append: only needs ∃L for the second condition. *)
Theorem emitted_insts_prefix_split:
  ∀ st mid fin.
    mid.cs_current_insts = st.cs_current_insts ++ emitted_insts st mid ∧
    (∃L. fin.cs_current_insts = mid.cs_current_insts ++ L) ⇒
    emitted_insts st fin = emitted_insts st mid ++ emitted_insts mid fin
Proof
  rpt strip_tac >>
  irule emitted_insts_append >> gvs[] >>
  once_rewrite_tac[emitted_insts_def] >>
  asm_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* compile_clamp only appends instructions *)
Theorem compile_clamp_extends:
  ∀ val_op ty st st'.
    compile_clamp val_op ty st = ((), st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_clamp_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  chain_extends_tac
QED

Theorem clamp_and_return_extends:
  ∀ res ty st st' op.
    clamp_and_return res ty st = (op, st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[clamp_and_return_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[comp_return_def] >>
  imp_res_tac compile_clamp_extends >> gvs[]
QED

Theorem compile_mul_overflow_check_extends:
  ∀ x y res is_signed bits st st'.
    compile_mul_overflow_check x y res is_signed bits st = ((), st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_mul_overflow_check_def :: monad_unfold) >>
  rpt (pairarg_tac >> gvs[comp_return_def]) >>
  Cases_on `is_signed ∧ bits = 256` >> gvs[comp_return_def] >>
  gvs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  chain_extends_tac
QED

(* ASSERT either reverts (v=0w) or is a no-op preserving state (v≠0w).
   When chained after a prefix, the full sequence either:
   - Aborts (revert), or
   - Succeeds with the SAME state as before the ASSERT. *)
Theorem assert_chain:
  ∀ op cs st' v ss st0 ss0.
    emit_void ASSERT [op] cs = ((), st') ∧
    eval_operand op ss = SOME v ∧
    fresh_vars_wrt cs ss ∧
    run_inst_seq (emitted_insts st0 cs) ss0 = OK ss ∧
    cs.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 cs ∧
    same_blocks cs st'
    ⇒
    (v ≠ 0w ∧ run_inst_seq (emitted_insts st0 st') ss0 = OK ss) ∨
    (∃ss'. run_inst_seq (emitted_insts st0 st') ss0 = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `v = 0w`
  >- (gvs[] >>
      drule_all emit_void_ASSERT_revert >> strip_tac >>
      imp_res_tac emit_void_extends >>
      suspend "revert")
  >> suspend "ok"
QED

Resume assert_chain[revert]:
  drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

Resume assert_chain[ok]:
  disj1_tac >>
  drule_all emit_void_ASSERT_ok >> strip_tac >>
  imp_res_tac emit_void_extends >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

Finalise assert_chain

(* Final ASSERT tactic. Defined after assert_chain to avoid a mutable theorem
   reference initialized with a placeholder. *)
fun chain_assert_tac (g : goal) : Context.t -> goal list * validation =
  (forward_all_evals >>
   imp_res_tac emit_void_extends >>
   drule_all_then strip_assume_tac assert_chain >>
   chain_assert_branch) g;

(* assert_chain_bridged: Like assert_chain but takes two prefix runs
   st0→mid and mid→cs, combining them internally.
   For proofs where chain_steps accumulate from an intermediate state. *)
Theorem assert_chain_bridged:
  ∀ op cs st' v ss mid ss_mid st0 ss0.
    emit_void ASSERT [op] cs = ((), st') ∧
    eval_operand op ss = SOME v ∧
    fresh_vars_wrt cs ss ∧
    run_inst_seq (emitted_insts st0 mid) ss0 = OK ss_mid ∧
    run_inst_seq (emitted_insts mid cs) ss_mid = OK ss ∧
    mid.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 mid ∧
    cs.cs_current_insts = mid.cs_current_insts ++ emitted_insts mid cs ∧
    same_blocks cs st'
    ⇒
    (v ≠ 0w ∧ run_inst_seq (emitted_insts st0 st') ss0 = OK ss) ∨
    (∃ss'. run_inst_seq (emitted_insts st0 st') ss0 = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  `run_inst_seq (emitted_insts st0 cs) ss0 = OK ss` by gvs[] >>
  drule_all assert_chain >> strip_tac >> gvs[]
QED

(* assert_chain_ok: When ASSERT succeeds (ok ≠ 0w) after a successful prefix
   run, the full sequence produces a 5+1-conjunct result.
   The extra conjunct preserves eval_operand from the ASSERT input state (ss),
   not just from ss0. This is crucial for _in_range proofs where we need
   eval_operand of a fresh variable created during the prefix. *)
Theorem assert_chain_ok:
  ∀ ok_op cs st' v ss st0 ss0.
    emit_void ASSERT [ok_op] cs = ((), st') ∧
    eval_operand ok_op ss = SOME v ∧
    v ≠ 0w ∧
    fresh_vars_wrt cs ss ∧
    run_inst_seq (emitted_insts st0 cs) ss0 = OK ss ∧
    cs.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 cs ∧
    (∀op w. eval_operand op ss0 = SOME w ⇒ eval_operand op ss = SOME w) ∧
    same_blocks st0 cs
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st0 st') ss0 = OK ss' ∧
      fresh_vars_wrt st' ss' ∧
      st'.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st' ∧
      (∀op w. eval_operand op ss0 = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      same_blocks st0 st' ∧
      (∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  imp_res_tac emit_void_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists `ss` >> gvs[] >>
  metis_tac[same_blocks_trans]
QED

(* Strengthened clamp: OK branch preserves all eval_operand facts.
   This is true because compile_clamp only emits check instructions
   (SLT/SGT/GT/ISZERO/AND/ASSERT), each of which preserves eval_operand,
   and ASSERT_ok returns the same state. *)
Theorem compile_clamp_correct_full:
  ∀ val_op ty ss st st' v.
    compile_clamp val_op ty st = ((), st') ∧
    eval_operand val_op ss = SOME v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       (∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_clamp_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume compile_clamp_correct_full[signed]:
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  chain_step (elim_lit 2 emit_op_SGT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_AND_correct >>
  chain_assert_tac
QED

Resume compile_clamp_correct_full[unsigned]:
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_GT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  chain_assert_tac
QED

Finalise compile_clamp_correct_full

Theorem compile_clamp_correct:
  ∀ val_op ty ss st st' v.
    compile_clamp val_op ty st = ((), st') ∧
    eval_operand val_op ss = SOME v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  drule_all compile_clamp_correct_full >> strip_tac >>
  qexists `ss'` >> gvs[]
QED

(* compile_clamp_ok: When the value is in the type's range,
   compile_clamp succeeds (doesn't revert). This is the key helper for
   _in_range theorems in the bits < 256 path. *)
Theorem compile_clamp_ok:
  ∀ val_op ty ss st st' v.
    compile_clamp val_op ty st = ((), st') ∧
    eval_operand val_op ss = SOME v ∧
    fresh_vars_wrt st ss ∧
    in_type_range ty (math_val ty v) ∧
    type_bits ty ≤ 256
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      fresh_vars_wrt st' ss' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      (∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      same_blocks st st'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_clamp_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume compile_clamp_ok[signed]:
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  chain_step (elim_lit 2 emit_op_SGT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_AND_correct >>
  forward_all_evals >>
  (* Show ok ≠ 0w from in_type_range *)
  `¬(v < lo) ∧ ¬(v > hi)` by (
    gvs[type_bounds_def, in_type_range_def, math_val_def, LET_THM,
        integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi] >>
    `type_bits ty − 1 ≤ 255` by simp[] >>
    `w2i (i2w (-&(2 ** (type_bits ty − 1))) : bytes32) =
       -&(2 ** (type_bits ty − 1))` by (
      irule w2i_i2w_neg_pow2 >> first_assum ACCEPT_TAC) >>
    `w2i (i2w (&(2 ** (type_bits ty − 1) − 1)) : bytes32) =
       &(2 ** (type_bits ty − 1) − 1)` by (
      irule w2i_i2w_pow2_sub1 >> first_assum ACCEPT_TAC) >>
    asm_rewrite_tac[] >> intLib.COOPER_TAC) >>
  `bool_to_word (bool_to_word (v < lo) = 0w) &&
   bool_to_word (bool_to_word (v > hi) = 0w) ≠ 0w` by gvs[] >>
  `same_blocks st cs'⁵'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss'⁵' = SOME w`
    by compose_eval_pres >>
  drule_all assert_chain_ok >>
  disch_then strip_assume_tac >> first_assum (irule_at Any) >> gvs[]
QED

Resume compile_clamp_ok[unsigned]:
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_GT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  forward_all_evals >>
  (* Show ¬(w2n v > w2n hi) from in_type_range *)
  `¬(w2n v > w2n hi)` by (
    qspecl_then [`ty`, `v`, `lo`, `hi`] mp_tac unsigned_in_range_not_gt_hi >>
    impl_tac >- asm_rewrite_tac[] >>
    simp[]) >>
  `bool_to_word (bool_to_word (w2n v > w2n hi) = 0w) ≠ 0w` by gvs[] >>
  `same_blocks st cs''` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss'' = SOME w`
    by compose_eval_pres >>
  drule_all assert_chain_ok >>
  disch_then strip_assume_tac >> first_assum (irule_at Any) >> gvs[]
QED

Finalise compile_clamp_ok

(* compile_clamp_out_of_range: the abort counterpart of compile_clamp_ok.
   A value out of the type's range fails the ASSERT. *)
Theorem compile_clamp_out_of_range:
  ∀ val_op ty ss st st' v.
    compile_clamp val_op ty st = ((), st') ∧
    eval_operand val_op ss = SOME v ∧
    fresh_vars_wrt st ss ∧
    ¬in_type_range ty (math_val ty v) ∧
    type_bits ty ≤ 256
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_clamp_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[] >>
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[])
  >- ((* signed: v < lo or v > hi, so the AND is 0w *)
      chain_step (elim_lit 2 emit_op_SLT_correct) >>
      chain_step emit_op_ISZERO_correct >>
      chain_step (elim_lit 2 emit_op_SGT_correct) >>
      chain_step emit_op_ISZERO_correct >>
      chain_step emit_op_AND_correct >>
      forward_all_evals >>
      `v < lo ∨ v > hi` by (
        gvs[type_bounds_def, in_type_range_def, math_val_def, LET_THM,
            integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi] >>
        `type_bits ty − 1 ≤ 255` by simp[] >>
        `w2i (i2w (-&(2 ** (type_bits ty − 1))) : bytes32) =
           -&(2 ** (type_bits ty − 1))` by (
          irule w2i_i2w_neg_pow2 >> first_assum ACCEPT_TAC) >>
        `w2i (i2w (&(2 ** (type_bits ty − 1) − 1)) : bytes32) =
           &(2 ** (type_bits ty − 1) − 1)` by (
          irule w2i_i2w_pow2_sub1 >> first_assum ACCEPT_TAC) >>
        asm_rewrite_tac[] >> intLib.COOPER_TAC) >>
      `bool_to_word (bool_to_word (v < lo) = 0w) &&
       bool_to_word (bool_to_word (v > hi) = 0w) = 0w` by
        (Cases_on `v < lo` >> fs[]) >>
      imp_res_tac emit_void_extends >>
      drule_all_then strip_assume_tac assert_chain >>
      first_assum (irule_at Any)) >>
  (* unsigned: v > hi *)
  chain_step (elim_lit 2 emit_op_GT_correct) >>
  chain_step emit_op_ISZERO_correct >>
  forward_all_evals >>
  `w2n v > w2n hi` by (
    (* only the bounds matter: drop the run facts before unfolding *)
    qpat_x_assum `¬in_type_range _ _` mp_tac >>
    qpat_x_assum `type_bounds _ = _` mp_tac >>
    qpat_x_assum `¬is_signed_type _` mp_tac >>
    qpat_x_assum `type_bits _ ≤ 256` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    gvs[type_bounds_def, in_type_range_def, math_val_def, LET_THM] >>
    `0 < 2 ** type_bits ty ∧ 2 ** type_bits ty ≤ 2 ** 256` by simp[] >>
    `2 ** type_bits ty − 1 < 2 ** 256` by decide_tac >>
    simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def]) >>
  imp_res_tac emit_void_extends >>
  drule_all_then strip_assume_tac assert_chain >>
  TRY (gvs[] >> NO_TAC) >>
  first_assum (irule_at Any)
QED

(* clamp_and_return_ok: When the value is in range, clamp_and_return succeeds
   and returns the same value. Used for bits < 256 path of _in_range proofs. *)
Theorem clamp_and_return_ok:
  ∀ res ty mid op fin base ss0 ss_mid v.
    clamp_and_return res ty mid = (op, fin) ∧
    run_inst_seq (emitted_insts base mid) ss0 = OK ss_mid ∧
    eval_operand res ss_mid = SOME v ∧
    fresh_vars_wrt mid ss_mid ∧
    mid.cs_current_insts = base.cs_current_insts ++ emitted_insts base mid ∧
    in_type_range ty (math_val ty v) ∧
    type_bits ty ≤ 256
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts base fin) ss0 = OK ss' ∧
      eval_operand op ss' = SOME v
Proof
  rpt gen_tac >> strip_tac >>
  gvs[clamp_and_return_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac compile_clamp_extends >>
  drule_all compile_clamp_ok >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

(* clamp_and_return_out_of_range: the abort counterpart of
   clamp_and_return_ok. *)
Theorem clamp_and_return_out_of_range:
  ∀ res ty mid op fin base ss0 ss_mid v.
    clamp_and_return res ty mid = (op, fin) ∧
    run_inst_seq (emitted_insts base mid) ss0 = OK ss_mid ∧
    eval_operand res ss_mid = SOME v ∧
    fresh_vars_wrt mid ss_mid ∧
    mid.cs_current_insts = base.cs_current_insts ++ emitted_insts base mid ∧
    ¬in_type_range ty (math_val ty v) ∧ type_bits ty ≤ 256
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts base fin) ss0 = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[clamp_and_return_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac compile_clamp_extends >>
  drule_all compile_clamp_out_of_range >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

(* clamp_and_return_correct: Encapsulates the common pattern of
   chaining a prefix run with clamp_and_return. Avoids drule_all
   non-determinism when there are many ci-extension facts.
   Used in: add[lt256], sub[lt256], div[signed_lt256], mul. *)
Theorem clamp_and_return_correct:
  ∀ res ty mid op fin base ss0 ss_mid v.
    clamp_and_return res ty mid = (op, fin) ∧
    run_inst_seq (emitted_insts base mid) ss0 = OK ss_mid ∧
    eval_operand res ss_mid = SOME v ∧
    fresh_vars_wrt mid ss_mid ∧
    mid.cs_current_insts = base.cs_current_insts ++ emitted_insts base mid
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts base fin) ss0 = OK ss' ∧
       eval_operand op ss' = SOME v) ∨
      run_inst_seq (emitted_insts base fin) ss0 = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[clamp_and_return_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac compile_clamp_extends >>
  drule_all compile_clamp_correct_full >>
  strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

(* ===== Comparison ===== *)

Definition eval_compare_def:
  eval_compare Lt ty a b =
    (if is_uint256 ty then w2n a < w2n b else w2i a < w2i b) ∧
  eval_compare Gt ty a b =
    (if is_uint256 ty then w2n a > w2n b else w2i a > w2i b) ∧
  eval_compare Eq ty a b = (a = b) ∧
  eval_compare NotEq ty a b = (a ≠ b) ∧
  eval_compare LtE ty a b =
    (if is_uint256 ty then w2n a ≤ w2n b else w2i a ≤ w2i b) ∧
  eval_compare GtE ty a b =
    (if is_uint256 ty then w2n a ≥ w2n b else w2i a ≥ w2i b) ∧
  eval_compare _ ty a b = F
End

Theorem compile_compare_correct:
  ∀ cmp_op x y ty ss st op st' a b.
    compile_compare cmp_op x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    MEM cmp_op [Lt; Gt; Eq; NotEq; LtE; GtE]
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (bool_to_word (eval_compare cmp_op ty a b))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  fs[compile_compare_def, eval_compare_def, comp_bind_def,
     comp_return_def, comp_ignore_bind_def, LET_THM]
  >- suspend "Lt"
  >- suspend "Gt"
  >- suspend "Eq"
  >- suspend "NotEq"
  >- suspend "LtE"
  >> suspend "GtE"
QED

Resume compile_compare_correct[Lt]:
  Cases_on `is_uint256 ty` >> gvs[]
  >- (drule_all emit_op_LT_correct >> strip_tac >>
      qexists `ss'` >> simp[])
  >> drule_all emit_op_SLT_correct >> strip_tac >>
     qexists `ss'` >> gvs[GSYM integer_wordTheory.WORD_LTi]
QED

Resume compile_compare_correct[Gt]:
  Cases_on `is_uint256 ty` >> gvs[]
  >- (drule_all emit_op_GT_correct >> strip_tac >>
      qexists `ss'` >> simp[])
  >> drule_all emit_op_SGT_correct >> strip_tac >>
     qexists `ss'` >> gvs[GSYM integer_wordTheory.WORD_GTi]
QED

Resume compile_compare_correct[Eq]:
  drule_all emit_op_EQ_correct >> metis_tac[]
QED

Resume compile_compare_correct[NotEq]:
  pairarg_tac >> gvs[] >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists `ss''` >> gvs[]
QED

Resume compile_compare_correct[LtE]:
  pairarg_tac >> gvs[] >>
  Cases_on `is_uint256 ty` >> gvs[]
  >- (drule_all emit_op_GT_correct >> strip_tac >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      imp_res_tac emit_op_extends >>
      drule_all run_inst_seq_chain >> gvs[] >>
      gvs[arithmeticTheory.NOT_GREATER, arithmeticTheory.GREATER_EQ])
  >> drule_all emit_op_SGT_correct >> strip_tac >>
     drule_all emit_op_ISZERO_correct >> strip_tac >>
     imp_res_tac emit_op_extends >>
     drule_all run_inst_seq_chain >> gvs[] >>
     gvs[GSYM integer_wordTheory.WORD_LEi, wordsTheory.WORD_NOT_GREATER]
QED

Resume compile_compare_correct[GtE]:
  pairarg_tac >> gvs[] >>
  Cases_on `is_uint256 ty` >> gvs[]
  >- (drule_all emit_op_LT_correct >> strip_tac >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      imp_res_tac emit_op_extends >>
      drule_all run_inst_seq_chain >>
      simp[arithmeticTheory.GREATER_EQ, arithmeticTheory.NOT_LESS])
  >> drule_all emit_op_SLT_correct >> strip_tac >>
     drule_all emit_op_ISZERO_correct >> strip_tac >>
     imp_res_tac emit_op_extends >>
     drule_all run_inst_seq_chain >>
     simp[GSYM integer_wordTheory.WORD_GEi,
          wordsTheory.WORD_GREATER_EQ, wordsTheory.WORD_NOT_LESS,
          arithmeticTheory.GREATER_EQ, arithmeticTheory.NOT_LESS]
QED

Finalise compile_compare_correct

(* ===== Safe Modulo ===== *)

Theorem compile_safe_mod_by_zero:
  ∀ x y ty ss st op st' a.
    compile_safe_mod x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME 0w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_mod_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[] >>
  drule_all zero_check_reverts >> strip_tac >>
  imp_res_tac emit_op_extends >>
  `∀s. run_inst_seq (emitted_insts st cs'³') ss ≠ OK s` by gvs[] >>
  drule_all run_inst_seq_chain_err >> strip_tac >> gvs[]
QED

Theorem compile_safe_mod_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_mod x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if is_signed_type ty then safe_smod a b
              else safe_mod a b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_mod_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all zero_check_passes >> strip_tac >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- ((* Signed: SMOD *)
      `eval_operand x ss' = SOME a` by metis_tac[] >>
      `eval_operand y ss' = SOME b` by metis_tac[] >>
      drule_all emit_op_SMOD_correct >> strip_tac >>
      imp_res_tac emit_op_extends >>
      drule_all run_inst_seq_chain >> strip_tac >> gvs[] >>
      metis_tac[])
  >> (* Unsigned: Mod *)
     `eval_operand x ss' = SOME a` by metis_tac[] >>
     `eval_operand y ss' = SOME b` by metis_tac[] >>
     drule_all emit_op_Mod_correct >> strip_tac >>
     imp_res_tac emit_op_extends >>
     drule_all run_inst_seq_chain >> strip_tac >> gvs[]
QED

(* ===== Safe Division ===== *)

Theorem compile_safe_div_by_zero:
  ∀ x y ty ss st op st' a.
    compile_safe_div x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME 0w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_div_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed"
  >> (* Unsigned: Div *)
     drule_all zero_check_reverts >> strip_tac >>
     imp_res_tac emit_op_extends >>
     `∀s. run_inst_seq (emitted_insts st cs'³') ss ≠ OK s` by gvs[] >>
     drule_all run_inst_seq_chain_err >> strip_tac >> gvs[]
QED

Resume compile_safe_div_by_zero[signed]:
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all zero_check_reverts >> strip_tac >>
  `∀s. run_inst_seq (emitted_insts st cs'³') ss ≠ OK s` by gvs[] >>
  Cases_on `type_bits ty = 256` >> gvs[]
  >- suspend "signed_256"
  >> Cases_on `type_bits ty < 256` >> gvs[]
  >- suspend "signed_lt256"
  >> gvs[comp_return_def] >>
     imp_res_tac emit_op_extends >>
     `∀s. run_inst_seq (emitted_insts st cs'³') ss ≠ OK s` by gvs[] >>
     drule_all run_inst_seq_chain_err >> strip_tac >> gvs[]
QED

Resume compile_safe_div_by_zero[signed_256]:
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts st mid) ss = Abort _ _` >>
  qmatch_goalsub_abbrev_tac `emitted_insts st fin` >>
  `∀s. run_inst_seq (emitted_insts st mid) ss ≠ OK s` by gvs[] >>
  `∃ L. fin.cs_current_insts = mid.cs_current_insts ++ L`
    by (simp[Abbr `fin`] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  mp_tac abort_propagates >> disch_then (qspecl_then [`st`,`mid`,`fin`,`ss`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >> gvs[]
QED

Resume compile_safe_div_by_zero[signed_lt256]:
  gvs[clamp_and_return_def, compile_clamp_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def,
                           comp_ignore_bind_def, LET_THM]) >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts st mid) ss = Abort _ _` >>
  qmatch_goalsub_abbrev_tac `emitted_insts st fin` >>
  `∀s. run_inst_seq (emitted_insts st mid) ss ≠ OK s` by gvs[] >>
  `∃ L. fin.cs_current_insts = mid.cs_current_insts ++ L`
    by (simp[Abbr `fin`] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  mp_tac abort_propagates >> disch_then (qspecl_then [`st`,`mid`,`fin`,`ss`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >> gvs[]
QED

Finalise compile_safe_div_by_zero

Theorem compile_safe_div_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_div x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' =
         SOME (if is_signed_type ty then safe_sdiv a b
               else safe_div a b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_safe_div_def :: monad_unfold) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed"
  >> (* unsigned: zero_check + Div *)
     drule_all zero_check_passes >> strip_tac >>
     chain_last emit_op_Div_correct
QED

(* Bridged version: takes two separate run segments *)
Theorem clamp_and_return_correct_bridged:
  ∀ res ty mid op fin base pre ss0 ss_pre ss_mid v.
    clamp_and_return res ty mid = (op, fin) ∧
    run_inst_seq (emitted_insts base pre) ss0 = OK ss_pre ∧
    run_inst_seq (emitted_insts pre mid) ss_pre = OK ss_mid ∧
    eval_operand res ss_mid = SOME v ∧
    fresh_vars_wrt mid ss_mid ∧
    pre.cs_current_insts = base.cs_current_insts ++ emitted_insts base pre ∧
    mid.cs_current_insts = pre.cs_current_insts ++ emitted_insts pre mid
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts base fin) ss0 = OK ss' ∧
       eval_operand op ss' = SOME v) ∨
      run_inst_seq (emitted_insts base fin) ss0 = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  (* Resolve: run(base→mid) = run(pre→mid) = OK ss_mid *)
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all clamp_and_return_correct >> strip_tac >> gvs[]
QED

Resume compile_safe_div_correct[signed]:
  drule_all zero_check_passes >> strip_tac >>
  gvs monad_unfold >> pairarg_tac >> gvs[] >>
  `eval_operand x ss' = SOME a` by metis_tac[] >>
  `eval_operand y ss' = SOME b` by metis_tac[] >>
  drule_all emit_op_SDIV_correct >> strip_tac >>
  Cases_on `type_bits ty < 256` >> gvs[]
  >- (* <256: clamp *)
     (imp_res_tac emit_op_extends >>
      drule_all clamp_and_return_correct_bridged >> strip_tac >> gvs[])
  >> Cases_on `type_bits ty = 256` >> gvs[]
  >- (* =256: EQ(x, INT_MIN), NOT(y), ISZERO, AND, ISZERO, ASSERT *)
     (gvs monad_unfold >> rpt (pairarg_tac >> gvs[]) >>
      (* Compose zero_check + SDIV into single run from st *)
      qpat_x_assum `emit_op SDIV _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      qpat_x_assum `run_inst_seq _ ss' = OK _` kall_tac >>
      qpat_x_assum `run_inst_seq _ ss = OK ss'` kall_tac >>
      (* EQ step *)
      forward_all_evals >>
      drule_all (elim_lit 2 emit_op_EQ_correct) >> strip_tac >>
      qpat_x_assum `emit_op EQ _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      (* NOT step *)
      forward_all_evals >>
      drule_all emit_op_NOT_correct >> strip_tac >>
      qpat_x_assum `emit_op NOT _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      (* ISZERO step *)
      forward_all_evals >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      qpat_x_assum `emit_op ISZERO [ny] _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      (* AND step *)
      forward_all_evals >>
      drule_all emit_op_AND_correct >> strip_tac >>
      qpat_x_assum `emit_op AND _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      (* ISZERO step *)
      forward_all_evals >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      qpat_x_assum `emit_op ISZERO [bad] _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
      asm_rewrite_tac[] >> strip_tac >>
      (* ASSERT *)
      chain_assert_tac)
  >> (* >256: just return *)
     gvs[comp_return_def] >>
     imp_res_tac emit_op_extends >>
     drule_all run_inst_seq_chain >> strip_tac >>
     qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >>
     forward_all_evals >> gvs[]
QED

Finalise compile_safe_div_correct

(* ===== Safe Addition ===== *)

Theorem compile_safe_add_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (a + b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  (* res = ADD [x; y], so eval_operand res ss' = SOME (a + b) *)
  drule_all emit_op_ADD_correct >> strip_tac >>
  Cases_on `type_bits ty < 256` >> gvs[]
  >- suspend "lt256"
  >> Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed_256"
  >> suspend "unsigned_256"
QED

Resume compile_safe_add_correct[lt256]:
  imp_res_tac emit_op_extends >>
  drule_all clamp_and_return_correct >> strip_tac >> gvs[]
QED

Resume compile_safe_add_correct[signed_256]:
  (* (y < 0) == (res < x): SLT [y; Lit 0w], SLT [res; x], EQ, ASSERT *)
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_SLT_correct >>
  chain_step emit_op_EQ_correct >>
  chain_assert_tac
QED

Resume compile_safe_add_correct[unsigned_256]:
  (* res < x means overflow: LT [res; x], ISZERO, ASSERT *)
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step emit_op_LT_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_assert_tac
QED

Finalise compile_safe_add_correct

(* ===== Word arithmetic bridge lemmas for _in_range proofs ===== *)

(* word negation distributes through i2w *)
Theorem word_i2w_neg:
  -(i2w b : 'a word) = i2w (-b)
Proof
  `i2w (-b) + i2w b = 0w : 'a word` by (
    rewrite_tac[integer_wordTheory.word_i2w_add] >>
    `(-b + b : int) = 0` by intLib.COOPER_TAC >>
    pop_assum (fn th => rewrite_tac[th]) >>
    simp[integer_wordTheory.i2w_def]) >>
  fs[wordsTheory.WORD_SUM_ZERO]
QED

(* i2w distributes over subtraction *)
Theorem word_i2w_sub:
  i2w a - i2w b = i2w (a - b) : 'a word
Proof
  rewrite_tac[wordsTheory.word_sub_def, integerTheory.int_sub] >>
  rewrite_tac[GSYM integer_wordTheory.word_i2w_add, word_i2w_neg]
QED

(* w2i preserves addition when result fits in signed range *)
Theorem w2i_add_no_overflow:
  ∀ (a:'a word) b.
    INT_MIN (:'a) ≤ w2i a + w2i b ∧ w2i a + w2i b ≤ INT_MAX (:'a) ⇒
    w2i (a + b) = w2i a + w2i b
Proof
  rpt gen_tac >> strip_tac >>
  `a + b = i2w (w2i a + w2i b)` by
    metis_tac[integer_wordTheory.i2w_w2i,
              integer_wordTheory.word_i2w_add] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule integer_wordTheory.w2i_i2w >> simp[]
QED

(* w2i preserves subtraction when result fits in signed range *)
Theorem w2i_sub_no_overflow:
  ∀ (a:'a word) b.
    INT_MIN (:'a) ≤ w2i a - w2i b ∧ w2i a - w2i b ≤ INT_MAX (:'a) ⇒
    w2i (a - b) = w2i a - w2i b
Proof
  rpt gen_tac >> strip_tac >>
  `a - b = i2w (w2i a - w2i b)` by
    metis_tac[integer_wordTheory.i2w_w2i, word_i2w_sub] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule integer_wordTheory.w2i_i2w >> simp[]
QED

(* w2i preserves multiplication when result fits in signed range *)
Theorem w2i_mul_no_overflow:
  ∀ (a:'a word) b.
    INT_MIN (:'a) ≤ w2i a * w2i b ∧ w2i a * w2i b ≤ INT_MAX (:'a) ⇒
    w2i (a * b) = w2i a * w2i b
Proof
  rpt gen_tac >> strip_tac >>
  `a * b = i2w (w2i a * w2i b)` by
    metis_tac[integer_wordTheory.i2w_w2i,
              integer_wordTheory.word_i2w_mul] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule integer_wordTheory.w2i_i2w >> simp[]
QED

(* w2n preserves multiplication when result fits in unsigned range *)
Theorem w2n_mul_no_overflow:
  ∀ (a:'a word) b.
    w2n a * w2n b < dimword (:'a) ⇒
    w2n (a * b) = w2n a * w2n b
Proof
  rpt gen_tac >> strip_tac >>
  simp[wordsTheory.word_mul_def, wordsTheory.w2n_n2w]
QED

Theorem w2n_add_overflow:
  !a b : bytes32.
    dimword (:256) <= w2n a + w2n b ==> w2n (a + b) < w2n a
Proof
  rpt strip_tac >>
  `w2n a < dimword (:256) /\ w2n b < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `w2n (a + b) = (w2n a + w2n b) MOD dimword (:256)` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
  `(w2n a + w2n b) MOD dimword (:256) =
   (w2n a + w2n b - dimword (:256)) MOD dimword (:256)` by
    (irule (GSYM arithmeticTheory.SUB_MOD) >> simp[]) >>
  `(w2n a + w2n b - dimword (:256)) MOD dimword (:256) =
   w2n a + w2n b - dimword (:256)` by
    (irule arithmeticTheory.LESS_MOD >> fs[]) >>
  fs[]
QED

(* math_val of word addition equals integer addition when in type range.
   This is the KEY bridge: connects word-level operation to math-level range check.
   Works for ANY type with type_bits ≤ 256. *)
(* Helper: from in_type_range (signed) with type_bits ≤ 256,
   extract INT_MIN/INT_MAX bounds for w2i_{add,sub,mul}_no_overflow.
   The key insight: in_type_range gives bounds in terms of 2^(bits-1),
   and bits ≤ 256 ⇒ 2^(bits-1) ≤ 2^255 = INT_MIN(:256). *)
Theorem in_type_range_signed_256:
  ∀ ty v.
    is_signed_type ty ∧ type_bits ty ≤ 256 ∧
    in_type_range ty v ⇒
    INT_MIN (:256) ≤ v ∧ v ≤ INT_MAX (:256)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[in_type_range_def, LET_THM] >>
  `type_bits ty − 1 ≤ 255` by simp[] >>
  `2 ** (type_bits ty − 1) ≤ 2 ** 255` by simp[bitTheory.TWOEXP_MONO2] >>
  `2 ** 255 = 57896044618658097711785492504343953926634992332820282019728792003956564819968n`
    by EVAL_TAC >>
  conj_tac >> intLib.COOPER_TAC
QED

(* Helper: from in_type_range (unsigned) with type_bits ≤ 256,
   extract bound < dimword(:256). *)
Theorem in_type_range_unsigned_dimword:
  ∀ ty v.
    ¬is_signed_type ty ∧ type_bits ty ≤ 256 ∧
    in_type_range ty (&v) ⇒
    v < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[in_type_range_def, LET_THM] >>
  `2 ** type_bits ty ≤ 2 ** 256` by simp[bitTheory.TWOEXP_MONO2] >>
  `2 ** 256 =
    115792089237316195423570985008687907853269984665640564039457584007913129639936n`
    by EVAL_TAC >>
  `dimword (:256) = 2 ** 256` by EVAL_TAC >>
  intLib.COOPER_TAC
QED

Theorem math_val_add_in_range:
  ∀ ty (a:bytes32) b.
    in_type_range ty (math_val ty a + math_val ty b) ∧
    type_bits ty ≤ 256 ⇒
    math_val ty (a + b) = math_val ty a + math_val ty b
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_signed_type ty` >> gvs[math_val_def]
  >- (irule w2i_add_no_overflow >>
      drule_all in_type_range_signed_256 >> simp[])
  >> (`w2n a + w2n b < dimword (:256)` by (
        irule in_type_range_unsigned_dimword >>
        qexists `ty` >> gvs[integerTheory.INT_ADD]) >>
      simp[wordsTheory.w2n_add_2, integerTheory.INT_ADD])
QED

Theorem math_val_sub_in_range:
  ∀ ty (a:bytes32) b.
    in_type_range ty (math_val ty a - math_val ty b) ∧
    type_bits ty ≤ 256 ⇒
    math_val ty (a - b) = math_val ty a - math_val ty b
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_signed_type ty` >> asm_rewrite_tac[math_val_def]
  >- (irule w2i_sub_no_overflow >>
      `in_type_range ty (w2i a − w2i b)` by fs[math_val_def] >>
      drule_all in_type_range_signed_256 >> simp[])
  >> (`w2n b ≤ w2n a` by (
        fs[in_type_range_def, LET_THM, math_val_def] >>
        intLib.COOPER_TAC) >>
      `b ≤₊ a` by simp[wordsTheory.WORD_LS] >>
      `w2n (a − b) = w2n a − w2n b`
        by metis_tac[wordsTheory.word_sub_w2n] >>
      simp[GSYM integerTheory.INT_SUB])
QED

Theorem math_val_mul_in_range:
  ∀ ty (a:bytes32) b.
    in_type_range ty (math_val ty a * math_val ty b) ∧
    type_bits ty ≤ 256 ⇒
    math_val ty (a * b) = math_val ty a * math_val ty b
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_signed_type ty` >> asm_rewrite_tac[math_val_def]
  >- (irule w2i_mul_no_overflow >>
      `in_type_range ty (w2i a * w2i b)` by fs[math_val_def] >>
      drule_all in_type_range_signed_256 >> simp[])
  >> (`w2n a * w2n b < dimword (:256)` by (
        irule in_type_range_unsigned_dimword >>
        qexists `ty` >>
        fs[math_val_def, integerTheory.INT_OF_NUM_MUL]) >>
      simp[w2n_mul_no_overflow, integerTheory.INT_OF_NUM_MUL])
QED

(* NOTE: Added type_bits ty ≤ 256 — theorem is false without it.
   Counterexample: ty = IntT 512, a = i2w(2^255-1), b = i2w(1).
   in_type_range (IntT 512) (2^255) = T but 256-bit overflow check reverts.
   The overflow check is calibrated for 256-bit words and only correct when
   the type's bit width ≤ 256. All Vyper types satisfy this. *)
Theorem compile_safe_add_in_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty ≤ 256 ∧
    in_type_range ty (math_val ty a + math_val ty b)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (a + b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  Cases_on `type_bits ty < 256` >> gvs[]
  >- suspend "lt256"
  >> Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed_256"
  >> suspend "unsigned_256"
QED

Resume compile_safe_add_in_range[lt256]:
  `type_bits ty ≤ 256` by simp[] >>
  `math_val ty (a + b) = math_val ty a + math_val ty b` by (
    irule math_val_add_in_range >> simp[]) >>
  `in_type_range ty (math_val ty (a + b))` by metis_tac[] >>
  qpat_x_assum `emit_op _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  irule clamp_and_return_ok >>
  qexistsl [`cs'`, `res`, `ss'`, `ty`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume compile_safe_add_in_range[signed_256]:
  fs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_SLT_correct >>
  chain_step emit_op_EQ_correct >>
  forward_all_evals >>
  (* Key arithmetic: w2i(a+b) = w2i a + w2i b *)
  `w2i (a + b) = w2i a + w2i b` by (
    irule w2i_add_no_overflow >>
    `in_type_range ty (w2i a + w2i b)` by fs[math_val_def] >>
    drule_all in_type_range_signed_256 >> simp[]) >>
  (* Overflow check: (w2i b < 0) ⟺ (w2i(a+b) < w2i a) *)
  `(w2i b < 0) = (w2i (a + b) < w2i a)` by intLib.COOPER_TAC >>
  (* Connect word_lt to w2i via WORD_LTi *)
  `bool_to_word (word_lt b 0w) = bool_to_word (word_lt (a + b) a)` by
    simp[integer_wordTheory.WORD_LTi, integer_wordTheory.word_0_w2i] >>
  (* EQ of equal bool_to_words gives 1w ≠ 0w *)
  `bool_to_word (bool_to_word (word_lt b 0w) =
                  bool_to_word (word_lt (a + b) a)) ≠ 0w` by (
    pop_assum (fn th => rewrite_tac[th]) >> simp[]) >>
  (* Close with assert_chain_ok *)
  `same_blocks st cs'³'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss'³' = SOME w`
    by compose_eval_pres >>
  (* ASSERT succeeds (ok ≠ 0w), returns same state *)
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  (* Clear intermediate ci/run facts to avoid drule_all mismatch *)
  qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  qexists `ss'⁵'` >> gvs[]
QED

Resume compile_safe_add_in_range[unsigned_256]:
  fs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step emit_op_LT_correct >>
  chain_step emit_op_ISZERO_correct >>
  forward_all_evals >>
  (* Key: w2n(a+b) = w2n a + w2n b, so ¬(w2n(a+b) < w2n a) *)
  `w2n a + w2n b < dimword (:256)` by (
    `in_type_range ty (&(w2n a + w2n b))` by (
      `math_val ty a + math_val ty b = &(w2n a + w2n b)` by
        simp[math_val_def, integerTheory.INT_ADD] >>
      metis_tac[]) >>
    drule_all in_type_range_unsigned_dimword >> simp[]) >>
  `w2n (a + b) = w2n a + w2n b` by simp[wordsTheory.w2n_add_2] >>
  `¬(w2n (a + b) < w2n a)` by simp[] >>
  `bool_to_word (bool_to_word (w2n (a + b) < w2n a) = 0w) ≠ 0w` by
    simp[] >>
  (* ASSERT ending — same pattern as signed *)
  `same_blocks st cs''` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss'' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  qexists `ss'³'` >>
  `eval_operand op ss'³' = SOME (a + b)` by (
    first_x_assum drule >> simp[]) >>
  gvs[]
QED

Finalise compile_safe_add_in_range

(* An overflowing unsigned 256-bit add reverts: the abort counterpart of
   compile_safe_add_in_range. *)
Theorem compile_safe_add_overflow:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty = 256 ∧ ¬is_signed_type ty ∧
    dimword (:256) ≤ w2n a + w2n b
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (a + b) < w2n a` by (irule w2n_add_overflow >> fs[]) >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step emit_op_LT_correct >>
  chain_step emit_op_ISZERO_correct >>
  forward_all_evals >> imp_res_tac emit_void_extends >>
  drule_all_then strip_assume_tac assert_chain
  >- gvs[bool_to_word_def] >>
  metis_tac[]
QED

(* A signed 256-bit add whose integer sum is out of range has operands of
   one sign and a sum of the other, so the sign check fails. *)
Theorem add_overflow_sign_check:
  ∀(a:'a word) b.
    ¬(INT_MIN (:'a) ≤ w2i a + w2i b ∧ w2i a + w2i b ≤ INT_MAX (:'a)) ⇒
    ((b < 0w) ⇔ ¬(a + b < a))
Proof
  rpt gen_tac >> strip_tac >>
  `w2i (a + b) ≠ w2i a + w2i b` by
    (strip_tac >>
     qspec_then `a + b` mp_tac integer_wordTheory.w2i_ge >>
     qspec_then `a + b` mp_tac integer_wordTheory.w2i_le >>
     intLib.COOPER_TAC) >>
  fs[integer_wordTheory.overflow, wordsTheory.word_msb_neg,
     GSYM integer_wordTheory.w2i_lt_0, integer_wordTheory.WORD_LTi] >>
  intLib.COOPER_TAC
QED

(* An overflowing signed 256-bit add reverts. *)
Theorem compile_safe_add_overflow_signed_256:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty = 256 ∧ is_signed_type ty ∧
    ¬in_type_range ty (w2i a + w2i b)
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  fs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_SLT_correct >>
  chain_step emit_op_EQ_correct >>
  forward_all_evals >>
  `(b < 0w) ⇔ ¬(a + b < a)` by
    (irule add_overflow_sign_check >>
     qpat_x_assum `¬in_type_range _ _` mp_tac >>
     simp[in_type_range_def, LET_THM, wordsTheory.INT_MIN_def,
          wordsTheory.INT_MAX_def, venomMemPropsTheory.dimindex_256] >>
     intLib.ARITH_TAC) >>
  imp_res_tac emit_void_extends >>
  drule_all_then strip_assume_tac assert_chain
  >- (Cases_on `a + b < a` >> gvs[]) >>
  first_assum (irule_at Any)
QED

(* An add below 256 bits whose word sum is out of the type's range fails
   the clamp. *)
Theorem compile_safe_add_out_of_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_add x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty < 256 ∧
    ¬in_type_range ty (math_val ty (a + b))
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  qpat_x_assum `emit_op _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  irule clamp_and_return_out_of_range >> simp[] >>
  qexistsl [`cs'`, `op`, `res`, `ss'`, `ty`, `a + b`] >> simp[]
QED

(* The code of an unsigned 256-bit safe add stays in the current block and
   emits no INVOKE or terminator. *)
Theorem compile_safe_add_unsigned_256_shape:
  ∀ x y ty st op st'.
    compile_safe_add x y ty st = (op, st') ∧
    type_bits ty = 256 ∧ ¬is_signed_type ty ⇒
    st'.cs_blocks = st.cs_blocks ∧ st'.cs_current_bb = st.cs_current_bb ∧
    isPREFIX st.cs_current_insts st'.cs_current_insts ∧
    EVERY (λi. i.inst_opcode ≠ INVOKE ∧ ¬is_terminator i.inst_opcode)
      (emitted_insts st st')
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_add_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op ADD [x; y] st = (op, st1)` >>
  rename1 `emit_op LT [op; x] st1 = (lt, st2)` >>
  rename1 `emit_op ISZERO [lt] st2 = (ok, st3)` >>
  rename1 `emit_void ASSERT [ok] st3 = ((), st4)` >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  `emitted_insts st3 st4 = [mk_inst st3.cs_next_id ASSERT [ok] []]` by
    (qpat_x_assum `emit_void ASSERT _ _ = _` mp_tac >>
     simp[emit_void_assert_inst] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `emitted_insts st st4 =
   emitted_insts st st1 ++ emitted_insts st1 st2 ++ emitted_insts st2 st3 ++
   emitted_insts st3 st4 /\
   st4.cs_current_insts = st.cs_current_insts ++ emitted_insts st st4` by
    (`emitted_insts st2 st4 = emitted_insts st2 st3 ++ emitted_insts st3 st4`
       by (irule emitted_insts_append >> simp[]) >>
     `st4.cs_current_insts = st2.cs_current_insts ++ emitted_insts st2 st4`
       by simp[] >>
     `emitted_insts st1 st4 = emitted_insts st1 st2 ++ emitted_insts st2 st4`
       by (irule emitted_insts_append >> simp[]) >>
     `st4.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st4`
       by simp[] >>
     `emitted_insts st st4 = emitted_insts st st1 ++ emitted_insts st1 st4`
       by (irule emitted_insts_append >> simp[]) >>
     simp[]) >>
  `st4.cs_blocks = st.cs_blocks /\ st4.cs_current_bb = st.cs_current_bb` by
    fs[same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st4)` by
    (imp_res_tac emitted_insts_emit_op >>
     asm_rewrite_tac[] >>
     simp[venomInstTheory.mk_inst_def, is_terminator_def]) >>
  asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND3]
QED

(* ===== Safe Subtraction ===== *)

Theorem compile_safe_sub_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_sub x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (a - b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_sub_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_SUB_correct >> strip_tac >>
  Cases_on `type_bits ty < 256` >> gvs[]
  >- suspend "lt256"
  >> Cases_on `is_signed_type ty` >> gvs[]
  >- suspend "signed_256"
  >> suspend "unsigned_256"
QED

Resume compile_safe_sub_correct[lt256]:
  imp_res_tac emit_op_extends >>
  drule_all clamp_and_return_correct >> strip_tac >> gvs[]
QED

Resume compile_safe_sub_correct[signed_256]:
  (* (y < 0) == (res > x): SLT [y; Lit 0w], SGT [res; x], EQ, ASSERT *)
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_SGT_correct >>
  chain_step emit_op_EQ_correct >>
  chain_assert_tac
QED

Resume compile_safe_sub_correct[unsigned_256]:
  (* res > x means underflow: GT [res; x], ISZERO, ASSERT *)
  gvs[comp_bind_def, comp_return_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  chain_step emit_op_GT_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_assert_tac
QED

Finalise compile_safe_sub_correct

(* The simplifier normalizes a - b to a + -1w * b. This conversion
   restores subtraction form. Use after gvs/simp/fs. *)
val word_sub_normalize = prove(
  ``(a:'a word) + -1w * b = a - b``,
  rewrite_tac[cj 5 wordsTheory.WORD_SUB_INTRO,
              GSYM wordsTheory.word_sub_def]);

val restore_word_sub : tactic =
  RULE_ASSUM_TAC (REWRITE_RULE [word_sub_normalize]) >>
  rewrite_tac [word_sub_normalize];

(* NOTE: Added type_bits ty ≤ 256 — theorem is false without it.
   Same counterexample as compile_safe_add_in_range. *)
Theorem compile_safe_sub_in_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_sub x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty ≤ 256 ∧
    in_type_range ty (math_val ty a - math_val ty b)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (a - b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_sub_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_SUB_correct >> strip_tac >>
  restore_word_sub >>
  Cases_on `type_bits ty < 256`
  >- (fs[] >> suspend "lt256")
  >> `type_bits ty = 256` by fs[] >>
  Cases_on `is_signed_type ty`
  >- (fs[] >> restore_word_sub >> suspend "signed_256")
  >> fs[] >> restore_word_sub >> suspend "unsigned_256"
QED

Resume compile_safe_sub_in_range[lt256]:
  `type_bits ty ≤ 256` by simp[] >>
  `math_val ty (a - b) = math_val ty a - math_val ty b` by (
    irule math_val_sub_in_range >> simp[]) >>
  `in_type_range ty (math_val ty (a - b))` by metis_tac[] >>
  qpat_x_assum `emit_op _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  irule clamp_and_return_ok >>
  qexistsl [`cs'`, `res`, `ss'`, `ty`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  (* in_type_range goal has normalized a + -1w * b; bridge via rewrite *)
  rewrite_tac[word_sub_normalize] >> first_assum ACCEPT_TAC
QED

Resume compile_safe_sub_in_range[signed_256]:
  fs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >> restore_word_sub >>
  chain_step (elim_lit 2 emit_op_SLT_correct) >>
  chain_step emit_op_SGT_correct >>
  chain_step emit_op_EQ_correct >>
  forward_all_evals >>
  (* Key arithmetic: w2i(a-b) = w2i a - w2i b *)
  `in_type_range ty (w2i a - w2i b)` by (
    qpat_x_assum `in_type_range _ _` mp_tac >>
    simp[math_val_def]) >>
  `type_bits ty ≤ 256` by simp[] >>
  `INT_MIN (:256) ≤ w2i a - w2i b ∧
   w2i a - w2i b ≤ INT_MAX (:256)` by (
    drule_all in_type_range_signed_256 >> simp[]) >>
  `w2i (a - b) = w2i a - w2i b` by (
    irule w2i_sub_no_overflow >> simp[]) >>
  (* Overflow check: (w2i b < 0) ⟺ (w2i(a-b) > w2i a) *)
  `(w2i b < 0) = (w2i (a - b) > w2i a)` by intLib.COOPER_TAC >>
  (* Connect word_lt/word_gt to w2i via WORD_LTi/WORD_GTi *)
  `bool_to_word (word_lt b 0w) = bool_to_word (word_gt (a - b) a)` by
    simp[integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi,
         integer_wordTheory.word_0_w2i] >>
  (* EQ of equal bool_to_words gives 1w ≠ 0w *)
  `bool_to_word (bool_to_word (b < 0w) =
                  bool_to_word (a - b > a)) ≠ 0w` by (
    pop_assum (fn th => rewrite_tac[th]) >> simp[]) >>
  (* ASSERT ending *)
  `same_blocks st cs'³'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss'³' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  qexists `ss'⁵'` >> gvs[]
QED

Resume compile_safe_sub_in_range[unsigned_256]:
  fs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >> restore_word_sub >>
  chain_step emit_op_GT_correct >>
  chain_step emit_op_ISZERO_correct >>
  forward_all_evals >>
  (* Key: w2n a ≥ w2n b from in_type_range, so w2n(a-b) = w2n a - w2n b *)
  `w2n b ≤ w2n a` by (
    qpat_x_assum `in_type_range _ _` mp_tac >>
    simp[math_val_def, in_type_range_def] >>
    intLib.COOPER_TAC) >>
  `w2n (a - b) = w2n a - w2n b` by
    simp[wordsTheory.word_sub_w2n, wordsTheory.WORD_LS] >>
  `¬(w2n (a - b) > w2n a)` by simp[] >>
  `bool_to_word (bool_to_word (w2n (a - b) > w2n a) = 0w) ≠ 0w` by
    simp[] >>
  (* ASSERT ending *)
  `same_blocks st cs''` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss = SOME w ⇒ eval_operand op ss'' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  qexists `ss'³'` >>
  `eval_operand op ss'³' = SOME (a - b)` by (
    first_x_assum drule >> simp[]) >>
  gvs[]
QED

Finalise compile_safe_sub_in_range

(* A sub below 256 bits whose word difference is out of the type's range
   fails the clamp. *)
Theorem compile_safe_sub_out_of_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_sub x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty < 256 ∧
    ¬in_type_range ty (math_val ty (a - b))
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_sub_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_SUB_correct >> strip_tac >>
  qpat_x_assum `emit_op _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  irule clamp_and_return_out_of_range >> simp[] >>
  qexistsl [`cs'`, `op`, `res`, `ss'`, `ty`, `a - b`] >> simp[]
QED

(* The sign check of a signed sub fails when the integer difference is out
   of range. *)
Theorem sub_overflow_sign_check:
  ∀(a:'a word) b.
    ¬(INT_MIN (:'a) ≤ w2i a − w2i b ∧ w2i a − w2i b ≤ INT_MAX (:'a)) ⇒
    ((b < 0w) ⇔ ¬(a − b > a))
Proof
  rpt gen_tac >> strip_tac >>
  `w2i (a − b) ≠ w2i a − w2i b` by
    (strip_tac >>
     qspec_then `a − b` mp_tac integer_wordTheory.w2i_ge >>
     qspec_then `a − b` mp_tac integer_wordTheory.w2i_le >>
     intLib.COOPER_TAC) >>
  fs[integer_wordTheory.sub_overflow, wordsTheory.word_msb_neg,
     GSYM integer_wordTheory.w2i_lt_0, integer_wordTheory.WORD_LTi,
     integer_wordTheory.WORD_GTi] >>
  intLib.COOPER_TAC
QED

(* An unsigned sub that borrows wraps above its minuend. *)
Theorem w2n_sub_borrow:
  ∀(a:'a word) b. w2n a < w2n b ⇒ w2n (a − b) > w2n a
Proof
  rpt strip_tac >>
  simp[wordsTheory.word_sub_def, wordsTheory.word_add_def,
       wordsTheory.word_2comp_def, wordsTheory.w2n_n2w] >>
  qspec_then `a` assume_tac wordsTheory.w2n_lt >>
  qspec_then `b` assume_tac wordsTheory.w2n_lt >>
  `w2n a + (dimword (:'a) − w2n b) < dimword (:'a)` by decide_tac >>
  simp[]
QED

(* An overflowing 256-bit sub reverts. *)
Theorem compile_safe_sub_overflow_256:
  ∀ x y ty ss st op st' a b.
    compile_safe_sub x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty = 256 ∧
    ¬in_type_range ty (math_val ty a − math_val ty b)
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_safe_sub_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_SUB_correct >> strip_tac >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- (fs monad_unfold >>
      rpt (pairarg_tac >> gvs[]) >>
      chain_step (elim_lit 2 emit_op_SLT_correct) >>
      chain_step emit_op_SGT_correct >>
      chain_step emit_op_EQ_correct >>
      forward_all_evals >>
      `(b < 0w) ⇔ ¬(a − b > a)` by
        (irule sub_overflow_sign_check >>
         qpat_x_assum `¬in_type_range _ _` mp_tac >>
         simp[in_type_range_def, math_val_def, LET_THM,
              wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
              venomMemPropsTheory.dimindex_256] >>
         intLib.ARITH_TAC) >>
      imp_res_tac emit_void_extends >>
      drule_all_then strip_assume_tac assert_chain
      >- (Cases_on `a − b > a` >> gvs[]) >>
      first_assum (irule_at Any)) >>
  restore_word_sub >> fs monad_unfold >>
  rpt (pairarg_tac >> gvs[]) >> restore_word_sub >>
  chain_step emit_op_GT_correct >>
  chain_step emit_op_ISZERO_correct >>
  forward_all_evals >> restore_word_sub >>
  `w2n (a − b) > w2n a` by
    (irule w2n_sub_borrow >>
     qpat_x_assum `¬in_type_range _ _` mp_tac >>
     simp[in_type_range_def, math_val_def, LET_THM] >>
     qspec_then `a` assume_tac wordsTheory.w2n_lt >>
     fs[wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
  imp_res_tac emit_void_extends >>
  drule_all_then strip_assume_tac assert_chain >>
  TRY (gvs[] >> NO_TAC) >>
  first_assum (irule_at Any)
QED

(* ===== Safe Multiplication ===== *)

(* Helper: overflow check either succeeds or reverts.
   Proves the result from the check's own base state (pre). *)
Theorem mul_overflow_check_ok_or_revert:
  ∀ x y res is_signed bits pre fin ss_pre v a b.
    compile_mul_overflow_check x y res is_signed bits pre = ((), fin) ∧
    eval_operand res ss_pre = SOME v ∧
    eval_operand x ss_pre = SOME a ∧
    eval_operand y ss_pre = SOME b ∧
    fresh_vars_wrt pre ss_pre
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts pre fin) ss_pre = OK ss' ∧
       fresh_vars_wrt fin ss' ∧
       fin.cs_current_insts = pre.cs_current_insts ++ emitted_insts pre fin ∧
       (∀ op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss' = SOME w) ∧
       same_blocks pre fin) ∨
      run_inst_seq (emitted_insts pre fin) ss_pre = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_mul_overflow_check_def :: monad_unfold) >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_signed ∧ bits = 256` >> gvs[]
  >- suspend "special"
  >> suspend "no_special"
QED

Resume mul_overflow_check_ok_or_revert[no_special]:
  (* no special: SDIV/Div, EQ, ISZERO, OR, ASSERT — from pre.
     Use targeted chaining (qpat_x_assum + MATCH_MP emit_op_extends)
     to avoid imp_res_tac O(N²) explosion. *)
  gvs[comp_return_def] >>
  Cases_on `is_signed` >> gvs[]
  >- (* SDIV case *)
     (drule_all emit_op_SDIV_correct >> strip_tac >>
      qpat_x_assum `emit_op SDIV _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      forward_all_evals >>
      drule_all emit_op_EQ_correct >> strip_tac >>
      qpat_x_assum `emit_op EQ _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      qpat_x_assum `emit_op ISZERO _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      drule_all emit_op_OR_correct >> strip_tac >>
      qpat_x_assum `emit_op OR _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      (* ASSERT + 5-conjunct close *)
      forward_all_evals >>
      imp_res_tac emit_void_extends >>
      drule_all_then strip_assume_tac assert_chain >>
      suspend "sdiv_assert")
  >> (* Div case *)
     (drule_all emit_op_Div_correct >> strip_tac >>
      qpat_x_assum `emit_op Div _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      forward_all_evals >>
      drule_all emit_op_EQ_correct >> strip_tac >>
      qpat_x_assum `emit_op EQ _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      drule_all emit_op_ISZERO_correct >> strip_tac >>
      qpat_x_assum `emit_op ISZERO _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      drule_all emit_op_OR_correct >> strip_tac >>
      qpat_x_assum `emit_op OR _ _ = _`
        (strip_assume_tac o MATCH_MP emit_op_extends) >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      imp_res_tac emit_void_extends >>
      drule_all_then strip_assume_tac assert_chain >>
      suspend "div_assert")
QED

Resume mul_overflow_check_ok_or_revert[sdiv_assert]:
  markerLib.RESUME_TAC >> chain_assert_branch
QED

Resume mul_overflow_check_ok_or_revert[div_assert]:
  markerLib.RESUME_TAC >> chain_assert_branch
QED

Resume mul_overflow_check_ok_or_revert[special]:
  (* signed 256: SDIV, EQ, ISZERO, OR, EQ(INT_MIN), NOT, ISZERO, AND, ISZERO, AND, ASSERT *)
  gvs monad_unfold >> rpt (pairarg_tac >> gvs[]) >>
  suspend "special_start"
QED

Resume mul_overflow_check_ok_or_revert[special_start]:
  (* Step 1: SDIV *)
  drule_all emit_op_SDIV_correct >> strip_tac >>
  qpat_x_assum `emit_op SDIV _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  (* Step 2: EQ [div_res; x] *)
  forward_all_evals >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  qpat_x_assum `emit_op EQ [div_res; x] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 3: ISZERO [y] *)
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  qpat_x_assum `emit_op ISZERO [y] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 4: OR [div_ok; y_zero] *)
  forward_all_evals >>
  drule_all emit_op_OR_correct >> strip_tac >>
  qpat_x_assum `emit_op OR _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 5: EQ [x; Lit INT_MIN] *)
  forward_all_evals >>
  drule_all (elim_lit 2 emit_op_EQ_correct) >> strip_tac >>
  qpat_x_assum `emit_op EQ [x; _] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 6: NOT [y] *)
  forward_all_evals >>
  drule_all emit_op_NOT_correct >> strip_tac >>
  qpat_x_assum `emit_op NOT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 7: ISZERO [ny] *)
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  qpat_x_assum `emit_op ISZERO [ny] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 8: AND [x_min; y_neg1] *)
  forward_all_evals >>
  drule_all emit_op_AND_correct >> strip_tac >>
  qpat_x_assum `emit_op AND [x_min; y_neg1] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 9: ISZERO [special] *)
  forward_all_evals >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  qpat_x_assum `emit_op ISZERO [special] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* Step 10: AND [ok; not_special] *)
  forward_all_evals >>
  drule_all emit_op_AND_correct >> strip_tac >>
  qpat_x_assum `emit_op AND [ok; not_special] _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run >>
  (* ASSERT + 5-conjunct close *)
  forward_all_evals >>
  imp_res_tac emit_void_extends >>
  drule_all_then strip_assume_tac assert_chain >>
  suspend "special_assert"
QED

Resume mul_overflow_check_ok_or_revert[special_assert]:
  markerLib.RESUME_TAC >> chain_assert_branch
QED

Finalise mul_overflow_check_ok_or_revert

Theorem compile_safe_mul_correct:
  ∀ x y ty ss st op st' a b.
    compile_safe_mul x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    ¬is_decimal_type ty
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME (a * b)) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_safe_mul_def :: monad_unfold) >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  Cases_on `128 < type_bits ty` >> gvs[]
  >- (* bits > 128: overflow check + clamp or return *)
     (pairarg_tac >> gvs[] >>
      Cases_on `type_bits ty < 256` >> gvs[]
      >- suspend "ovf_clamp"
      >> suspend "ovf_256")
  >> (* bits ≤ 128: just MUL + clamp *)
     (gvs[comp_return_def] >>
      imp_res_tac emit_op_extends >>
      drule_all clamp_and_return_correct >> strip_tac >> gvs[])
QED

Resume compile_safe_mul_correct[ovf_clamp]:
  (* bits in (128,256): overflow check then clamp_and_return *)
  forward_all_evals >>
  imp_res_tac emit_op_extends >>
  imp_res_tac compile_mul_overflow_check_extends >>
  imp_res_tac clamp_and_return_extends >>
  drule_all mul_overflow_check_ok_or_revert >>
  strip_tac
  >- suspend "ok"
  >> suspend "abort"
QED

Resume compile_safe_mul_correct[ok]:
  forward_all_evals >>
  drule_all clamp_and_return_correct_bridged >>
  strip_tac >> gvs[]
QED

Resume compile_safe_mul_correct[abort]:
  (* Chain: run(st→cs') = OK, run(cs'→cs'') = Abort
     ⇒ run(st→cs'') = Abort ⇒ run(st→st') = Abort *)
  qpat_x_assum `run_inst_seq (emitted_insts st _) _ = OK _`
    (fn run_ok =>
      qpat_x_assum `cs'.cs_current_insts = _`
        (fn ci1 =>
          qpat_x_assum `cs''.cs_current_insts = cs'.cs_current_insts ++ _`
            (fn ci2 =>
              strip_assume_tac
                (MATCH_MP run_inst_seq_chain (LIST_CONJ [ci1, ci2, run_ok]))))) >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  mp_tac abort_propagates >>
  disch_then (qspecl_then [`st`,`cs''`,`st'`,`ss`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

Resume compile_safe_mul_correct[ovf_256]:
  (* bits >= 256: overflow check only, comp_return (st' = cs'') *)
  gvs[comp_return_def] >>
  forward_all_evals >>
  imp_res_tac emit_op_extends >>
  imp_res_tac compile_mul_overflow_check_extends >>
  drule_all mul_overflow_check_ok_or_revert >> strip_tac
  >- (* OK: chain runs, propagate eval *)
     (drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
      forward_all_evals >>
      qexists `ss''` >> disj1_tac >> gvs[])
  >> (* Abort: chain run *)
     (drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
      qexists `ss''` >> disj2_tac >> gvs[])
QED

Finalise compile_safe_mul_correct

(* Division roundtrip: unsigned *)
Theorem safe_div_mul_cancel:
  ∀ (a:bytes32) b.
    b ≠ 0w ∧ w2n a * w2n b < dimword (:256) ⇒
    safe_div (a * b) b = a
Proof
  rpt strip_tac >>
  simp[safe_div_def, wordsTheory.word_div_def] >>
  `0 < w2n b` by (Cases_on `b` >> fs[]) >>
  `w2n (a * b) = w2n a * w2n b` by (
    irule w2n_mul_no_overflow >> simp[]) >>
  asm_rewrite_tac[] >>
  simp[arithmeticTheory.MULT_DIV]
QED

(* Division roundtrip: signed *)
Theorem safe_sdiv_mul_cancel:
  ∀ (a:bytes32) b.
    b ≠ 0w ∧
    INT_MIN (:256) ≤ w2i a * w2i b ∧ w2i a * w2i b ≤ INT_MAX (:256) ∧
    ¬(a * b = INT_MINw ∧ b = -1w) ⇒
    safe_sdiv (a * b) b = a
Proof
  rpt strip_tac >>
  simp[safe_sdiv_def] >>
  `w2i (a * b) = w2i a * w2i b` by (
    irule w2i_mul_no_overflow >> simp[]) >>
  simp[integer_wordTheory.word_quot] >>
  `w2i b ≠ 0` by (
    strip_tac >>
    `b = 0w` by metis_tac[integer_wordTheory.w2i_11, integer_wordTheory.word_0_w2i] >>
    fs[]) >>
  `(w2i a * w2i b) quot w2i b = w2i a` by (
    irule integerTheory.INT_QUOT_UNIQUE >>
    qexists `0` >> simp[integerTheory.INT_ABS_NUM] >>
    simp[integerTheory.INT_ABS_EQ0] >>
    intLib.COOPER_TAC) >>
  simp[]
QED

Theorem bool_to_word_and_eq_0w:
  ∀ (P:bool) (Q:bool). ¬(P ∧ Q) ⇒ (bool_to_word P :bytes32) && bool_to_word Q = 0w
Proof
  rpt strip_tac >> Cases_on `P` >> Cases_on `Q` >>
  gvs[bool_to_word_def] >> blastLib.BBLAST_TAC
QED

Theorem word_1comp_eq_0w:
  ∀ (b:bytes32). word_1comp b = 0w ⇒ b = -1w
Proof
  metis_tac[wordsTheory.WORD_NOT_NOT, wordsTheory.WORD_NOT_0, wordsTheory.WORD_NEG_1]
QED

(* Overflow check succeeds when division roundtrip holds.
   Used by compile_safe_mul_in_range to rule out the Abort case. *)
Theorem mul_overflow_check_ok:
  ∀ x y res is_signed bits pre fin ss_pre a b.
    compile_mul_overflow_check x y res is_signed bits pre = ((), fin) ∧
    eval_operand res ss_pre = SOME (a * b) ∧
    eval_operand x ss_pre = SOME a ∧
    eval_operand y ss_pre = SOME b ∧
    fresh_vars_wrt pre ss_pre ∧
    (¬is_signed ⇒ safe_div (a * b) b = a) ∧
    (is_signed ⇒ safe_sdiv (a * b) b = a) ∧
    (is_signed ∧ bits = 256 ⇒ ¬(a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 - 1)))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts pre fin) ss_pre = OK ss' ∧
      fresh_vars_wrt fin ss' ∧
      fin.cs_current_insts = pre.cs_current_insts ++ emitted_insts pre fin ∧
      (∀ op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      same_blocks pre fin
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_mul_overflow_check_def :: monad_unfold) >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_signed ∧ bits = 256` >> gvs[]
  >- suspend "special"
  >> suspend "no_special"
QED

Resume mul_overflow_check_ok[no_special]:
  gvs[comp_return_def] >>
  Cases_on `is_signed` >> gvs[]
  >- suspend "sdiv"
  >> suspend "div"
QED

Resume mul_overflow_check_ok[sdiv]:
  chain_step emit_op_SDIV_correct >>
  chain_step emit_op_EQ_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_OR_correct >>
  forward_all_evals >>
  (* Prove ASSERT value ≠ 0w *)
  `bool_to_word (safe_sdiv (a * b) b = a) = 1w` by simp[] >> fs[] >>
  `bool_to_word (b = 0w) ‖ (1w:bytes32) ≠ 0w` by blastLib.BBLAST_TAC >>
  (* ASSERT ending *)
  `same_blocks pre cs'⁴'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss'⁴' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss_pre = run_inst_seq _ _` collapse_run >>
  first_assum (irule_at Any) >> gvs[] >>
  rpt conj_tac >> TRY (compose_eval_pres) >>
  TRY (metis_tac[same_blocks_trans])
QED

Resume mul_overflow_check_ok[div]:
  chain_step emit_op_Div_correct >>
  chain_step emit_op_EQ_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_OR_correct >>
  forward_all_evals >>
  `bool_to_word (safe_div (a * b) b = a) = 1w` by simp[] >> fs[] >>
  `bool_to_word (b = 0w) ‖ (1w:bytes32) ≠ 0w` by blastLib.BBLAST_TAC >>
  `same_blocks pre cs'⁴'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss'⁴' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss_pre = run_inst_seq _ _` collapse_run >>
  first_assum (irule_at Any) >> gvs[] >>
  rpt conj_tac >> TRY (compose_eval_pres) >>
  TRY (metis_tac[same_blocks_trans])
QED

Resume mul_overflow_check_ok[special]:
  gvs monad_unfold >> rpt (pairarg_tac >> gvs[]) >>
  chain_step emit_op_SDIV_correct >>
  chain_step emit_op_EQ_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_OR_correct >>
  chain_step (elim_lit 2 emit_op_EQ_correct) >>
  chain_step emit_op_NOT_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_AND_correct >>
  chain_step emit_op_ISZERO_correct >>
  (* Remove first AND fact to prevent drule_all misfiring *)
  qpat_x_assum `emit_op AND [x_min; y_neg1] _ = _` kall_tac >>
  chain_step emit_op_AND_correct >>
  forward_all_evals >>
  (* Simplify: safe_sdiv roundtrip → bool_to_word = 1w *)
  `bool_to_word (safe_sdiv (a * b) b = a) = 1w` by simp[] >> fs[] >>
  (* Prove special = 0w from ¬(a = INT_MIN ∧ b = -1w) *)
  `bool_to_word (a = n2w (2 ** 255)) && bool_to_word (word_1comp b = 0w) = 0w` by (
    irule bool_to_word_and_eq_0w >> strip_tac >>
    imp_res_tac word_1comp_eq_0w >>
    `n2w (2 ** 256 - 1) : bytes32 = -1w` by wordsLib.WORD_DECIDE_TAC >>
    gvs[]) >>
  fs[] >>
  (* Now final_ok = 1w && (bool_to_word(b=0w) || 1w) ≠ 0w *)
  `(1w:bytes32) && (bool_to_word (b = 0w) ‖ (1w:bytes32)) ≠ 0w`
    by blastLib.BBLAST_TAC >>
  (* ASSERT ending *)
  `same_blocks pre cs'⁵'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss'⁵' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'¹⁰'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁹'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁸'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁷'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁶'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁴'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁹' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁸' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁷' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁶' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁴' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss_pre = run_inst_seq _ _` collapse_run >>
  first_assum (irule_at Any) >> gvs[] >>
  rpt conj_tac >> TRY (compose_eval_pres) >>
  TRY (metis_tac[same_blocks_trans])
QED

Finalise mul_overflow_check_ok

(* Overflow check always passes when b = 0w (the y_zero OR flag
   ensures final_ok ≠ 0w regardless of the division result). *)
Theorem mul_overflow_check_ok_b_zero:
  ∀ x y res is_signed bits pre fin ss_pre a.
    compile_mul_overflow_check x y res is_signed bits pre = ((), fin) ∧
    eval_operand res ss_pre = SOME (a * 0w) ∧
    eval_operand x ss_pre = SOME a ∧
    eval_operand y ss_pre = SOME 0w ∧
    fresh_vars_wrt pre ss_pre
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts pre fin) ss_pre = OK ss' ∧
      fresh_vars_wrt fin ss' ∧
      fin.cs_current_insts = pre.cs_current_insts ++ emitted_insts pre fin ∧
      (∀ op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss' = SOME w) ∧
      same_blocks pre fin
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_mul_overflow_check_def :: monad_unfold) >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_signed ∧ bits = 256` >> gvs[]
  >- suspend "special"
  >> suspend "no_special"
QED

Resume mul_overflow_check_ok_b_zero[no_special]:
  gvs[comp_return_def] >>
  Cases_on `is_signed` >> gvs[]
  >- (chain_step emit_op_SDIV_correct >>
      chain_step emit_op_EQ_correct >>
      chain_step emit_op_ISZERO_correct >>
      chain_step emit_op_OR_correct >>
      forward_all_evals >>
      (* y_zero = bool_to_word(0w = 0w) = 1w, so ok = div_ok || 1w ≠ 0w *)
      `(bool_to_word (safe_sdiv 0w 0w = a) ‖
        bool_to_word (0w = (0w:bytes32))) ≠ 0w` by (
        simp[bool_to_word_def] >> blastLib.BBLAST_TAC) >>
      `same_blocks pre cs'⁴'` by metis_tac[same_blocks_trans] >>
      `∀op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss'⁴' = SOME w`
        by compose_eval_pres >>
      drule_all emit_void_ASSERT_ok_full >> strip_tac >>
      qpat_x_assum `emit_void ASSERT _ _ = _`
        (strip_assume_tac o MATCH_MP emit_void_extends) >>
      qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
      qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
      qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ ss_pre = run_inst_seq _ _` collapse_run >>
      first_assum (irule_at Any) >> gvs[] >>
      rpt conj_tac >> TRY (compose_eval_pres) >>
      TRY (metis_tac[same_blocks_trans]))
  >> (chain_step emit_op_Div_correct >>
      chain_step emit_op_EQ_correct >>
      chain_step emit_op_ISZERO_correct >>
      chain_step emit_op_OR_correct >>
      forward_all_evals >>
      `(bool_to_word (safe_div 0w 0w = a) ‖
        bool_to_word (0w = (0w:bytes32))) ≠ 0w` by (
        simp[bool_to_word_def] >> blastLib.BBLAST_TAC) >>
      `same_blocks pre cs'⁴'` by metis_tac[same_blocks_trans] >>
      `∀op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss'⁴' = SOME w`
        by compose_eval_pres >>
      drule_all emit_void_ASSERT_ok_full >> strip_tac >>
      qpat_x_assum `emit_void ASSERT _ _ = _`
        (strip_assume_tac o MATCH_MP emit_void_extends) >>
      qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
      qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
      qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
      drule_all run_inst_seq_chain >> strip_tac >>
      qpat_x_assum `run_inst_seq _ ss_pre = run_inst_seq _ _` collapse_run >>
      first_assum (irule_at Any) >> gvs[] >>
      rpt conj_tac >> TRY (compose_eval_pres) >>
      TRY (metis_tac[same_blocks_trans]))
QED

Resume mul_overflow_check_ok_b_zero[special]:
  gvs monad_unfold >> rpt (pairarg_tac >> gvs[]) >>
  chain_step emit_op_SDIV_correct >>
  chain_step emit_op_EQ_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_OR_correct >>
  chain_step (elim_lit 2 emit_op_EQ_correct) >>
  chain_step emit_op_NOT_correct >>
  chain_step emit_op_ISZERO_correct >>
  chain_step emit_op_AND_correct >>
  chain_step emit_op_ISZERO_correct >>
  qpat_x_assum `emit_op AND [x_min; y_neg1] _ = _` kall_tac >>
  chain_step emit_op_AND_correct >>
  forward_all_evals >>
  (* Simplify: word_1comp 0w ≠ 0w, so special AND = 0w, not_special = 1w *)
  `word_1comp (0w:bytes32) ≠ 0w` by blastLib.BBLAST_TAC >>
  `bool_to_word (word_1comp (0w:bytes32) = 0w) = 0w` by simp[] >>
  fs[] >>
  (* After fs[], final_ok = 1w && (div_ok || 1w). Order matters for drule_all. *)
  `(1w:bytes32) && (bool_to_word (a = safe_sdiv 0w 0w) ‖ (1w:bytes32)) ≠ 0w`
    by blastLib.BBLAST_TAC >>
  `same_blocks pre cs'⁵'` by metis_tac[same_blocks_trans] >>
  `∀op w. eval_operand op ss_pre = SOME w ⇒ eval_operand op ss'⁵' = SOME w`
    by compose_eval_pres >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _`
    (strip_assume_tac o MATCH_MP emit_void_extends) >>
  qpat_x_assum `cs'¹⁰'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁹'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁸'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁷'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁶'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'⁴'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'³'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs''.cs_current_insts = _` kall_tac >>
  qpat_x_assum `cs'.cs_current_insts = _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁹' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁸' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁷' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁶' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'⁴' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'³' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs'' _) _ = OK _` kall_tac >>
  qpat_x_assum `run_inst_seq (emitted_insts cs' _) _ = OK _` kall_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss_pre = run_inst_seq _ _` collapse_run >>
  first_assum (irule_at Any) >> gvs[] >>
  rpt conj_tac >> TRY (compose_eval_pres) >>
  TRY (metis_tac[same_blocks_trans])
QED

Finalise mul_overflow_check_ok_b_zero

(* NOTE: Added type_bits ty ≤ 256 — theorem is false without it.
   Same counterexample as compile_safe_add_in_range. *)
Theorem compile_safe_mul_in_range:
  ∀ x y ty ss st op st' a b.
    compile_safe_mul x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    ¬is_decimal_type ty ∧
    type_bits ty ≤ 256 ∧
    in_type_range ty (math_val ty a * math_val ty b)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (a * b)
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_safe_mul_def :: monad_unfold) >>
  pairarg_tac >> gvs[] >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  Cases_on `128 < type_bits ty` >> gvs[]
  >- (* bits > 128: overflow check + clamp or return *)
     (pairarg_tac >> gvs[] >>
      Cases_on `type_bits ty < 256` >> gvs[]
      >- suspend "ovf_clamp"
      >> suspend "ovf_256")
  >> (* bits ≤ 128: just MUL + clamp *)
     suspend "le128"
QED

(* ===== Decimal Division ===== *)

Theorem compile_safe_decimal_div_correct:
  ∀ x y divisor ty ss st op st' a b.
    compile_safe_decimal_div x y divisor ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss' w.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME w) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_safe_decimal_div_def :: monad_unfold) >>
  rpt (pairarg_tac >> gvs[]) >>
  (* Step 1: MUL — second arg is Lit *)
  `eval_operand (Lit (n2w divisor)) ss = SOME (n2w divisor)`
    by simp[eval_operand_lit] >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  qpat_x_assum `emit_op MUL _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  forward_all_evals >>
  (* Step 2: zero check — passes since b ≠ 0w *)
  drule_all zero_check_passes >> strip_tac >>
  (* Compose MUL + zero_check runs *)
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  forward_all_evals >>
  (* Step 3: SDIV *)
  drule_all emit_op_SDIV_correct >> strip_tac >>
  qpat_x_assum `emit_op SDIV _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  forward_all_evals >>
  (* Step 4: clamp_and_return — OK ∨ Abort *)
  drule_all clamp_and_return_correct >> strip_tac >> gvs[]
QED

Resume compile_safe_mul_in_range[le128]:
  gvs[comp_return_def] >>
  `math_val ty (a * b) = math_val ty a * math_val ty b` by (
    irule math_val_mul_in_range >> simp[]) >>
  `in_type_range ty (math_val ty (a * b))` by metis_tac[] >>
  qpat_x_assum `emit_op _ _ _ = _`
    (strip_assume_tac o MATCH_MP emit_op_extends) >>
  irule clamp_and_return_ok >>
  qexistsl [`cs'`, `res`, `ss'`, `ty`] >>
  simp[]
QED


(* The INT_MIN edge case: if in_type_range for signed multiplication,
   then we can't have a*b = INT_MIN ∧ b = -1w.
   This is because INT_MIN * -1 = -INT_MIN = INT_MAX + 1 which overflows. *)
Theorem int_min_edge_from_in_type_range:
  ∀ (a:bytes32) b ty.
    is_signed_type ty ∧ type_bits ty ≤ 256 ∧
    in_type_range ty (w2i a * w2i b) ∧
    a * b = n2w (2 ** 255) ∧ b = n2w (2 ** 256 - 1)
    ⇒ F
Proof
  rpt strip_tac >>
  drule_all in_type_range_signed_256 >> strip_tac >>
  (* Use w2i_mul_no_overflow to connect word equation to integers *)
  `w2i (a * b) = w2i a * w2i b` by (
    irule w2i_mul_no_overflow >> simp[]) >>
  (* Evaluate w2i on concrete values before gvs *)
  `n2w (2 ** 256 - 1) :bytes32 = -1w` by EVAL_TAC >>
  `n2w (2 ** 255) :bytes32 = INT_MINw` by EVAL_TAC >>
  gvs[] >>
  (* Now: w2i(INT_MINw) = w2i a * w2i(-1w) = -w2i a *)
  `w2i (INT_MINw :bytes32) = INT_MIN (:256)` by EVAL_TAC >>
  `w2i (-1w:bytes32) = -1` by EVAL_TAC >>
  `INT_MIN (:256) = -&(2 ** 255)` by EVAL_TAC >>
  `INT_MAX (:256) = &(2 ** 255) - 1` by EVAL_TAC >>
  `w2i a ≤ INT_MAX (:256)` by simp[integer_wordTheory.w2i_le] >>
  fs[] >> intLib.COOPER_TAC
QED

(* chain_conclude: After drule_all mul_overflow_check_ok (or _b_zero),
   chain the two runs and solve the 5 conclusion conjuncts. *)
val chain_conclude : tactic =
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ ss = run_inst_seq _ _` collapse_run >>
  first_assum (irule_at Any) >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- metis_tac[same_blocks_trans]
  >- solve_ci
  >> compose_eval_pres;

(* Helper: from in_type_range, MUL + overflow check succeeds.
   Chains MUL execution with overflow check, producing combined run. *)
Theorem mul_plus_overflow_check_ok:
  ∀ x y res ty st cs' cs'' ss ss' a b.
    emit_op MUL [x; y] st = (res, cs') ∧
    compile_mul_overflow_check x y res (is_signed_type ty) (type_bits ty) cs' = ((), cs'') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    type_bits ty ≤ 256 ∧
    in_type_range ty (math_val ty a * math_val ty b) ∧
    run_inst_seq (emitted_insts st cs') ss = OK ss' ∧
    eval_operand res ss' = SOME (a * b) ∧
    fresh_vars_wrt cs' ss' ∧
    same_blocks st cs' ∧
    cs'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs' ∧
    (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
    ⇒
    ∃ ss_fin.
      run_inst_seq (emitted_insts st cs'') ss = OK ss_fin ∧
      eval_operand res ss_fin = SOME (a * b) ∧
      fresh_vars_wrt cs'' ss_fin ∧
      same_blocks st cs'' ∧
      cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss_fin = SOME w)
Proof
  rpt gen_tac >> strip_tac >>
  forward_all_evals >>
  Cases_on `b = 0w`
  >- suspend "b_zero"
  >> Cases_on `is_signed_type ty`
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume mul_plus_overflow_check_ok[b_zero]:
  pop_assum (fn beq =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [beq]) >>
    assume_tac beq) >>
  drule_all mul_overflow_check_ok_b_zero >> strip_tac >>
  chain_conclude
QED

Resume mul_plus_overflow_check_ok[signed]:
  qpat_x_assum `in_type_range _ _` mp_tac >> simp[math_val_def] >>
  strip_tac >>
  drule_all in_type_range_signed_256 >> strip_tac >>
  `¬(a * b = INT_MINw ∧ b = -1w)` by (
    strip_tac >> irule int_min_edge_from_in_type_range >>
    qexistsl [`a`, `b`, `ty`] >>
    simp[EVAL ``INT_MINw :bytes32``, EVAL ``-1w :bytes32``,
         EVAL ``n2w (2**255) :bytes32``, EVAL ``n2w (2**256 - 1) :bytes32``]) >>
  `is_signed_type ty ⇒ safe_sdiv (a * b) b = a` by (
    strip_tac >> match_mp_tac safe_sdiv_mul_cancel >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `¬is_signed_type ty ⇒ safe_div (a * b) b = a` by simp[] >>
  `is_signed_type ty ∧ type_bits ty = 256 ⇒
   ¬(a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 - 1))` by (
    rpt strip_tac >> gvs[] >>
    qpat_x_assum `_ ≤ INT_MAX _` mp_tac >>
    EVAL_TAC) >>
  drule_all mul_overflow_check_ok >> strip_tac >>
  chain_conclude
QED

Resume mul_plus_overflow_check_ok[unsigned]:
  qpat_x_assum `in_type_range _ _` mp_tac >>
  simp[math_val_def, integerTheory.INT_OF_NUM_MUL] >> strip_tac >>
  `w2n a * w2n b < dimword (:256)` by (
    irule in_type_range_unsigned_dimword >> qexists `ty` >> simp[]) >>
  `¬is_signed_type ty ⇒ safe_div (a * b) b = a` by (
    strip_tac >> irule safe_div_mul_cancel >> simp[]) >>
  `is_signed_type ty ⇒ safe_sdiv (a * b) b = a` by simp[] >>
  `is_signed_type ty ∧ type_bits ty = 256 ⇒
   ¬(a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 - 1))` by simp[] >>
  drule_all mul_overflow_check_ok >> strip_tac >>
  chain_conclude
QED

Finalise mul_plus_overflow_check_ok

Resume compile_safe_mul_in_range[ovf_clamp]:
  qpat_x_assum `emit_op MUL _ _ = _`
    (fn th => strip_assume_tac (MATCH_MP emit_op_extends th) >>
              assume_tac th) >>
  `type_bits ty ≤ 256` by simp[] >>
  drule_all mul_plus_overflow_check_ok >> strip_tac >>
  `math_val ty (a * b) = math_val ty a * math_val ty b` by (
    irule math_val_mul_in_range >> simp[]) >>
  `in_type_range ty (math_val ty (a * b))` by metis_tac[] >>
  drule_all clamp_and_return_ok >> simp[]
QED

Resume compile_safe_mul_in_range[ovf_256]:
  gvs[comp_return_def] >>
  qpat_x_assum `emit_op MUL _ _ = _`
    (fn th => strip_assume_tac (MATCH_MP emit_op_extends th) >>
              assume_tac th) >>
  `type_bits ty ≤ 256` by simp[] >>
  drule_all mul_plus_overflow_check_ok >> strip_tac >>
  qexists `ss_fin` >> simp[]
QED

Finalise compile_safe_mul_in_range

(* ===== Multiplication overflow ===== *)

val int_min_256 = EVAL ``INT_MIN (:256)``;
val int_max_256 = EVAL ``INT_MAX (:256)``;
val w2i_int_min_w_256 =
  EVAL ``w2i (0x8000000000000000000000000000000000000000000000000000000000000000w : bytes32)``;
val w2i_neg1_256 = EVAL ``w2i (-1w : bytes32)``;

fun ostep th pat =
  forward_all_evals >>
  drule_all th >> strip_tac >>
  qpat_x_assum pat (strip_assume_tac o MATCH_MP emit_op_extends) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` collapse_run;

fun fstep th pat =
  drule_all th >> strip_tac >>
  qpat_x_assum pat (strip_assume_tac o MATCH_MP emit_op_extends);

val mul_check_close =
  forward_all_evals >>
  imp_res_tac emit_void_extends >>
  drule_all_then strip_assume_tac assert_chain >>
  TRY (gvs[] >> NO_TAC) >>
  first_assum (irule_at Any);

fun mul_check_plain_tac opth pat = gvs[comp_return_def] >>
  fstep opth pat >>
  ostep emit_op_EQ_correct `emit_op EQ _ _ = _` >>
  ostep emit_op_ISZERO_correct `emit_op ISZERO _ _ = _` >>
  ostep emit_op_OR_correct `emit_op OR _ _ = _` >>
  mul_check_close;

(* mul_overflow_check_reverts: the abort counterpart of
   mul_overflow_check_ok.  The division check fails, or the int256
   INT_MIN * -1 check does. *)
Theorem mul_overflow_check_reverts:
  ∀ x y res is_signed bits pre fin ss_pre a b.
    compile_mul_overflow_check x y res is_signed bits pre = ((), fin) ∧
    eval_operand res ss_pre = SOME (a * b) ∧
    eval_operand x ss_pre = SOME a ∧
    eval_operand y ss_pre = SOME b ∧
    fresh_vars_wrt pre ss_pre ∧ b ≠ 0w ∧
    ((if is_signed then safe_sdiv (a * b) b else safe_div (a * b) b) ≠ a ∨
     (is_signed ∧ bits = 256 ∧ a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 - 1)))
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts pre fin) ss_pre = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
  gvs (compile_mul_overflow_check_def :: monad_unfold) >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_signed ∧ bits = 256` >> gvs[]
  (* the int256 goals, whose code has the INT_MIN * -1 check *)
  >>~- ([`emit_op NOT _`],
      fs monad_unfold >> rpt (pairarg_tac >> gvs[]) >>
      fstep emit_op_SDIV_correct `emit_op SDIV _ _ = _` >>
      ostep emit_op_EQ_correct `emit_op EQ [div_res; x] _ = _` >>
      ostep emit_op_ISZERO_correct `emit_op ISZERO [y] _ = _` >>
      ostep emit_op_OR_correct `emit_op OR _ _ = _` >>
      ostep (elim_lit 2 emit_op_EQ_correct) `emit_op EQ [x; _] _ = _` >>
      ostep emit_op_NOT_correct `emit_op NOT _ _ = _` >>
      ostep emit_op_ISZERO_correct `emit_op ISZERO [ny] _ = _` >>
      ostep emit_op_AND_correct `emit_op AND [x_min; y_neg1] _ = _` >>
      ostep emit_op_ISZERO_correct `emit_op ISZERO [special] _ = _` >>
      ostep emit_op_AND_correct `emit_op AND [ok; not_special] _ = _` >>
      forward_all_evals >>
      imp_res_tac emit_void_extends >>
      drule_all_then strip_assume_tac assert_chain >>
      TRY (gvs[] >> NO_TAC) >>
      first_assum (irule_at Any)) >>
  Cases_on `is_signed` >> gvs[]
  >- mul_check_plain_tac emit_op_SDIV_correct `emit_op SDIV _ _ = _` >>
  mul_check_plain_tac emit_op_Div_correct `emit_op Div _ _ = _`
QED

(* An unsigned product that overflows the word fails the division check. *)
Theorem safe_div_mul_overflow:
  ∀(a:bytes32) b.
    b ≠ 0w ∧ dimword (:256) ≤ w2n a * w2n b ⇒ safe_div (a * b) b ≠ a
Proof
  rpt gen_tac >> strip_tac >>
    simp[safe_div_def, wordsTheory.word_div_def] >>
    `0 < w2n b` by (`w2n b <> 0` by fs[wordsTheory.w2n_eq_0] >> decide_tac) >>
    qabbrev_tac `p = w2n (a * b)` >>
    `p < dimword (:256)` by simp[Abbr `p`, wordsTheory.w2n_lt] >>
    `p DIV w2n b < dimword (:256)` by
      (irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists_tac `p` >>
       simp[arithmeticTheory.DIV_LESS_EQ]) >>
    strip_tac >>
    `w2n (n2w (p DIV w2n b) : bytes32) = w2n a` by asm_rewrite_tac[] >>
    `(p DIV w2n b) MOD dimword (:256) = p DIV w2n b` by
      simp[arithmeticTheory.LESS_MOD] >>
    `p DIV w2n b = w2n a` by metis_tac[wordsTheory.w2n_n2w] >>
    `w2n a * w2n b <= p` by
      (qspecl_then [`w2n a`, `p`, `w2n b`] mp_tac
         arithmeticTheory.X_LE_DIV >> simp[]) >>
    decide_tac
QED

Theorem abs_le_abs_mul:
  ∀(x:int) y. y ≠ 0 ⇒ ABS x ≤ ABS (x * y)
Proof
  rpt strip_tac >>
    Cases_on `x = 0` >- simp[] >>
    rewrite_tac[GSYM integerTheory.INT_ABS_MUL] >>
    `1 ≤ ABS y ∧ 0 < ABS x` by
      (fs[integerTheory.INT_ABS] >> rw[] >> intLib.ARITH_TAC) >>
    qspecl_then [`ABS x`, `1`, `ABS y`] mp_tac integerTheory.INT_LE_MONO >>
    simp[]
QED

(* A signed product out of the 256-bit range fails the division check,
   but for INT_MIN * -1, which the int256 check catches. *)
Theorem safe_sdiv_mul_overflow:
  ∀(a:bytes32) b.
    b ≠ 0w ∧
    ¬(INT_MIN (:256) ≤ w2i a * w2i b ∧ w2i a * w2i b ≤ INT_MAX (:256)) ∧
    ¬(a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 - 1)) ⇒
    safe_sdiv (a * b) b ≠ a
Proof
  rpt gen_tac >> strip_tac >>
    simp[safe_sdiv_def, integer_wordTheory.word_quot] >> strip_tac >>
    `w2i b ≠ 0` by
      (strip_tac >>
       `b = 0w` by metis_tac[integer_wordTheory.w2i_11, integer_wordTheory.word_0_w2i] >>
       fs[]) >>
    `i2w (w2i (a * b)) = a * b` by simp[integer_wordTheory.i2w_w2i] >>
    `a * b = i2w (w2i a * w2i b)` by
      simp[GSYM integer_wordTheory.word_i2w_mul, integer_wordTheory.i2w_w2i] >>
    `INT_MIN (:256) ≤ w2i a ∧ w2i a ≤ INT_MAX (:256) ∧
     INT_MIN (:256) ≤ w2i b ∧ w2i b ≤ INT_MAX (:256) ∧
     INT_MIN (:256) ≤ w2i (a * b) ∧ w2i (a * b) ≤ INT_MAX (:256)` by
      simp[integer_wordTheory.w2i_ge, integer_wordTheory.w2i_le] >>
    qabbrev_tac `A = w2i a` >> qabbrev_tac `B = w2i b` >>
    qabbrev_tac `P = w2i (a * b)` >>
    qabbrev_tac `qq = P quot B` >> qabbrev_tac `rr = P rem B` >>
    `P = qq * B + rr ∧ ABS rr < ABS B` by
      (qspec_then `B` mp_tac integerTheory.INT_REMQUOT >>
       simp[Abbr `qq`, Abbr `rr`]) >>
    `ABS (qq * B) ≤ ABS P` by
      (simp[Abbr `qq`] >> irule integerTheory.INT_ABS_QUOT >> simp[]) >>
    `ABS qq ≤ ABS (qq * B)` by (irule abs_le_abs_mul >> simp[]) >>
    fs[int_min_256, int_max_256] >>
    (`ABS qq ≤ 57896044618658097711785492504343953926634992332820282019728792003956564819968` by
      (irule integerTheory.INT_LE_TRANS >> qexists_tac `ABS (qq * B)` >> simp[] >>
       irule integerTheory.INT_LE_TRANS >> qexists_tac `ABS (qq * B + rr)` >> simp[] >>
       simp[integerTheory.INT_ABS] >> rw[] >> intLib.ARITH_TAC) >>
    Cases_on `qq ≤ 57896044618658097711785492504343953926634992332820282019728792003956564819967`
    >- ((* the quotient is in range: it is A, so the remainder is 0 *)
        `w2i (i2w qq : bytes32) = qq` by
          (irule integer_wordTheory.w2i_i2w >> simp[int_min_256, int_max_256] >>
           fs[integerTheory.INT_ABS] >> rw[] >> fs[] >> intLib.ARITH_TAC) >>
        `A = qq` by (fs[markerTheory.Abbrev_def] >> metis_tac[]) >>
        `i2w rr = (0w : bytes32)` by
          (qpat_x_assum `i2w (qq * B + rr) = _` mp_tac >>
           simp[GSYM integer_wordTheory.word_i2w_add]) >>
        `rr = 0` by
          (`w2i (i2w rr : bytes32) = rr` by
             (irule integer_wordTheory.w2i_i2w >> simp[int_min_256, int_max_256] >>
              fs[integerTheory.INT_ABS] >> rw[] >> fs[] >> intLib.ARITH_TAC) >>
           qpat_x_assum `w2i _ = rr` (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
           qpat_x_assum `i2w rr = _`
             (fn th => REWRITE_TAC [th, integer_wordTheory.word_0_w2i])) >>
        gvs[] >> intLib.ARITH_TAC) >>
    (* the quotient is 2 ** 255: then B = -1 and a = INT_MIN *)
    `qq = 57896044618658097711785492504343953926634992332820282019728792003956564819968` by
      (fs[integerTheory.INT_ABS] >> Cases_on `qq < 0` >> fs[] >> intLib.ARITH_TAC) >>
    `B = 1 ∨ B = -1` by
      (qpat_x_assum `ABS (qq * B) ≤ ABS P` mp_tac >>
       qpat_x_assum `P = _` (fn th => rewrite_tac[th]) >>
       fs[integerTheory.INT_ABS] >> rw[] >> intLib.ARITH_TAC)
    >- (gvs[integerTheory.INT_ABS] >> rw[] >> fs[] >> intLib.ARITH_TAC) >>
    `b = i2w (-1)` by
      (qpat_x_assum `Abbrev (B = _)` mp_tac >> rw[markerTheory.Abbrev_def] >>
       metis_tac[integer_wordTheory.i2w_w2i]) >>
    qpat_x_assum `i2w qq = a` (assume_tac o SYM) >> gvs[] >>
    qpat_x_assum `_ ⇒ i2w _ ≠ _` mp_tac >> EVAL_TAC)
QED

(* Values of a type of at most 128 bits multiply without wrapping. *)
Theorem math_val_mul_narrow:
  ∀ty (a:bytes32) b.
    type_bits ty ≤ 128 ∧
    in_type_range ty (math_val ty a) ∧ in_type_range ty (math_val ty b) ⇒
    math_val ty (a * b) = math_val ty a * math_val ty b
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_signed_type ty` >>
    fs[math_val_def, in_type_range_def, LET_THM]
    >- (irule w2i_mul_no_overflow >>
        qabbrev_tac `X = 2 ** (type_bits ty − 1)` >>
        `0 < X ∧ X ≤ 2 ** 127` by simp[Abbr `X`] >>
        `&(X − 1) = &X − 1 : int` by simp[integerTheory.INT_SUB] >>
        `ABS (w2i a) ≤ &(2 ** 127) ∧ ABS (w2i b) ≤ &(2 ** 127)` by
          (fs[integerTheory.INT_ABS_LE] >> intLib.ARITH_TAC) >>
        `∃m n. ABS (w2i a) = &m ∧ ABS (w2i b) = &n` by
          metis_tac[integerTheory.NUM_POSINT_EXISTS, integerTheory.INT_ABS_POS] >>
        `m ≤ 2 ** 127 ∧ n ≤ 2 ** 127` by
          (rpt (qpat_x_assum `ABS _ ≤ _` mp_tac) >>
           asm_rewrite_tac[integerTheory.INT_LE] >> rpt strip_tac >>
           asm_rewrite_tac[]) >>
        `m * n ≤ 2 ** 127 * 2 ** 127` by
          (irule arithmeticTheory.LESS_MONO_MULT2 >> asm_rewrite_tac[]) >>
        `ABS (w2i a * w2i b) ≤ &(2 ** 254)` by
          (rewrite_tac[GSYM integerTheory.INT_ABS_MUL] >>
           asm_rewrite_tac[integerTheory.INT_MUL, integerTheory.INT_LE] >> fs[]) >>
        fs[integerTheory.INT_ABS_LE, wordsTheory.INT_MIN_def,
           wordsTheory.INT_MAX_def, venomMemPropsTheory.dimindex_256] >>
        intLib.ARITH_TAC) >>
    irule w2n_mul_no_overflow >>
    `2 ** type_bits ty ≤ 2 ** 128` by simp[] >>
    `w2n a ≤ 2 ** 128 − 1 ∧ w2n b ≤ 2 ** 128 − 1` by decide_tac >>
    `w2n a * w2n b ≤ (2 ** 128 − 1) * (2 ** 128 − 1)` by
      (irule arithmeticTheory.LESS_MONO_MULT2 >> asm_rewrite_tac[]) >>
    fs[wordsTheory.dimword_def]
QED

(* An abort before the final clamp, or the return, of compile_safe_mul is
   an abort of the whole. *)
Theorem clamp_or_return_after_abort:
  ∀st cs'' st' ss r ty res op c.
    run_inst_seq (emitted_insts st cs'') ss = Abort Revert_abort r ∧
    cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'' ∧
    (if c then clamp_and_return res ty else comp_return res) cs'' = (op, st') ⇒
    ∃ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
    `∃L. st'.cs_current_insts = cs''.cs_current_insts ++ L` by
      (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
       rw[comp_return_def]
       >- (imp_res_tac clamp_and_return_extends >>
           qexists_tac `emitted_insts cs'' st'` >> asm_rewrite_tac[]) >>
       qexists_tac `[]` >> simp[]) >>
    qspecl_then [`st`, `cs''`, `st'`, `ss`] mp_tac abort_propagates >>
    impl_tac >- (simp[] >> metis_tac[]) >>
    simp[]
QED

val mul_sdiv_mismatch_tac =
  strip_tac >>
  reverse (Cases_on `a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 − 1)`)
  >- (`safe_sdiv (a * b) b ≠ a` suffices_by simp[] >>
      irule safe_sdiv_mul_overflow >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- (simp[int_min_256, int_max_256] >> fs[]) >>
      first_assum ACCEPT_TAC) >>
  `type_bits ty = 256` suffices_by simp[] >>
  CCONTR_TAC >> `type_bits ty < 256` by decide_tac >>
  `2 ** (type_bits ty − 1) < 2 ** 255` by simp[] >>
  qpat_x_assum `in_type_range ty (math_val ty a)` mp_tac >>
  qpat_x_assum `a = _ ∧ _` (fn th => rewrite_tac [CONJUNCT1 th]) >>
  simp[math_val_def, in_type_range_def, w2i_int_min_w_256] >> intLib.ARITH_TAC;

(* An integer multiplication whose product is out of the type's range
   reverts: by the clamp up to 128 bits, by the division check when the
   product overflows the word, by the clamp otherwise. *)
Theorem compile_safe_mul_overflow:
  ∀ x y ty ss st op st' a b.
    compile_safe_mul x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧
    ¬is_decimal_type ty ∧ 0 < type_bits ty ∧ type_bits ty ≤ 256 ∧
    in_type_range ty (math_val ty a) ∧ in_type_range ty (math_val ty b) ∧
    ¬in_type_range ty (math_val ty a * math_val ty b)
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
    gvs (compile_safe_mul_def :: monad_unfold) >>
    pairarg_tac >> gvs[] >>
    drule_all emit_op_MUL_correct >> strip_tac >>
    Cases_on `128 < type_bits ty` >> gvs[]
    >- (pairarg_tac >> gvs[] >>
        qpat_x_assum `emit_op MUL _ _ = _`
          (strip_assume_tac o MATCH_MP emit_op_extends) >>
        imp_res_tac compile_mul_overflow_check_extends >>
        forward_all_evals >>
        `b ≠ 0w` by
          (strip_tac >>
           gvs[math_val_def, in_type_range_def, LET_THM,
               integer_wordTheory.word_0_w2i] >> rw[] >> fs[]) >>
        `run_inst_seq (emitted_insts st cs'') ss =
           run_inst_seq (emitted_insts cs' cs'') ss' ∧
         cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs''` by
          (irule run_inst_seq_chain >> asm_rewrite_tac[]) >>
        Cases_on `if is_signed_type ty then
                    INT_MIN (:256) ≤ w2i a * w2i b ∧ w2i a * w2i b ≤ INT_MAX (:256)
                  else w2n a * w2n b < dimword (:256)`
        >- ((* the product fits in a word: the check passes, the clamp fails *)
            `type_bits ty < 256` by
              (CCONTR_TAC >> `type_bits ty = 256` by decide_tac >>
               Cases_on `is_signed_type ty` >>
               fs[in_type_range_def, math_val_def, LET_THM,
                  wordsTheory.INT_MIN_def, wordsTheory.INT_MAX_def,
                  venomMemPropsTheory.dimindex_256, wordsTheory.dimword_def] >>
               intLib.ARITH_TAC) >>
            `math_val ty (a * b) = math_val ty a * math_val ty b` by
              (Cases_on `is_signed_type ty` >> fs[math_val_def]
               >- (irule w2i_mul_no_overflow >> fs[]) >>
               simp[integerTheory.INT_MUL] >> irule w2n_mul_no_overflow >> fs[]) >>
            `¬is_signed_type ty ⇒ safe_div (a * b) b = a` by
              (rw[] >> irule safe_div_mul_cancel >>
               qpat_x_assum `if _ then _ else _` mp_tac >> simp[]) >>
            `is_signed_type ty ⇒ safe_sdiv (a * b) b = a` by
              (rw[] >> irule safe_sdiv_mul_cancel >>
               qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
               `w2i (a * b) = w2i a * w2i b` by
                 (irule w2i_mul_no_overflow >> simp[int_min_256, int_max_256]) >>
               simp[int_min_256, int_max_256] >> rpt strip_tac >> gvs[w2i_int_min_w_256, w2i_neg1_256] >>
               qspec_then `a` assume_tac integer_wordTheory.w2i_le >>
               fs[int_max_256] >> intLib.ARITH_TAC) >>
            `is_signed_type ty ∧ type_bits ty = 256 ⇒
             ¬(a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 − 1))` by simp[] >>
            drule_all mul_overflow_check_ok >> strip_tac >>
            `run_inst_seq (emitted_insts st cs'') ss = OK ss''` by
              (qpat_x_assum `run_inst_seq (emitted_insts st cs'') ss = _`
                 SUBST1_TAC >> first_assum ACCEPT_TAC) >>
            `eval_operand res ss'' = SOME (a * b)` by
              (first_x_assum irule >> first_assum ACCEPT_TAC) >>
            qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >> simp[] >>
            strip_tac >>
            irule clamp_and_return_out_of_range >>
            qexistsl [`cs''`, `op`, `res`, `ss''`, `ty`, `a * b`] >> simp[]) >>
        (* the product overflows a word: the check fails *)
        `(if is_signed_type ty then safe_sdiv (a * b) b else safe_div (a * b) b)
           ≠ a ∨
         (is_signed_type ty ∧ type_bits ty = 256 ∧ a = n2w (2 ** 255) ∧
          b = n2w (2 ** 256 − 1))` by
          (Cases_on `is_signed_type ty` >> fs[] >- mul_sdiv_mismatch_tac >- mul_sdiv_mismatch_tac >>
           irule safe_div_mul_overflow >> fs[]) >>
        qspecl_then [`x`, `y`, `res`, `is_signed_type ty`, `type_bits ty`, `cs'`,
                     `cs''`, `ss'`, `a`, `b`] mp_tac mul_overflow_check_reverts >>
        (impl_tac >- simp[]) >> strip_tac >>
        `∃r. run_inst_seq (emitted_insts st cs'') ss = Abort Revert_abort r` by
          fs[] >>
        irule clamp_or_return_after_abort >> asm_rewrite_tac[] >>
        metis_tac[]) >>
    gvs[comp_return_def] >>
    `math_val ty (a * b) = math_val ty a * math_val ty b` by
      (irule math_val_mul_narrow >> simp[]) >>
    qpat_x_assum `emit_op _ _ _ = _`
      (strip_assume_tac o MATCH_MP emit_op_extends) >>
    irule clamp_and_return_out_of_range >> simp[] >>
    qexistsl [`cs'`, `op`, `res`, `ss'`, `ty`, `a * b`] >> simp[]
QED

(* ===== Division ===== *)

val w2i_not0_256 = EVAL ``w2i (¬0w : bytes32)``;

(* The signed quotient of a value of the type by a non-zero value is of the
   type, but for the type's minimum by -1. *)
Theorem sdiv_in_type_range:
  ∀ty (A:int) B.
    is_signed_type ty ∧ in_type_range ty A ∧ B ≠ 0 ∧
    ¬(A = -&(2 ** (type_bits ty − 1)) ∧ B = -1) ⇒
    in_type_range ty (A quot B)
Proof
  rpt gen_tac >> strip_tac >>
    fs[in_type_range_def, LET_THM] >>
    qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
    qabbrev_tac `X = 2 ** (type_bits ty − 1)` >>
    `0 < X` by simp[Abbr `X`] >>
    `&(X − 1) = &X − 1 : int` by simp[integerTheory.INT_SUB] >>
    qabbrev_tac `q = A quot B` >>
    `ABS (q * B) ≤ ABS A` by
      (simp[Abbr `q`] >> irule integerTheory.INT_ABS_QUOT >> simp[]) >>
    `ABS q ≤ ABS (q * B)` by (irule abs_le_abs_mul >> simp[]) >>
    `ABS A ≤ &X` by (simp[integerTheory.INT_ABS_LE] >> intLib.ARITH_TAC) >>
    `ABS q ≤ &X` by
      (irule integerTheory.INT_LE_TRANS >> qexists_tac `ABS (q * B)` >> simp[] >>
       irule integerTheory.INT_LE_TRANS >> qexists_tac `ABS A` >> simp[]) >>
    reverse (Cases_on `q = &X`)
    >- (fs[integerTheory.INT_ABS_LE] >> intLib.ARITH_TAC) >>
    `ABS (q * B) ≤ &X` by
      (irule integerTheory.INT_LE_TRANS >> qexists_tac `ABS A` >> simp[]) >>
    `ABS B ≤ 1` by
      (qpat_x_assum `ABS (q * B) ≤ &X` mp_tac >>
       rewrite_tac[GSYM integerTheory.INT_ABS_MUL] >> asm_rewrite_tac[] >>
       simp[integerTheory.INT_ABS_NUM] >> strip_tac >>
       `&X * ABS B ≤ &X * 1` by simp[] >>
       qspecl_then [`&X`, `ABS B`, `1`] mp_tac integerTheory.INT_LE_MONO >>
       simp[]) >>
    `B = 1 ∨ B = -1` by
      (qpat_x_assum `ABS B ≤ 1` mp_tac >> qpat_x_assum `B ≠ 0` mp_tac >>
       simp[integerTheory.INT_ABS] >> rw[] >> intLib.ARITH_TAC)
    >- (qpat_x_assum `Abbrev (q = _)` mp_tac >>
        simp[markerTheory.Abbrev_def, integerTheory.INT_QUOT_1] >>
        intLib.ARITH_TAC) >>
    qpat_x_assum `Abbrev (q = _)` mp_tac >>
    simp[markerTheory.Abbrev_def, integerTheory.INT_QUOT_NEG,
         integerTheory.INT_QUOT_1] >>
    strip_tac >> `A = -&X` by intLib.ARITH_TAC >> fs[]
QED

val div256_tac =
  fs monad_unfold >> rpt (pairarg_tac >> fs[]) >>
    ostep (elim_lit 2 emit_op_EQ_correct) `emit_op EQ _ _ = _` >>
    ostep emit_op_NOT_correct `emit_op NOT _ _ = _` >>
    ostep emit_op_ISZERO_correct `emit_op ISZERO [ny] _ = _` >>
    ostep emit_op_AND_correct `emit_op AND _ _ = _` >>
    ostep emit_op_ISZERO_correct `emit_op ISZERO [bad] _ = _` >>
    forward_all_evals >>
    `¬(a = 0x8000000000000000000000000000000000000000000000000000000000000000w ∧ ¬b = 0w)` by
      (strip_tac >>
       qpat_x_assum `¬b = 0w` (assume_tac o AP_TERM ``word_1comp : bytes32 -> bytes32``) >>
       fs[wordsTheory.WORD_NOT_NOT] >>
       gvs[w2i_int_min_w_256, w2i_not0_256, w2i_neg1_256]) >>
    `bool_to_word (bool_to_word (a = 0x8000000000000000000000000000000000000000000000000000000000000000w) && bool_to_word (¬b = 0w) = 0w) ≠ 0w` by
      (Cases_on `a = 0x8000000000000000000000000000000000000000000000000000000000000000w` >> fs[]) >>
    imp_res_tac emit_void_extends >>
    rpt (qpat_x_assum `emitted_insts _ _ = _ ++ _` kall_tac) >>
    rename1 `emit_void ASSERT [ok] s_ok = _` >>
    rename1 `eval_operand ok m_ok = SOME _` >>
    qspecl_then [`ok`, `s_ok`, `st'`,
       `bool_to_word (bool_to_word (a = 0x8000000000000000000000000000000000000000000000000000000000000000w) && bool_to_word (¬b = 0w) = 0w)`,
       `m_ok`, `st`, `ss`] mp_tac assert_chain_ok >>
    impl_tac
    >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY compose_eval_pres >> TRY solve_same_blocks >> fs[]) >>
    strip_tac >> qpat_x_assum `res = op` (SUBST_ALL_TAC o SYM) >>
    first_assum (irule_at Any) >> fs[];

val sdiv_ok_tac =
  drule_all zero_check_passes >> strip_tac >>
    rename1 `run_inst_seq (emitted_insts st _) ss = OK m1` >>
    gvs monad_unfold >> pairarg_tac >> gvs[] >>
    rename1 `emit_op SDIV _ _ = (res, s_div)` >>
    `eval_operand x m1 = SOME a ∧ eval_operand y m1 = SOME b` by metis_tac[] >>
    drule_all emit_op_SDIV_correct >> strip_tac >>
    rename1 `eval_operand res m2 = SOME (safe_sdiv a b)` >>
    qpat_x_assum `emit_op SDIV _ _ = _`
      (strip_assume_tac o MATCH_MP emit_op_extends) >>
    drule_all run_inst_seq_chain >> strip_tac >>
    qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
    asm_rewrite_tac[] >> strip_tac >>
    `w2i b ≠ 0` by fs[integer_wordTheory.w2i_eq_0] >>
    `w2i (safe_sdiv a b) = w2i a quot w2i b` by
      (simp[safe_sdiv_def, integer_wordTheory.word_quot] >>
       irule integer_wordTheory.w2i_i2w >>
       qspecl_then [`ty`, `w2i a quot w2i b`] mp_tac in_type_range_signed_256 >>
       impl_tac >- (simp[] >> irule sdiv_in_type_range >> simp[]) >> simp[]) >>
    Cases_on `type_bits ty = 256` >> fs[]
    >- div256_tac >>
    `type_bits ty < 256` by decide_tac >> fs[] >>
    `in_type_range ty (math_val ty (safe_sdiv a b))` by
       (simp[math_val_def] >> irule sdiv_in_type_range >> simp[]) >>
    qspecl_then [`res`, `ty`, `s_div`, `op`, `st'`, `st`, `ss`, `m2`,
                 `safe_sdiv a b`] mp_tac clamp_and_return_ok >>
    simp[];

(* compile_safe_div_ok: a division by a non-zero word, but for the signed
   minimum by -1, runs through and gives the word quotient.  The success
   counterpart of compile_safe_div_by_zero and compile_safe_div_overflow. *)
Theorem compile_safe_div_ok:
  ∀ x y ty ss st op st' a b.
    compile_safe_div x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧ b ≠ 0w ∧ type_bits ty ≤ 256 ∧
    (is_signed_type ty ⇒
       in_type_range ty (w2i a) ∧
       ¬(w2i a = -&(2 ** (type_bits ty − 1)) ∧ w2i b = -1))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if is_signed_type ty then safe_sdiv a b else safe_div a b)
Proof
  rpt gen_tac >> strip_tac >>
    gvs (compile_safe_div_def :: monad_unfold) >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    Cases_on `is_signed_type ty` >> gvs[]
    >- sdiv_ok_tac >>
    drule_all zero_check_passes >> strip_tac >>
    chain_last emit_op_Div_correct
QED

(* The signed minimum divided by -1 reverts: by the int256 check, or by the
   clamp of a narrower type. *)
Theorem compile_safe_div_overflow:
  ∀ x y ty ss st op st' a b.
    compile_safe_div x y ty st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    fresh_vars_wrt st ss ∧ is_signed_type ty ∧ 0 < type_bits ty ∧
    type_bits ty ≤ 256 ∧
    w2i a = -&(2 ** (type_bits ty − 1)) ∧ w2i b = -1
    ⇒
    ∃ ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt gen_tac >> strip_tac >>
    `b ≠ 0w` by (strip_tac >> fs[integer_wordTheory.word_0_w2i]) >>
    gvs (compile_safe_div_def :: monad_unfold) >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    drule_all zero_check_passes >> strip_tac >>
    rename1 `run_inst_seq (emitted_insts st _) ss = OK m1` >>
    gvs monad_unfold >> pairarg_tac >> gvs[] >>
    rename1 `emit_op SDIV _ _ = (res, s_div)` >>
    `eval_operand x m1 = SOME a ∧ eval_operand y m1 = SOME b` by metis_tac[] >>
    drule_all emit_op_SDIV_correct >> strip_tac >>
    rename1 `eval_operand res m2 = SOME (safe_sdiv a b)` >>
    qpat_x_assum `emit_op SDIV _ _ = _`
      (strip_assume_tac o MATCH_MP emit_op_extends) >>
    drule_all run_inst_seq_chain >> strip_tac >>
    qpat_x_assum `run_inst_seq _ _ = run_inst_seq _ _` mp_tac >>
    asm_rewrite_tac[] >> strip_tac >>
    `b = -1w` by
      (`b = i2w (w2i b)` by simp[integer_wordTheory.i2w_w2i] >>
       pop_assum SUBST1_TAC >> asm_rewrite_tac[] >> EVAL_TAC) >>
    Cases_on `type_bits ty = 256` >> fs[]
  >- (`a = 0x8000000000000000000000000000000000000000000000000000000000000000w` by
      (`a = i2w (w2i a)` by simp[integer_wordTheory.i2w_w2i] >>
       pop_assum SUBST1_TAC >> asm_rewrite_tac[] >> EVAL_TAC) >>
    fs monad_unfold >> rpt (pairarg_tac >> fs[]) >>
    ostep (elim_lit 2 emit_op_EQ_correct) `emit_op EQ _ _ = _` >>
    ostep emit_op_NOT_correct `emit_op NOT _ _ = _` >>
    ostep emit_op_ISZERO_correct `emit_op ISZERO [ny] _ = _` >>
    ostep emit_op_AND_correct `emit_op AND _ _ = _` >>
    ostep emit_op_ISZERO_correct `emit_op ISZERO [bad] _ = _` >>
    forward_all_evals >>
    imp_res_tac emit_void_extends >>
    drule_all_then strip_assume_tac assert_chain >>
    TRY (gvs[] >> NO_TAC) >>
    first_assum (irule_at Any)) >>
  `type_bits ty < 256` by decide_tac >>
  qabbrev_tac `X = 2 ** (type_bits ty − 1)` >>
  `0 < X ∧ X ≤ 2 ** 254` by simp[Abbr `X`] >>
  `w2i (safe_sdiv a b) = &X` by (simp[safe_sdiv_def, integer_wordTheory.word_quot, integerTheory.INT_QUOT_NEG, integerTheory.INT_QUOT_1] >> irule integer_wordTheory.w2i_i2w_pos >> simp[wordsTheory.INT_MAX_def, wordsTheory.INT_MIN_def, venomMemPropsTheory.dimindex_256] >> irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `2 ** 254` >> simp[]) >>
  `¬in_type_range ty (math_val ty (safe_sdiv a b))` by
      (simp[math_val_def, in_type_range_def] >> intLib.ARITH_TAC) >>
  qspecl_then [`res`, `ty`, `s_div`, `op`, `st'`, `st`, `ss`, `m2`,
                 `safe_sdiv a b`] mp_tac clamp_and_return_out_of_range >>
    simp[]
QED

(* ===== Decimal multiplication and division ===== *)

(* A product that overflows 256 bits quotients outside the decimal range. *)
Theorem decimal_quot_overflow:
  !p:int. ~(-&(2 ** 255) <= p /\ p <= &(2 ** 255) - 1) ==>
    ~in_type_range (BaseT DecimalT) (p quot 10000000000)
Proof
  gen_tac >> STRUCT_CASES_TAC (Q.SPEC `p` integerTheory.INT_NUM_CASES) >>
    TRY (`-&n quot 10000000000 = -(&n quot 10000000000) : int` by
           simp[integerTheory.INT_QUOT_NEG]) >>
    simp[in_type_range_def, type_bits_def, is_signed_type_def,
         integerTheory.INT_QUOT] >> strip_tac >>
    qspecl_then [`10000000000`, `2 ** 255`, `n`] mp_tac
      arithmeticTheory.DIV_LE_MONOTONE >> simp[]
QED

Theorem decimal_quot_in_256:
  !p:int. -&(2 ** 255) <= p /\ p <= &(2 ** 255) - 1 ==>
    -&(2 ** 255) <= p quot 10000000000 /\
    p quot 10000000000 <= &(2 ** 255) - 1
Proof
  gen_tac >> STRUCT_CASES_TAC (Q.SPEC `p` integerTheory.INT_NUM_CASES) >>
    TRY (`-&n quot 10000000000 = -(&n quot 10000000000) : int` by
           simp[integerTheory.INT_QUOT_NEG]) >>
    simp[integerTheory.INT_QUOT] >> strip_tac >>
    `n DIV 10000000000 <= n` by simp[arithmeticTheory.DIV_LESS_EQ] >>
    intLib.ARITH_TAC
QED

(* Decimal *: MUL with the 256-bit overflow check, SDIV by 10^10 truncating
   toward zero, then the 168-bit clamp. *)
Theorem compile_safe_decimal_mul_run:
  !x y ss st op st' d1 d2.
    compile_safe_mul x y (BaseT DecimalT) st = (op, st') /\
    eval_operand x ss = SOME (i2w d1) /\ eval_operand y ss = SOME (i2w d2) /\
    fresh_vars_wrt st ss /\
    in_type_range (BaseT DecimalT) d1 /\ in_type_range (BaseT DecimalT) d2 ==>
    (in_type_range (BaseT DecimalT) (d1 * d2 quot 10000000000) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
           eval_operand op ss' = SOME (i2w (d1 * d2 quot 10000000000))) /\
    (~in_type_range (BaseT DecimalT) (d1 * d2 quot 10000000000) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
    gvs (compile_safe_mul_def :: monad_unfold) >>
    pairarg_tac >> gvs[] >>
    drule_all emit_op_MUL_correct >> strip_tac >>
    gvs[type_bits_def, is_decimal_type_def, is_signed_type_def,
        decimal_divisor_def] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    qpat_x_assum `emit_op MUL _ _ = _`
      (strip_assume_tac o MATCH_MP emit_op_extends) >>
    qpat_x_assum `emit_op SDIV _ _ = _`
      (fn th => strip_assume_tac (MATCH_MP emit_op_extends th) >>
                assume_tac th) >>
    imp_res_tac compile_mul_overflow_check_extends >>
    imp_res_tac clamp_and_return_extends >>
    forward_all_evals >>
    `INT_MIN (:256) <= d1 /\ d1 <= INT_MAX (:256) /\
     INT_MIN (:256) <= d2 /\ d2 <= INT_MAX (:256)` by
      (qspecl_then [`BaseT DecimalT`, `d1`] mp_tac in_type_range_signed_256 >>
       qspecl_then [`BaseT DecimalT`, `d2`] mp_tac in_type_range_signed_256 >>
       simp[type_bits_def, is_signed_type_def]) >>
    `w2i (i2w d1 : bytes32) = d1 /\ w2i (i2w d2 : bytes32) = d2` by
      simp[integer_wordTheory.w2i_i2w] >>
    `(i2w d1 * i2w d2 : bytes32) = i2w (d1 * d2)` by
      metis_tac[integer_wordTheory.word_mul_i2w] >>
    `run_inst_seq (emitted_insts st cs'') ss =
       run_inst_seq (emitted_insts cs' cs'') ss' /\
     cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs''` by
      (irule run_inst_seq_chain >> asm_rewrite_tac[]) >>
    `(i2w d2 = (0w : bytes32)) <=> d2 = 0` by
      (eq_tac >> strip_tac >> simp[integer_wordTheory.i2w_0] >>
       qpat_x_assum `w2i (i2w d2) = d2` (SUBST1_TAC o SYM) >>
       asm_simp_tac std_ss [integer_wordTheory.word_0_w2i]) >>
    fs[int_min_256, int_max_256] >>
    Cases_on `-&(2 ** 255) <= d1 * d2 /\ d1 * d2 <= &(2 ** 255) - 1`
    >- ((* the product fits in a word: the check passes *)
        `?ss2. run_inst_seq (emitted_insts st cs'') ss = OK ss2 /\
               eval_operand res ss2 = SOME (i2w (d1 * d2)) /\
               fresh_vars_wrt cs'' ss2` by
          (Cases_on `d2 = 0`
           >- (gvs[integer_wordTheory.i2w_0] >>
               qspecl_then [`x`, `y`, `res`, `T`, `168`, `cs'`, `cs''`, `ss'`,
                            `i2w d1`] mp_tac mul_overflow_check_ok_b_zero >>
               simp[] >> strip_tac >> qexists_tac `ss''` >> simp[]) >>
           `~((i2w d1 * i2w d2 : bytes32) = INT_MINw /\
              (i2w d2 : bytes32) = -1w)` by
             (strip_tac >>
              `d2 = -1` by
                (qpat_x_assum `w2i (i2w d2) = d2` mp_tac >>
                 simp[w2i_neg1_256]) >>
              `w2i (i2w (d1 * d2) : bytes32) = w2i (INT_MINw : bytes32)` by
                metis_tac[] >>
              `w2i (i2w (d1 * d2) : bytes32) = d1 * d2` by
                (irule integer_wordTheory.w2i_i2w >>
                 fs[int_min_256, int_max_256]) >>
              `w2i (INT_MINw : bytes32) = INT_MIN (:256)` by
                simp[integer_wordTheory.w2i_INT_MINw] >>
              `d1 * d2 = INT_MIN (:256)` by metis_tac[] >>
              qpat_x_assum `in_type_range (BaseT DecimalT) d1` mp_tac >>
              qpat_x_assum `d1 * d2 = _` mp_tac >>
              qpat_x_assum `d2 = -1` SUBST1_TAC >>
              simp[in_type_range_def, type_bits_def, is_signed_type_def,
                   int_min_256] >>
              intLib.ARITH_TAC) >>
           `safe_sdiv (i2w d1 * i2w d2) (i2w d2) = i2w d1 : bytes32` by
             (irule safe_sdiv_mul_cancel >> fs[int_min_256, int_max_256]) >>
           qspecl_then [`x`, `y`, `res`, `T`, `168`, `cs'`, `cs''`, `ss'`,
                        `i2w d1`, `i2w d2`] mp_tac mul_overflow_check_ok >>
           simp[] >> strip_tac >> qexists_tac `ss''` >> simp[]) >>
        qspecl_then [`res`, `Lit 0x2540BE400w`, `i2w (d1 * d2)`,
                     `0x2540BE400w`, `cs''`, `res1`, `cs'''`, `ss2`]
          mp_tac emit_op_SDIV_correct >>
        simp[eval_operand_def] >> strip_tac >>
        `safe_sdiv (i2w (d1 * d2)) 0x2540BE400w =
           i2w (d1 * d2 quot 10000000000) : bytes32` by
          (`w2i (i2w (d1 * d2) : bytes32) = d1 * d2` by
             (irule integer_wordTheory.w2i_i2w >> fs[int_min_256, int_max_256]) >>
           `w2i (0x2540BE400w : bytes32) = 10000000000` by EVAL_TAC >>
           simp[safe_sdiv_def, integer_wordTheory.word_quot]) >>
        `run_inst_seq (emitted_insts st cs''') ss =
           run_inst_seq (emitted_insts cs'' cs''') ss2 /\
         cs'''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'''` by
          (irule run_inst_seq_chain >> asm_rewrite_tac[]) >>
        `math_val (BaseT DecimalT) (i2w (d1 * d2 quot 10000000000) : bytes32) =
           d1 * d2 quot 10000000000` by
          (simp[math_val_def, is_signed_type_def] >>
           irule integer_wordTheory.w2i_i2w >>
           qspec_then `d1 * d2` mp_tac decimal_quot_in_256 >>
           simp[int_min_256, int_max_256]) >>
        conj_tac >> strip_tac
        >- (irule clamp_and_return_ok >>
            qexistsl [`cs'''`, `res1`, `ss''`, `BaseT DecimalT`] >>
            gvs[type_bits_def]) >>
        irule clamp_and_return_out_of_range >>
        qexistsl [`cs'''`, `op`, `res1`, `ss''`, `BaseT DecimalT`,
                  `i2w (d1 * d2 quot 10000000000)`] >> gvs[type_bits_def]) >>
    (* the product overflows a word: the check reverts *)
    `~in_type_range (BaseT DecimalT) (d1 * d2 quot 10000000000)` by
      (irule decimal_quot_overflow >> asm_rewrite_tac[]) >>
    simp[] >>
    `d2 <> 0` by (strip_tac >> fs[]) >>
    `safe_sdiv (i2w d1 * i2w d2) (i2w d2) <> i2w d1 : bytes32` by
      (irule safe_sdiv_mul_overflow >> rpt conj_tac
       >- (strip_tac >> qpat_x_assum `w2i (i2w d1) = d1` mp_tac >>
           qpat_x_assum `i2w d1 = _` SUBST1_TAC >>
           `w2i (n2w (2 ** 255) : bytes32) = INT_MIN (:256)` by EVAL_TAC >>
           simp[int_min_256] >> strip_tac >>
           fs[in_type_range_def, type_bits_def, is_signed_type_def] >>
           intLib.ARITH_TAC) >>
       fs[int_min_256, int_max_256]) >>
    qspecl_then [`x`, `y`, `res`, `T`, `168`, `cs'`, `cs''`, `ss'`,
                 `i2w d1`, `i2w d2`] mp_tac mul_overflow_check_reverts >>
    (impl_tac >- (rpt conj_tac >> simp[] >> metis_tac[])) >> strip_tac >>
    qspecl_then [`st`, `cs''`, `st'`, `ss`] mp_tac abort_propagates >>
    (impl_tac
     >- (rpt conj_tac >- first_assum ACCEPT_TAC
         >- (qexists_tac `emitted_insts cs'' cs''' ++ emitted_insts cs''' st'` >>
             simp[]) >>
         gvs[])) >>
    gvs[]
QED

(* Decimal /: MUL by 10^10, the zero-divisor ASSERT, SDIV, then the clamp. *)
Theorem compile_safe_decimal_div_run:
  !x y ss st op st' a b.
    compile_safe_decimal_div x y 10000000000 (BaseT DecimalT) st = (op, st') /\
    eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
    fresh_vars_wrt st ss ==>
    (b = 0w ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss') /\
    (b <> 0w /\
     in_type_range (BaseT DecimalT) (w2i (safe_sdiv (a * n2w 10000000000) b)) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
           eval_operand op ss' = SOME (safe_sdiv (a * n2w 10000000000) b)) /\
    (b <> 0w /\
     ~in_type_range (BaseT DecimalT) (w2i (safe_sdiv (a * n2w 10000000000) b)) ==>
     ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  rpt gen_tac >> strip_tac >>
    gvs (compile_safe_decimal_div_def :: monad_unfold) >>
    rpt (pairarg_tac >> gvs[]) >>
    rename1 `emit_op MUL _ st = (x_scaled, s1)` >>
    rename1 `emit_op ISZERO [y] s1 = (y_zero, s2)` >>
    rename1 `emit_op ISZERO [y_zero] s2 = (y_nonzero, s3)` >>
    rename1 `emit_void ASSERT [y_nonzero] s3 = (_, s4)` >>
    rename1 `emit_op SDIV _ s4 = (res, s5)` >>
    `eval_operand (Lit (n2w 10000000000)) ss = SOME (n2w 10000000000)`
      by simp[eval_operand_lit] >>
    drule_all emit_op_MUL_correct >> strip_tac >>
    rename1 `run_inst_seq (emitted_insts st s1) ss = OK m1` >>
    qpat_x_assum `emit_op MUL _ _ = _`
      (strip_assume_tac o MATCH_MP emit_op_extends) >>
    forward_all_evals >>
    `0x2540BE400w * a = a * 0x2540BE400w : bytes32` by
      MATCH_ACCEPT_TAC wordsTheory.WORD_MULT_COMM >>
    pop_assum SUBST1_TAC >>
    qpat_x_assum `emit_op SDIV _ _ = _`
      (fn th => strip_assume_tac (MATCH_MP emit_op_extends th) >>
                assume_tac th) >>
    imp_res_tac clamp_and_return_extends >>
    Cases_on `b = 0w` >> asm_simp_tac std_ss []
    >- ((* zero divisor: the ASSERT reverts *)
        qspecl_then [`y`, `s1`, `y_zero`, `s2`, `y_nonzero`, `s3`,
                     `s4`, `m1`] mp_tac zero_check_reverts >>
        simp[] >> strip_tac >>
        rename1 `Abort Revert_abort m2` >>
        `run_inst_seq (emitted_insts st s4) ss = Abort Revert_abort m2` by
          (qspecl_then [`st`, `s1`, `s4`, `ss`, `m1`] mp_tac
             run_inst_seq_chain >> simp[]) >>
        qspecl_then [`st`, `s4`, `st'`, `ss`] mp_tac abort_propagates >>
        (impl_tac
         >- (rpt conj_tac
             >- (qspecl_then [`st`, `s1`, `s4`, `ss`, `m1`] mp_tac
                   run_inst_seq_chain >> simp[])
             >- (qexists_tac `emitted_insts s4 s5 ++
                              emitted_insts s5 st'` >> simp[]) >>
             gvs[])) >>
        gvs[]) >>
    (* nonzero divisor: SDIV, then the 168-bit clamp *)
    qspecl_then [`y`, `s1`, `y_zero`, `s2`, `y_nonzero`, `s3`,
                 `s4`, `m1`, `b`] mp_tac zero_check_passes >>
    simp[] >> strip_tac >>
    rename1 `run_inst_seq (emitted_insts s1 s4) m1 = OK m2` >>
    `run_inst_seq (emitted_insts st s4) ss = OK m2 /\
     s4.cs_current_insts = st.cs_current_insts ++ emitted_insts st s4` by
      (qspecl_then [`st`, `s1`, `s4`, `ss`, `m1`] mp_tac
         run_inst_seq_chain >> simp[]) >>
    `eval_operand x_scaled m2 = SOME (a * 0x2540BE400w) /\
     eval_operand y m2 = SOME b` by simp[] >>
    qspecl_then [`x_scaled`, `y`, `a * 0x2540BE400w`, `b`, `s4`, `res`,
                 `s5`, `m2`] mp_tac emit_op_SDIV_correct >>
    simp[] >> strip_tac >>
    rename1 `run_inst_seq (emitted_insts s4 s5) m2 = OK m3` >>
    `run_inst_seq (emitted_insts st s5) ss = OK m3 /\
     s5.cs_current_insts = st.cs_current_insts ++ emitted_insts st s5` by
      (qspecl_then [`st`, `s4`, `s5`, `ss`, `m2`] mp_tac
         run_inst_seq_chain >> simp[]) >>
    conj_tac >> strip_tac
    >- (irule clamp_and_return_ok >>
        qexistsl [`s5`, `res`, `m3`, `BaseT DecimalT`] >>
        gvs[type_bits_def, math_val_def, is_signed_type_def]) >>
    irule clamp_and_return_out_of_range >>
    qexistsl [`s5`, `op`, `res`, `m3`, `BaseT DecimalT`,
              `safe_sdiv (a * 0x2540BE400w) b`] >>
    gvs[type_bits_def, math_val_def, is_signed_type_def]
QED
