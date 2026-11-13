(*
 * Fuel bounds for expressions: compile_expr and its two dispatchers.
 *
 * compile_expr reaches its children only through the child callbacks,
 * which either recurse on a smaller argument or fall back to
 * invalid_expr_call (an INVALID); the helper lemmas take fuel_ok of an
 * arbitrary callback as a hypothesis, so the recursion is an induction
 * over compile_expr_ind.  The bodies case-split on pure values inside
 * their state-passing code; fuel_ok_pointwise lets a proof split them
 * with the state applied.
 *
 * TOP-LEVEL:
 *   fuel_ok_pointwise, fuel_ok_compile_expr, fuel_ok_lower_value_compile_expr
 *)

Theory fragFuelExpr
Ancestors
  fragFuel fragFuelStmtGlue fragFuelContextBase fragFuelContext
  fragFuelExprHelpers fragFuelBuiltins fragFuelAbi fragFuelExprCfn exprLowering exprCallBounds
  compileEnv emitHelper context venomInst pair
Libs
  fragFuelLib

(* fuel_ok constrains each run m st on its own. *)
Theorem fuel_ok_pointwise:
  !m Wv L E.
    (!st. ?m'. fuel_ok Wv L E m' /\ m st = m' st) ==> fuel_ok Wv L E m
Proof
  rw[fuel_ok_def] >> metis_tac[]
QED

Theorem cond_return_eta[local]:
  !b x y. (\s:compile_state. if b then (x, s) else (y, s)) =
          comp_return (if b then x else y)
Proof
  rw[FUN_EQ_THM, comp_return_def] >> rw[]
QED

(* ?m'. fuel_ok Wv L E m' /\ t = m' st: take m' = \st. t. *)
fun pw_tac (g as (_, w)) =
  let
    val (_, body) = dest_exists w
    val eq = snd (dest_conj body)
    val (t, rhs_) = dest_eq eq
    val st = rand rhs_
  in
    (EXISTS_TAC (mk_abs (st, t)) >> reverse conj_tac
     >- (BETA_TAC >> REFL_TAC)
     >> TRY (CONV_TAC (RAND_CONV ETA_CONV))) g
  end

(* fuel_ok of \s. body where body cases on (or tests) a value that doesn't
   depend on s or on anything bound in body: split it with s applied. *)
fun split_step (g as (asl, w)) =
  let
    val m = rand w
    val (s, body) = dest_abs m
    val gfvs = free_varsl (w :: asl)
    fun closed x = List.all (fn v => tmem v gfvs) (free_vars x)
    fun ok t =
      (TypeBase.is_case t andalso
       (let val (_, x, _) = TypeBase.dest_case t in closed x end)) orelse
      (is_cond t andalso closed (#1 (dest_cond t)))
    val _ = find_term ok body
  in
    (match_mp_tac fuel_ok_pointwise >> gen_tac >> BETA_TAC >>
     (BasicProvers.TOP_CASE_TAC ORELSE IF_CASES_TAC) >> pw_tac) g
  end

(* A pure pair let `let (a, b) = p in t` with p closed. *)
fun pair_let_step (g as (asl, w)) =
  let
    val m = rand w
    val (s, body) = dest_abs m
    val gfvs = free_varsl (w :: asl)
    fun closed x = List.all (fn v => tmem v gfvs) (free_vars x)
    fun ok t =
      (case strip_comb t of
         (c, [_, p]) => same_const c pairSyntax.uncurry_tm andalso
                        closed p andalso not (is_var p)
       | _ => false)
    val t = find_term ok body
  in
    (Cases_on `^(rand t)` >> PURE_REWRITE_TAC [pairTheory.UNCURRY_DEF] >>
     BETA_TAC) g
  end

(* A bind whose continuation takes a pair: !p. fuel_ok (UNCURRY f p). *)
fun pair_step (g as (_, w)) =
  let
    val (v, _) = dest_forall w
    val _ = pairSyntax.dest_prod (type_of v)
  in
    (CONV_TAC (HO_REWR_CONV pairTheory.FORALL_PROD) >>
     rpt gen_tac >> PURE_REWRITE_TAC [pairTheory.UNCURRY_DEF] >> BETA_TAC) g
  end

fun eta_step (g as (_, w)) =
  (CONV_TAC (RAND_CONV ETA_CONV)) g

(* The bodies are written in state-passing style (let (x, st') = m st in
   ...); these put them back into comp_bind/comp_return form. *)
Theorem uncurry_comp_bind[local]:
  !f m s. UNCURRY f (m s) = comp_bind m f s
Proof
  rw[comp_bind_def] >> Cases_on `m s` >> simp[]
QED

Theorem pair_comp_return[local]:
  !v. ($, v : compile_state -> 'a # compile_state) = comp_return v
Proof
  rw[FUN_EQ_THM, comp_return_def]
QED

Theorem cond_app[local]:
  !b (f:'a compiler) g s. (if b then f s else g s) = (if b then f else g) s
Proof
  rw[]
QED

val to_monadic =
  PURE_REWRITE_CONV [uncurry_comp_bind, pair_comp_return, cond_app] THENC
  DEPTH_CONV ETA_CONV

fun mon_step (g as (_, w)) =
  (case strip_comb w of
     (c, [_, _, _, _]) =>
       if is_const c andalso fst (dest_const c) = "fuel_ok" then
         CHANGED_TAC (CONV_TAC (RAND_CONV to_monadic)) g
       else NO_TAC g
   | _ => NO_TAC g)

(* Leaves indexed by the head constant of their action, so a goal tries
   only the lemmas about its own action (and those with no constant head). *)
fun action_head t =
  (case strip_comb (rand t) of
     (h, _) => if is_const h then
                 SOME (let val {Thy, Name, ...} = dest_thy_const h in (Thy, Name) end)
               else NONE)
  handle HOL_ERR _ => NONE

fun dispatch_tac ths =
  let
    val tbl =
      map (fn th => (action_head (snd (strip_imp (snd (strip_forall (concl th))))),
                     leaf_tac th)) ths
  in
    fn (g as (_, w)) =>
      let val h = action_head w
      in FIRST (List.mapPartial
                  (fn (k, tac) => if not (isSome k) orelse k = h then SOME tac
                                  else NONE) tbl) g
      end
  end

fun fuel_steps2 ths =
  let val leaves = dispatch_tac (leaf_thms ths) in
    FIRST [pair_step, mon_step,
           CHANGED_TAC (PURE_REWRITE_TAC [cond_return_eta]),
           fuel_step, leaves,
           first_assum MATCH_ACCEPT_TAC, eta_step, split_step,
           pair_let_step]
  end

fun fuel_auto2 ths = rpt (fuel_steps2 ths)

Theorem fuel_ok_invalid_expr_call:
  !ty Wv E. fuel_ok Wv {} E (invalid_expr_call ty)
Proof
  rpt gen_tac >> simp_tac std_ss [eta_def invalid_expr_call_def] >>
  fuel_auto2 [fuel_ok_emit_inst_any] >> simp[]
QED

Theorem fuel_ok_child_callbacks:
  (!bound f.
     (!c t e Wv E. expr_size e < bound ==> fuel_ok Wv {} E (f c t e)) ==>
     !c t e Wv E. fuel_ok Wv {} E (expr_child_callback bound f c t e)) /\
  (!bound f.
     (!c rt t bi es Wv E. list_size expr_size es < bound ==>
        fuel_ok Wv {} E (f c rt t bi es)) ==>
     !c rt t bi es Wv E.
       fuel_ok Wv {} E (builtin_child_callback bound f c rt t bi es)) /\
  (!bound f.
     (!c vt t tb rt es Wv E. list_size expr_size es < bound ==>
        fuel_ok Wv {} E (f c vt t tb rt es)) ==>
     !c vt t tb rt es Wv E.
       fuel_ok Wv {} E (type_child_callback bound f c vt t tb rt es))
Proof
  rpt conj_tac >> rpt strip_tac >> irule fuel_ok_pointwise >> gen_tac >>
  simp[] >> IF_CASES_TAC >> pw_tac >>
  simp[fuel_ok_invalid_expr_call]
QED

(* Every helper lemma `... ==> fuel_ok Wv L E (c args)` (c a constant) of
   the helper theories, as leaves for fuel_auto2.  A callback lemma
   `!cfn. hyp ==> !args. fuel_ok ...` becomes `!cfn args. hyp ==> ...`. *)
fun flatten_imp th =
  let
    fun go th =
      let val th1 = UNDISCH_ALL (SPEC_ALL th)
      in if is_forall (concl th1) orelse is_imp (concl th1) then go th1
         else th1 end
  in GEN_ALL (PURE_REWRITE_RULE [AND_IMP_INTRO] (DISCH_ALL (go th))) end

fun helper_lemmas thys =
  let
    fun concl_m th =
      let val c = snd (strip_imp (snd (strip_forall (concl th)))) in rand c end
    fun is_helper th =
      List.all (fn c => let val m = concl_m (flatten_imp c)
                            val (h, _) = strip_comb m
                        in is_const h end
                        handle HOL_ERR _ => false)
               (CONJUNCTS (SPEC_ALL th))
  in
    List.concat (map (fn thy =>
      List.mapPartial (fn ((n, th)) =>
        if String.isPrefix "fuel_ok_" n andalso is_helper th then
          SOME (LIST_CONJ (map flatten_imp (CONJUNCTS (SPEC_ALL th))))
        else NONE) (DB.thms thy handle HOL_ERR _ => []))
      thys)
  end

val expr_lemmas =
  [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_emit_inst_any,
   fuel_ok_return, fuel_ok_invalid_expr_call, fuel_ok_as_stack_val,
   fuel_ok_as_ptr_val] @
  helper_lemmas ["fragFuelContextBase", "fragFuelContext",
                 "fragFuelLoopWcopy", "fragFuelLoopSarray",
                 "fragFuelLoopDynarray", "fragFuelExprHelpers",
                 "fragFuelBuiltins", "fragFuelLoopUint2str", "fragFuelAbi",
                 "fragFuelExprCfn"];

(* An IfExp is a diamond: JNZ to the two arms, each assigning the fresh
   result variable and jumping to the exit block. *)
fun bq lm lf tac =
  match_mp_tac (Q.SPECL [lm, lf, `\st:compile_state. T`] fuel_okS_bindQ) >>
  rpt conj_tac
  >- simp[next_stable_def]
  >- simp[]
  >- simp[pred_setTheory.SUBSET_DEF]
  >- tac
  >> gen_tac >> BETA_TAC

val okS_tac = match_mp_tac fuel_okS_of_ok

Theorem fuel_ok_compile_expr_body_ifexp[local]:
  !f g h cenv ty t c a b Wv E.
    (!c t e Wv E. fuel_ok Wv {} E (f c t e)) ==>
    fuel_ok Wv {} E (compile_expr_body f g h cenv ty (IfExp t c a b))
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC [eta_def compile_expr_body_def, LET_THM] >> BETA_TAC >>
  PURE_REWRITE_TAC [TypeBase.case_def_of ``:expr``] >> BETA_TAC >>
  CONV_TAC (RAND_CONV to_monadic) >>
  match_mp_tac fuel_ok_of_okS >> qexists_tac `\st. T` >>
  conj_tac >- simp[] >>
  bq `{}` `{}` (okS_tac >> irule fuel_ok_lower_value >>
                first_assum ACCEPT_TAC) >>
  match_mp_tac fuel_okS_fresh_var >> gen_tac >> BETA_TAC >>
  bq `{}` `{}` (okS_tac >> simp[fuel_ok_prims]) >>
  bq `{}` `{}` (okS_tac >> simp[fuel_ok_prims]) >>
  bq `{}` `{}` (okS_tac >> simp[fuel_ok_prims]) >>
  rename1 `emit_inst JNZ [_; Label l_then; Label l_else] _` >>
  rename1 `emit_inst JMP [Label l_exit] []` >>
  bq `{}` `{l_then; l_else}`
    (okS_tac >> match_mp_tac fuel_ok_emit_inst_jnz >> simp[]) >>
  bq `{l_then}` `{l_else}` (okS_tac >> MATCH_ACCEPT_TAC fuel_ok_new_block) >>
  bq `{}` `{l_else}` (okS_tac >> first_assum MATCH_ACCEPT_TAC) >>
  bq `{}` `{l_else}` (okS_tac >> MATCH_ACCEPT_TAC fuel_ok_compile_ifexp_arm) >>
  bq `{}` `{l_else}`
    (okS_tac >> match_mp_tac fuel_ok_emit_inst_any >> simp[is_terminator_def]) >>
  bq `{}` `{l_else; l_exit}`
    (okS_tac >> match_mp_tac fuel_ok_emit_inst_jmp >> simp[]) >>
  bq `{l_else}` `{l_exit}` (okS_tac >> MATCH_ACCEPT_TAC fuel_ok_new_block) >>
  bq `{}` `{l_exit}` (okS_tac >> first_assum MATCH_ACCEPT_TAC) >>
  bq `{}` `{l_exit}` (okS_tac >> MATCH_ACCEPT_TAC fuel_ok_compile_ifexp_arm) >>
  bq `{}` `{l_exit}`
    (okS_tac >> match_mp_tac fuel_ok_emit_inst_any >> simp[is_terminator_def]) >>
  bq `{}` `{l_exit}`
    (okS_tac >> match_mp_tac fuel_ok_emit_inst_jmp >> simp[]) >>
  bq `{l_exit}` `{}` (okS_tac >> MATCH_ACCEPT_TAC fuel_ok_new_block) >>
  okS_tac >> IF_CASES_TAC >> MATCH_ACCEPT_TAC fuel_ok_return
QED

val ea = fuel_auto2 expr_lemmas >> simp[is_terminator_def];
(* One round of ea, for unrolling it where a goal needs per-step budgets. *)
val ea1 = TRY (fuel_steps2 expr_lemmas);

(* The Builtin case of compile_expr_body is the builtin callback or one of
   the three modular-arithmetic special forms. *)
val case_lift_thms =
  let val tys = [``:'a list``, ``:expr``]
      fun constant ty = Prim_rec.prove_case_const_thm
        {case_def = TypeBase.case_def_of ty,
         nchotomy = TypeBase.nchotomy_of ty}
  in map TypeBase.case_rand_of tys @ map constant tys end;

Theorem compile_expr_body_builtin_pred[local]:
  !P bf ce bi sa f tf ty ann args.
  (!rt ty es. P (bf ce rt ty bi es sa)) /\
  (!rt aty a bty b mty m. P (compile_addmod_names ce rt aty a bty b mty m sa)) /\
  (!rt aty a bty b mty m. P (compile_mulmod_names ce rt aty a bty b mty m sa)) /\
  (!rt aty a bty b. P (compile_powmod256_names ce rt aty a bty b sa)) ==>
  P (compile_expr_body f bf tf ce ty (Builtin ann bi args) sa)
Proof
  gen_tac >> strip_tac >> Cases_on `bi` >>
  simp([compile_expr_body_def, LET_THM] @ case_lift_thms)
QED

Theorem fuel_ok_compile_expr_body_builtin[local]:
  !f g h cenv ty t b l Wv E.
    (!c rt t bi es Wv E. fuel_ok Wv {} E (g c rt t bi es)) ==>
    fuel_ok Wv {} E (compile_expr_body f g h cenv ty (Builtin t b l))
Proof
  rpt strip_tac >> irule fuel_ok_pointwise >> gen_tac >>
  irule (BETA_RULE (Q.ISPEC
    `\r:vyper_value # compile_state.
       ?m':vyper_value compiler. fuel_ok Wv {} E m' /\ r = m' st`
    compile_expr_body_builtin_pred)) >>
  rpt conj_tac >> rpt gen_tac >> pw_tac >> ea
QED

Theorem fuel_ok_compile_expr_body:
  !f g h cenv ty e Wv E.
    (!c t e Wv E. fuel_ok Wv {} E (f c t e)) /\
    (!c rt t bi es Wv E. fuel_ok Wv {} E (g c rt t bi es)) /\
    (!c vt t tb rt es Wv E. fuel_ok Wv {} E (h c vt t tb rt es)) ==>
    fuel_ok Wv {} E (compile_expr_body f g h cenv ty e)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?t c a b. e = IfExp t c a b`
  >- (fs[] >> irule fuel_ok_compile_expr_body_ifexp >> first_assum ACCEPT_TAC) >>
  Cases_on `?t b l. e = Builtin t b l`
  >- (fs[] >> irule fuel_ok_compile_expr_body_builtin >> first_assum ACCEPT_TAC) >>
  irule fuel_ok_pointwise >> gen_tac >>
  PURE_REWRITE_TAC [compile_expr_body_def, LET_THM] >> BETA_TAC >>
  (* TOP_CASE_TAC, with its simplification run per goal under the step budget *)
  BasicProvers.PURE_TOP_CASE_TAC >>
  FIRST [ASM_REWRITE_TAC [] >> CONV_TAC BasicProvers.CASE_SIMP_CONV] >> pw_tac
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (fs[] >> metis_tac[])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (fs[] >> metis_tac[])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >- (FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
      FIRST [ea])
  >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea]
QED

Theorem fuel_ok_builtin_dispatch_bop[local]:
  !f cenv ret_ty ty op args Wv E.
    (!c t e Wv E. fuel_ok Wv {} E (f c t e)) ==>
    fuel_ok Wv {} E
      (compile_builtin_dispatch_body f cenv ret_ty ty (Bop op) args)
Proof
  rpt strip_tac >> irule fuel_ok_pointwise >> gen_tac >>
  PURE_REWRITE_TAC [compile_builtin_dispatch_body_def, LET_THM,
                    TypeBase.case_def_of ``:builtin``] >> BETA_TAC >>
  qabbrev_tac `e2 = HD (TL args)` >> Cases_on `e2` >>
  TRY (qmatch_assum_rename_tac `Abbrev (Builtin _ bb _ = _)` >> Cases_on `bb`) >>
  PURE_REWRITE_TAC [TypeBase.case_def_of ``:expr``,
                    TypeBase.case_def_of ``:builtin``] >>
  BETA_TAC >> pw_tac >>
  (* ea per goal, one round per step *)
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea]
QED

Theorem fuel_ok_compile_builtin_dispatch_body:
  !f cenv ret_ty ty bi args Wv E.
    (!c t e Wv E. fuel_ok Wv {} E (f c t e)) ==>
    fuel_ok Wv {} E (compile_builtin_dispatch_body f cenv ret_ty ty bi args)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bi`
  >~ [`compile_builtin_dispatch_body _ _ _ _ (Bop _) _`]
  >- (irule fuel_ok_builtin_dispatch_bop >> first_assum ACCEPT_TAC)
  >> irule fuel_ok_pointwise >> gen_tac >>
  PURE_REWRITE_TAC [compile_builtin_dispatch_body_def, LET_THM,
                    TypeBase.case_def_of ``:builtin``] >>
  BETA_TAC >> pw_tac >>
  (* ea per goal, one round per step *)
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea]
QED

Theorem fuel_ok_compile_type_builtin_dispatch_body:
  !f cenv vv_ty ty tb ret_ty args Wv E.
    (!c t e Wv E. fuel_ok Wv {} E (f c t e)) ==>
    fuel_ok Wv {} E
      (compile_type_builtin_dispatch_body f cenv vv_ty ty tb ret_ty args)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `tb` >>
  irule fuel_ok_pointwise >> gen_tac >>
  PURE_REWRITE_TAC [compile_type_builtin_dispatch_body_def, LET_THM,
                    TypeBase.case_def_of ``:type_builtin``] >>
  BETA_TAC >> pw_tac >>
  (* ea per goal, one round per step *)
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >> FIRST [ea1] >>
  FIRST [ea]
QED

Theorem fuel_ok_compile_expr:
  (!cenv ty e (st:compile_state) Wv E.
     fuel_ok Wv {} E (compile_expr cenv ty e)) /\
  (!cenv ret_ty ty bi args (st:compile_state) Wv E.
     fuel_ok Wv {} E (compile_builtin_dispatch cenv ret_ty ty bi args)) /\
  (!cenv vv_ty ty tb ret_ty args (st:compile_state) Wv E.
     fuel_ok Wv {} E (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args))
Proof
  ho_match_mp_tac compile_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac
  >- (PURE_ONCE_REWRITE_TAC [eta_def compile_expr_raw_def] >>
      CONV_TAC (RAND_CONV ETA_CONV) >>
      irule fuel_ok_compile_expr_body >> rpt conj_tac
      >- (irule (cj 1 fuel_ok_child_callbacks) >> metis_tac[])
      >- (irule (cj 2 fuel_ok_child_callbacks) >> metis_tac[]) >>
      irule (cj 3 fuel_ok_child_callbacks) >> metis_tac[])
  >- (PURE_ONCE_REWRITE_TAC [eta_def compile_expr_raw_def] >>
      CONV_TAC (RAND_CONV ETA_CONV) >>
      irule fuel_ok_compile_builtin_dispatch_body >>
      irule (cj 1 fuel_ok_child_callbacks) >> metis_tac[]) >>
  PURE_ONCE_REWRITE_TAC [eta_def compile_expr_raw_def] >>
  PURE_REWRITE_TAC [COND_CLAUSES] >>
  CONV_TAC (RAND_CONV ETA_CONV) >>
  irule fuel_ok_compile_type_builtin_dispatch_body >>
  irule (cj 1 fuel_ok_child_callbacks) >> metis_tac[]
QED

Theorem fuel_ok_lower_value_compile_expr:
  !cenv ty e Wv E. fuel_ok Wv {} E (lower_value compile_expr cenv ty e)
Proof
  rpt gen_tac >> irule fuel_ok_lower_value >> metis_tac[fuel_ok_compile_expr]
QED
