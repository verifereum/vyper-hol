(*
 * Fuel bounds for the statement forms that compose other statements: If
 * and a statement list (compile_stmts), given bounds for their parts.
 *
 * Both run statements under the precondition cenv_ptrs_below, which only
 * needs the variables allocated so far to stay allocated (next_stable), so
 * the rules here sequence fuel_okS actions with forward labels the way
 * fuel_ok_seq_fwd does.  Their code also reads the compile state
 * (block_is_terminated): fuel_okS_get_pin fixes the state, so the jumps an
 * If emits to its exit block are known, and the exit block is emitted
 * exactly when one of its branches jumps there.
 *
 * TOP-LEVEL:
 *   fuel_okS_seqQ, fuel_okS_bindQ, fuel_okS_get_pin, fuel_okS_compile_if,
 *   fuel_okS_compile_stmts_cons
 *)

Theory fragFuelStmtGlue
Ancestors
  fragFuel fragFuelStmtBase stmtLowering exprLowering compileEnv emitHelper
  context venomInst finite_map pred_set ASCIInumbers
Libs
  fragFuelLib

Theorem fuel_okS_E_mono[local]:
  !P Wv L E E' m. fuel_okS P Wv L E m /\ E SUBSET E' ==> fuel_okS P Wv L E' m
Proof
  metis_tac[fuel_okS_mono, SUBSET_REFL]
QED

Theorem fuel_okS_pre_mono[local]:
  !P P' Wv L E m.
    fuel_okS P Wv L E m /\ (!st. P' st ==> P st) ==> fuel_okS P' Wv L E m
Proof
  metis_tac[fuel_okS_mono, SUBSET_REFL]
QED

(* Sequencing: m starts under P, the rest under Q, which P implies and every
   action keeps; the rest starts the blocks labelled Lf, which m may jump
   to. *)
Theorem fuel_okS_bindQ:
  !Lm Lf Q P m f Wv L E.
    next_stable Q /\ (!st. P st ==> Q st) /\ L SUBSET Lm UNION Lf /\
    fuel_okS P Wv Lm (E UNION Lf) m /\ (!a. fuel_okS Q Wv Lf E (f a)) ==>
    fuel_okS P Wv L E (comp_bind m f)
Proof
  rpt strip_tac >>
  `fuel_okS P Wv (Lm UNION Lf) E (comp_bind m f)` suffices_by
    metis_tac[fuel_okS_mono, SUBSET_REFL] >>
  match_mp_tac (Q.SPECL [`P`, `\a. Q`, `m`, `f`, `Wv`, `Lm`, `Lf`,
                         `E UNION Lf`, `E`, `E`] fuel_okS_bind) >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  fs[fuel_okS_def, next_stable_def] >> metis_tac[]
QED

Theorem fuel_okS_seqQ:
  !Lm Lf Q P m f Wv L E.
    next_stable Q /\ (!st. P st ==> Q st) /\ L SUBSET Lm UNION Lf /\
    fuel_okS P Wv Lm (E UNION Lf) m /\ fuel_okS Q Wv Lf E f ==>
    fuel_okS P Wv L E (comp_ignore_bind m f)
Proof
  rw[comp_ignore_bind_def] >>
  match_mp_tac (Q.SPECL [`Lm`, `Lf`, `Q`] fuel_okS_bindQ) >> fs[]
QED

(* Reading the compile state: the rest runs from that very state. *)
Theorem fuel_okS_get_pin:
  !P f Wv L E.
    (!cs. P cs ==> fuel_okS (\st. P st /\ st = cs) Wv L E (f cs)) ==>
    fuel_okS P Wv L E (comp_bind comp_get f)
Proof
  rw[fuel_okS_def, comp_bind_def, comp_get_def] >> metis_tac[]
QED

Theorem fuel_okS_ejint_done[local]:
  !P cs l Wv E.
    block_is_terminated cs ==>
    fuel_okS (\st. P st /\ st = cs) Wv {} E (emit_jmp_if_not_terminated l)
Proof
  rpt strip_tac >>
  `fuel_okS (\st. P st /\ st = cs) Wv {} E (comp_return ())` by
    (irule fuel_okS_of_ok >> simp[fuel_ok_return]) >>
  fs[fuel_okS_def, emit_jmp_if_not_terminated_def, comp_bind_def,
     comp_get_def, comp_return_def] >> metis_tac[]
QED

val ok_tac = match_mp_tac fuel_okS_of_ok

fun sq lm lf tac =
  match_mp_tac (Q.SPECL [lm, lf, `P`] fuel_okS_seqQ) >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- simp[]
  >- simp[SUBSET_DEF]
  >- tac

val nb_tac = ok_tac >> MATCH_ACCEPT_TAC fuel_ok_new_block
val jmp_tac =
  ok_tac >> match_mp_tac fuel_ok_emit_jmp_if_not_terminated >> simp[]
val asm_tac =
  match_mp_tac fuel_okS_E_mono >> qexists_tac `E` >> conj_tac
  >- first_assum ACCEPT_TAC >> simp[SUBSET_DEF]
val ret_tac = ok_tac >> MATCH_ACCEPT_TAC fuel_ok_return

(* Split on a boolean and rewrite the goal with the case. *)
fun bcase q =
  Cases_on q >>
  pop_assum (fn th =>
    assume_tac th >>
    PURE_REWRITE_TAC [if is_neg (concl th) then EQF_INTRO th else EQT_INTRO th,
                      NOT_CLAUSES, OR_CLAUSES, COND_CLAUSES])

fun label_tac v =
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (ok_tac >> simp[fuel_ok_prims]) >>
  qx_gen_tac v >> BETA_TAC

(* An If: each branch jumps to the exit block unless it ended in a
   terminator, and the exit block is emitted unless both did. *)
Theorem fuel_okS_compile_if:
  !P cenv lctx ty c tb eb Wv E.
    next_stable P /\
    fuel_ok Wv {} E (lower_value compile_expr cenv (BaseT BoolT) c) /\
    fuel_okS P Wv {} E (compile_stmts cenv lctx ty tb) /\
    fuel_okS P Wv {} E (compile_stmts cenv lctx ty eb) ==>
    fuel_okS P Wv {} E (compile_stmt cenv lctx ty (If c tb eb))
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC [compile_stmt_def] >>
  PURE_REWRITE_TAC [comp_bind_return] >> BETA_TAC >>
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (ok_tac >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `cop` >> BETA_TAC >>
  label_tac `l_then` >> label_tac `l_else` >> label_tac `l_exit` >>
  sq `{}` `{l_then; l_else}`
    (ok_tac >> match_mp_tac fuel_ok_emit_inst_jnz >> simp[]) >>
  sq `{l_then}` `{l_else}` nb_tac >>
  sq `{}` `{l_else}` asm_tac >>
  match_mp_tac fuel_okS_get_pin >> qx_gen_tac `cs1` >> strip_tac >>
  BETA_TAC >>
  bcase `block_is_terminated cs1`
  >- (sq `{}` `{l_else}`
        (match_mp_tac fuel_okS_ejint_done >> first_assum ACCEPT_TAC) >>
      sq `{l_else}` `{}` nb_tac >>
      sq `{}` `{}` asm_tac >>
      match_mp_tac fuel_okS_get_pin >> qx_gen_tac `cs2` >> strip_tac >>
      BETA_TAC >>
      bcase `block_is_terminated cs2`
      >- (sq `{}` `{}`
            (match_mp_tac fuel_okS_ejint_done >> first_assum ACCEPT_TAC) >>
          ret_tac) >>
      sq `{}` `{l_exit}` jmp_tac >>
      sq `{l_exit}` `{}` nb_tac >> ret_tac) >>
  sq `{}` `{l_else; l_exit}` jmp_tac >>
  sq `{l_else}` `{l_exit}` nb_tac >>
  sq `{}` `{l_exit}` asm_tac >>
  match_mp_tac fuel_okS_get_pin >> qx_gen_tac `cs2` >> strip_tac >>
  BETA_TAC >>
  sq `{}` `{l_exit}` jmp_tac >>
  sq `{l_exit}` `{}` nb_tac >> ret_tac
QED

Theorem declare_stmt_local_other[local]:
  !cenv s. (!id vt e. s <> AnnAssign id vt e) ==>
           declare_stmt_local cenv s = comp_return cenv
Proof
  Cases_on `s` >> simp[declare_stmt_local_def]
QED

Theorem cenv_ptrs_below_declare[local]:
  !n cenv cenv2 id sz.
    cenv_ptrs_below n cenv /\
    cenv2.ce_vars =
      cenv.ce_vars |+ (id, PtrVar (Var (STRING #"%" (toString n))) sz) ==>
    cenv_ptrs_below (n + 1) cenv2
Proof
  rw[cenv_ptrs_below_def, FLOOKUP_UPDATE] >> gvs[AllCaseEqs()]
  >- (rw[var_below_def] >> fs[]) >>
  res_tac >> irule var_below_le >> qexists_tac `n` >> simp[]
QED

Theorem cenv_ptrs_in_declare[local]:
  !Wv cenv cenv2 id sz x.
    cenv_ptrs_in Wv cenv /\
    cenv2.ce_vars = cenv.ce_vars |+ (id, PtrVar (Var x) sz) ==>
    cenv_ptrs_in (x INSERT Wv) cenv2
Proof
  rw[cenv_ptrs_in_def, FLOOKUP_UPDATE] >> gvs[AllCaseEqs()] >> res_tac >> simp[]
QED

val use_ih =
  rpt conj_tac >- simp[next_stable_cenv_ptrs_below] >>
  first_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC

(* A statement list: the next statement runs unless the block already ended
   in a terminator; a declaration's pointer variable is fresh, so the rest
   of the list may write it. *)
Theorem fuel_okS_compile_stmts_cons:
  !cenv lctx ty s ss Wv E.
    (!cenv' Wv'. cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E cenv' lctx ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E
         (compile_stmt cenv' lctx ty s)) /\
    (!cenv' Wv'. cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E cenv' lctx ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E
         (compile_stmts cenv' lctx ty ss)) /\
    cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
      (compile_stmts cenv lctx ty (s::ss))
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC [compile_stmt_def] >>
  match_mp_tac fuel_okS_get_pin >> qx_gen_tac `cs` >> strip_tac >>
  BETA_TAC >> IF_CASES_TAC >- ret_tac >>
  match_mp_tac fuel_okS_pre_mono >>
  qexists_tac `\st. cenv_ptrs_below st.cs_next_var cenv` >>
  reverse conj_tac >- simp[] >>
  Cases_on `?id vt e. s = AnnAssign id vt e`
  >- (
    gvs[declare_stmt_local_def] >>
    PURE_REWRITE_TAC [declare_local_def, LET_THM] >> BETA_TAC >>
    IF_CASES_TAC
    >- (
      PURE_REWRITE_TAC [comp_bind_assoc] >> BETA_TAC >>
      PURE_REWRITE_TAC [comp_bind_return] >> BETA_TAC >>
      match_mp_tac fuel_okS_fresh_var >> qx_gen_tac `n` >> BETA_TAC >>
      qmatch_goalsub_abbrev_tac `compile_stmts cenvN lctx ty ss` >>
      `cenvN.ce_vars =
         cenv.ce_vars |+ (id, PtrVar (Var (STRING #"%" (toString n)))
                                (type_memory_bytes cenv vt)) /\
       cenvN.ce_ctor_exit_label = cenv.ce_ctor_exit_label` by
        simp[Abbr `cenvN`] >>
      match_mp_tac fuel_okS_pre_mono >>
      qexists_tac `\st. cenv_ptrs_below st.cs_next_var cenvN` >>
      reverse conj_tac
      >- (rw[] >>
          qpat_x_assum `_ = st.cs_next_var` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
          irule cenv_ptrs_below_declare >> metis_tac[]) >>
      `cenv_ptrs_in (STRING #"%" (toString n) INSERT Wv) cenvN /\
       stmt_exits_in E cenvN lctx` by
        (conj_tac
         >- (irule cenv_ptrs_in_declare >> metis_tac[])
         >> fs[stmt_exits_in_def]) >>
      match_mp_tac fuel_okS_ignore_bind_keep >> use_ih) >>
    PURE_REWRITE_TAC [comp_bind_return] >> BETA_TAC >>
    qmatch_goalsub_abbrev_tac `compile_stmts cenvN lctx ty ss` >>
    `cenv_ptrs_in Wv cenvN /\ stmt_exits_in E cenvN lctx /\
     !n. cenv_ptrs_below n cenvN = cenv_ptrs_below n cenv` by
      (fs[Abbr `cenvN`, cenv_ptrs_in_def, cenv_ptrs_below_def,
          stmt_exits_in_def] >> metis_tac[]) >>
    match_mp_tac fuel_okS_pre_mono >>
    qexists_tac `\st. cenv_ptrs_below st.cs_next_var cenvN` >>
    reverse conj_tac >- simp[] >>
    match_mp_tac fuel_okS_ignore_bind_keep >> use_ih) >>
  `declare_stmt_local cenv s = comp_return cenv` by
    (irule declare_stmt_local_other >> fs[]) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th, comp_bind_return]) >> BETA_TAC >>
  match_mp_tac fuel_okS_ignore_bind_keep >> use_ih
QED
