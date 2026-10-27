(*
 * Statement simulation: For over a literal range (#637)
 *
 * TOP-LEVEL:
 *   compile_for_range_frag        — For over a range with literal ends,
 *                                   under a loop invariant
 *   compile_for_range_frag_simple — the same with the body's judgment at
 *                                   every source state
 *)

Theory stmtSimFor
Ancestors
  stmtSim stmtSimForParts stmtSimForLoop
  list rich_list finite_map pred_set
  fragExec localPtrsProps exprSim loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding
  vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

(* ===== For over a literal range ===== *)

Theorem reserved_fresh_not_local[local]:
  !cenv st n scs.
    local_ptrs_reserved cenv st /\ st.cs_next_var <= n ==>
    not_local_ptr cenv scs (STRING #"%" (toString n))
Proof
  rw[not_local_ptr_def] >> strip_tac >>
  fs[local_ptrs_reserved_def, not_fresh_at_def] >>
  qpat_x_assum `!n1 n2 p sz1 sz2. _`
    (qspecl_then [`name`, `name`, `STRING #"%" (toString n)`, `sz`, `sz`]
       mp_tac) >>
  simp[] >> qexists_tac `n` >> simp[]
QED

(* For over a range with literal ends: the loop variable's ALLOCA, the
   entry block, then the loop from the first counter value; on a normal
   finish the code ends at the start of the exit block.  The body's
   judgment is assumed for the environment declare_local gives, at the
   iteration states over source states where the invariant P holds; P
   holds at the start and again after each iteration that goes on.  P sees
   the state and not the counter, so this composes with an induction whose
   hypothesis holds at every state satisfying an invariant, not with one
   over the evaluator's recursion, which gives the body only at the visited
   (state, counter) pairs.  Only for n1 <= n2 (not the source's "no range"
   error), a loop variable of one word, and ce_alloca_locals, which the
   lowering sets for external functions only. *)
Theorem compile_for_range_frag:
  !P ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es res es'
   tyv.
    eval_stmt cx
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    P es /\
    (!st0 c st1 ex inc ei j r2 es2.
       declare_local cenv id fty st0 = (c, st1) /\
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) r2 es2) /\
    (!ei j r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j) |>)) :: ei.scopes) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
            bound stmts)) es res es'
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [stmt_frag_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty
              (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
                 bound stmts) sa` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_stmt _ _ _ _ sa = (uu, sb)` >>
  `uu = ()` by simp[oneTheory.one] >> gvs[] >>
  (* the code and the source loop *)
  qspecl_then [`cenv`, `lctx`, `ty`, `id`, `fty`, `a1`, `n1`, `a2`, `n2`,
               `bound`, `stmts`, `sa`, `sb`, `func`]
    mp_tac compile_for_range_parts >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  drule_all eval_stmt_for_range_lit >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  (* the loop variable's ALLOCA *)
  qabbrev_tac `sz = type_memory_bytes cenv fty` >>
  qabbrev_tac `A = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]` >>
  `MEM A (fn_insts func)` by
    (qpat_assum `lookup_block sa.cs_current_bb _ = _`
       (mp_tac o MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] lookup_block_fn_insts)) >>
     simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (simp[not_local_ptr_def] >> rpt strip_tac >>
     fs[local_ptrs_reserved_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w sz)] /\
   A.inst_outputs = [p] /\ A.inst_id = sa.cs_next_id` by
    simp[Abbr `A`, venomInstTheory.mk_inst_def] >>
  `step_inst_base A s0 = exec_alloca A s0 (n2w sz : bytes32)` by
    simp[Abbr `A`, step_inst_base_def, venomInstTheory.mk_inst_def] >>
  `?s1. exec_alloca A s0 (n2w sz : bytes32) = OK s1` by
    (simp[exec_alloca_def] >> BasicProvers.every_case_tac >> simp[]) >>
  fs[] >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `s0`, `A`, `p`,
               `n2w sz : bytes32`, `s1`] mp_tac stmt_state_rel_exec_alloca >>
  impl_tac >- fs[] >> strip_tac >>
  `s1.vs_current_bb = s0.vs_current_bb /\ s1.vs_inst_idx = s0.vs_inst_idx /\
   ~s1.vs_halted /\ (!x. x <> p ==> lookup_var x s1 = lookup_var x s0) /\
   (!a b. FLOOKUP s0.vs_allocas a = SOME b ==>
          FLOOKUP s1.vs_allocas a = SOME b)` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >> simp[exec_alloca_def] >>
     BasicProvers.every_case_tac >> rw[] >>
     fs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> rw[] >>
     fs[FLOOKUP_DEF] >> metis_tac[]) >>
  `w2n (n2w sz : bytes32) = sz` by fs[] >> fs[] >>
  (* the start and entry blocks *)
  qspecl_then [`ctx`, `func`, `s0`, `s1`, `A`, `sa.cs_current_insts`,
               `sa.cs_current_bb`, `entry_lbl`, `sa.cs_next_id + 1`]
    mp_tac for_start_block >>
  impl_tac >- fs[] >> strip_tac >>
  qspecl_then [`ctx`, `func`, `jump_to entry_lbl s1`, `cv`, `ev`, `i2w n1`,
               `i2w n2 - i2w n1`, `entry_lbl`, `cond_lbl`, `sa.cs_next_id + 2`,
               `sa.cs_next_id + 3`, `sa.cs_next_id + 4`]
    mp_tac for_entry_block >>
  impl_tac >- fs[jump_to_def] >>
  REWRITE_TAC [wordsTheory.WORD_SUB_ADD2] >> strip_tac >>
  (* the variables *)
  `sb0.cs_next_var <= sb1.cs_next_var` by metis_tac[] >>
  `dv <> p /\ dv <> cv /\ dv <> ev /\ nv <> cv /\ nv <> ev /\ nv <> p /\
   cv <> ev /\ cv <> p /\ ev <> p` by (fs[] >> rw[] >> fs[]) >>
  `(!scs. not_local_ptr cenv scs cv) /\ (!scs. not_local_ptr cenv scs ev) /\
   (!scs. not_local_ptr cenv scs dv) /\ (!scs. not_local_ptr cenv scs nv)` by
    (rpt conj_tac >> gen_tac >>
     qpat_assum `cv = _` SUBST1_TAC >> qpat_assum `ev = _` SUBST1_TAC >>
     qpat_assum `dv = _` SUBST1_TAC >> qpat_assum `nv = _` SUBST1_TAC >>
     irule reserved_fresh_not_local >> qexists_tac `sa` >> fs[]) >>
  `local_ptrs_reserved bc sb0` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa with cs_next_var := sa.cs_next_var + 1` >> simp[] >>
     irule declare_local_reserved >> metis_tac[]) >>
  `!scs. lookup_scopes id scs = NONE ==> not_local_ptr bc (FEMPTY::scs) p` by
    (rpt strip_tac >>
     `not_local_ptr cenv (FEMPTY::scs) p` by
       (qpat_assum `p = _` SUBST1_TAC >> irule reserved_fresh_not_local >>
        qexists_tac `sa` >> simp[]) >>
     fs[not_local_ptr_def] >> rpt strip_tac >>
     `name <> id` by (strip_tac >> fs[lookup_scopes_def]) >> metis_tac[]) >>
  (* the state at the condition block *)
  qabbrev_tac `cc = jump_to cond_lbl (update_var ev (i2w n2)
                  (update_var cv (i2w n1) (jump_to entry_lbl s1)))` >>
  `stmt_state_rel func cenv cx es cc` by
    (simp[Abbr `cc`, stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >>
     conj_tac >- (irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
     irule stmt_state_rel_update_var >>
     conj_tac >- (irule reserved_fresh_not_local >> qexists_tac `sa` >> simp[]) >>
     fs[stmt_state_rel_jump_to]) >>
  `lookup_var p cc = SOME w` by
    (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE] >>
     qpat_x_assum `lookup_var p s1 = _` mp_tac >>
     qpat_assum `p = _` (fn th => REWRITE_TAC [th]) >> simp[lookup_var_def]) >>
  `FLOOKUP cc.vs_allocas A.inst_id = SOME (w2n w, sz)` by
    (simp[Abbr `cc`, jump_to_def, update_var_def] >>
     qpat_x_assum `FLOOKUP s1.vs_allocas A.inst_id = _` mp_tac >>
     qpat_assum `A.inst_id = _` (fn th => REWRITE_TAC [th])) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
         lookup_var x cc = SOME v` by
    (rpt strip_tac >>
     `x <> p /\ x <> cv /\ x <> ev` by
       (fs[not_fresh_at_def] >> rpt conj_tac >> first_x_assum irule >>
        simp[]) >>
     simp[Abbr `cc`, lookup_var_def, jump_to_def, update_var_def,
          FLOOKUP_UPDATE] >>
     fs[GSYM lookup_var_def] >> metis_tac[]) >>
  `ret_pc_ok cenv sa cc` by
    (qspecl_then [`cenv`, `cenv`, `sa`, `sa`, `s0`, `cc`] mp_tac
       ret_pc_ok_frame >>
     impl_tac >- fs[] >> simp[]) >>
  `!fuel rr. run_from fuel ctx func cc = rr /\ (!e. rr <> Error e) ==>
             ?fuel'. run_from fuel' ctx func s0 = rr` by
    (simp[Abbr `cc`] >> metis_tac[]) >>
  `!a b. FLOOKUP s0.vs_allocas a = SOME b ==> FLOOKUP cc.vs_allocas a = SOME b`
    by simp[Abbr `cc`, jump_to_def, update_var_def] >>
  `cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
   lookup_var cv cc = SOME (i2w (n1 + 0)) /\ lookup_var ev cc = SOME (i2w n2)`
    by (simp[Abbr `cc`, jump_to_def, update_var_def, lookup_var_def,
             FLOOKUP_UPDATE] >> fs[jump_to_def]) >>
  (* the loop *)
  qspecl_then [`Num (n2 - n1)`, `P`, `ctx`, `func`, `cenv`, `bc`, `cx`, `lctx`,
               `RetQ`, `ty`, `stmts`, `id`, `tyv`, `p`, `sz`, `A`, `cv`, `ev`,
               `dv`, `nv`, `n1`, `n2`, `cond_lbl`, `exit_lbl`, `body_lbl`,
               `incr_lbl`, `sa.cs_next_id + 5`, `sa.cs_next_id + 6`,
               `sa.cs_next_id + 7`, `bbb`, `sj.cs_next_id`, `sj.cs_next_id + 1`,
               `sj.cs_next_id + 2`, `sb0`, `sb1`, `sj`, `sa`, `0`, `es`, `cc`,
               `w`, `res`, `es'`] mp_tac for_loop >>
  impl_tac
  >- (REWRITE_TAC [for_code_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (simp[block_is_terminated_def, venomInstTheory.mk_inst_def,
                is_terminator_def] >> NO_TAC) >>
      TRY (fs[] >> NO_TAC) >>
      TRY (simp[not_fresh_at_def] >> NO_TAC) >>
      TRY (rw[not_fresh_at_def] >>
           TRY (first_x_assum (qspec_then `sj.cs_next_var` mp_tac)) >>
           simp[] >> NO_TAC) >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  strip_tac
  >- (rename1 `s9.vs_current_bb = exit_lbl` >> disj1_tac >>
      qexists_tac `s9` >> qexists_tac `cenv` >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[stmt_lands_def]
      >- simp[block_is_terminated_def]
      >- simp[cenv_top_ext_refl]
      >- metis_tac[]
      >- metis_tac[] >>
      rpt strip_tac >> metis_tac[]) >>
  disj2_tac >> rename1 `exit_result r9` >>
  drule exit_result_not_error >> strip_tac >> metis_tac[]
QED

(* The same with the body's judgment at every source state. *)
Theorem compile_for_range_frag_simple:
  !ctx func cx lctx RetQ cenv ty id fty a1 n1 a2 n2 bound stmts es res es'
   tyv.
    eval_stmt cx
      (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
         bound stmts) es = (res, es') /\
    evaluate_type (get_tenv cx) fty = SOME tyv /\ type_memory_size tyv = 32 /\
    32 <= type_memory_bytes cenv fty /\
    type_memory_bytes cenv fty < dimword (:256) /\
    n1 <= n2 /\ Num (n2 - n1) <= bound /\ Num (n2 - n1) < dimword (:256) /\
    cenv.ce_alloca_locals /\ lookup_scopes id es.scopes = NONE /\
    (!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
    (!c lc sa sb. compile_stmts c lc ty stmts sa = ((), sb) ==>
                  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    (!st0 c st1 ex inc es1 r2 es2.
       declare_local cenv id fty st0 = (c, st1) /\
       eval_stmts cx stmts es1 = (r2, es2) ==>
       stmt_frag ctx func cx (InLoop ex inc) RetQ c
         (stmts_env c (InLoop ex inc) ty stmts) es1 r2 es2) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty
         (For id fty (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2)))
            bound stmts)) es res es'
Proof
  rpt strip_tac >>
  MATCH_MP_TAC (BETA_RULE (Q.SPEC `\e. T` compile_for_range_frag)) >>
  qexists_tac `tyv` >> simp[] >> rpt strip_tac
  >- (qpat_x_assum `!c lc sa sb. _` drule >> simp[])
  >- (qpat_x_assum `!c lc sa sb. _` drule >> simp[]) >>
  qpat_x_assum `!st0 c st1 ex inc es1 r2 es2. _` irule >> metis_tac[]
QED
