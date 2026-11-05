# TASK: counted range-loop round and loop

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/stmtSimForLoopScript.sml

## Theorem Statement (FROZEN)

The four theorems below, as they stand in `lowering/stmtSimForLoopScript.sml`.
`for_loop_alloca` is consumed by later theories and is strictly frozen, as
are `for_iteration` and `for_loop`. `for_iteration_alloca` is `[local]` and
weakly frozen: change it only if it is false, and say why.

```sml
Theorem for_iteration_alloca[local]:
  !ctx func cenv bc cx lctx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv
   nv n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st vs.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the iteration *)
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (esk with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes;
                   gas_obs := [] |>) /\
    gas_admissible (eval_for cx tyv id stmts (IntV (n1 + &k) :: vs))
      (stmt_res_ok lctx) esk ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (do push_scope_with_var id tyv (IntV (n1 + &k));
          finally
            (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
            pop_scope
       od) (esk, cc)
      (\res ee t. ?broke. res = INL broke /\
         t.vs_inst_idx = 0 /\ ~t.vs_halted /\
         stmt_state_rel ctx func cenv cx ee t /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x t = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP t.vs_allocas a = SOME b) /\
         (broke ==> t.vs_current_bb = exit_lbl) /\
         (~broke ==> t.vs_current_bb = cond_lbl /\
                     lookup_var cv t = SOME (i2w (n1 + &(k + 1))) /\
                     lookup_var ev t = SOME (i2w n2) /\
                     lookup_var p t = SOME w))
      (\res ee r. ?ex. res = INR ex /\
         !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)

Theorem for_iteration:
  !ctx func cenv bc cx lctx RetQ ty stmts esk cc id tyv p sz w ainst cv ev dv
   nv n1 n2 k cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st vs cap.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    not_local_ptr bc (FEMPTY :: esk.scopes) p /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the iteration *)
    n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    cap <= w2n w /\
    (cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module esk cap) /\
    stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
      (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
      (esk with <| scopes :=
         (FEMPTY |+ (id, <| assignable := F; type := tyv;
                            value := IntV (n1 + &k); popped := [] |>)) :: esk.scopes;
                   gas_obs := [] |>) /\
    gas_admissible (eval_for cx tyv id stmts (IntV (n1 + &k) :: vs))
      (stmt_res_ok lctx) esk ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (do push_scope_with_var id tyv (IntV (n1 + &k));
          finally
            (try (do eval_stmts cx stmts; return F od) handle_loop_exception)
            pop_scope
       od) (esk, cc)
      (\res ee t. ?broke. res = INL broke /\
         t.vs_inst_idx = 0 /\ ~t.vs_halted /\
         stmt_state_rel ctx func cenv cx ee t /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x t = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP t.vs_allocas a = SOME b) /\
         (broke ==> t.vs_current_bb = exit_lbl) /\
         (~broke ==> t.vs_current_bb = cond_lbl /\
                     lookup_var cv t = SOME (i2w (n1 + &(k + 1))) /\
                     lookup_var ev t = SOME (i2w n2) /\
                     lookup_var p t = SOME w))
      (\res ee r. ?ex. res = INR ex /\
         !tail. stmt_exit RetQ (ee with gas_obs := tail) (INR ex) r)

Theorem for_loop_alloca:
  !m P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (* the body, at the iteration states over a source state where P holds *)
    (!ei j.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (* P holds again after an iteration that goes on, whatever the gas *)
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    (* the loop from iteration k *)
    k + m = Num (n2 - n1) /\
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
      (stmt_res_ok lctx) esk /\
    P (esk with gas_obs := []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
      (esk, cc)
      (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
         s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel ctx func cenv cx ee s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b))
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)

Theorem for_loop:
  !m P ctx func cenv bc cx lctx RetQ ty stmts id tyv p sz ainst cv ev dv nv
   n1 n2 cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3
   sb0 sb1 sj st k esk cc w cap.
    (* the code and the variables *)
    for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
      cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
    (!scs. lookup_scopes id scs = NONE ==>
           not_local_ptr bc (FEMPTY :: scs) p) /\
    st.cs_next_var <= sb0.cs_next_var /\ ret_pc_ok cenv st cc /\
    (!x. not_fresh_at st x ==> x <> dv /\ x <> cv /\ x <> nv) /\
    (!ei. P ei /\ cenv.ce_is_ctor ==>
       immutable_prefix_bound cenv cx.txn.target cenv.ce_module ei cap) /\
    (* the body, at the iteration states over a source state where P holds *)
    (!ei j.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) ==>
       stmt_frag ctx func cx (InLoop exit_lbl incr_lbl) RetQ bc
         (stmts_env bc (InLoop exit_lbl incr_lbl) ty stmts) (eval_stmts cx stmts)
         (ei with scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes)) /\
    (* P holds again after an iteration that goes on, whatever the gas *)
    (!ei j gs r2 es2 sc rest.
       P ei /\ lookup_scopes id ei.scopes = NONE /\ j < Num (n2 - n1) /\
       eval_stmts cx stmts
         (ei with <| scopes :=
            (FEMPTY |+ (id, <| assignable := F; type := tyv;
                               value := IntV (n1 + &j); popped := [] |>)) :: ei.scopes;
                     gas_obs := gs |>) = (r2, es2) /\
       (r2 = INL () \/ r2 = INR ContinueException) /\
       es2.scopes = sc :: rest ==>
       P (es2 with scopes := rest)) /\
    n1 <= n2 /\ Num (n2 - n1) < dimword (:256) /\
    (* the loop from iteration k *)
    k + m = Num (n2 - n1) /\
    gas_admissible (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
      (stmt_res_ok lctx) esk /\
    P (esk with gas_obs := []) /\
    cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
    stmt_state_rel ctx func cenv cx esk cc /\
    lookup_scopes id esk.scopes = NONE /\
    lookup_var cv cc = SOME (i2w (n1 + &k)) /\
    lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
    FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w, sz) /\
    cap <= w2n w ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (eval_for cx tyv id stmts (GENLIST (\j. IntV (n1 + &(k + j))) m))
      (esk, cc)
      (\res ee s. res = INL () /\ s.vs_current_bb = exit_lbl /\
         s.vs_inst_idx = 0 /\ ~s.vs_halted /\
         stmt_state_rel ctx func cenv cx ee s /\
         (!x v. not_fresh_at st x /\ lookup_var x cc = SOME v ==>
                lookup_var x s = SOME v) /\
         (!a b. FLOOKUP cc.vs_allocas a = SOME b ==>
                FLOOKUP s.vs_allocas a = SOME b))
      (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
```

Each keeps its existing (old) proof in the file, written for the old
statement; it will fail and is only a starting point.

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build stmtSimForLoopTheory` passes with zero CHEAT warnings in `stmtSimForLoopTheory` and its ancestors, and zero failures.
2. The four statements above are unchanged.
3. No duplicate or near-duplicate lemmas: search the `lowering/` theories before adding a helper; each helper exists once, in its most general form.
4. No change to any definition, and no change to any file outside `lowering/stmtSimForLoopScript.sml`.

**If a theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build stmtSimForLoopTheory
```

## Background

The compiler-correctness proof for Vyper's lowering to Venom IR has changed its
statement judgment. `stmt_frag` now takes the whole source action and its
entry state instead of one fixed source result, because the gas oracle
(`msg.gas`, and the target's GAS instructions) makes the source run depend on
gas readings chosen by the target execution. Its conclusion is `gas_outcome`:
either a `gas_summary_at` (an actual marked target path whose explicit GAS
readings, fed to the source, produce the source result, with a post on a
normal finish or an exit post on an exit), or a `gas_exempt_cert` (an exempt
error carried through the enclosing source structure).

These four theorems are the range `For` loop's round and loop, from the
condition block. The old versions took a fixed body run and a fixed loop run
(`eval_stmts ... = (r2, es2)`, `eval_for ... = (res, es')`) and concluded
`run_from` facts; see `git show HEAD~1:lowering/stmtSimForLoopScript.sml`
for them. The new versions take the round's source action
(`push_scope_with_var`, the body under `try`/`handle_loop_exception`,
`finally pop_scope`, exactly eval_for's step) or the whole `eval_for`, and
conclude `gas_outcome`. Hypotheses that used to talk about the one body run
now quantify over every gas reading sequence `gs`.

`eval_for_rounds` in `lowering/stmtSimForRoundsScript.sml` (already proved)
composes a loop's rounds: give it a counted outcome for each round from the
loop invariant, and a GAS-free path from the invariant after the last value
to the loop's exit. The loop blocks themselves (condition, increment, body
entry) read no GAS.

## Domain Constraints

- No `cheat`, no new axioms, no oracles, no change to definitions (source
  semantics, compiler, or proof-internal judgments such as `gas_exempt_cert`).
- `gas_exempt_cert` is an inductive relation over the syntactic source term:
  a pointwise equality of two sources does not transfer a certificate. Lift
  certificates with its rules (and `vyperStateTheory.bind_assoc` rewriting of
  the source term).
- Every ordinary branch needs an actual counted path (`gas_marked_exec` /
  `gas_marked_path`).
- holbuild's per-step tactic timeout (2.5 s) is fixed: never raise it. A slow
  step is a proof bug; split it.
- Never wrap `metis_tac` or other search in `TRY`/`ORELSE`; select goals with
  `>~`, `>-`, `>|`.
- Proofs at most ~50 lines each; give a hard subgoal its own lemma.
- Follow `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target file | `lowering/stmtSimForLoopScript.sml` | the theorems, `for_code_def`, and the old `run_from`-style block lemmas (`for_cond_block`, `for_incr_block`, `for_body_entry`); counted zero-GAS paths for the condition, body entry and increment don't exist yet |
| Round composition | `lowering/stmtSimForRoundsScript.sml` | `eval_for_rounds` and its helpers |
| Judgments | `lowering/stmtSimDefsScript.sml` | `stmt_frag`, `stmt_framed_frag`, `stmt_res_ok`, `stmt_exit`, `stmt_post` |
| Source semantics | `semantics/vyperInterpreterScript.sml` (`eval_for`, `handle_loop_exception_def`), `lowering/stmtSimForPartsScript.sml` (`eval_for_cons_cases`), `semantics/vyperStateScript.sml` (monad, `bind_assoc`), `semantics/vyperEvalPreservesScopesScript.sml` | |
| Gas outcome | `lowering/gasOutcomeScript.sml`, `lowering/gasSummaryScript.sml`, `lowering/gasSummaryComposeScript.sml` | `gas_outcome`, `gas_summary_at`, `gas_marked_exec`, bind composition |
| Paths | `lowering/fragGasModeScript.sml`, `lowering/fragGasPathScript.sml` (`gas_path_edge`), `lowering/stmtSimPropsScript.sml` (`emit_jump_zero_path`, `assert_jnz_zero_path`) | `gas_marked_path`, `gas_marked_path_then`, zero-GAS path building blocks |
| Exempt certificates | `lowering/gasExemptCertScript.sml` | `gas_exempt_cert` rules |
| Admissibility | `lowering/gasContextScript.sml`, `lowering/stmtSimSeqEnvScript.sml` | `gas_admissible`, `gas_admissible_stmts_tail` |
| Worked compositions | `lowering/stmtSimSeqEnvScript.sml` (`stmt_frag_cons_env`), `lowering/stmtSimIfCountedScript.sml` (`compile_if_stmt_frag`) | two counted outcomes in sequence; a branch with zero-gas blocks around counted fragments |

## Notes

- The round's body judgment is taken at `gas_obs := []`, and the loop's `P`
  at `esk with gas_obs := []`: the certificate bind rules and
  `gas_marked_exec_bind_normal` hand a continuation `mid with gas_obs := []`,
  so after `push_scope_with_var` the body starts there. The counted `If`
  needed the same (`if_branch_outcome_cleanup` in
  `lowering/stmtSimIfPropsScript.sml`).
- `stmt_exit` reads only `es' with scopes := []`, so the popped and unpopped
  exit states agree.
