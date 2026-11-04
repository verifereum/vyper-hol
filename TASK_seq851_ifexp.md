# TASK: Repair the IfExp simulation after the arm-layout copy

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root

## Theorem Statement (FROZEN)

In `lowering/exprSimIfExpScript.sml` (restated: the `~is_word_type t ==>` arm hypothesis is new):

```sml
Theorem compile_ifexp_vv_sim:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (~is_word_type t ==>
     !e. (e = a \/ e = b) ==>
         int_calls_expr e = [] \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!tv es1. (do result <- eval_expr cx c; read_result cx result od) es = (INL tv, es1) ==>
       expr_sim ctx func cenv cx ty a es1 /\
       expr_sim ctx func cenv cx ty b es1) ==>
    !sa sb vv res es' s0.
      compile_expr cenv ty (IfExp t c a b) sa = (vv, sb) /\
      eval_expr cx (IfExp t c a b) es = (res, es') /\ expr_read_res_ok cx es' res /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?tv. res = INL tv /\
                  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 es' tv vv s)
        (expr_exit res)
```

In `lowering/exprSimOperatorsScript.sml` (the `~nocalls ==>` hypothesis is new in the last three; `compile_ifexp_word_case` and `compile_ifexp_sim` are unchanged):

```sml
Theorem compile_ifexp_word_case:
  !nocalls ctx func cenv cx t c a b.
    is_word_type t /\ expr_sim_case nocalls ctx func cenv cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     expr_sim_case nocalls ctx func cenv cx a /\
     expr_sim_case nocalls ctx func cenv cx b) ==>
    expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)
Theorem compile_ifexp_aggregate_case:
  !nocalls ctx func cenv cx t c a b.
    ~is_word_type t /\
    (~nocalls ==>
     !e. (e = a \/ e = b) ==>
         int_calls_expr e = [] \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    expr_sim_case nocalls ctx func cenv cx c /\
    expr_vv_case nocalls ctx func cenv cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     expr_sim_case nocalls ctx func cenv cx a /\
     expr_vv_case nocalls ctx func cenv cx a /\
     expr_sim_case nocalls ctx func cenv cx b /\
     expr_vv_case nocalls ctx func cenv cx b) ==>
    expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)
Theorem compile_ifexp_case:
  !nocalls ctx func cenv cx t c a b.
    (~nocalls ==>
     !e. (e = a \/ e = b) ==>
         int_calls_expr e = [] \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    expr_sim_case nocalls ctx func cenv cx c /\
    expr_vv_case nocalls ctx func cenv cx c /\
    ((?s tv s'. eval_expr cx c s = (INL tv, s')) ==>
     expr_sim_case nocalls ctx func cenv cx a /\
     expr_vv_case nocalls ctx func cenv cx a /\
     expr_sim_case nocalls ctx func cenv cx b /\
     expr_vv_case nocalls ctx func cenv cx b) ==>
    expr_sim_case nocalls ctx func cenv cx (IfExp t c a b) /\
    expr_vv_case nocalls ctx func cenv cx (IfExp t c a b)
Theorem compile_ifexp_sim:
  !cenv ann c e1 e2.
    expr_sim_below cenv (expr_size (IfExp ann c e1 e2)) ==>
    expr_vv_ok cenv (IfExp ann c e1 e2)
```

In `lowering/bodySimExprCasesScript.sml` (`body_ifexp_case` unchanged; `body_ifexp_widened_call_arm` is new and stays `cheat`: it is an approved open obligation of a later piece of work, do not prove or change it):

```sml
Theorem body_ifexp_widened_call_arm:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e3) /\
    body_expr_ok cx e1 ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) es /\
      (?e. (e = e2 \/ e = e3) /\ int_calls_expr e <> [] /\
           ~same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) ==>
      expr_sim ctx func cenv cx ty (IfExp v5 e1 e2 e3) es /\
      expr_vv_sim ctx func cenv cx ty (IfExp v5 e1 e2 e3) es
Theorem body_ifexp_case:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ok cx e3) /\
    body_expr_ok cx e1 ==>
    body_expr_ok cx (IfExp v5 e1 e2 e3)
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
Every other theorem header outside `lowering/exprSimIfExpScript.sml` is frozen too.

## Completion Criteria

- `exprSimIfExpTheory`, `exprSimOperatorsTheory` and `bodySimExprCasesTheory` build with the command below, at the default per-step limit.
- The only `cheat` in these three theories is the existing proof of `body_ifexp_widened_call_arm` plus the cheats already present in `bodySimExprCasesScript.sml` before this task (the `body_intcall_case` family); nothing new.
- No new definitions, axioms or changed premises outside what this file allows.

## Build

```sh
holbuild -j4 build exprSimIfExpTheory exprSimOperatorsTheory bodySimExprCasesTheory
```

## Background

The IfExp lowering changed (`compile_expr_body_def`, `lowering/defs/exprLoweringScript.sml`, the `IfExp` branch, and `compile_ifexp_arm_def` just above it). Each arm used to be `lower_value compile_expr cenv ty arm`; it is now `compile_expr cenv ty arm` followed by `compile_ifexp_arm cenv ret_ty (lowered_value_type cenv arm) vv`. For a non-word result whose arm's lowered type doesn't have `same_memory_layout` with the result type, `compile_ifexp_arm` allocates a fresh buffer of `type_memory_bytes cenv res_ty`, unwraps the arm's value, and copies it in with `compile_store_memory cenv src tmp.buf_operand res_ty arm_ty`. Otherwise it is `unwrap_value`, exactly the old code.

So every proof in `exprSimIfExpScript.sml` that unfolds the lowering (starting with `compile_expr_ifexp`, line 34) is stale. Only `compile_ifexp_vv_sim` is used outside that theory, so the other theorems there (`compile_expr_ifexp`, `compile_expr_ifexp_states`, `ifexp_branch_sim`, `ifexp_arm_frag`, `ifexp_jnz_arm`, `expr_post_ifexp`, ...) may be restated, split, added or removed as the proof needs.

Notes from a read-only audit (not built):
- The `lower_value` monotonicity hypotheses of `compile_ifexp_vv_sim` are now unused; `compile_expr_grows` (`lowering/exprLoweringPropsScript.sml`) and `ci_mono_compile_ifexp_arm` cover the new arm code unconditionally.
- `lowered_value_type` differs from `expr_type` only for String/Bytes literals, `AbiEncode`, Concat-shaped buffers and internal calls. For the rest `same_memory_layout t t` holds and the arm code is the old one.
- The new hypothesis excludes internal-call arms whose layout differs (their `expr_sim` at `expr_type` can't describe a value laid out at the callee's type). The copy branch is then reached by literal/`AbiEncode`-like bytestring arms, whose value is a memory `LocatedValue`, so `unwrap_value` emits no code; the copy reads the source footprint (32 + len bytes) and writes inside the fresh `ALLOCA`, whose id lies in `[sa.cs_next_id, sb.cs_next_id)`.
- `compile_ifexp_case` with `nocalls = T` gets the arm hypothesis from `int_calls_expr (IfExp ..) = []`; `compile_ifexp_sim` uses `nocalls = T`.
- `body_ifexp_case`: case on whether some arm has internal calls and a layout that differs; if so, `body_ifexp_widened_call_arm`; otherwise `compile_ifexp_case`.

## Domain Constraints

- Keep every executable definition unchanged. No new premise, no feature exclusion, no new cheat.
- Search for existing helpers before adding one (`exprSimUnwrap`, `exprSimLiteralBuffer`, `exprSimStorageCopy`, the `compile_store_memory`/`compile_store_bytestring` sims in `lowering/`).
- No `TRY`/`ORELSE` around `metis_tac` or other search. Never raise tactic timeouts. No `holbuild run`/`repl`, no Holmake, no `--skip-*` flags, no `--force`.
- A step timeout at a line you didn't touch is box load: rerun that theory once before treating it as a proof problem.
- Commit proof source only (not task/state files). Commit trailer: `Bot: opus (Claude Opus 5.5)`. Do not push.

## Available Resources

- `lowering/exprSimIfExpScript.sml`, `lowering/exprSimOperatorsScript.sml`, `lowering/bodySimExprCasesScript.sml`: the targets
- `lowering/defs/exprLoweringScript.sml`: `compile_expr_body_def`, `compile_ifexp_arm_def`, `lowered_value_type_def`, `lower_value_def`
- `lowering/defs/contextScript.sml`: `same_memory_layout_def`, `compile_store_memory`
- `lowering/exprSimScript.sml`: `expr_sim_def`, `vv_post_def`, `vv_holds_def`, `vv_at`
- `lowering/exprSimHypsScript.sml`: `expr_sim_case_def`, `expr_vv_case_def`, `expr_body_pre_def`
- `lowering/exprLoweringPropsScript.sml`: `compile_expr_grows`, `ci_mono_compile_ifexp_arm`
- `lowering/exprSimLiteralBufferScript.sml`, `lowering/exprSimStorageCopyScript.sml`, `lowering/exprSimUnwrapScript.sml`: buffer/copy simulations
- `semantics/type/vyperTypeCallGraphScript.sml`: `int_calls_expr_def`

## Notes

The statements were checked by a read-only audit; the restated `compile_ifexp_vv_sim` excludes the one counterexample it found (a widened internal-call arm). Report a counterexample if you find another.
