# TASK: Prove actual internal-call body gas-exception transport

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/gasIntCallBodyScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem gas_exempt_intcall_body:
  !memory tops ctx func cx ty src fn args drv es s0 left values mid t
   ts mut params ret body env tv invoke callee entered right err ee leaf finish.
    ~MEM (src, fn) cx.stk /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (mut, F, params, [], ret, body) /\
    LENGTH args = LENGTH params /\
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr_results cx args) (read_results cx))
      (es, s0) left (INL values) mid (OK t) /\
    bind_arguments (get_tenv cx) params values = SOME env /\
    evaluate_type (get_tenv cx) ret = SOME tv /\
    gas_marked_exec memory (ctx, func) (set_scopes [env])
      (mid with gas_obs := [], t) [] (INL ())
      (mid with scopes := [env]) (OK invoke) /\
    gas_invoke_entry (ctx, func) invoke callee entered /\
    gas_exempt_cert memory tops (ctx, callee)
      (ignore_bind
        (eval_stmts (cx with stk updated_by CONS (src, fn)) body) (return ()))
      ((mid with scopes := [env]) with gas_obs := [], entered)
      right (err, ee) (leaf, finish) ==>
    gas_exempt_cert memory tops (ctx, func)
      (ignore_bind (eval_expr cx (Call ty (IntCall (src, fn)) args drv))
        (return ()))
      (es, s0) (left ++ right)
      (err, ee with scopes := mid.scopes) (leaf, finish)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. The frozen theorem has a checked proof; the exact build below passes with no new CHEAT, parser warnings or failed proofs.
2. No duplicate lemmas: reuse existing results or move/export common helpers beside their definitions. Keep other inherited admissions outside this root's ancestry unchanged.
3. Every executable definition and the gas certificate/origin/mode definitions remain unchanged. The other independent frozen call-wrapper theorem is outside this task.

## Build

```sh
holbuild -j4 build gasIntCallBodyTheory
```

## Background

This theorem transports a concrete compiler gas-exception certificate through the actual source internal-call interpreter. The certificate keeps the target focus endpoint and exact selected source readings. Ordinary and memory-safe target paths retain their distinct entry domains. Internal calls capture argument results before reading them, execute the source scope cleanup, and preserve the original certified exemption origin.

## Domain Constraints

- The theorem, definitions, hypotheses and exemption gates are frozen. No new axiom, final cheat, generic source-equivalence certificate rule, opcode-absence restriction or additional stage/top-level hypothesis.
- Keep default tactic timeout, checkpoints and proof steps. Do not raise limits or use TRY/ORELSE to filter proof search.
- Do not edit other independent main theorem statements or replace existing proof code with a placeholder.
- No new evaluator or synthetic source semantics. Use actual interpreter operations and concrete existing certificate rules.

## Available Resources

- lowering/gasIntCallBodyScript.sml: the assigned frozen root.
- lowering/gasExemptCertScript.sml: concrete origins, typed sequencing, cleanup, handlers, saved scopes and actual INVOKE entry.
- lowering/gasExemptOriginScript.sml: fixed Convert/ABI origins with full normal child post.
- lowering/gasSummaryScript.sml and gasSummaryComposeScript.sml: marked source/target execution and composition.
- lowering/fragGasFocusScript.sml and fragGasModeScript.sml: exact target call entry and execution modes.
- semantics/prop/vyperCallScript.sml: shared internal-call source normalization and empty defaults.
- semantics/vyperInterpreterScript.sml and semantics/vyperStateScript.sml: actual call, scopes, monadic operations and source result types.

## Notes

The exact statement and the concrete get_scopes certificate rule have been independently checked against their definitions. A counterexample must exercise this stated relation, preserving its concrete origin provenance.
