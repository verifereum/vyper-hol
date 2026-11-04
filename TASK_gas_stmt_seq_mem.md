# TASK: Counted memory-safe statement-list composition

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimSeqMemScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem stmt_frag_cons_env_mem:
  !d ctx func cx lctx RetQ cenv ty stmt ss es.
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_mem d ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss)) (eval_stmts cx (stmt::ss)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `stmtSimSeqMemTheory` builds with the frozen theorem proved and STMT_SEQUENCE_MEM_AUDIT passing.
2. No new admissions, axioms, definitions or strengthened hypotheses. Preserve all existing theorem statements and definitions.
3. Reuse existing helpers; do not duplicate a theorem even if its current copy is local. Keep the five existing stmtSimSeqEnv helpers exported.

## Build

```sh
holbuild -j2 build stmtSimSeqEnvTheory stmtSimSeqMemTheory
```

## Background

This is the memory-safe counterpart of the checked counted statement-list theorem in stmtSimSeqEnv. The source action may consume msg.gas readings. The target path retains checked memory edges, caller return buffers, allocation history and a monotone allocation frontier. Terminal results retain an arbitrary return predicate and its unused readings suffix. The actual consumer is the body statement-list closure; its old fixed-result implementation is being migrated separately.

## Domain Constraints

- The frozen root and every existing definition/theorem statement are unchanged. Internal helper proofs may change. Search for existing equivalents before adding helper theorems, and place shared facts by their definitions.
- The old fixed-result proof body is deliberately retained. Replace it with a checked proof, never with an admission.
- Preserve actual marked execution, memory checks, source exemption certificates, all return cases and oracle quantifiers. No no-GAS restriction or equality of the input/output oracle is authorized.
- Do not change holproject.toml, tactic timeouts, executable semantics, lowering definitions or any other worktree. Do not push.
- Do not wrap proof search in TRY/ORELSE. Default tactic timeout remains enabled.
- Do not import admitted correctness results to discharge the root. The dependency audit must pass.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Frozen root | lowering/stmtSimSeqMemScript.sml | Retained old fixed-result proof and counted memory-safe statement |
| Checked ordinary composition | lowering/stmtSimSeqEnvScript.sml | stmt_frag_cons_env and exported gas_admissible_stmts_head/tail, stmt_post_normal_entry, stmt_post_exception_endpoint, stmt_post_sequence |
| Counted judgments | lowering/stmtSimDefsScript.sml | stmt_frag_mem, stmt_post, stmt_exit and loop control facts |
| Compiler state transport | lowering/stmtSimPropsScript.sml | stmt_env_reserved and return-PC/frame facts |
| Return buffer transport | lowering/bodyMemoryDefsScript.sml | return_buf_frame_frame |
| Marked execution composition | lowering/gasSummaryComposeScript.sml | Actual source-action bind laws |
| Outcome and context | lowering/gasOutcomeScript.sml; lowering/gasContextScript.sml | Counted outcome and admissibility |
| Memory-safe execution | lowering/fragGasPathMemScript.sml | Memory-safe edges, histories and path composition |
| Source exemptions | lowering/gasExemptCertScript.sml | Certificates retaining completed execution prefixes |
| Shared source/target posts | lowering/loweringPostsScript.sml | stmt_lands and environment relations |
| Source scopes | semantics/prop/vyperEvalPreservesScopesScript.sml | Scope-domain preservation (locate by filename if path differs) |

## Notes

Independent source audit found the frozen theorem PROVABLE with its current assumptions and checked the consumer's producer structure. The owner command reached and parsed the theorem, then failed in the retained old proof at line 39: its qpat_x_assum has the obsolete fixed-result arity (11 arguments instead of 10). The five exported helpers and required parent theories built successfully. No theorem statement change is authorized to repair the proof.
