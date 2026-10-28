# TASK: Repair the internal-call callee prologue proof

## Meta
Status: planned
Priority: P1
Created: 2026-10-28
Location: lowering/intCallCalleeScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem mat_stack_head_run[local]:
  !func cenv env st s mid f0 mr name off sz p caps.
    mat_inv func cenv env st s f0 mr /\
    mat_pending cenv env st s f0 mr ((name,T,Var p)::caps) /\
    ~MEM name (MAP FST caps) /\
    FLOOKUP cenv.ce_vars name = SOME (MemLoc off sz) /\
    mid.cs_next_var = st.cs_next_var + 1 /\ mid.cs_next_id = st.cs_next_id + 2 /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
           [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
    fn_inst_ids_distinct func /\ s.vs_alloca_next + sz < dimword (:256) ==>
    ?t. run_inst_seq
          [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)]
             [STRING #"%" (toString st.cs_next_var)];
           mk_inst (st.cs_next_id + 1) MSTORE
             [Var (STRING #"%" (toString st.cs_next_var)); Var p] []] s = OK t /\
        mat_inv func
          (cenv with ce_vars updated_by
            (\m. m |+ (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) sz)))
          env mid t f0 mr /\
        mat_pending
          (cenv with ce_vars updated_by
            (\m. m |+ (name, PtrVar (Var (STRING #"%" (toString st.cs_next_var))) sz)))
          env mid t f0 mr caps /\
        mat_frame st s t /\ t.vs_alloca_next = s.vs_alloca_next + sz
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
All pre-existing theorem statements, attributes and definition bodies in
`lowering/intCallCalleeScript.sml` are also frozen. Proof bodies may be repaired.

## Completion Criteria

- `intCallCalleeTheory` builds through its final exported theorem with no failed
  proof, parser warning, admission or undischarged hypothesis.
- Preserve every pre-existing definition, theorem statement and attribute exactly.
  Add no supported-subset checks or stronger hypotheses.
- Keep the repair focused on this theory and necessary reusable helpers. Existing
  compiler behavior, source language semantics and ABI consolidation contracts
  remain unchanged.
- Commit the checked source changes. The supervisor performs separate forced,
  checkpoint-free/cache-free CI-flags certification and declaration comparison;
  do not block completion on command-line flags absent from your build tool.

## Build

```sh
holbuild --max-heap 7000 -j2 build intCallCalleeTheory
```

## Background

The callee prologue materializes stack-passed internal arguments with ALLOCA and
MSTORE before establishing the callee statement-state relation. The existing
proof of `mat_stack_head_run` fails during a base-branch integration; repair the
proof while preserving the existing API. The rest of this theory must continue
to build. No unproved replacement or altered theorem contract is acceptable.

## Domain Constraints

- Use holbuild and the normal proof-step timeout. Never raise or disable it.
- No axioms, admissions, `cheat`, hypotheses strengthened for convenience, or
  `TRY`/`ORELSE` around proof search.
- No interactive proof-state workflow and no hol4-mcp.
- Reuse existing definitions; do not encode the desired conclusion in a new
  invariant. New helper statements must be independently provable.
- Do not edit unrelated encoder proofs, fixtures, workflows or build roots.
- Only this Alan instance may mutate its task state. Keep other tracked files
  and task files untouched.

## Available Resources

| Resource | Location | Purpose |
| -- | -- | -- |
| Callee proof and invariants | `lowering/intCallCalleeScript.sml` | Materialization, framing, prologue exports |
| Local pointer relation | `lowering/localPtrsPropsScript.sml` | Source values and pointer regions |
| Fragment execution | `lowering/fragExecScript.sml` | Execution/framing helpers |
| Memory effects | `venom/props/venomMemPropsScript.sml` | ALLOCA/store and region facts |
| Allocation definitions | `venom/defs/venomMemDefsScript.sml` | Allocation state and invariants |
| Value representation | `lowering/valueEncodingPropsScript.sml` | Source value/byte representation |
| Generated signatures | `.holbuild/obj/lowering/` | Existing exported theorem interfaces |
| Build configuration | `holproject.toml` | Pinned HOL/dependencies |

## Notes

The existing CI failure is `mat_stack_head_run`, the `by` proof block beginning
at line961 of the pre-repair source. Its statement already parses and the earlier
lemmas are saved before the failure. A semantic preflight classified the statement
as PROVABLE against its existing invariants/helpers; this is not build evidence.
Other failures in this same theory may be repaired with their statements frozen.
