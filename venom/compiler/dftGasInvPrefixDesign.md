# C1.4.3: oracle prefix boundary diagnostic

This report proposes interfaces; it is not a proof of simulation.

## Checked boundaries

| Source | Exact relevant interface / limitation |
|---|---|
| dftGasInvCallBoundaryScript.sml:5 | `ev_step_invoke_OK`: opcode INVOKE and an OK step expose decode, lookup, eval_operands, setup, an actual `ev_blocks orc ((d,id)::p) d fuel ctx callee cs = IntRet ret cs'`, and bind_outputs. No termination assumption. |
| dftGasOracleDefsScript.sml:68 | `ev_block` uses the same fuel and depth for every instruction. Nonterminating OK steps increment vs_inst_idx; successful terminators return OK or Halt. |
| dftGasOracleDefsScript.sml:83 | `ev_blocks ... (SUC fuel) ...` executes phis and `ev_block ... (SUC d) fuel ...`; a successful block continuation recurses at fuel and SUC d. |
| dftGasOracleDefsScript.sml:121 | `ev_function` initializes label and index and starts `ev_blocks` at path [] and depth 0. |
| dftGasOracleDefsScript.sml:130 | `ev_context` looks up entry and clears vs_prev_bb. |
| dftGasOracleDefsScript.sml:156 | reachable next permits a fresh existential fuel at EVERY step. For an INVOKE the above inversion exposes its finite returning callee computation. |
| dftGasOracleDefsScript.sml:164 | reachable block changes depth to SUC d and applies enters_block. Terminator success must be reflected as well. |
| dftGasOracleDefsScript.sml:171 | reachable callee needs no returning computation; setup and entry suffice. It extends path by (d,id) and increments depth. |
| dftRunRelScript.sml:16 | dft_res_rel is directional; source Error excludes target OK/IntRet but allows target Halt/Abort. Successful source runs give exact results. |
| dftRunRelScript.sml:116 | dft_fn_rel includes SSA, wf_function, instruction well-formedness, pseudo prefix, no ALLOCA, LIST_REL block relation, fallible order. |
| dftRunRelScript.sml:2939 | dft_run_block_gas assumes SSA/function wf, membership, EVERY inst_wf, no alloca ops, unique IDs, block relation, pseudo prefix, strict_dom_vars_defined, nonstatic call context, label binding, and abort-order preservation. It concludes existence of a gas-readings-adjusted input and dft_res_rel between two run_block executions at the SAME fuel and context. Not an oracle execution or changed-context result. |

## Proposed returning-run boundary (unproved)

A first exact statement to investigate, with equal input state and explicit fuel:

```sml
!orc p d fuel C D fn gn cs ret ts.
  LIST_REL dft_fn_rel C.ctx_functions D.ctx_functions /\
  dft_fn_rel fn gn /\ o1_ctx_shape C /\
  ctx_labels_bound C cs.vs_labels /\ o1_run_state_ok cs /\
  strict_dom_vars_defined fn cs /\
  ev_blocks orc p d fuel D gn cs = IntRet ret ts ==>
  ?ss. ev_blocks orc p d fuel C fn cs = IntRet ret ss /\
       gas_variant ss ts
```

This is NOT validated. In particular `strict_dom_vars_defined fn cs` must be checked at setup, after phis and across jumps; it cannot simply be assumed at every reachable call. Whether same fuel is sufficient needs proof that corresponding blocks take the same control flow. Calls must transport fn metadata used by setup_callee, not merely fn_name. No missing premise is silently considered established.

For a two-input generalized version, replace the common cs with cs/ct and add `gas_variant cs ct`; before accepting that generalization check every step_inst_base consumer for gas-readings dependence and the exact projections needed by strict_dom_vars_defined. The frozen target only supplies one initial state. The simpler common-input version is therefore a design candidate, not a reason to exclude later invariant generalization.

## Induction parameters and gaps

Outer complete induction on fuel, generalized over path, depth, contexts, related functions and call states. At SUC fuel, block semantics calls ev_block at fuel; any INVOKE there calls ev_blocks at fuel, so the outer IH is available. Inside ev_block, fuel does not decrease: a separate finite instruction-list/permutation argument is mandatory. Successful target returns alone cannot be reflected using dft_run_block_gas, whose existential modified GAS input is fundamentally different.

A conditional oracle block theorem must assume smaller-fuel IntRet reflection for every related callee and every valid setup state; it should conclude backward successful block-result correspondence. Its proof needs oracle-aware commutation and readiness, including steps that might abort. Syntactic non-INVOKE locality is trivial but does not itself establish commutation or availability.

For reachability, equal states at equal instruction indices are invalid. A residual-source-list invariant must identify already executed instructions, current common block entry, available SSA definitions and effect ordering. It must expose operand agreement at a selected target instruction plus initial FMP agreement; earlier source instructions must actually succeed to construct a source reachable witness. Keeping incompatible aborts in order alone is not a success proof. The report intentionally does not invent a residual execution predicate or assert a missing success lemma.

Next strategist decision: choose an oracle-aware conditional block interface and its preserved state invariant, then explicitly discharge setup/phi/jump preservation before the finite-run or reachability theorem. Avoid a whole reachability induction with an unproved call-return premise.
