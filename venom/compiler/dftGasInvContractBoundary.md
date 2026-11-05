# Corrected task-contract premise audit

`dft_fn_rel_def` (dftRunRel) explicitly requires
`EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn)`.
The frozen theorem's second LIST_REL premise supplies this relation for every
matched function. It is not necessary to infer allocation exclusion from
`o1_ctx_shape`, from order inversions, or from `build_full_eda`.

The new boundary has signature:

```
dft_fn_rel fn fn' /\ MEM bb fn.fn_blocks ==>
EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions
```

`inv_dft_fn_rel_block_no_alloca` reuses the existing general
`ctxLookupAgreeHelpers.EVERY_fn_block` (EVERY over fn_insts plus block membership
implies EVERY over the block), then classifies opcodes with `is_alloca_op_def`.
DALLOCA is not excluded. No duplicate list/block transfer lemma was introduced.

`inv_alloc_probe_outside_contract` proves the actual-function allocation/pure
witness from the preceding diagnostic cannot satisfy `dft_fn_rel` for any target
function. Thus its checked inversion does not obstruct equality-based exchange
under the full task contract. The other allocation rows also contain ALLOCA;
the report's limited consumer envelopes must not be confused with dft_fn_rel.
No allocation-renaming invariant is required on account of those examples.

This closes only the missing no-ALLOCA producer. Fixed-oracle one-success
exchange, returning-call replay, source-prefix extraction, and cross-context
reflection remain separate obligations. The frozen theorem and definitions
were not modified.
