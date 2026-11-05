# Concrete barrier-order producer probe (C1.4.9.5)

## Result: canonical bridge is missing at the actual scheduler

The proposed use of `canonical_tc_incomp_not_barrier` does not currently have
the required producer. This is an interface diagnosis, not a counterexample to
the frozen theorem or a proof that the desired barrier exclusion is false.
No conditional nonbarrier helper or new scheduler induction was introduced.

### Actual definitions, not the alternate full-EDA model

* `venom/passes/dft/defs/dftDefsScript.sml:235-237`:

```sml
dft_eda block_insts = add_abort_run_deps block_insts (build_eda block_insts)
```

* The same file, 574-583, defines **`dft_block order bb`** (two arguments):
  it prepends the pseudo filter to `schedule_from_entries bb.bb_instructions
  order eda offspring_map entries`, with **eda = dft_eda bb.bb_instructions**.
  No fallback to original order occurs in this definition.
* `schedule_from_entries_def:547-555` takes exactly the output of a bounded
  FUNPOW DFS execution, initialized with process tasks for entries. There is
  no check/fallback replacing that output with a full-EDA schedule.
* The different definition `build_full_eda_def:306-310` uses
  `add_alloca_deps (add_barrier_deps (add_abort_deps (build_eda ...)))`.
  Barrier dependencies therefore cannot be transferred to dft_eda by simply
  unfolding build_full_eda. These are different dependency constructions.

### Existing relevant checked interfaces

`dftCanonicalDepScript.sml:330-336` exports:

```sml
!bi x y.
  MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
  MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
  x <> y /\
  ~TC (canonical_dep bi) x y /\ ~TC (canonical_dep bi) y x ==>
  ~is_barrier x /\ ~is_barrier y
```

`dftCorrectnessScript.sml:9010-9015`,
`canonical_dep_imp_full_dep_local`, exports:

```sml
!bi x y.
  ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
  canonical_dep bi x y /\
  from_block bi x /\ from_block bi y ==>
  full_dep (build_full_eda bi) x y
```

Its conclusion is **not** full_dep (dft_eda bi) x y.
`topo_sorted_full_dep_dft_eda` (1939-1941) only weakens
`topo_sorted (full_dep (dft_eda bi)) l` to
`topo_sorted (full_dep (build_eda bi)) l`; it does not strengthen to
canonical_dep or build_full_eda.

`topo_sorted_tc_closed` (2002-2006) requires topo_sorted dep, ALL_DISTINCT l,
and closure of every dep endpoint on l, before producing topo_sorted (TC dep).
The orientation of topo_sorted is consumer-to-producer: an earlier list
position cannot depend on a later one. It cannot supply missing canonical
edge preservation. `canonical_dep_cross_bi_equiv`
(`dftCorrectnessFinalScript.sml:86-96`) handles representative ID equivalence,
but also does not establish topological order of a concrete dft_block.

### Exact requested producer, still unproved

Correcting the probe's one-argument notation, the desired statement is:

```sml
wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
EVERY inst_wf bb.bb_instructions /\
ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
MEM x bb.bb_instructions /\ MEM y bb.bb_instructions /\
~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id y.inst_id /\
id_before (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions)
  y.inst_id x.inst_id ==>
~is_barrier x /\ ~is_barrier y
```

These premises are an intended consumer envelope, not asserted minimal or
sufficient premises: there is no proof of this statement in this checkpoint.
It remains particularly important to test ALLOCA, whose allocation chain is
present in build_full_eda but not explicitly installed in dft_eda. This report
does not assume canonical incomparability as a new hypothesis.

### Premise provenance and consumer mapping

| Required item | Status |
|---|---|
| x/y membership in nonpseudo filter | original membership plus nonpseudo, by MEM_FILTER |
| x<>y | source strict ID order plus unique IDs |
| source topo order for canonical_dep | must justify under SSA/shape and actual body filtering; not inferred merely from list order |
| target topo order for canonical_dep | MISSING: actual scheduler uses dft_eda, whereas checked canonical bridge targets build_full_eda |
| both negative TC facts | cannot obtain from opposite source/target ID orders without both topo facts, endpoint closure and representative bridge |
| flipped target representatives | from_block allows flip_operands; IDs are stable, but TC/order lifting still required; record equality must not be assumed |
| exclusion of allocation after nonbarrier | immediate from is_barrier_def, once its antecedent is genuinely produced |
| exclusion of INVOKE after nonbarrier | immediate: is_volatile INVOKE = T (`venomInstScript.sml:451`), and is_barrier includes is_volatile |

In the occurrence-ID normalization invariant of dftGasInvExchangeDesign.md,
each adjacent inversion would instantiate the displayed producer using its
original representatives x,y, original source order and reversed scheduled
order. If proved, its local ~is_alloca_op conclusions would permit a new local
swap-contract derivation using the SSA/effect argument of
`dft_crossing_swap_pair`; one must not apply that existing theorem with its
unproved block-wide EVERY non-alloca premise. It would exclude INVOKE from
each *exchange pair*, not from the entire consumed trace. Since the producer
is missing, neither exclusion is available at that consumer today.

## Review request

Per the bounded probe instruction, stop here rather than launching a new
scheduler induction. The key question is whether concrete dft_eda inversions
actually exclude all barriers. The canonical/build_full_eda bridge alone
cannot justify that claim. A next bounded computation could test ALLOCA/pure
inversions in the actual dft_block definition before any attempt to prove the
producer or use it to eliminate same-context INVOKE. No weakening of the
frozen statement, block-wide allocation exclusion, or actual oracle exchange
has been implemented.
