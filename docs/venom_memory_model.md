# Venom Memory Model Design

Status: design draft

## Goal

Venom should support aggressive memory optimizations without inheriting C/LLVM-style undefined behavior.

The semantics should be defined for unsafe programs. Optimizations may require explicit safety or analysis obligations before they can be applied.

```text
No UB in the core semantics.
Optimization power comes from explicit proof obligations.
```

## Current issue

The current executable semantics models `ALLOCA` with:

```sml
vs_allocas     : (num, num # num) fmap   (* inst_id -> (offset, size), current frame *)
vs_alloca_next : num                     (* global concrete bump frontier *)
```

This deliberately backs `ALLOCA` by physical EVM memory: values remain raw words, and memory operations do not need semantic pointer provenance to decide what memory space to access.

That choice is coherent and useful, but it creates proof friction when metadata is treated as observable state:

- `concretize_mem_loc` proves dynamic physical allocation addresses can be replaced by statically chosen physical addresses.
- `function_inliner` must reconcile real callee-frame alloca metadata with cloned inline alloca metadata in the caller frame.
- IRCF/RICF reason about physical regions, dead copied memory, and forwarded pointers through frame-local metadata.
- `result_equiv {}` currently requires exact `vs_allocas` and `vs_alloca_next` equality, which is often stronger than the actual observable semantics.

## Design principle

Separate four concepts:

```text
1. Core word/memory semantics: defined behavior for executing Venom.
2. Dialects/phases: pre-CML has dynamic ALLOCA; post-CML has static concrete addresses and no ALLOCA.
3. Ghost predicates/analyses: obligations that justify optimizations.
4. Equivalence relations: choose what metadata is semantically relevant for a pass.
```

Do not encode optimization assumptions as undefined behavior. Unsafe programs still execute according to the core word/memory semantics; an optimizer simply may not be applicable without its proof obligations.

## Chosen model: physical memory with ghost allocation/provenance facts

Keep runtime values as raw EVM words.

```sml
value = bytes32
vs_memory : byte list
```

`ALLOCA` is backed by physical memory:

```text
ALLOCA sz:
  choose base = current physical allocation frontier
  record inst_id -> (base, sz) in current-frame alloca metadata
  advance the physical frontier
  return n2w base
```

Current state fields:

```sml
vs_allocas     : (num, num # num) fmap   (* inst_id -> (base,size), current frame *)
vs_alloca_next : num                     (* physical allocation frontier *)
```

`vs_alloca_next` is operational allocator state, not observable program output. `vs_allocas` is frame-local allocation metadata used by ALLOCA idempotence, analyses, and proofs. Both should be related only as strongly as a theorem needs.

This avoids semantic pointer provenance:

```text
MLOAD/MSTORE/MCOPY always operate on raw vs_memory addresses.
Pointer provenance is proof/analysis metadata, not needed to choose runtime behavior.
```

## Dialects and safety predicates

Pre-CML and post-CML are different IR dialects, but they share the same raw word/memory execution model.

```text
Pre-CML dialect:
  ALLOCA is present.
  Dynamic allocation chooses physical memory addresses at runtime.
  Ghost allocation/provenance predicates describe which words are alloca pointers.

Post-CML dialect:
  ALLOCA is eliminated.
  Former alloca pointers are statically chosen concrete addresses.
  Memory operations still use raw vs_memory.

Safety predicates:
  constrain programs/analyses but do not change instruction execution.
```

Core predicates:

```sml
alloca_bounds_safe ctx fn
```

All memory operations through alloca-derived pointers stay within the owning allocation's `(base,size)` range.

```sml
alloca_no_escape ctx fn
```

Frame-local alloca pointers are not used after their owning frame returns and do not escape into places where they outlive the frame, unless the pass/theorem explicitly accounts for that behavior.

```sml
alloca_init_safe ctx fn
```

Reads from alloca-backed regions observe initialized bytes when a pass relies on initialized contents.

```sml
provenance_sound analysis ctx fn
```

The analysis/ghost facts that identify alloca-derived addresses, offsets, and regions agree with word-level execution.

```sml
layout_safe amap ctx fn
```

A CML allocation map chooses non-overlapping concrete memory ranges that fit in EVM address space and preserve required raw-memory behavior.

Predicate bundles can define phase names:

```sml
memopt_ready analysis ctx fn <=
  alloca_bounds_safe ctx fn /\
  alloca_no_escape ctx fn /\
  alloca_init_safe ctx fn /\
  provenance_sound analysis ctx fn

cml_ready amap analysis ctx fn <=
  memopt_ready analysis ctx fn /\
  layout_safe amap ctx fn

codegen_ready ctx fn <=
  no_alloca_ops fn /\
  no_phi_ops fn /\
  ...
```

These predicates are ghost obligations. They justify transformations; they are not alternate semantics.

## Pass theorem shape

Most optimization passes are intra-dialect conditional correctness theorems.

```sml
Theorem pass_correct:
  pass_precond ctx fn ==>
  pass_correct R
    (\fuel. run_blocks fuel ctx fn s)
    (\fuel. run_blocks fuel ctx (pass fn) s)
```

Preservation of obligations is separate:

```sml
Theorem pass_preserves_memopt_ready:
  memopt_ready analysis ctx fn ==>
  memopt_ready analysis' ctx (pass fn)
```

Examples:

```text
DSE:
  requires sound dead-store analysis and whatever memory/provenance safety that analysis relies on.

Load elimination:
  requires sound no-intervening-write/load analysis and provenance facts for memory regions.

IRCF/RICF:
  require copy-forward preconditions, no-clobber facts, and sound identification of source/destination alloca regions.

Function inliner:
  requires call/callee well-formedness and an equivalence that ignores dead frame-local alloca metadata while preserving raw memory effects and relevant allocation/provenance facts.

CML:
  requires cml_ready and proves dynamic alloca addresses can be replaced by static concrete addresses.
```

## CML target theorem

CML is the dialect boundary from dynamic physical allocation to static physical layout.

It should not prove equivalence between abstract object memory and raw EVM memory. Instead it proves that, under a safe layout, the dynamically chosen raw addresses used by pre-CML ALLOCA can be replaced by statically chosen raw addresses in post-CML code.

```sml
Theorem concretize_mem_loc_correct:
  cml_ready amap analysis ctx fn /\
  cml_state_rel amap s_pre s_post ==>
  observable_result_equiv
    (run_blocks fuel ctx fn s_pre)
    (run_blocks fuel' ctx (concretize_function amap fn) s_post)
```

The state relation maps pre-CML dynamic alloca regions to post-CML static regions:

```text
pre dynamic region:  inst_id -> (base_dyn, size)
post static region:  amap/out/inst_id -> base_static
relation: bytes at base_dyn+off in pre memory correspond to bytes at base_static+off in post memory
```

CML obligations include:

```text
static regions non-overlap
static addresses fit word/address bounds
all alloca-derived accesses are in bounds
raw memory regions that matter are preserved or shown disjoint
provenance analysis correctly identifies rewritten alloca pointers
```

## Function inliner implications

Original execution:

```text
caller frame invokes callee frame
callee ALLOCAs record metadata in callee frame
callee writes raw memory and advances physical frontier
return restores caller vs_allocas but keeps raw memory effects/frontier
```

Inlined execution:

```text
caller executes cloned callee body
cloned ALLOCAs record metadata in caller frame
raw memory effects/frontier should match the original call behavior
return is rewritten to assignments + jump
```

The observable behavior can match even when allocation metadata differs:

```text
original:    caller vs_allocas only
transformed: caller vs_allocas plus dead cloned-callee entries
```

So function inliner should use a relation such as:

```sml
alloca_meta_equiv live_ids s1 s2 <=
  s1.vs_alloca_next = s2.vs_alloca_next /\
  (!aid. aid IN live_ids ==>
    FLOOKUP s1.vs_allocas aid = FLOOKUP s2.vs_allocas aid)
```

or a pass-specific variant that allows extra dead cloned alloca entries while preserving raw memory, return values, logs/accounts/storage, and future allocator behavior.

## IRCF/RICF implications

Copy-forwarding passes should reason about physical regions described by ghost metadata:

```text
source region and destination region have equal bytes
removed copy writes only to dead destination locations
rewritten uses read from source region in memory-address positions
no intervening clobber invalidates the relation
future ALLOCAs remain compatible via frontier/equivalence assumptions
```

The correctness relation may allow raw memory differences at proven-dead locations, but must preserve live region contents and observable effects.

## Unsafe programs

Unsafe programs are supported by the semantics as ordinary word-memory executions.

```text
out-of-bounds relative to an alloca object:
  not UB in the core semantics; it is a failed safety obligation for passes that rely on alloca bounds.

use-after-frame of an alloca-derived word:
  not UB in the core semantics; it is a failed no-escape/provenance obligation unless explicitly modeled by a theorem.

uninitialized read:
  follows raw memory semantics unless a pass requires initialized-read obligations.
```

Malformed instructions may still produce `Error` as usual. But memory-optimization assumptions should live in predicates, not in undefined behavior.

This preserves support for unsafe/low-level programs while still allowing strong optimizations under explicit obligations.

## Migration plan

### Phase 0: Current semantics, improved relations

Keep the current physical-memory-backed ALLOCA model.

Add pass-specific equivalences where raw `result_equiv {}` is too strong:

```text
- ignore dead alloca metadata where justified
- require allocator/frontier compatibility where future ALLOCA behavior matters
- make memory differences explicit for copy-forwarding dead regions
- distinguish observable state from proof/analysis metadata
```

### Phase 1: Factor allocation/provenance predicates

Add shared theories for ghost facts over the existing semantics:

```text
venom/memory/allocaSafetyDefsScript.sml
venom/memory/allocaSafetyPropsScript.sml
venom/memory/provenanceDefsScript.sml
venom/memory/provenancePropsScript.sml
```

Define:

```text
alloca_bounds_safe
alloca_no_escape
alloca_init_safe
provenance_sound
layout_safe
live/dead alloca metadata equivalence
region/memory equivalence for copy-forwarding
```

### Phase 2: Prove key local lemmas

Prioritize reusable lemmas:

```text
alloca_next_valid implies fresh dynamic allocation
allocated regions do not overlap
writes outside a region preserve that region
reads/writes over corresponding regions preserve layout relation
dead-region memory differences are observationally irrelevant under no-read facts
provenance facts are preserved by ASSIGN/PHI/arithmetic patterns used for pointers
```

### Phase 3: Retarget CML around address-layout relation

Prove CML as dynamic-physical-address to static-physical-address equivalence under `cml_ready`.

### Phase 4: Migrate memory optimization proofs to shared predicates

Move DSE/load-elim/MCE/IRCF/RICF/function-inliner proofs to use shared alloca/provenance/equivalence relations instead of ad hoc state equalities.

### Phase 5: Re-evaluate abstract object semantics only if needed

If physical word semantics becomes a genuine blocker, revisit a tagged `ObjPtr` dialect as a separate design. It is not the current recommendation.

## Open decisions

1. How strong should default `result_equiv` be about allocation metadata?

   Recommendation: observable/execution equivalence should not require exact `vs_allocas` equality by default. Use stronger alloca-metadata relations only for passes that need them.

2. Should `vs_alloca_next` be included in default execution equivalence?

   Recommendation: include it only when future ALLOCA behavior is in scope. For terminal/observable equivalence after CML or at program end, it should usually be irrelevant.

3. What is the canonical provenance representation?

   Options:
   - analysis relation from variables/operands to `(alloc_id, offset)` facts
   - region predicates over evaluated operands
   - lightweight ghost maps in proof state

   Recommendation: start with relation/predicate style, not semantic tagged values.

4. What is uninitialized read behavior for optimization purposes?

   Recommendation: core semantics follows raw memory behavior. Passes that rely on initialized contents require `alloca_init_safe` or a stronger analysis-specific obligation.

5. How much no-escape is needed?

   Recommendation: do not require global no-escape for every memory optimization. State pass-local obligations: e.g. CML needs enough to justify layout; IRCF/RICF need enough to justify rewritten uses and dead destinations.

## Summary

Chosen target:

```text
Venom values remain raw words.
ALLOCA is backed by physical vs_memory and returns a raw address.
Allocation/provenance/escape/bounds facts are ghost predicates and analyses.
Unsafe programs are defined; optimizations require explicit obligations.
CML replaces dynamic physical allocation addresses with static physical layout addresses.
Equivalence relations must avoid treating dead allocation metadata as observable behavior.
```

Rejected as current direction:

```text
Pre-CML semantic ObjPtr values and abstract object memory.
```

That model is principled but invasive. Keep it as a fallback if physical word semantics becomes a proof or expressiveness blocker.
