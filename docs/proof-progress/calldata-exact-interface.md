# Exact calldata decoder interface checkpoint (C1.9.4)

## Scope and status

This is an **interface diagnostic**, not an exact decoder proof, a receiving-cone
qualification, or a proof of either S1 target. No new semantic relation, axiom,
or admitted theorem is introduced. The diagnostic theory is
`lowering/calldataExactInterfaceProbeScript.sml`; its ML quotations are **terms,
not theorems**. Its checks inspect actual existing theorem statements.

Build: `holbuild(targets=["calldataExactInterfaceProbeTheory"])`.
The build validates the expanded schema's HOL types, absence of unintended free
parser variables, child-map substitutions, and the five bounded statement checks
below. It does not discharge a constructor's mathematical obligations.

## Expanded candidate interface

The full, non-abbreviated HOL quotation is `exact_decoder_contract` in the
companion diagnostic script. Its only free parameters are `ce env sf ty tv`
(also printed and checked at build time); all compiler intervals, ambient limit,
states, allocations, operands and ghosts are quantified. The universal closures
`universal_array_child`, `universal_struct_child`, and
`universal_positional_child` close these five parameters too. These are the
candidate higher-order hypotheses for conditional constructors, **not supplied
facts**.

The input includes the following HOL clauses (the script contains all clauses,
including complete scratch-site and phi-prefix conditions):

```sml
abi_decoder_coherent ce env sf ty tv /\
compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
  (type_to_abi_dec_info sf ce ty) st = ((),last) /\
fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
last.cs_next_var <= limit.cs_next_var /\
fresh_vars_wrt limit initial /\
unit_alloca_budget ctx < dimword (:256) /\
eval_operand src initial = SOME p /\
eval_operand (Var child) initial = SOME (n2w d) /\
abi_decoder_operand_live st.cs_next_var src /\
abi_decoder_operand_live st.cs_next_var (Var child) /\
alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
(oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
d+type_memory_size tv < dimword (:256) /\
ptr_covers G tn child initial (type_memory_size tv) /\
op_taint tn src = {} /\ op_prov G src = NONE /\
allocas_from lower initial /\ lower <= initial.vs_alloca_next /\
~ctx_has_dalloca ctx /\ ~initial.vs_halted /\
initial.vs_current_bb = st.cs_current_bb /\
initial.vs_inst_idx = LENGTH st.cs_current_insts
```

The rejection alternative fixes witnesses **before** dead-set quantification:

```sml
cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
?z H u. z.vs_returndata = [] /\
  (?fuel. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) /\
  (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
    (initial,G,tn) [] (Abort Revert_abort z,H,u))
```

The success alternative begins:

```sml
?v x sc H u.
  cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
  ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
  v.vs_inst_idx = LENGTH last.cs_current_insts /\
  value_has_type tv x /\ val_wf tv x /\
  val_in_memory tv x d v.vs_memory /\ ...
```

Here `...` is documentation only, not a HOL abbreviation or hypothesis: the
script's expanded quotation spells out safe continuation transport, unchanged
call context/data section, allocation invariant/frontier and scratch ownership,
monotone allocation frontier, preservation of old allocations and old operands,
allocation equality outside the instruction interval, footprint framing and
scratch support, `fresh_vars_wrt limit v`, `ptr_covers H u child v`, old
variable provenance/taint preservation, memory-taint inclusion, unchanged
storage/transient/immutable taints, and finally

```sml
!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
  (initial,G,tn) [] (OK v,H,u)
```

No witness is chosen separately for each `D` or `explicit`.

## Five bounded boundary tests and concrete residuals

### 1. Scalar clamp

Inspected `calldataClampPtr.calldata_clamp_overwrite_prefix_uniform_origin`
(lines 537–569) and the finite typed word supplier. The build checks that the
clamp theorem has a `run_inst_seq` premise and no `cd_decode` output.
The exact residual is

```sml
run_inst_seq (emitted_insts sa sb) s = OK t
```

Clean scalar provenance (`op_prov G op = NONE`) is independently required,
not implied by empty taint. The clamp supplier gives common successful endpoint
state/ghost witnesses and a zero-event origin path, but only **after** a
successful clamp run has been supplied. It does not construct rejection or
identify clamp truth/failure with source `cd_decode`. Needed: arbitrary-input
clamp outcome/source correspondence, including empty-data ASSERT rejection,
plus framing of the fresh load result. An unrelated memory-only
revert-or-typed-success cannot decide which source alternative holds.

### 2. Bulk success

Inspected `calldataBulkUniformPtr.calldata_bulk_decoder_endpoint_ptr_uniform_origin`
(lines 156–179). The build checks successful `run_inst_seq` is an input and a
uniform origin path, but not `cd_decode`, occurs in its output. It additionally
requires a concrete count observation

```sml
abi_decode_load CALLDATALOAD a s = n2w n
```

and `32+n*mem_sz <= capacity`, `d+32 < dimword (:256)`, and
`n*mem_sz < dimword (:256)`. Its path requires
`d+32+n*mem_sz <= s.vs_alloca_next`. A destination allocation/end bound can
supply this only after the count/capacity arithmetic has been established.
The supplier already chooses `H,u` before `!D explicit`; reuse it for success.
Needed separately: source-exact count/bounds and payload value, successful
execution, and each rejecting guard's uniform empty-data path. No theorem
failure or missing premise of an admitted contract has been demonstrated here.

### 3. Recursive array child

Inspected `calldataRecursiveExecution.calldata_recursive_nonbulk_owned`
(lines 21–120; local conditional shell) and its public
`calldata_coherent_owned_run`. The build checks the public result has
`val_in_memory` but neither `cd_decode` nor `gas_origin_ptr_path`.
The local shell quantifies child compiler states and child run states; its
child result is only memory-safe rejection or typed memory success.
Needed for the exact join: at each iteration compute the actual source member
position, retain accepted prefix values, choose common child state/ghost
witnesses, carry the ambient freshness limit, frame parent root/counter and
scratch allocations, and compose the shared zero-event path. The expanded
array child quotation keeps `env,sf` and the ambient `limit` unchanged; its
universal closure permits each varying state/interval/ghost instantiation.
It is not a discharge of those premises at a loop header.

### 4. Struct child

`abiDecoderCoherence.abi_decoder_coherent_struct_iff` (lines 106–116) gives

```sml
LIST_REL (abi_decoder_coherent ce (env \\ nsid)
  (sf \\ nsid_to_string nsid)) (MAP SND args) tvs
```

The typechecked `struct_child_contract` substitutes **both** maps in the
entire expanded schema; `ce` remains unchanged. Parsing substitutions in the
schema's context is necessary to avoid independently inferred map types.
Needed: member source offsets and destination suballocation bounds, empty
source taint/provenance after navigation, preservation of prior fields and
scratch support, and uniform accepted-prefix/rejected-child composition.
Using full `sf` or deleting only `env` is not the coherence induction's child.
The bounded test validates substitution/type shape, not those execution facts.

### 5. Positional registration

`calldataRegistrationExec.registration_positional_owned_run` (lines 1415–1462)
provides allocated typed outputs and a memory-safe continuation or revert.
The build checks its result contains allocations and typed memory but no
`calldata_decode_args` or uniform origin path. Its decoder metadata uses
`abi_decoder_coherent ce env ce.ce_struct_fields`; the positional child quote
substitutes this `sf` exactly. Allocation IDs must initially be absent from
the whole registration instruction interval. Needed: correlate each output
with its source argument and dynamic/static head offset; advance accepted
prefixes until the first `NONE`; preserve root/caller ghosts through the
allocation/navigation prelude; retain empty returndata and shared uniform
ghosts on rejection. `calldata_decode_args = NONE` alone cannot select the
revert branch of this memory-only disjunction.

## Ambient freshness check

`fresh_vars_wrt_mono` transports freshness only to a **larger** counter:

```sml
fresh_vars_wrt st ss /\ st'.cs_next_var >= st.cs_next_var ==>
fresh_vars_wrt st' ss
```

Thus `last.cs_next_var <= limit.cs_next_var` and freshness at `limit` do not
supply freshness at `last` or at a smaller child compiler state. The schema
requires the child to preserve freshness at the *same* ambient `limit`.
A concrete `%0` freshness probe was attempted, did not close, and was removed;
there is **no checked freshness counterexample theorem** in this delivery.
No task target or supplier is claimed false. This diagnostic relies on the
actual direction of the existing monotonicity theorem, not that failed probe.

## Conclusion for planning

The expanded terms typecheck and the existing suppliers' output strengths are
now mechanically distinguished. The five residual lists above remain proof
obligations. In particular the current memory-only induction cannot simply be
joined to success-only uniform pointer endpoints to obtain source-exact
rejection. This receipt does not release any Risk-3 construction automatically;
the strategist must account for source observations, ambient freshness and
uniform ghost composition before authorizing those construction leaves.
