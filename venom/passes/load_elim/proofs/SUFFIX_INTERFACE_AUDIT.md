# Latest-join suffix interface audit (C1.P.4.2.3.4.2.12)

This is a diagnostic proposal, NOT a theorem, axiom, or new premise of the
frozen result. No consumer-currentness claim is certified here.

## 1. Exact source goal and shared hypotheses

In the signatures below `H` is a **textual abbreviation only** for this
conjunction (not a proposed HOL constant):

```
wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
(!v. bp_get_ptrs ctx.lctx_bp v = []) /\
ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
fn_entry_label fn = SOME s0.vs_current_bb /\
is_fixpoint (df_process_block Forward NONE load_join load_transfer
  load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
  (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
  (load_analyze ctx fn) /\
le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
(!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
  (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u')
```

Proposed actual-action source interface, expanding H at declaration time:

```
H /\
compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key
  s.vs_current_bb i = SOME pa /\
bb.bb_label = pa.pa_join_lbl /\
i.inst_opcode = ctx.lctx_config.lc_load /\
i.inst_operands = [addr] /\
key = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
  (normalize_operand ctx.lctx_dfg []) i /\
FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
  s.vs_current_bb s.vs_inst_idx)) key = SOME ops /\
1 < LENGTH ops /\
(!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl)
==> le_key_read ctx.lctx_addr_space key u =
    le_key_read ctx.lctx_addr_space key s
```

The load-shape and point lookup must be linked to the actual action use site,
not merely to an arbitrary action returned for some other instruction. The
candidate is not asserted proved or sufficient for all subsequent rounds.
The local sufficient certificate below deliberately separates this remaining
static extraction obligation from semantic read preservation.

## 2. Capture's ORIGINAL PHIs: no-write justification exists

`le_phi_definition_key_cut` already proves that a reachable PHI output `v`
forces the index-zero lookup of `LK_Op (Var v)` to be NONE. It is NOT
singleton-restricted. Thus any SOME ops at the capture block's index zero
excludes its address variable from **all original PHI outputs**. Use
`le_occ_phi_static`, `le_phi_prefix_take`, and `phi_prefix_all_phi` exactly
as in `le_retained_occ_key_no_write`, but replace its singleton predicate
by index-zero presence. `le_ordinary_definition_key_cut` likewise excludes
an ordinary output from a key present immediately before that instruction.
Neither requires simultaneous evaluation of the alternatives.

`le_absolute_key_occ_after` then transports the address across the capture
PhiOcc; `le_phi_read_occ_after` transports fixed-address reads. The chain
must start at u, INCLUDE `PhiOcc bb u p`, and end at s. Starting only at p
would omit the key-address hazard. LK_Loc is handled by
`le_absolute_location_address`; literal LK_Op needs no variable no-write.

## 3. Exact sufficient retention certificate and its missing extraction

For every StepOcc b n k x y in `PhiOcc bb u p :: suffix`, require

```
?vs. 1 < LENGTH vs /\
 FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
   b.bb_label n)) key = SOME vs /\
 FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
   b.bb_label (SUC n))) key = SOME vs
```

For every PhiOcc b x y in that list, require

```
?vs. 1 < LENGTH vs /\
 FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
   b.bb_label 0)) key = SOME vs
```

Lists may DIFFER between blocks. The sufficient semantic signature is H,
these two universal membership conditions, and
`le_absolute_key ctx.lctx_addr_space key`, implying the equality in section
1. Address existence need not be a new premise: if its value at u is NONE,
address transport makes both key reads NONE; if SOME a, word evaluation or
the absolute-location shape gives a < dimword (:256).

Missing local generalizations: `le_configured_retained_step_read` and
`le_retained_occ_read` currently take SOME [op] and non-generation. For a
multivalue output no generator can have overwritten that key (generators
write singletons). Store invalidation membership and nonstore effect lemmas
in TransferRetention are singleton-shaped although their proofs only use
presence plus exclusion of overwrite. Reuse `le_retained_store_regions`
and the region/read interfaces; do not duplicate their alias analysis.
`le_occ_chain_retained_read` is ALREADY general enough once local read
preservation and address no-write are established.

Missing STATIC extraction from section 1: reverse the find_join walk along
the actual suffix, stopping at its latest join occurrence. For each FULL
intermediate block use `le_two_distinct_boundary_preserves` and
`le_analyze_boundary_preserving_reverse`; reverse inclusion gives a superset,
not an identical list. Transport two distinct alternatives. For the PARTIAL
consumer block use `le_analyze_multivalue_origin` and the transfer-fold
multivalue-through-prefix fact, not a theorem about its final boundary.
At capture only its input and executed prefix need retain the key; do NOT
require its whole block fold to preserve if capture and consumer coincide.
PHI transfer is identity; `le_analyze_phi_prefix_lookup` supplies the bridge.
Point support gives ALL_DISTINCT before length is used to choose two values.
Placement alone does not export these per-occurrence conditions yet.

## 4. Target extension/framing and exclusion of recapture

Existing EXACT extensions (OperationalHistory) are:

```
le_oper_history r h /\
step_inst fuel C j (le_history_end r h) = OK t
==> le_oper_history r (h ++ [(set j.inst_outputs,t)])

le_oper_history r h /\ eval_phis (le_history_end r h) js = OK t
==> le_oper_history r (h ++ [(le_phi_outputs js,t)])
```

`le_oper_history_neutral_extend` handles index/edge normalization; use the
actual normalizations from occurrence semantics. `le_oper_history_frame`
then derives framing, rather than assuming framed target execution.

Needed syntactic interfaces (not present as named load-elim theorems):

```
set (load_elim_inst ctx actions ll inst).inst_outputs SUBSET
  set inst.inst_outputs

le_phi_outputs (phis_for_block actions lbl ++ rest) SUBSET
  ({a.pa_phi_out | MEM a actions /\ a.pa_join_lbl = lbl} UNION
   le_phi_outputs rest)
```

The first follows from `load_elim_inst_changed` and shared mk_assign/mk_nop
definitions (NOP clears outputs). The second uses generated PHI shape and
its leading-PHI prefix, not an assumption that all of rest is PHIs.
For source-origin instructions, prefix freshness excludes pa.pa_phi_out.
For inserted outputs, `le_collected_action_outputs_distinct` says any action
writing pa.pa_phi_out equals pa; latest join selection excludes that action's
label from later PhiOccs. This excludes writes to ONE selected captured
output, not to every generated variable forever. Normalization events have
empty write sets. Derive zero epoch and use history lookup persistence.

## 5. Target rest-PHI success is not automatic

`execEquivParamBase.eval_phis_agreement` is NOT an appropriate interface
for the frozen padded-memory relations: `valid_state_rel_def` requires exact
`vsr_frame` equality, including memory. Differing trailing zero bytes violate
that requirement. Do not attempt to discharge it with variable agreement.

The checked replacement is `loadElimPhiTransportTheory`:

- `le_snapshot_batch_transport` transports successful snapshot batches and
  relates their results under any relation closed under paired identical
  `update_var` operations. Reads always use the original incoming snapshots.
- `le_eval_phis_transport` specializes this to the leading PHI prefix.
- `le_eval_phis_prefix_eq` gives exact result equality for equal leading
  prefixes, including errors, reusing `abiEncoderObserver.eval_phis_prefix`.
- `le_eval_one_phi_agreement` derives incoming read agreement from equal
  `vs_prev_bb`, equal `vs_labels`, and lookup agreement on Var operands.
  Label operands require label-map agreement; no memory agreement is used.
- `le_configured_rest_phis_transport` combines these with .21's
  `le_configured_transformed_phi_prefix` for arbitrary indexed input lattices.
  From successful source PHIs and incoming agreement it constructs successful
  transformed rest PHIs and relates their results. It does not assume target
  rest success or require an exact-memory relation.

Source freshness and prefix-excluded lookup agreement must still discharge
this consumer's Var condition. Its explicit paired-update closure must be
proved for the relation used by coupling; the frozen equivalences are not
imported or redefined by the helper theory.

`le_occ_prefix_all_entries_phis_success` can then extend rest success to the
prepended batch. Its selected-input availability comes from
ReachedSourceAgreement, not from assuming success of the augmented batch.
The new transport theorem only relates the ORIGINAL/rest PHI results: the
inserted prefix writes fresh outputs on the target side alone. A separate
captured-prefix framing argument must extend that relation while recording
the selected generated output and its key read. Paired identical updates
must NOT be imposed on that inserted prefix. DynamicCapture's rest-success
premise is now constructible through the checked consumer, but its selected
input and full-batch capture/framing obligations remain at actual use sites.
Neither this interface nor source retention supplies local step simulation
for .13: singleton loads, multivalue loads using captured values, redundant
stores with padded memory, calls, and invariant closure still need checked
pass-specific boundaries before constructing actual target suffix execution.

## 6. Noncircular coupling signature and dependency order

Proposed generic history-construction signature, with explicit local
obligations rather than postulated target transitions:

```
(!x y r. E x y /\ R x r ==> ?outs t.
   le_oper_event r outs t /\ R y t) ==>
!x y r. RTC E x y /\ R x r ==>
 ?h. le_oper_history r h /\ R y (le_history_end r h)
```

This is a standard RTC witness-construction SCHEMA, not a missing pass proof: the
hard premise is the local extension for the pass-specific coupled invariant.
For load elimination R must carry source/target state agreement, actual
prefix position and captured outputs needed at that position. E must expose
one real source occurrence, and the local premise must construct the actual
transformed instruction/batch and index/edge normalization, not an arbitrary
le_oper_event. Do not introduce this weak generic schema as a substitute for
the pass simulation framework's real control-flow/run_blocks obligations.

Order: (a) multivalue static retention extraction; (b) presence-based key
no-write including capture PHIs and generalized local retained-read semantics;
(c) source u-to-s read equality independent of ANY target trace;
(d) syntactic target write subsets and padded relation/PHI agreement;
(e) coupled induction, deriving target rest success and augmented success
at each entry, then capture, constructing real step/phi/neutral history;
(f) at a replaced load, use (c) plus capture-output persistence to discharge
its local simulation obligation. All earlier replaced loads in (e) must be
handled by the induction hypothesis on their reached prefixes; assuming the
complete target suffix to justify them is circular. Other singleton/store
simulation and invariant preservation remain separate prerequisites, not
consequences of this audit. Current source has conditional history transport,
NOT this coupled induction. Do not rate its discharge mechanical yet.

Search audit: checked existing DefinitionCuts, SingletonSuffix,
SingletonCurrentness, TransferRetention, RetainedStore, DynamicCapture,
JoinPlacement and OperationalHistory; searched shared pass helpers, simulation
(eval_phis_agreement), analysis definitions/cut machinery and proved memory
pass framing locations. No new duplicate lemma was introduced.
