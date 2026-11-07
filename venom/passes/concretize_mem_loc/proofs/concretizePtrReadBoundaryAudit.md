# Retrospective read interface audit (C1.5.90.45)

This is a design artifact, not an admitted theorem or a claim of global prefix
coverage. The checked addition is `ptr_chrono_history_interval_byte_frame` in
OperationalBytes. No executable or protected contract file was changed.

## Sampling decision and indices

Use a strictly increasing embedding `e : num -> num` of target **pre-state**
indices into source chronological pre-state indices. Within a block,
`e j = EL j indices` (up to the two entry offsets); derive its strictness and
coverage from LedgerAlignment, not a second positions-rewrite lemma.

At a retained writer j:

```
source: ... h[e j] --write--> h[e j+1] --NOP*--> h[e(j+1)] ... h[e n]
target: ... t[j]   --write--> t[j+1]                       ... t[n]
```

The ledger agreement is at source `e j + 1`, NOT at `e(j+1)` and NOT
at `e(j+1)+1`. Sample source memory at `e k`; gap framing promotes the
writer agreement to sample `j+1`. For intermediate k use the union of source
write footprints over `[e k,e(k+1))`, or use the new interval byte-frame theorem
directly. The target footprint remains that of event k. Never substitute
`source_writer_index` for `target_writer_index`.

The existing interference fixture has a non-retained event: its proved read
endpoint is s5 versus t4, with the last initializing store at s2 -> s3 and
t2 -> t3, a deleted NOP s3 -> s4, then the interfering store s4 -> s5 versus
t3 -> t4. Thus e(2)=2, e(3)=4, e(4)=5. Source writer post-index 3 is not
sample post-index 4. Reuse `ptr_interference_read_bytes`,
`ptr_interference_write_exclusion` and `ptr_interference_masked_read`; do not
restate this fixture as another proof. For a final source read h[e n],
ProtectedLivesets returns w with w+1 < LENGTH h: w is a pre-state, and its
initialization is available at w+1. A retained writer must have a unique j
with e j=w. NOPs cannot initialize memory.

Checked sampling probe: `ptr_chrono_history_interval_byte_frame` establishes
source byte constancy on any finite subinterval of an actual history. With
`ptr_gap_scan_fields`, deleted-gap source memories are identical (only idx
changes). This removes the equal-length obstacle in ByteHistory. It does NOT
prove a single target writer harmless.

## Exact proposed local integration contract

The following is an UNPROVED proposed HOL signature for the first integration
boundary. It is deliberately root/block-local, MSTORE-writer-only, and owned
byte only. It must NOT be installed as a speculative production theorem.
This restriction is explicit: it does not purport to cover calls, returns,
copy initialization, fixed-byte initialization, or every memory-read opcode.
`rho` is coherent for every retained root birth, not an arbitrary relocation
chosen separately at a read. The existing write-pair predicate is an actual
past ledger fact, not an endpoint-read-equality or target-exclusion premise.

```sml
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_chrono_history vs C' ht at /\
  LENGTH ht = SUC n /\ LENGTH h = SUC (EL n indices) /\
  MEM bb a.po_fn.fn_blocks /\ MEM bt at.po_fn.fn_blocks /\
  ptr_ledger_block_alignment layout bb.bb_instructions
    bt.bb_instructions indices /\ n < LENGTH indices /\
  lookup_function a.po_fn.fn_name C'.ctx_functions = SOME at.po_fn /\
  at.po_fn = concretize_function_with_positions layout a.po_fn /\
  (!k. k < LENGTH h ==>
    (EL k h).po_fn = a.po_fn /\ (EL k h).po_stack = [] /\
    (EL k h).po_state.vs_current_bb = bb.bb_label /\
    (EL k h).po_state.vs_inst_idx = k /\
    (EL k h).po_inst = EL k bb.bb_instructions) /\
  (!j. j <= n ==>
    (EL j ht).po_fn = at.po_fn /\ (EL j ht).po_stack = [] /\
    (EL j ht).po_state.vs_current_bb = bt.bb_label /\
    (EL j ht).po_state.vs_inst_idx = j /\
    (EL j ht).po_inst = EL j bt.bb_instructions /\
    (?ts rg bs pt tg sv.
      ptr_source_ownership vs C (TAKE (SUC (EL j indices)) h)
        (EL (EL j indices) h) ts rg bs pt tg sv /\
      ptr_vars_transport bs positions tg (EL (EL j indices) h).po_taint
        (EL (EL j indices) h).po_state (EL j ht).po_state)) /\
  (!site pos size. FLOOKUP positions site = SOME (pos,size) <=>
    MEM (site,pos,size) at.po_fn.fn_mems_used) /\
  (!site pos size. MEM (site,pos,size) at.po_fn.fn_mems_used ==>
    pos + size < dimword(:256)) /\
  (!token aid base size pos.
    FLOOKUP births (token,aid) = SOME (base,size) /\
    FLOOKUP positions (Allocation aid) = SOME (pos,size) ==>
    !k. k < size ==> rho (base+k) = pos+k) /\
  (!x. x < lo ==> rho x = x) /\
  (!j. j < n /\
    source_memory_write_ranges (EL (EL j indices) h).po_inst
      (EL (EL j indices) h).po_state <> [] ==>
    (EL (EL j indices) h).po_inst.inst_opcode = MSTORE /\
    ptr_ledger_write_pair C C' rho
      (EL (EL j indices) h) (EL (SUC (EL j indices)) h)
      (EL j ht) (EL (SUC j) ht)) /\
  a.po_inst.inst_opcode = MLOAD /\ a.po_inst.inst_operands = [Var v] /\
  ~in_revert_forward a.po_fn a.po_state /\
  FLOOKUP a.po_state.vs_allocas aid = SOME (base,size) /\
  FLOOKUP a.po_prov v = SOME (base,size) /\
  FLOOKUP positions (Allocation aid) = SOME (pos,size) /\
  lo <= base+k /\ k < size /\ base+k NOTIN a.po_taint.t_mem ==>
  read_byte (base+k) a.po_state.vs_memory =
    read_byte (pos+k) at.po_state.vs_memory
```

This proposal still needs strategist validation, especially whether requiring
`ptr_ledger_write_pair` for all earlier stores is the correct ledger granularity
for pointer-valued stores. Its agreement is only for source post-write
untainted bytes. It must be derived while constructing the prefix, never
supplied by the final arbitrary-target-prefix coverage theorem.

The MLOAD consumer needs this conclusion for k=0..31 at the evaluated address,
not for all bytes of an allocation. Discharge with
`ptr_mload_masked_value` followed by `ptr_mload_transport_back`; the latter
constructs successful source MLOAD from successful target MLOAD. A successful
source MLOAD endpoint is not an input to this proposed contract.

## Missing-implication table (not additional assumptions to hide in a relation)

| Case/boundary | Existing checked interface | Still required from actual paired execution |
|---|---|---|
| Source last initializing writer | `ptr_endpoint_protected_history`, `ptr_endpoint_protected_livesets` | Derive wf/inst-wf/fn_ptr_ok and stage views from the frozen task; classify endpoint address and identify its actual owner. Match each returned w with a retained event j, not numerical indices by fiat. Source post-write taint must exclude the selected byte. |
| Deleted NOP gaps | `ptr_ledger_alignment_order/source/gap`, `ptr_gap_scan_fields`, new `ptr_chrono_history_interval_byte_frame` | Promote adjacent write ledger entry at e(j)+1 to sampled boundary e(j+1). For global executions concatenate block embeddings and include block-entry/call/return events; block index lists alone are not global chronological alignment. |
| Same tagged owner | `ptr_mstore_transport_same_owner_exclusion`, `ptr_mstore_same_owner_exclusion` | Derive tagged destination owner, source bounds, position lookup, strict word endpoint and empty address taint from source access_ok/ownership. Source last-writer exclusion then transports; tags alone do not give byte offsets. Generic same-owner exclusion for other writers remains absent. |
| Different local allocation in same activation | `ptr_endpoint_local_interval_exclusion`, `ptr_endpoint_local_mstore_exclusion`, `ptr_endpoint_local_copy_exclusion`; underlying `ptr_output_local_local_separation` | Derive concrete target footprint containment, production allocation items, BP write-origin membership and metadata/position coherence from the writer's actual operands. Different tags are not sufficient. |
| Descendant activation while endpoint owner suspended | `ptr_endpoint_descendant_interval_exclusion`, mstore/copy specializations; `ptr_output_suspended_descendant_separation` | Identify ancestor stack index and live owner depth at the intervening writer. Derive descendant birth, positive size when footprint nonempty, and coherent imported position in the ancestor's stage view. |
| Writes through an imported ancestor pointer | Same-owner transport when exact same owner; otherwise owner-relative local/local or local/import separation (`ptr_output_local_import_separation`) | Classify by tagged destination owner, not executing function. Rebase BP origin/position facts to the actual owner and prove imported position equals owner's placement. Descendant-local exclusion cannot be applied merely because the executor is a callee. |
| Returned activation / sibling call | No theorem inspected proves that distinct activation tokens have distinct static addresses (they need not) | Use protected owner's retained lifetime and stack geometry to place writer in the correct local/descendant/import case. A returned allocation's bytes cannot simply be carried as live demand after return. Establish that endpoint provenance has a still-valid owner or prove its exclusion from valid source reads. Root-only signature avoids, but does not solve, this case. |
| Fixed writer versus owned read | `ptr_mstore_transport_fixed_exclusion`, `ptr_write_transport_fixed_containment` | Derive scalar/untainted operands and `write_end <= lo`; also derive owned target byte >= lo from production reservations. fixed_region_reserved alone is a source reservation fact, not the target lower bound proof. |
| Owned writer versus fixed read | Production layout reservation/disjointness, not same-owner byte exclusion | Derive target owned footprints disjoint from reserved fixed bytes. Initial fixed-byte sentinel starts at initial state (no w exists); preserve source and target bytes through all later writes or use a later fixed writer. No arbitrary initial memory equality on relocated allocations is valid. |
| MSTORE initialization ledger | `ptr_ledger_write_pair` is a definition; finite fixture proves particular written bytes | Derive paired post-write untainted-byte agreement from actual value/taint transport. Check pointer-valued stores instead of demanding all written bytes agree. |
| Other writes | `ptr_step_write_opcode`, `ptr_source_write_classification`, `ptr_write_transport_owner_containment/fixed_containment` | Exhaustive cases include MSTORE8, ISTORE, EXTCODECOPY, CALL/STATICCALL/DELEGATECALL, DRET as well as the existing copy list. CALL actual writes use MIN requested size/returndata length. DRET uses call-entry FMP and possibly wrapping padded cursors; generic max-size operand transport does not cover it. MCOPY initialization needs earlier source-byte agreement (well-founded read induction), not just scalar operand transport. |
| Initial fixed bytes | Same initial runtime memory; source/target history entry memory preservation | Separate initial sentinel case from last-writer case. `ptr_bytes_agree_last_writers` requires w<n, so cannot handle n=0 or never-written fixed bytes without an initial alternative. |
| Retained birth extension | SourceOwnership + ActivationBirths retained-cache theorems, OwnedAllocationPrefix | Freeze endpoint owner lookup while using earlier birth maps for operand transport; do not replace earlier maps with an unrelated final map without retention. SourceOwnership registry is token->source function, NOT the older token->ptr_ledger_activation registry. Connect target metadata by stage lookup, not by conflating registry types. |
| Endpoint demand / exceptional mode | `ptr_ledger_read_demand`, `ptr_mload_transport_back` | Owned-byte contract must be combined with fixed and zero-length cases and revert-forward exemption. Scalar addresses and other read opcodes remain outside MLOAD's Var-address specialization. |

## Result

Sampling is adequate for the index problem. The missing hard part is exhaustive
production-derived writer-owner classification and write-content transport,
not a stronger abstract last-writer theorem. No universal noninterference or
read simulation result has been proved here. The proposed narrow contract is
for strategist review, not authorization to spend further sessions adding
conditional opcode wrappers. A global contract needs a coherent event-aligned
ownership/placement interface across calls and returns before its signature can
be both precise and useful; a new predicate that simply stores target exclusion
or endpoint read agreement would not resolve that problem.

## Strategist verdict (E0254 review / PLAN refinement)

1. Sampling is the appropriate index boundary. Actual writer post-state is
   e(j)+1; it must be framed through deleted NOPs before using e(j+1).
2. The proposed root/block-local implication above is **NOT validated and NOT
   authorized for installation as a theorem**. The inspected interfaces do not
   discharge all writer-owner and placement cases from its premises. Its exact
   text is retained only to make that failed integration boundary inspectable.
3. Post-write untainted-byte agreement is an appropriate MSTORE initializer
   interface, but no general production derivation was established by this
   audit. In ptrDiscipline, `written_taint_def` (289–305) maps the MSTORE
   value's tainted byte indices to destination addresses. `mem_taint_def`
   (309–312) removes overwritten old taint, then adds written taint. Thus a
   ledger must require equality only outside **post-write source taint**;
   it must not demand identical relocated pointer representations. Deriving
   the ledger requires masked-value byte transport and actual address
   relocation from the operational store semantics.
4. A single rho on raw addresses must not become the global interface.
   Owner-indexed (token,aid,offset) placement supports temporal reuse without
   forcing a raw address to have one image across different lifetimes.
5. Global integration must jointly establish event correspondence (including
   entry, call and return), retained owner validity, original-owner-relative
   stage placement, and actual write-content transport. The executor's
   function is not necessarily the pointer's owner. This design is an
   enclosing integration obligation, outside this bounded audit leaf.
6. Initial fixed-byte sentinel, MCOPY read-before-write dependence, external
   CALL's actual MIN footprint, and DRET cursor semantics remain unresolved
   consumers. Do not insert their desired conclusions as assumptions in a
   purported arbitrary-target-prefix coverage predicate.

The bounded audit is complete; the enclosing universal retrospective-read
integration is not. The only theorem added here is the checked source-only
interval framing probe. Builds in E0254 verify the relevant existing fixtures
and consumers, not the unproved displayed candidate.
