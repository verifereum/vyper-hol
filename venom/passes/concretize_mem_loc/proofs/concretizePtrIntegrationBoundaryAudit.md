# Current-observation / history-extension integration audit

Diagnostic C1.5.90.67.integrationBoundaryAudit. No theorem is proved by this
report. Existing suppliers were inspected in source; ForwardingTransport and
ObservationInterface built cleanly at audit entry. No SML changes were made.

## 1. Two separate universal consumers

`observation_range_transport_schema` (ObservationInterface:51-75) is a quotation,
not a theorem. Its fixed-or-allocation conclusion is stronger than needed.
The appropriate eventual current-observation consumer is the following exact
proposed statement (not a new assumption for the frozen theorem):

```sml
ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
  (o1_walk_view rpolicy 2) C Ct /\
o1_ctx_shape C /\ o1_run_state_ok vs /\
EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
mem_inv raw_mem_ok C vs /\
fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
EVERY all_reachable C.ctx_functions /\
EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom Ct = SOME eom /\
LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
ptr_stage_placements Ct positions /\
ptr_paired_prefix R lp positions lo vs C Ct
  h a ht at done tokens registry births PT TG saved entries H calls ws /\
a.po_inst.inst_opcode <> NOP /\
at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst ==>
in_revert_forward at.po_fn at.po_state \/
(!off len.
  MEM (off,len) (source_memory_read_ranges at.po_inst at.po_state ++
                source_memory_write_ranges at.po_inst at.po_state) ==>
  len = 0 \/ off + len <= eom)
```

There is deliberately no departure, `step_inst`, `step_writes`, or target
success premise. `ptr_paired_prefix_forwarding` supplies the first alternative
from source forwarding. `ptr_paired_terminal_static_bound` supplies the bound
for source RETURN/REVERT when not forwarding, under precisely this stage,
placement, prefix and alignment supply. They do not supply the other opcodes.
Raw reachable-to-history conversion and final mem_inv packaging remain later
consumers, not consequences of these two local suppliers alone.

## 2. Actual current range inventory

Sources: contextCodegenRel:79-201, codegenRel:131-225;
memLocDefs:188-344; ptrDiscipline:85-140,530-558,566-585.
`R` means source_memory_read_ranges; `W` means source_memory_write_ranges.
Operand order below is semantic order, not stack-pop order. All ranges are
prestate observations. An evaluation failure produces [] where indicated;
there is no requirement that the whole instruction succeeds.

Supply codes used in the table:

* **P**: scalar provenance exclusion must be derived from ptr_use_ok and
  FDOM support. A pointer variable can occur only once in a non-preserving
  memory instruction and must be a read/write descriptor's address. It
  therefore cannot also occupy a size position. This is already exported for
  write maximum sizes by ptr_write_max_size_not_pointer / _no_provenance.
  Read-size generalization is NOT exported by terminal_length_prov.
* **T**: taint_ok's first clause excludes taint on address and length operands
  in these families. Only MSTORE/ISTORE data operands can remain tainted;
  MSTORE8 has no such exception. Write max-size untaint is already exported
  as ptr_write_max_size_untainted. Terminal lengths have a dedicated export.
* **N**: ptr_nonopaque_instruction_operands, using opaque_use_ok, membership,
  and label_positions_ok, supplies EVERY nonopaque for these instructions;
  select descriptor operands by membership. For constants no premise is needed.
* **E**: ptr_mixed_vars_eval_presence preserves success/failure of evaluation
  for EVERY operand, even opaque ones, from mixed vars and label equality.
  This is enough for gate operands; their word values need not be equal.
* **V**: ptr_mixed_vars_eval transports an address; ptr_mixed_scalar_eval
  gives size equality once P/T/N and numerical erasure are supplied.
  These are existing evaluation interfaces, not full range theorems.

| Family | Direction; address; size/max size | Other current-range gates | P/T/N and applicable transport |
|---|---|---|---|
| MLOAD, ILOAD `[off]` | R; off; Lit 32 | eval off succeeds | constant size; T,N,V for off. ILOAD's variable operands are outside fn_pv by fn_ptr_ok, so its address is scalar. Current range extraction still missing generically. |
| MSTORE, ISTORE `[dst;value]` | W; dst; Lit 32 | eval dst AND value succeed | constant size; T for dst, N,V; E for value (may be tainted). ISTORE forbids all pointer operands. Successful-write helper is insufficient for this observation. |
| MSTORE8 `[dst;value]` | W; dst; Lit 1 | eval dst AND value succeed | constant size; T,N,V for dst; E for value. No tainted-value exception. |
| MCOPY `[dst;src;n]` | R src / W dst; n in both | eval all three succeeds | P for n must account for BOTH descriptors and repeated operands; T,N,V. _write_max_size_* already supplies n purity. ptr_paired_prefix_mcopy needs a target chrono departure and is not an observation theorem. |
| CALLDATACOPY, RETURNDATACOPY, DLOADBYTES, CODECOPY `[dst;src;n]` | W; dst; n | eval all three succeeds | write P/T exports; N,V for dst/n; E for nonmemory src. RETURNDATACOPY may fail bounds after these evaluations: its range must still be covered. |
| EXTCODECOPY `[external;dst;src;n]` | W; dst; n | eval external then sized triple | write P/T exports; N,V; E for external/src. |
| RETURN, REVERT `[off;n]` | R; off; n | eval both succeeds | terminal_length_prov / _taint, N,V; ptr_terminal_read_range_transport and ptr_paired_terminal_static_bound close the actual current-observation bound. W=[] whether or not execution departs. |
| SHA3 `[off;n]` | R; off; n | eval both succeeds | read P missing in generic form; T,N,V. Hash computation/output is irrelevant to range safety. |
| LOG `Lit tc :: topics ++ [n;off]` with LENGTH topics=w2n tc | R; off; n (last two) | exact rest length; eval all topics then off/n | T,N,V; E for topics. Read P needs the LOG shape. **Zero-topic LOG is a descriptor exception**, discussed below. |
| CALL `[gas;external;value;argoff;argn;retoff;retn]` | R argoff/argn; W retoff/retn | R gate eval gas/external/value/retoff/retn; W gate eval ALL operands | write P/T exports for retn; generic read P for argn missing. T,N,V on each address/size; E on all gates. W uses MAX requested retn, not actual returned-byte count. No successful call or poststate is needed to observe it. |
| STATICCALL, DELEGATECALL `[gas;external;argoff;argn;retoff;retn]` | R argoff/argn; W retoff/retn | R gate gas/external/retoff/retn; W all operands | as CALL. DELEGATECALL extra storage-taint side condition in taint_ok is not needed merely to compare ranges. |
| CREATE `[value;off;n]`, CREATE2 `[value;off;n;salt]` | R; off; n | eval value (and salt) then off/n | generic read P missing; T,N,V; E for value/salt. No W range. |
| DRET | R list of (src,len) dynamic pairs; W state-dependent sequence based on vs_call_entry_fmp | parse_dret_shape, eval ALL operands, pair_dret_words over TAKE/DROP | **excluded**, not scalar-transported: fn_ptr_ok forbids DRET. ptr_discipline_no_dret / ptr_stage_observation_no_dret export this for actual observations. No descriptor for DRET in mem_read/write_ops. |
| every other opcode, including INVOKE/ALLOCA/DALLOCA/NOP | R=[] and W=[] | none | bounds vacuous. INVOKE nested memory is covered through callee observations, not a direct caller range. |

DRET W consists of the encoded dynamic return buffer, not just the input
read pairs; a general arbitrary-opcode descriptor theorem would be wrong.
Its exclusion is already proved and should be reused.

### Important descriptor mismatch: zero-topic LOG

For `inst_operands = [Lit 0w; n; off]`, the actual read definition permits a
range. But mem_read_ops LOG matches `REVERSE operands` against
`ofst :: sz :: _ :: _`, which requires at least FOUR operands. Thus for this
three-operand shape it is NONE. No claim that EVERY current nonempty range
has a mem_read_ops descriptor is valid, even under inst_wf.

This is not a counterexample to the task: ptr_use_ok then forbids provenance
on every variable operand of this LOG, so n and off are scalar; taint_ok
excludes taint; eval_presence handles gates. Source access_ok with no read
descriptor forces a nonzero source range below lo. Scalar equality preserves
it. An all-range transport interface must have a no-descriptor scalar branch.
The frozen executable definitions must NOT be edited to remove this mismatch.

### Failing observations

Bad operand-list shapes and failed required operand evaluation yield [].
Target range membership supplies exactly those gates needed in the target;
E reflects them to the source. Value equality is needed for the selected
address/size, NOT every gate. Later semantic failures (return-data bounds,
call/create failures, halting RETURN/REVERT, etc.) do not erase an already
defined range. step_writes may be empty without these range lists being
empty. In particular ptr_ordinary_write_operand_transport:212-232 requires
`q IN range_bytes (step_writes inst tgt postt)` and `inst <> DRET`;
it cannot be applied backwards from current W membership. Its existing
write max-size purity and eval-presence ingredients ARE reusable.

## 3. Terminal supply chain and remaining generalization

The terminal proof obtains, in order:

1. ptr_paired_prefix_endpoint / _transcript; structural_transcript_erasure;
   structural_trace_ownership; gap_ownership_history; chrono_history_reachable:
   actual source frame_reachable (no departure).
2. ptr_frame_sizes, source shape: current function and instruction membership,
   inst_wf, fn_shape_ok; nonopaque_instruction_operands.
3. paired_sample + core_shared/shared_fields: mixed_vars and label equality.
4. source_ownership_prov_erases and frame_current_static: erasure and numerical
   provenance support in fn_pv; source ptr_discipline: taint_ok and fn_ptr_ok.
5. terminal_length_prov / _taint, mixed_scalar_eval, mixed_vars_eval: exact
   length equality and address transport with empty operand taint.
6. terminal_read_range_transport reflects current range membership;
   paired_read_range_static_bound uses paired_read_range_classification,
   stage_fixed_region_bound and stage_placements_endpoint_bound.

Steps 1-4 are common supply, not missing new hypotheses. Step 5 is only
terminal-specialized for reads. Step 6 has no generic current write analogue;
ptr_access_range_classification is already symmetric in R/W, but lifting
its owned alternative to tagged historical placement is still required
for writes. Do not use a historical write's relocation witness for a
current failing observation. The historical ownership exports and the read
classification proof are source-grounded ingredients, not that lift itself.

## 4. Exact history-coverage extension premise

HistoryCoverage:17-30 requires the following entire premise:

```sml
!h a ht at done tokens registry births PT TG saved entries H calls ws zt.
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step Ct at zt ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C Ct
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
```

It cannot be proved from the weak outer hypotheses of HistoryCoverage alone;
the stage consumer must discharge it using the full frozen assumptions and
production bridges. universal_normalized_step_schema is also a quotation.
Stage-to-LIST_REL/placements, root hypotheses and shape/name/local-coverage
bridges must still be assembled in the final consumer; accepting conditional
exports does not supply those bridges automatically.

There are exactly four chronological constructors (ChronologicalHistory:29-71):

| Constructor | Actual source signature / supplier | Residual obligations (not silently dropped) |
|---|---|---|
| next | active_inst; nonterminator/non-INVOKE; `step_inst ... = OK post`; active next at SUC index | ptr_paired_prefix_ordinary_nonwrite:124-152 additionally requires SOURCE success, source next instruction, post allocas/current_bb/prev_bb, target stack/function/control projections, id equality, distinct labels, local allocation coverage, tagged TG', paired_sample, paired_params, and EMPTY source step_writes. This is an attachment theorem, not generic backward execution. |
| next ALLOCA | ptr_paired_structural_prefix_normalize covers ALLOCA or RET in exactly the normalized existential conclusion | Requires full stage assumptions, LIST_REL, EVERY source fn_inst_wf/retpc_shape/opaque/first-block-no-phi/bb-wf/distinct-label/local ALLOCA coverage, target distinct labels and code-name equality. No new source-success premise. |
| next ASSIGN/PARAM/MLOAD | ptr_paired_prefix_assign / _param / _mload | Full frozen assumptions (callee_first names instantiated, max-live bound included), paired_prefix, selected opcode and target chrono step. They yield an immediate singleton prefix, not the normalized final source non-NOP and rewrite equation. Apply prefix_normalize with source fn_inst_wf; combine delta and snapshots, preserving nonempty delta. |
| next MSTORE/MCOPY | ptr_paired_prefix_mstore / _mcopy | MSTORE full frozen assumptions except max-live bound not required there; MCOPY includes it. Actual target step required. They conclude an immediate prefix and ledger extension (MSTORE one reloc; MCOPY extra=[] or singleton conditional on footprint), not normalized extension. Same normalization/concat step required. |
| next environment reads | ptr_paired_prefix_environment_read | Exact list: CALLER, ADDRESS, CALLVALUE, ORIGIN, GASPRICE, CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, CALLDATASIZE, RETURNDATASIZE. Full frozen assumptions and target chrono step. Not all nonmemory opcodes! Immediate prefix then normalize. |
| next remaining | no universal supplier found | Arithmetic/comparisons/affine/bitwise, storage, ILOAD/ISTORE/MSTORE8, other copies, call/create/hash/log/etc. cannot be credited merely because ordinary_nonwrite or value-level transport exists. Source backward execution, taint/shared fields and ledger attachment remain real semantic work. DALLOCA/MEMTOP/FMP-family/DRET exclusions must be used where applicable, not simulated. |
| block | target terminator step OK, not halted, enters_block, active entry | ptr_paired_jump_prefix_normalize handles JMP, with fn_inst_wf, retpc_shape, no-DALLOCA, bb-wf, both label-distinctness, local ALLOCA coverage and explicit target constructor witnesses. JNZ variant additionally ASSUMES `[cond;Label yes;Label no]`, nonopaque cond, `op_prov TG cond = NONE`, empty cond taint. These scalar premises still need derivation. No blanket terminator supplier. Halting RETURN/REVERT have no block successor, but still need current range safety. |
| call | INVOKE decode, target lookup, eval args, setup, enters_block, active callee; pushes frame | ptr_paired_invoke_prefix_normalize gives immediate+gap normalized prefix, but requires ptr_discipline, opaque_use_ok caller, LIST_REL/name equality, EVERY first-block-no-phi/fn_inst_wf/bb-wf/source distinct labels/local allocation coverage, target label distinctness, and explicit target constructor witnesses. These are not assumptions of the bare coverage extension premise; supply them from stage/shape/prefix first. No memory read equality premise is hidden here. |
| ret | step IntRet, bind outputs after adopt/merge, active restored caller | ptr_paired_ret_prefix_immediate under full frozen assumptions + production/shape bridges concludes immediate prefix only. ptr_paired_structural_prefix_normalize already packages RET with subsequent gap normalization. DRET excluded via existing no-DRET results; do not claim all IntRet opcodes from the RET theorem alone. |

PHIs are handled by enters_block / entry_prov and paired jump/call entry,
not extra chronological constructors. Deleted source NOPs are scanned by
ptr_paired_prefix_normalize; they are not target next cases. Root coverage
is separately handled by ptr_paired_context_root. A generic future extension
proof must exhaust actual constructors/opcodes, not assume this table is a
complete dispatcher theorem.

## 5. One proposed next semantic boundary (for strategist review)

Prefer a single actual-current-range transport boundary over new size-only
wrappers. This exact candidate covers read and write observations, including
zero-topic LOG and evaluation failure gates, with NO departure premise.
Names ranges_s/ranges_t/mops are ordinary universally quantified variables;
there is no let, new definition, axiom, or changed frozen statement.

```sml
fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
opaque_use_ok fn /\ label_positions_ok inst /\
ptr_ledger_erases births TG G /\ FDOM G SUBSET fn_pv P fn /\
ptr_mixed_vars births positions TG tn fn ft src tgt /\
src.vs_labels = tgt.vs_labels /\ taint_ok fn tn inst src /\
((mops = mem_read_ops inst /\
  ranges_s = source_memory_read_ranges inst src /\
  ranges_t = source_memory_read_ranges inst tgt) \/
 (mops = mem_write_ops inst /\
  ranges_s = source_memory_write_ranges inst src /\
  ranges_t = source_memory_write_ranges inst tgt)) /\
MEM (off,len) ranges_t ==>
?off_s. MEM (off_s,len) ranges_s /\
  ((off = off_s /\
    ~(?ops. mops = SOME ops /\ op_prov G ops.iao_ofst <> NONE)) \/
   (?ops x y. mops = SOME ops /\
     eval_operand ops.iao_ofst src = SOME x /\
     eval_operand ops.iao_ofst tgt = SOME y /\
     off_s = w2n x /\ off = w2n y /\
     ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
       (SOME x) (SOME y)))
```

This is a proposed proof obligation, NOT a verified theorem. In particular
its no-descriptor branch is essential, not a convenience weakening.

Derivation plan to assess before authorizing proof:

* Conservatively split actual range families and reflect required gates with
  ptr_mixed_vars_eval_presence. DRET impossible by fn_ptr_ok. No case should
  expand full step_inst or require successful execution.
* Reuse write maximum purity exports (project G support through erasure if
  using TG variants). Derive read scalar purity using ptr_use_ok's unique
  occurrence test against BOTH address descriptors. LOG zero-topic must be
  a scalar-only branch, not an invented descriptor witness.
* Use taint_ok for selected address/size untaint and nonopaque_instruction_operands
  for opacity; use mixed_scalar_eval for length and mixed_vars_eval for address.
  Gate data may remain tainted and need only presence transport.
* Package the actual range membership with its unchanged length. For absent
  numerical provenance, erasure + scalar empty transport gives identical
  off; otherwise retain the address transport for ownership classification.

Consumers: paired current-observation eom safety above, via already proved
source access classification and fixed-region bound; descriptor-owned cases
use the historical active-owner/placement recovery employed by
ptr_paired_read_range_classification and stage_placements_endpoint_bound.
The read consumer exists; the analogous actual-current-write placement lift
must still be derived, not assumed from successful write transport.
This range boundary can also feed later copy/call descriptor consumers, but
DOES NOT prove opcode execution, result taint transport, ledger extension,
or universal target-history coverage. Those remain independent obligations.

## 6. Decision boundary

The audit supports continuing current-observation safety without successful
departure, and identifies an actual descriptor exception that a size-only
plan would miss. It does not justify claiming universal extension closed or
replacing its side conditions by a generic wrapper. Ask strategist review of
the proposed boundary and finite remaining dispatcher obligations before
editing SML. Preserve all accepted forwarding, terminal and producer proofs.
