# JMP complete-certificate integration audit

Scope: C1.5.90.67.11, following accepted canonical-root E0345.
This is a supplier audit, not a JMP simulation proof or universal coverage.

## Checked schema

`concretizePtrPairedJumpSchemaScript.sml` contains the exact candidate as a
HOL term quotation checked by `type_of`. It introduces no constant, theorem,
axiom or admission. Build target: `concretizePtrPairedJumpSchemaTheory`.
The term is an implication, not a proved assertion. Its free variables are
schematic (in particular `ws` is used rather than the existing combinator W).

Inputs are the existing complete prefix; a normalized instruction equality;
source JMP; source instruction/block/return-PC well-formedness; source and
target label distinctness; production ALLOCA coverage; no source DALLOCA;
and the actual target chronological block constructor premises. Its target
successor `bt` is **defined by equality to the actual block observation**,
not an arbitrary supplied post-state transport relation. Outputs existentially
bind the successful source jump, tagged successor b, new birth table B and
new tagged provenance TG', and the normalization gap/snapshots. The certificate
uses the exact pair index `LENGTH h - 1`, unchanged calls/ws, and the appended
historical snapshot `(tokens,registry,B,PT,TG',saved,entries)`. No source success,
source enters_block, mixed post-state or future byte agreement is an input.

## Semantic ordering and adversarial checks

1. `ptr_paired_prefix_endpoint` (PairedPrefix:292) gives mixed sample,
   paired code/cursor and parameter transport at a/at. Normalized equality
   plus `concretize_positions_terminator` (StepStructure:13) gives identical
   JMP instructions. `step_inst_non_invoke`, `step_inst_base_def` JMP branch
   (venomExecSemantics:667), and `jump_to_def` imply from target success that
   operands are `[Label lbl]`. Source success is then the corresponding
   `OK (jump_to lbl a.po_state)` using the SAME fuel, with no operand-value
   or memory-read recovery. Wrong operand shape is excluded by target OK,
   not by an extra source-success premise. Halted states remain a separate
   check: target constructor explicitly requires `~t_jump.vs_halted`;
   ptr_core_shared transports halted status.
2. `ptr_mixed_enters_production_block` (MixedPhi:143-155) has exact interface:
   `g.fn_blocks = (concretize_function_with_positions p f).fn_blocks`,
   `lookup_block s.vs_current_bb f.fn_blocks = SOME bb`, `MEM bb f.fn_blocks`,
   `bb_well_formed bb`, `EVERY inst_wf bb.bb_instructions`, equal current/prev
   labels, `retpc_shape_ok f`, mixed vars and core shared at s/t, and actual
   `enters_block g t t'`; it concludes existential source entry, mixed vars
   with `phis_prov s.vs_prev_bb TG bb.bb_instructions` and updated variable
   taint, core shared and equal current/prev labels. This supplies source
   entry success from target entry, not conversely. Target lookup inversion
   plus `concretize_positions_blocks`, `lookup_block_map` and block-label
   preservation supply the source block. Empty/deleted allocation prefixes
   do not permit assuming source and target instruction indices equal.
3. Construct b via `ptr_tagged_chrono_step_block` (SourceOwnership:32-41).
   Numerical ghosts use `entry_prov f s_jump a.po_prov` and
   `entry_taint_vars f s_jump a.po_taint`; tagged ghosts use
   `entry_prov f s_jump TG`. These match the PHI boundary after unfolding
   entry ghost selection at the known lookup block. Memory taint stays
   unchanged; PT, saved stack and runtime params stay unchanged. No memory
   agreement is required for JMP/PHIs.
4. Birth overlay cannot simply be omitted because JMP does not allocate.
   Transcript pair ALWAYS overlays the current cache. From transcript
   ownership get source birth caches; `ptr_source_birth_caches_active_lookup`
   (ActivationBirths:313-316) additionally needs the all-functions no-DALLOCA
   premise. Combined with JMP/PHI cache preservation and overlay lookup it
   supplies B=births (or at least the exact lookup agreement needed for
   transport). The schema therefore explicitly includes that task-derived
   premise. Completed activations' extra births must not be erased.

## Six-field certificate ledger

Here `d = done ++ [LENGTH h - 1]`, `hs=h++[b]`, `ts=ht++[bt]`, and
`H1=H++[(tokens,registry,B,PT,TG',saved,entries)]`.

| Field | Existing exact boundary / remaining supplier |
|---|---|
| transcript | `ptr_structural_transcript_pair` (StructuralTranscript:33-56): old transcript, source tagged step, target chrono step, same departing instruction id, and equal source/target stack lengths across the transition. Produces hs/ts/d and the computed activation maps/overlay/entries/H1. Since block steps keep stacks, activation_tokens/registry reduce to old maps and entries stay unchanged. Need semantic b and id equality, not extra source success hypotheses. |
| placements | `ptr_paired_prefix_placements`: Ct and positions unchanged. No new placement proof. |
| samples | `ptr_paired_samples_pair` (PairedPrefix:98-102): old samples and `ptr_paired_sample positions b bt snapshot` give samples on hs/ts/d/H1. MixedPhi plus birth-overlay coherence supply that sample. Existing samples are frozen, never replaced by endpoint facts. |
| alignment | `ptr_paired_alignment_def` (PairedPrefix:123-133): retain every old j using append EL algebra; new j=LENGTH ht needs paired code, cursor at b/bt, and paired params with PT. Code is unchanged function pair. Runtime params unchanged, but the transport branch also needs B=births; PT=[] equality is not available for arbitrary prefixes. **Missing durable boundary: production block-entry cursor after PHIs.** `ptr_paired_root_cursor` only covers index zero/no PHIs, so cannot be reused as if universal. |
| callers | `ptr_paired_callers_retained` (PairedFields:182-187): old callers, EVERY n<LENGTH h done, LENGTH done<LENGTH ht, LENGTH H=LENGTH h, unchanged source/target stacks imply callers on extended histories for any suffixes. Apply with hs suffix [b], ts suffix [bt], ds=[LENGTH h-1], snapshots=[snapshot]. No equality of current runtime state with saved frames required. |
| writes | `ptr_paired_writes_pair` (PairedFields:217-229): old writes, LENGTH H=LENGTH h, 0<LENGTH h, LENGTH ht=SUC(LENGTH done), EVERY n with SUC n<LENGTH h done, and optional extra entry/coverage. Use extra=[]; coverage implication has false `~is_terminator (LAST h).po_inst.inst_opcode` since LAST h=a and a is JMP. Hence unchanged ws is valid, including its completeness clause, not just EVERY old write retention. |

After assembling all six, `ptr_paired_prefix_normalize` (PairedPrefixProbe:339-353)
requires only the new complete prefix and `fn_inst_wf b.po_fn`. It returns
`bb,n,delta,snapshots`, appends actual source gap observations, preserves ghosts,
and aligns the new target active instruction with a non-NOP source instruction.
Do NOT invoke this theorem before obtaining the post-entry cursor certificate.

## Static supplier obligations

- fn_inst_wf, every block well formed, source distinct labels, retpc_shape_ok:
  task source o1_ctx_shape/SSA and lookup membership are intended suppliers;
  exact projection chain still must be instantiated at the current function
  via transcript reachability. These properties are NOT implied by
  ptr_paired_code alone.
- Target distinct labels: source distinctness plus production blocks/labels;
  alternatively task stage shape. Function metadata need not be equal.
- ALLOCA coverage: successful production layouts/stage witness; not part of
  paired_code. This explicit premise is needed to turn a deleted transformed
  allocation into a genuine source-NOP gap.
- no DALLOCA in source functions: frozen `~ctx_has_dalloca C`, followed by its
  definition; included for active cache/birth coherence.
- Normalized instruction equality: accepted root-normalized theorem initially;
  later extension uses normalize. Current prefix alone does not assert it.
- Source current active instruction and source/target histories, list lengths,
  old done bounds: transcript erasure/source/target and history endpoints.

## Structural reuse search and non-suppliers

Searched StepStructure, StepShape, StepCallChecks, StepRetpc and StageShape.
Reuse StepStructure's terminator, unchanged, blocks, block label, block wf,
inst wf, labels and preimage facts; StepShape's other_opcode/function shape;
StageShape's block PHI/provenance facts where applicable. No new theorem
about the positions rewrite is proposed. Existing MixedPhi already isolates
PHI evaluation across production deletion.

Old `concretize_step_branch_terminator` (concretizeMemLocProofs:2857) is a local
single-function `concretize_rel` result with pointer-confined/amap hypotheses
and lift_result conclusion; it is not a mixed chronological certificate
extension and cannot be silently used as one. No existing paired-prefix pair
constructor was found (only the gap constructor). This is a finite JMP gap,
not evidence that all ordinary opcodes are solved.

## Minimal next boundary and DAG (not implemented)

Next durable boundary: **post-PHI production cursor construction**. Inputs:
actual source and target enters_block successes for a production function
pair, actual target active instruction, source block wf/inst wf, both label
maps distinct, and production coverage. Conclusion: existence of a source
active instruction at its *actual* phi_prefix_length source entry cursor,
with ptr_paired_cursor. It must permit leading source NOPs after PHIs and
must not assume a source active instruction/cursor or source-target index
equality. It should use LedgerAlignment, existing production PHI preservation
and ptr_paired_covered_gap, not duplicate structural rewrite lemmas.

DAG: endpoint sample + normalized JMP + target OK -> source jump and shared
pre-entry states -> MixedPhi source entry/transport -> post-PHI cursor supplier
-> tagged block successor + birth-overlay coherence -> transcript pair,
samples pair, alignment append, callers retained, writes pair(extra=[])
-> complete prefix -> existing normalization.

No memory read recovery, return equality, post-call initialization or universal
target-prefix induction is established by this audit.
