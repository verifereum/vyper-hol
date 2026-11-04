# Positional recursive phase probe (C3.6.17)

## Checked interface and its limits

`dftPositionalPhaseScript.sml` defines a *candidate* relational phase, not a
simulation theorem. `dft_pos_slot` retains both list indices. In particular,
selection is `j = fi /\ k = bi`, never `bb = selected_bb`.
`dft_pos_certificate` retains the existing crossing certificate record but
replaces its functional delayed-function equation by an explicit selected slot.
`dft_pos_frame` uses the shared `dft_rel_frame` on ordinary frames; pending frames
retain `dft_crossing_evidence`, `dft_certificate_saved`, and the algebraic payload.
Stacks retain certificate alignment, and controls exclude the selected interior
cut. The phase retains path/visit equality, saved-list equality and length, and
both original-readiness predicates. Counts remain independently quantified.

Checked probes: `dft_pos_phase_root`, `dft_pos_plain_frame`,
`dft_pos_plain_frame_projection`, `dft_pos_phase_isolation`. Isolation does not
need block inequality and therefore applies even to structurally equal blocks.
These probes establish neither pending-frame preservation nor phase invariance.

## Proposed segment theorem (NOT an admitted HOL theorem)

Abbreviate D = dft_pos_edit_ctx fi bi pre x call post C;
fsel = EL fi C.ctx_functions; q = EL bi fsel.fn_blocks.
Proposed `dft_pos_segment_next`:

```
fi < LENGTH C.ctx_functions /\ bi < LENGTH fsel.fn_blocks /\
q.bb_instructions = pre ++ [x;call] ++ post /\
~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
x.inst_opcode <> GAS /\ x.inst_opcode <> ALLOCA /\ call.inst_opcode = INVOKE /\
dft_original_context Corig C /\ dft_original_context Dorig D /\
dft_pos_phase C D fi bi pre x call post c d /\
(!fn s ls n. c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls n /\
  fn = fsel /\ s.vs_inst_idx = LENGTH pre ==>
  ?f b. dft_recursive_crossing_ready f b q pre x call post s)
==>
?a b. (a = 1 \/ a = 2) /\ (b = 1 \/ b = 2) /\
  dft_pos_phase C D fi bi pre x call post
    (FUNPOW (dft_occ_oracle_next w C) a c)
    (FUNPOW (dft_occ_oracle_next w D) b d) /\
  PosAccount C D w a b c d
```

Here `PosAccount` is the following exact proposed accounting predicate, not yet
an HOL definition:
* endpoint count increments equal, as in dft_fixed_segment_account_def:12-13;
* for every instruction/address pair, existence of a GAS event at a left cut
  j<a iff existence at a right cut k<b (same event predicate and occurrence
  address, as lines 14-18);
* every left instruction observation fn,i,s at j<a with nonempty memory ranges
  has a right observation g,i,t at k<b with dft_pos_functions C D fn g,
  t.vs_memory=s.vs_memory and inst_mem_ranges i t=inst_mem_ranges i s;
* conversely every right observation g,i,t at k<b with nonempty ranges has
  such a left observation fn,i,s and the SAME directional function relation.

This proposes only the ordinary non-GAS partner / INVOKE edit class. GAS partner
edits and ordinary/ordinary swaps need separate semantic outputs. No same-fuel
native statement or uniform witness follows from the proposed theorem.

## Segment consumer premise ledger

Source consumer: dftRecursiveFixedSegmentScript.sml:319-356.

| Premise/branch | Available boundary | Missing positional output |
|---|---|---|
| edit bounds/decomposition | positional selected/other EL laws | none |
| original context on right | dft_pos_edit_original_context (static single-source edge certificate) | chain caller must supply its selected schedule_edges premise |
| readiness at selected active cut | dft_original_runtime_at_projection; dft_recursive_crossing_partner_success | positional original-label orbit wrapper tying current slot to its original block; do not reuse equality-edit wrapper literally |
| Enter one-step | dft_pos_edit_interface, dft_rel_enter | occurrence/saved-list lift preserving candidate phase with pending stack |
| ordinary At outside swapped slots | dft_pos_edit_instruction_outside and dft_rel_at | corresponding occurrence event/count agreement and phase preservation |
| ordinary INVOKE push | relational function lookup/setup in dftPositionalRuntime | relational plain stack push plus original readiness and path bookkeeping |
| crossing (2,1) | local partner success, disjointness, updates, crossing positions | selected-slot forward-certificate constructor, relational callee Enter and pending push |
| Done with no pending certificate | dft_rel_return; original_runtime_next | ordinary relational saved-stack pop with coordinate exclusion preserved |
| Done with pending certificate | dft_certificate_done_segment and dft_certificate_delayed_next | relational phase reentry and pending stack pop, plus observation/count account |
| half-open segment account | silent-cut / count arguments independent of maps | replace mapped-function observations by dft_pos_functions witnesses |

## Finite missing semantic inventory

1. Relational stack fill/length/saved-empty projections (zero budgets), pending
   constructor, and ordinary push/pop. Existing `dft_provenanced_frames_fill`
   and `...saved_empty` require a functional fm/bm and cannot consume this stack.
2. Relational forward-certificate construction: `dft_forward_certificate_def`
   (dftRecursiveActivePhase:106) hardcodes a globally edited delayed function.
   Construct the same evidence with selected related functions/blocks instead;
   retain the original-cut witness and algebraic update payload. Reuse local
   readiness-to-success and update/disjointness facts unchanged.
3. Enter and outside-At occurrence lifts, including INVOKE stack creation, using
   `dft_rel_interface`. `dft_recursive_pre_phase` and
   `dft_recursive_crossing_enter_exact` (ActivePhase:197,234) hardcode functional
   maps and must NOT be instantiated by guessing a map on duplicate values.
4. Pending-return reentry: `dft_certificate_done_segment` (ReturnPhase:88) already
   has explicit ordinary/delayed functions and is reusable once zero-budget tail
   facts are supplied. `dft_fixed_done_reentry` (FixedPhase:146) is not reusable:
   its final assembly demands functional fixed control/stack. The local return
   replay equalities remain reusable.
5. Relational segment accounting and assembly: `dft_fixed_segment_account_def`
   (Segment:10) hardcodes dft_gas_edit_fn in both memory-observation clauses;
   use the proposed PosAccount. Outside event and count lifts need positional
   instruction equality. Silent-done and local partner replay facts need no
   new execution model.

## Adversarial design checks

A duplicate source block can have both selected and unselected target partners.
The candidate permits existential slot witnesses, but *each* witness must be
retained jointly with its target block; no substitution by structural equality
may select the edit. First-match lookup only promises some aligned occurrence.
At returns the certificate explicitly supplies the selected slot. Outside
frames retain their own joint witness. The checked isolation theorem tests the
static part; the future preservation proofs must test the runtime part.

The candidate does not constrain original-context witnesses at definition time;
the segment proposal supplies those separately, matching the accepted pattern.
It does not assume termination or successful INVOKE. Return restoration failure
and halted/error results still require the existing all-result case split in a
relational Done boundary. Positive bounded segments alone do not establish
native adequacy or finite uniform GAS realization. Those are separate ancestor
obligations; this probe does not authorize their implementation.
