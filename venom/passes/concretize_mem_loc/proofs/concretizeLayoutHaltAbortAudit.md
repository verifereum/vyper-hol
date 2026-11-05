# Halt/Abort diagnostic: local obstruction; global compatibility unresolved

The frozen theorem is unchanged and is NOT yet disproved by a full checked
antecedent witness. The probe theory builds without cheats. Its local examples
are not claimed to satisfy the source-program hypotheses.

## Checked facts

`concretizeLayoutHaltAbortProbeTheory` checks:
- `final_demand_excludes_taint`: any final tainted source byte is absent from
  joint relocation demand, regardless of the target address. This does NOT say
  that the entire demand relation is empty.
- `probe_return_zero`, `probe_return_one`, `probe_return_not_related`: one-byte
  RETURN executions disagree observably when `D.d_ret [0w] = {}`.
- `probe_return_incoming_observation`, `probe_return_context`,
  `probe_return_local_relation`: the literal-address local examples have equal
  incoming Halt observations, environment and reader context, and satisfy the
  local relation with empty demand and arbitrary pointer/byte predicates.
- `return_payload_taint_allowed`: RETURN with literal clean operands satisfies
  taint_ok for arbitrary memory taint. RETURN is not a revert exemption case.
- `probe_alloc_step`, `probe_alloc_fresh_byte`: allocating one byte from the
  initial state produces base zero, frontier one, and taints byte zero.
- `probe_alloc_return_step`: RETURN through the allocated variable returns zero
  from the implicit zero tail. These semantic steps do not certify reachability.

## Concrete candidate

`probe_context` contains `probe_function`: one entry block with IDs 0 and 1,
`p = ALLOCA 1; RETURN p 1`. Initial state is `init_venom_state "entry"`.
Allocation does not expand physical memory, but marks its byte tainted through
`new_site_bytes`. A candidate target keeps p and all other fields, and changes
memory byte zero to one. The target need not itself be reachable. Use lo=0,
positions mapping the allocation site to zero, and a return dead mask that is
empty. This candidate has not been certified against all premises below.

## Full frozen antecedent ledger

| Premise | Evidence / remaining obligation |
|---|---|
| ctx_pass_stage and o1_walk_view | OPEN. ctx_pass_stage_def requires a fn_pass_step witness and observed unit/view for the concrete transformed function; no pass evaluation certified yet. |
| o1_ctx_shape; EVERY fn_eom=NONE | OPEN concrete shape evaluation. Raw function construction gives fn_eom=NONE by definition. |
| ctx_inst_ids_distinct | OPEN concrete evaluation; chosen IDs 0,1 differ. |
| o1_run_state_ok vs0 | OPEN concrete proof including code_layout_valid. o1_run_state_ok_def includes o1_initial_state_ok, fmp equality, layout and nonstatic context. Initial memory/vars/allocas are empty by construction. |
| EVERY wf_function | OPEN concrete evaluation for the candidate function. |
| mem_inv raw_mem_ok | OPEN universal raw-reachability proof. mem_inv_raw_reachable is the existing elimination/equivalence boundary; raw_mem_ok requires frontier below dimword and inst_mem_ok_in_fn. Candidate return range is [0,1), below frontier 1. |
| vs0.vs_allocas=FEMPTY | By init_venom_state_def; not separately exported for candidate. |
| ptr_discipline lo C vs0 | OPEN and critical: quantifies over ALL frame_reachable states, not just a chosen trace. Requires finite reachable-state characterization, then access_ok and taint_ok at both instructions. Allocation creates provenance for p. No such characterization proved here. |
| EVERY fn_ptr_ok P | OPEN concrete proof with P containing p. Must check reachable_fn variant required inside ptr_discipline too. |
| EVERY inst_wf | OPEN concrete evaluation. |
| joint_trace and final EL equality | OPEN. joint_trace_def is joint_initial plus joint_chain; joint_trace_snoc and joint_reachable_iff_trace exist. Need entry + one actual joint transition, including origins/history/provenance and control-index increment. |
| resolved_config_ok | OPEN. resolved_config_initial handles initial configuration; post-allocation resolved_frame_ok must be certified using real origin updates, not arbitrary rv/om. Definition constrains provenance/cache resolutions, not D. |
| lifetime_ok | OPEN concrete proof: [0] at depth zero and n>=0 follows lifetime_ok_def. No D restriction. |
| o1_fn_shape; fn_ptr_ok; MEM inst | OPEN concrete shape/membership checks. |
| relocation_env; relocation_reader_context | Memory-only perturbation preserves these by their definitions. Checked for the literal local pair; allocated pair not yet exported. |
| local_rel with guarded predicates and actual demand | OPEN. Guarded pointer relation needs actual allocation positions and resolved annotations. Byte-zero demand exclusion is checked; other reads/demand must be ruled out from joint_reads, not assumed empty. |
| relocation_taint_le | OPEN with actual demand/tn. Can choose target taint, but no specific witness is certified. No D restriction in relocation_taint_le_def. |
| opcode membership, source step, Halt/Abort disjunction | Concrete candidate source step checked by probe_alloc_return_step; list membership and r=Halt witness are routine but not packaged. |

The inspected rules `frame_reachable` (entry/next/block/call/ret) allow a simple
finite-state characterization for a one-block no-call program in principle.
Existing general projections include frame_reachable_raw,
frame_reachable_mem_inv, frame_reachable_has_origins; none found in this audit
provides the needed concrete two-state characterization. Universal invariants
must not be inferred from the two evaluated semantic steps.

## Exact missing RETURN observation

For evaluated offsets off, off' and common length len define, in this report only,
`rd = TAKE len (DROP off s.vs_memory ++ REPLICATE len 0w)` and
`rd' = TAKE len (DROP off' t.vs_memory ++ REPLICATE len 0w)`.
The exact RETURN payload requirement is:

    LENGTH rd = LENGTH rd' /\
    !i. i < LENGTH rd /\ i NOTIN D.d_ret rd ==> EL i rd = EL i rd'

This is the tight byte-level observation condition for this branch; together
with preservation of the other incoming observable fields, it suffices for
outgoing dead_result_rel. A conservative additional local premise is
`ret_taint tn inst s SUBSET D.d_ret rd` when the clean returned lanes are already
covered by relocation demand. The exact condition above is tighter because even
a tainted nondead lane can happen to agree. Neither condition is asserted to
follow from the full frozen antecedent. No condition has been added to it.
`~joint_read_exempt` does not fix this RETURN obstruction: taint_ok explicitly
permits RETURN to read tainted memory outside revert forwarding.
