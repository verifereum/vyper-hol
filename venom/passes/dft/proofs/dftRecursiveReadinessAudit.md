# Fixed-edit orbit readiness interface audit

Scope: C3.6.3, after accepted E0235. This is a source audit, not a theorem or a proof of the frozen compiler statement. No accepted SML source is changed.

## Finding

The remaining conditional readiness premise of `dft_fixed_orbit_ready` can be separated into an already preserved dynamic invariant and static edit/label facts. No new recursive pending-certificate invariant appears necessary for this particular premise. In particular, neither termination of callees nor successful INVOKE decoding/setup is required. The proposed theorem below is **not proved** by this audit.

## Premise inventory

The target definition is `dftRecursiveActivePhaseScript.sml:23-33`.

| Crossing-readiness conjunct | Available source/interface | What is still required at the consumer |
| --- | --- | --- |
| `dft_original_block f b q` | `dftOriginalRuntimeScript.sml:371-379`, runtime At projection | Obtain original readiness at the queried left orbit cut |
| `dft_original_cut f b q s` | Same projection, with the SAME existential f,b | Same; do not combine independent existential original blocks and cuts |
| block decomposition and current index | Fixed edit structure; queried coordinate in `dftRecursiveFixedOrbitScript.sml:16-19` | Static `q.bb_instructions = pre ++ [x;call] ++ post`; index is the premise of the quantified implication |
| value labels of x bound in current state | `dftOccurrenceOrdinaryClosureScript.sml:493-499` gives current fn membership and `s.vs_labels = L`; runtime projection gives q membership; `fn_insts` membership follows from these and decomposition | Static value-label bound for functions of CURRENT C, and x not INVOKE; this is not a consequence of original readiness alone |
| `~dft_must_order x call` | Static adjacent edit condition | Must be supplied by edit-chain construction; runtime projection cannot imply it |
| INVOKE and ordinary partner opcode exclusions | Static edit class | Supplied to the orbit consumer, not dynamic invariant consequences |
| `inst_wf x`, `inst_wf call` | `dftOriginalScheduleRuntimeScript.sml:37-42` transports membership q->b; `dftProtectedRuntimeScript.sml:6-14` includes `EVERY inst_wf b.bb_instructions` | Extract at this boundary; no SSA claim about the CURRENT reordered function is needed |

`dftOriginalRuntimeScript.sml:333-338` preserves original readiness over every finite left orbit cut. Its stronger label-ready wrapper, lines 342-369, also preserves source provenance. `dft_source_step` and `dft_source_run` in `dftOccurrenceOrdinaryClosureScript.sml:477-490` preserve fn membership and the complete label map independently of instruction success. Thus arbitrary divergent-callee cuts are included.

The independent value-label hypothesis is exactly the expanded predicate in `dftRunRelScript.sml:83-90` (`ctx_labels_bound`); calls/terminators/pseudos are intentionally excluded there. An INVOKE partner x must therefore be excluded before applying this predicate. This is derivable, not an added task restriction: `dftOccurrenceFrameScript.sml:7-17` (`dft_invoke_inversion_disjoint`) makes x's effects empty under `~dft_must_order x call` and `call.opcode=INVOKE`, whereas INVOKE has nonempty effects. The proposed boundary includes `x.opcode <> INVOKE` explicitly to make its label interface simple; a caller may discharge it from those static facts.

## Exact proposed boundary (unproved)

```sml
Theorem dft_original_recursive_orbit_ready:
  dft_original_context Corig C /\ dft_original_label_ready C L c /\
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!fn i l. MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\
    MEM (Label l) i.inst_operands /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_pseudo i.inst_opcode ==>
    l IN FDOM L) ==>
  !j fn s ls n.
    (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
      DftOpen (DftAt fn 0 q s) ls n /\ s.vs_inst_idx = LENGTH pre ==>
    ?f b. dft_recursive_crossing_ready f b q pre x call post s
```

The proof should use `dft_original_label_iter`, active-source projection, runtime At projection, original-block membership, and the readiness definition only at this boundary. There is no need to unfold execution semantics or fixed stacks. It can first prove a current-cut extraction and then iterate, if strategic review considers that interface useful.

## Root, callee, return, and edit-chain checks

* **Root**: `dft_original_label_root` (`dftOriginalRuntimeScript.sml:347-354`) needs `dft_original_function f fn`, reachability of the initial current block in f, strict dominator variables defined, membership in C, and initial labels L. `dft_original_runtime_root` alone does NOT supply source membership or labels. Eventual native root initialization must still discharge these premises from its entry/root contract. The audit does not certify native root adequacy.
* **Callee entry**: runtime-next handles At/INVOKE via `dft_original_runtime_at` (same file:310-330); the context relation supplies original callee lookup. Source provenance preservation covers successful setup. Failure branches become Done and have no At crossing premise. No assumption of successful calls is necessary.
* **Suspended return**: `dft_original_runtime_frame_projection` (381-392) retains the saved original cut, and runtime-next's Done branch invokes `dft_original_runtime_done`. Label provenance includes suspended callers (`dftOccurrenceOrdinaryClosureScript.sml:320-331,502ff`). No pending-certificate details are needed to establish readiness along the LEFT actual orbit.
* **Intermediate schedules**: `dft_original_context` (ScheduleRuntime:20-24) relates every current function to an original SSA function, without requiring current SSA. `dft_original_context_edit` (316-328) preserves it only when the swapped order obeys original schedule edges for every affected original block. Such static edge certificates, not arbitrary runtime projections, must accompany edit composition. The right context can use the same original context when this theorem applies; merely having separate unrelated Corig/Dorig premises is not an edit-chain proof.
* **Static labels across edits**: Since edits permute instructions without changing operands, the expanded label-bound predicate should be transported by instruction membership preservation. This consumer theorem is not supplied by the runtime projection and has not been checked here for a whole edit chain. The frozen task supplies the bound initially, but connection to each current C remains an integration obligation.
* **Partner success / prefix availability**: do NOT add these as assumptions. `dft_recursive_crossing_partner_success` (ActivePhase:35-52) already derives success from readiness, using `dft_original_crossing_cut` and `dft_original_cut_eval_operand` (ProtectedRuntime:41-54). Original cut contains the dynamic prefix availability. This boundary must not reconstruct it as an additional invariant.

## Still outside this audit

Derivation of a suitable original context and root for every composed edit, GAS-partner transport, terminal/native adequacy, finite uniform reading-list realization, and the frozen compiler theorem remain unproved. The ordinary-partner orbit observation/event results are conditional on exactly the audited premise; they are not yet a native simulation.
