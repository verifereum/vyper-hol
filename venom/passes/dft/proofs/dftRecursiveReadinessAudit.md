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

## C3.6.6 consumer ledger (source audit, not proof)

The proposed boundary above is now checked as `dft_original_recursive_orbit_ready`, and `dft_original_fixed_orbit_ready` is its checked wrapper (`dftRecursiveOrbitReadinessScript.sml:7-55`). The following ledger concerns **using** that wrapper, not changing it.

| Wrapper premise | Source or remaining obligation |
| --- | --- |
| `dft_original_context Corig C` | Required chain invariant. Definition is ScheduleRuntime:20-24; it records original SSA/wf/pseudo-prefix and block correspondence, NOT current SSA. Initial reflexivity still needs original block schedule initialization; the frozen LIST_REL premises alone are not this theorem. |
| `dft_original_label_ready C L c` | Checked label_root (OriginalRuntime:347-354), followed by label_iter (364-369) for cuts of the same context. Changing context requires a new paired root/phase construction; iteration in C does not initialize an edited orbit. |
| decomposition `q = pre ++ [x;call] ++ post` at instruction-list level | Supplied by an adjacent `inv_edit` witness (ScheduleEdits:6-10,36-44). Identifying its q with the concrete context block remains chain bookkeeping. |
| `~dft_must_order x call` | inv_edit_provenance requires ALL_DISTINCT destination and original-to-destination order preservation. It does not follow from mere PERM. |
| call INVOKE; partner neither pseudo, terminator, INVOKE, ALLOCA nor GAS | Ordinary/INVOKE edit-class classification obligation. This wrapper intentionally does not cover GAS partners or swaps with no INVOKE. Opcode exclusions must be derived from schedule facts/shape or sent to their own edit-class transport theorem. |
| expanded label-bound predicate | Exactly ctx_labels_bound_def (RunRel:83-90); original task supplies it in C. Transport to intermediate contexts is unproved, but instruction-membership preservation suffices. |
| `dft_fixed_phase ... c d` | Paired initialization/transport obligation. Neither original_label_root nor the static schedule certificates construct d. This remains separate from static readiness. |
| original context for edited C | Checked original_context_edit (ScheduleRuntime:316-328), provided its universal original-edge premise is established. Corig may then also serve as Dorig; unrelated original contexts are unnecessary. |

### Exact candidate interfaces for subsequent authorization (ALL UNPROVED HERE)

These candidates state missing boundaries, not extra assumptions on the frozen theorem.

1. Static membership and labels. The decomposition premise is essential: edit_block overwrites every block structurally equal to q, rather than swapping an arbitrary list in place.

```sml
Theorem dft_gas_edit_fn_insts_mem:
  q.bb_instructions = pre ++ [x;y] ++ post ==>
  (MEM i (fn_insts (dft_gas_edit_fn q pre x y post fn)) <=>
   MEM i (fn_insts fn))

Theorem dft_gas_edit_ctx_labels_bound:
  q.bb_instructions = pre ++ [x;y] ++ post /\ ctx_labels_bound C L ==>
  ctx_labels_bound (dft_gas_edit_ctx q pre x y post C) L
```

Definitions are OccurrenceGasEdit:6-19: block conditional, MAP over blocks, MAP over functions. Prove the membership boundary by block cases and fn_insts membership; then unfold ctx_labels_bound once and pull back function membership through MAP. No opcode or SSA assumptions are needed for this static fact.

2. Entry root, independent of native adequacy.

```sml
Theorem dft_original_label_entry_root:
  dft_original_function f fn /\ MEM fn C.ctx_functions /\
  fn_entry_label fn = SOME s.vs_current_bb /\ s.vs_labels = L ==>
  dft_original_label_ready C L
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
```

Source justification: fn_reachable_def (venomWf:543-546) is an existential entry plus RTC. original_function_entry transports the entry label to f; RTC reflexivity supplies entry reachability. original_root_dom (OriginalCutLifecycle:55-61) supplies strict_dom_vars_defined for **any** s at the entry, with no requirement on initial variables. Then apply original_label_root. Thus there is no missing semantic assumption for this candidate.

For actual run_context initialization, the required s is the input state with vs_prev_bb := NONE, vs_current_bb := lbl, vs_inst_idx := 0. run_context/run_function (ExecSemantics:1884-1907) perform exactly these resets and preserve labels. This observation is NOT an erasure/adequacy theorem. NONE entry/function/block cases return errors and need separate native terminal handling; they cannot be treated as initialized DftEnter roots.

3. Local original-context preservation, stated with a specific original list and a **universal** provenance obligation because the context edit acts on all structurally equal blocks:

```sml
Theorem dft_original_context_inv_edit:
  dft_original_context Corig C /\
  q.bb_instructions = pre ++ [x;y] ++ post /\
  inv_edit orig dest q.bb_instructions (pre ++ [y;x] ++ post) /\
  ALL_DISTINCT dest /\ schedule_edges orig dft_must_order dest /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
  (!f b. MEM f Corig.ctx_functions /\ MEM b f.fn_blocks /\
    dft_original_block f b q ==>
    b.bb_instructions = orig /\
    schedule_edges orig dft_must_order q.bb_instructions) ==>
  dft_original_context Corig (dft_gas_edit_ctx q pre x y post C)
```

inv_edit_schedule_edges (ScheduleEdits:161-169) and original_context_edit prove the intended route. This candidate is deliberately conditional: the universal original-list equality is NOT supplied by the frozen contract and must not be smuggled into it. A chain construction must either establish it for each affected original block (including duplicates across functions), establish the needed edges separately for every such block, or use a more localized edit representation in a separately authorized design. The existing context edit has no function/label selector.

### Chain construction audit

`inv_edit_factor` (ScheduleEdits:136-141) gives an RTC for distinct original lists and PERM destinations. `inv_edit_rtc_schedule_edges` (172-184) preserves original-edge order at all its prefixes; `inv_edit_rtc_perm` and `inv_edit_rtc_distinct` preserve membership/distinctness. These are list-level interfaces, not a context-level edit enumeration. A DFT consumer must connect the exact original/final lists (including fixed pseudos and terminator), prove their distinctness and final schedule_edges, classify every crossing, and lift each edit to the intended context. Equality-based replacement of repeated structurally equal blocks is the concrete outstanding bookkeeping issue; do not infer it from a single selected block's edge certificate.

No additional hypothesis on the frozen task is justified by this audit. What remains is deriving the above static/root certificates from the existing function relations and shape, constructing related occurrence roots, handling other edit classes, then native adequacy and finite uniform realization. In particular, the entry-root candidate would discharge readiness initialization only, not `dft_fixed_phase`, result compatibility, or all-fuel simulation.
