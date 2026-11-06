# MLOAD recovery-to-extension audit (.59)

## Certification boundary

The companion theory contains a **quotation only**, `mload_prefix_extension_candidate`.
It typechecks; no MLOAD producer or universal coverage theorem is asserted.
Search of run-owned proofs found `ptr_mload_transport[_back]` and
`ptr_mload_masked_value`, but no complete MLOAD paired-prefix producer.
The candidate includes the full frozen stage antecedent, explicit schedule
witness `names`, an existing paired prefix, MLOAD endpoint and an arbitrary
target chronological step. It assumes neither source success nor byte equality.
It asks for direct one-event extension of h/ht/done/H, unchanged calls/ws,
and `TG' = step_prov PT TG a.po_inst z.po_state`. Numerical taint is in z
and is constrained by the transcript, not an extra supplied post relation.

Cursor normalization is INCLUDED: the successor source cursor may be at the
start of a deleted-NOP gap, as allowed by ptr_paired_cursor. No extra source
stutter is silently appended to h. This follows the existing MSTORE candidate
shape; validating it for MLOAD remains part of the producer obligation.

## Supplier matrix

| Required interface | Installed supplier / exact limitation |
| --- | --- |
| Current source observation, mixed vars, core fields, code/cursor alignment | `ptr_paired_prefix_endpoint`, transcript erasure/source history, samples/alignment projections. Source reachability gives function/instruction membership and source discipline at a. |
| Same MLOAD instruction at target; operand/output arity | `concretize_positions_unchanged` from StepStructure, with paired cursor/ledger alignment (as in MSTORE). `inst_wf` from source shape gives one operand/output. Do not add a rewrite lemma. StepShape exports instruction shape/other opcode; StepCallChecks and Retpc export revert-path and opaque-use preservation; StageShape already covers stage structure. |
| Source operand exists given target success | `ptr_mixed_vars_eval_presence` requires mixed vars and equal labels. Unlike unrestricted ordinary transport, this permits opaque variables. Decompose target ordinary MLOAD step to its successful eval, then get source SOME value. |
| Address value relation | `ptr_nonopaque_instruction_operands`: opaque_use_ok, source inst membership and opcode not in [ASSIGN;PHI;RET;RETFMP;DRET] imply EVERY nonopaque operands. `ptr_mixed_vars_eval` then gives lookup transport for address, requiring equal labels. Source taint discipline must give empty address taint. |
| Non-revert/non-ASSIGN restrictions of both recoveries | MLOAD is not ASSIGN. Non-forwarding is NOT an opcode inequality alone: `in_revert_forward` is block/cursor based. Need active instruction plus `revert_forward_at` instruction-list characterization to exclude MLOAD at that cursor (or reuse a matching existing lemma). This implication has not been proved by this audit. |
| Source read classification | `access_ok_def` gives Var provenance and bounded [off,off+32) if it crosses lo or has provenance. Otherwise the whole scalar range is fixed. Need read descriptor/eval equation, discipline/taint facts and source ownership to identify current/saved owner cache. No read agreement is supplied as a premise. |
| Fixed masked byte | `ptr_paired_fixed_read_recovery` supplies read_byte x equality for x<lo and x outside endpoint taint, under full antecedent plus non-forwarding/non-ASSIGN. To match target address prove scalar transport implies y=x, then w2n y+k=w2n x+k. A per-byte fixed/owned split alone does not replace address classification. |
| Owned masked byte | `ptr_paired_owned_read_recovery` gives b+k -> pa+k equality, but needs owner depth/cache, Var operand/provenance, positive byte offset bound, analysis bp, output function/pass step/view/context names, placements lookup, and historical access/shape/ptr facts. Stage observation/placement and source ownership are ingredients, NOT an automatic application. Derive these witnesses for the SAME active/imported owner, never use retained-birth uniqueness. Address transport must identify w2n y+load_offset with pa+owner_offset (including natural/word range arithmetic). |
| Masked loaded word | `ptr_mload_masked_value`: exactly !k<32 outside tn.t_mem, read_byte(off+k,s)=read_byte(pos+k,t), gives word_agree_except(mem_word_taint tn.t_mem off) (mload off s) (mload pos t). This is usable independently of ordinary vars transport. |
| Backward step transport | `ptr_mload_transport_back` additionally REQUIRES ptr_vars_transport births positions TG tn s t and Var/Lit address. Current samples supply ptr_mixed_vars, NOT that premise. It cannot be applied directly. Labels, if allowed by shape, are a further Var/Lit eligibility check; mixed eval itself supports Label. |
| New output mixed relation | `ptr_mixed_vars_update` preserves opaque variables unchanged and needs new output value transport, untouched nonopaque lookup transport, plus token equality if output is retpc_var. Need source opaque-use/retpc-definition exclusion for MLOAD output. Use masked-word agreement for scalar output with step_prov/step_taint equations; do not equate opaque tokens across executions. This is the first consumer-specific semantic boundary to validate. |
| Tagged and numerical successor | step_prov/out_prov, step_taint/out_taint equations plus ptr_tagged_chrono_step ordinary rule; retain tokens/registry/births/PT/saved/entries. Need actual source OK step and active successor instruction, derived rather than assumed. |
| Shared fields/samples/params | MLOAD updates one variable and advances cursor; prove ptr_core_shared under those updates using existing shared-field boundaries. Samples must hold for all old indices plus new endpoint. Retain parameter alignment, saved callers and calls; no INVOKE/return branch is introduced. |
| Actual writes and ledger | MLOAD has empty actual step_writes by definition; ws remains unchanged. Historical clauses persist on old prefixes, new no-write clause must be discharged. This does not use requested-write framing. |
| Full extension | Assemble transcript, placements (unchanged), samples, alignment, callers and writes, the six clauses of ptr_paired_prefix_def. Existing MSTORE producer is a model for assembly, not a theorem for loads. No complete generic ordinary extension interface was established here. |

## Proposed next small boundary (not asserted)

A mixed MLOAD successor theorem should take the same MLOAD shape, mixed
vars, nonopaque address, equal labels, evaluated x/y, and masked byte premise,
plus target successful step; conclude source successful step and mixed vars
with step_prov/step_taint. Its output-retpc exclusion must come from source
opaque-use/shape facts, not an unjustified scalar assumption. This is a
consumer boundary, not a change to the paired-prefix invariant. After that,
derive its masked-byte premise from the accepted fixed/owned recoveries with
actual owner/stage witnesses, then authorize the full producer separately.

No theorem about positions rewrite was added or restated. No proof of source
success or read equality was smuggled into the candidate. Remaining gaps are
explicit obligations; typechecking the candidate does not certify them.

Verification: holbuild(concretizePtrMloadIntegrationAuditTheory) passes.

## .63 active-owner / production supplier audit (current source)

`mload_masked_bytes_candidate` is a second **quotation, not a theorem**.
It has exactly the classification antecedent, and asks for all 32 untainted
bytes to agree at the evaluated source/target addresses. It adds no owner,
production, byte-equality or source-success premise.

The earlier matrix is historical: its non-forwarding and classification
obligations are now discharged by `ptr_paired_mload_endpoint_inputs` and
`ptr_paired_mload_address_classification` (.61/.62). The mixed-success
consumer has also been checked separately; this audit does not assemble a
producer.

### Exact same-tag owner supplier: already exported

SourceOwnership exports (lines 566–573):
```
ptr_source_ownership vs C h a tokens registry births PT TG saved /\
EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
FLOOKUP TG v = SOME (token,aid) /\
FLOOKUP a.po_prov v = SOME (b,sz) ==>
?d. d <= LENGTH a.po_stack /\
    EL (LENGTH a.po_stack-d) tokens = token /\
    FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz)
```
This is `ptr_source_ownership_live_cache`. Its premises are supplied by
transcript erasure/trace ownership, `~ctx_has_dalloca C`, and the OWNED
classification alternative. It preserves the exact aid, b and sz; no
retained-birth uniqueness is required. Thus active membership is NOT a new
semantic gap.

More directly, `ptr_stage_placements_live_owner` (StagePlacements 59–77)
takes the stage, NONE input eoms, shape, distinct ids, callee_first,
run-state/no-dalloca, the same source ownership, stage placements, and
those same two TG/numerical lookups. It returns
```
?d owner output p.
 d <= LENGTH a.po_stack /\
 EL (LENGTH a.po_stack-d) tokens = token /\
 FLOOKUP registry token = SOME owner /\
 owner = (ptr_owner_view d a).cf_fn /\
 FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
 lookup_function owner.fn_name C'.ctx_functions = SOME output /\
 MEM (Allocation aid,p,sz) output.fn_mems_used /\
 FLOOKUP positions (Allocation aid) = SOME (p,sz)
```
The classified `pa` equals p by functional lookup. Prefer this boundary to
reconstructing historical placement or selecting another numerical owner.

### Recovery premise ledger

| Owned recovery premise (OwnedReadAudit 19–55) | Supplier / remaining assembly |
| --- | --- |
| Existing paired prefix and complete frozen stage antecedent | Identical candidate hypotheses. |
| `vs.vs_allocas = FEMPTY` | `o1_run_state_ok_def`, `o1_initial_state_ok_def`; no use of vs_alloca_next=0. |
| no DALLOCA everywhere | `ctx_has_dalloca_def`, EVERY/EXISTS duality. |
| `EVERY wf_function`, `EVERY fn_inst_wf`, every instruction wf | `o1_ctx_shape_def`, `o1_fn_shape_def`, `fn_inst_wf_def`, fn_insts membership. |
| `EVERY (fn_ptr_ok P)` | Extract existential P once from `ptr_discipline_def` (first conjunct inside EVERY). |
| `!obs. MEM obs h ==> access_ok ...` | transcript erasure/trace source yields `ptr_chrono_history vs C h`; `ptr_chrono_history_reachable` gives EVERY observation reachability; unfold only observation reachability and use ptr_discipline access projection. |
| non-forwarding and opcode not ASSIGN | Endpoint inputs, MLOAD constructor distinction. |
| same-aid owner depth/cache | `ptr_stage_placements_live_owner` above, or `ptr_source_ownership_live_cache`. No missing implication. |
| `lo <= b+k` | `ptr_reachable_owner_allocas_from`: observation reachability / discipline / d bound imply `allocas_from lo (ptr_owner_view d a).cf_state`. `allocas_from_def` plus the exact cache lookup gives lo<=b. |
| k<size, pure byte, numerical provenance | Set k=`w2n x-b+j`; classification b<=w2n x and w2n x+32<=b+sz, j<32 imply k<sz and b+k=w2n x+j. Candidate supplies purity. |
| operand membership, inst_read_op | classified op=Var v; singleton operand; `inst_read_op_def` at MLOAD. |
| output lookup | StagePlacements live-owner supplier above. |
| source owner lookup | `ptr_frame_sizes` gives MEM a.po_fn and EVERY saved cf_fn membership, from endpoint reachability and task shape/run/no-dalloca. Split current/saved with `ptr_owner_view_def`. Context wf supplies distinct function names, so membership implies lookup owner.fn_name C.ctx_functions=SOME owner. |
| production observed/s/out | `ptr_stage_lookup_origin`: stage and output lookup give source fn lookup, fn_pass_step, out.fpo_function=output, ctx names equality, and view. Compare its source lookup to the SAME owner lookup to identify fn=owner. |
| bp and mems equations | Choose precisely bp_analyze_fuel and the lambda in recovery lines 35–36; no semantic side condition. |
| placement and final target arithmetic | classification; w2n y=pa+(w2n x-b) implies w2n y+j=pa+k. No new word arithmetic needed. |

Exact production export (`ptr_stage_lookup_origin`, ImportOrigins 75–83):
```
ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
lookup_function name C'.ctx_functions = SOME g ==>
?fn observed s out.
 lookup_function name C.ctx_functions = SOME fn /\
 fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
 out.fpo_function = g /\
 ctx_fn_names observed.cu_context = ctx_fn_names C /\ view C' fn observed
```

### Decision

No genuinely missing semantic implication was found in the active-owner or
production chain: these are existing exported boundaries, not inferred from
retained births. Remaining work is a direct recovery assembly theorem for
the quoted candidate, with fixed branch using fixed recovery and owned branch
using the ledger above. This diagnostic does NOT prove that theorem. In
particular the source-lookup membership normalization and historical EVERY
access normalization have been inspected as interfaces, not implemented as
new theorems here. They should be handled locally in assembly; if they cause
large instantiation chains, stop and review the interface rather than add
conditional wrappers.

Verification (.63): `holbuild(targets=["concretizePtrMloadIntegrationAuditTheory"])`
passes with the masked-byte quotation. This theory intentionally does not
import MloadEndpoint: Endpoint already depends on IntegrationAudit, so such
an import creates a cycle. Endpoint theorems cited above are documentation
references only; no new theorem here consumes them. The future recovery
assembly belongs downstream of Endpoint, not in this quotation theory.
