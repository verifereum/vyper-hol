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
