# Universal induction inventory (C1.5.90.53)

Design artifact, not a theorem. No coverage, exclusion or falsehood is certified.
Reuses concretizePtrInterfaceAudit.md (.18), concretizePtrReadBoundaryAudit.md
(.45, including rejection of its local candidate), and E0267/.49
(TO_concretize_ptr-20261105T100526Z_m9496_t001). Their StagePtr/ctx_eom_bounded
references are historical. Only frozen StageStatic/max_live_eom is current.
.50--.52 supply local write CONTENT, not source execution or writer exclusion.

## Proposed coverage and simultaneous witnesses

Specification macros below are NOT installed HOL constants. A(rpolicy,C,Ct,vs,
lo,eom) means exactly the complete frozen antecedent, with C'=Ct, including
existential names and max_live_eom Ct = SOME eom. No additional hypotheses.
Proposed quantifiers:

```
!rpolicy C Ct vs lo eom ht at.
 A(rpolicy,C,Ct,vs,lo,eom) /\ ptr_chrono_history vs Ct ht at ==>
 ?positions R h a done tokens registry births PT TG saved entries H W.
   ptr_stage_placements Ct positions /\ ptr_chrono_history vs C h a /\
   ptr_structural_trace R vs C Ct h a ht at done
     tokens registry births PT TG saved entries /\
   Production(R,C,Ct,positions) /\
   Transport(lo,C,Ct,positions,h,a,ht,at,done,tokens,registry,births,
             PT,TG,saved,entries,H,W)
```

Production must connect each source function to its ACTUAL output lookup and
successful per-function positions rewrite, with preserved control structure.
Global positions maps keys to (position,size), not per-function positions.
The stage-to-rewrite witness must come from existing decomposition; R must not
be an arbitrary supplied relation or equality of full source/target functions.

Transport's finite data and obligations:

1. Actual corresponding function/block/predecessor labels, retained instruction
   cursors, equal inst ids; suspended return cursors have the same production
   mapping. Source current cursor normalized across only deleted NOPs.
2. H records the SAME tagged derivation underlying structural_trace, including
   tokens/registry/births/PT/TG/saved at every source observation and entry-index
   correspondence. Restriction to prefixes preserves these exact witnesses.
   For E=done++[LENGTH h-1], every j<LENGTH ht has H at E[j] satisfying
   `ptr_source_ownership vs C (TAKE (SUC (EL j E)) h)
   (EL (EL j E) h) tokensj registryj birthsj PTj TGj savedj` and
   `ptr_vars_transport birthsj positions TGj (EL (EL j E) h).po_taint
   (EL (EL j E) h).po_state (EL j ht).po_state`.
   Parameter/saved relations use these SAME historical tags and masks.
   Later births/entries agree on earlier domains; endpoint maps cannot silently
   replace historical maps. sample_ownership's fresh existentials do NOT give H.
3. Explicit relation for labels, call/tx/block environment, code/data, returndata,
   accounts/transient/logs/deletions, outcomes/requests, return-PC and params.
   FMP/allocator fields need a specified relation, not global state equality.
   Masked variable equality alone does not imply storage/log/request equality.
4. W records PAST actual paired successful writes: source pre/post w,w+1,
   target j,j+1, owner (fixed or token,aid), offset/size, actual footprints,
   and immediate postwrite equality outside source POST-taint. Equality is at
   w+1, not E[j+1]. Each entry retains historical operand/tag/placement evidence
   needed to classify it relative to a later read owner. Include fixed initial
   sentinel; do not assert equality for initially uninitialized owned memory.
   W contains NO target suffix exclusion and NO future read agreement.

H/W types, Production predicate and shared-field relation are still unresolved
implementation/specification boundaries. This report deliberately does NOT
pretend its macros are typechecked HOL. The exact outer quantifier direction
is fixed; the missing implications below must be resolved before installing
an invariant. An invariant with these gaps is not a closed proof specification.

## Quantified base/step obligations

I(h,a,ht,at,K) denotes the entire witness conjunction above, with K all internal
data. In every step, K' must extend the SAME old witnesses on earlier domains.
Each schema universally quantifies frozen parameters and all displayed inputs.
Source transitions/success and target exclusion appear ONLY as conclusions.

B: For A and each target entry derivation [at], construct source entry [a0],
root ownership, initial transport and finite source NOP gap to h,a,K; conclude
`?h a K. I(h,a,[at],at,K)`. Source enters_block/PHI success must be derived
from target entry and initial variables, not assumed. Same initial vs supplies
fixed sentinel equality. Do not use alloca_next=0 or assume initial owned bytes
agree at relocated positions.

G: For A,I before cursor normalization, if production says the source current
instruction is deleted, construct its actual NOP tagged step, preserve transport
and W, extend H, target unchanged. Iterate finitely to next retained cursor.
Use block wf/retained terminator to obtain a next active instruction: no imaginary
terminal gap. This is source-only trace gap, not another target event.

N: For A,I(h,a,ht,at,K),bt and EACH target next derivation at->bt, construct
b,PT',TG',saved' and actual `ptr_tagged_chrono_step C (HD tokens) a b PT TG
saved PT' TG' saved'`, equal inst ids, unchanged stack depths, post-transport,
W/H extensions; apply trace pair, then G to obtain I for ht++[bt]. Dispatch
partition below supplies the finite sub-obligations. No matching source OK is
a premise.

J: Same quantifiers for target block. Construct source OK/nonhalted result,
same successor selection, successful source enters_block and parallel PHIs
from pre-entry variables, ghost/taint changes and next active instruction;
pair, G. Only JMP/JNZ/DJMP have OK terminator dispatch. Changed whole blocks
are NOT equal; only PHI prefix/control/cursor boundaries should be used.

C: Same quantifiers for target call. Derive source decode, actual callee lookup,
argument eval, setup/entry success and active instruction. Push exact saved
caller maps/cursor; create source token LENGTH h and target entry LENGTH ht,
retain earlier registry/births/entries, relate callee PT/empty TG/shared fields;
pair, G. No completed callee execution is an input.

R: Same quantifiers for target ret. Invert IntRet/bind and derive source IntRet,
source bind success, scalar returned values, restored saved maps/token/cursors,
shared state and memory; pair, G. RET admitted; DRET/RETFMP excluded by source
fn_ptr_ok plus target preimages. Raw ret rule has no opcode guard: invert
step_inst. INVOKE converts nested IntRet to OK (run_defs:1704--1730), so cannot
supply this ret rule. Equal return list/source success cannot be premises.

D: For each I endpoint and current evaluated source read, derive agreement for
its untainted bytes BEFORE executing the read. Source reachable/access_ok/taint_ok
come from I and A. Owned byte (token,aid,k): select last initializing SOURCE
writer w<LENGTH h-1 with protected_history/livesets; prove unique departed target
j with E[j]=w (NOPs do not write); W gives equality at source w+1,target j+1.
Prove X for all intervening writes; frame source NOP gaps and apply interval
byte framing. Fixed bytes use last fixed writer or initial sentinel. Empty
ranges vacuous; tainted inputs require correct mask propagation, not equality.

X: For every such read/writer and j<q<LENGTH ht-1, classify actual target q
write relative to this endpoint owner using SAME H historical tags/placements.
Conclude relocated byte not in q's actual footprint. Source suffix protection
is available on already built prefix; target suffix protection is NOT a premise.

W-step: I plus current target transition -> D for old read bytes if needed ->
source success -> immediate postwrite content -> new W entry -> pair -> G.
MCOPY uses OLD memory even when overlapping, never its own W entry for its read.

Finite dependency graph:

```
A + target entry -> B/PHI -> actual source prefix + H
I_n + target transition -> operand/tag/placement facts
 -> D_n [W_<n + X_n + protected already-built SOURCE prefix]
 -> source step + post-fields -> W_n content -> trace pair -> G -> I_(n+1)
```

No future source endpoint is required for D_n. The missing historical-witness
retention and X implications are real gaps in this graph, not removed by local
content boundaries.

## Exhaustive dispatch partition

Checked against venomInstScript.sml:23--69, is_terminator_def:346ff and
venomExecSemanticsScript.sml:597--1183/1704--1730. Each opcode constructor occurs
once in the sets below. Classification uses SOURCE preimages: target ASSIGN
may be source ALLOCA, not ordinary assignment. Every residual remains unproved
unless the cited conditional boundary's premises are derived from I.

| Row | Disjoint opcode set | Chronological admission and remaining implication |
|---|---|---|
| N1 | ADD, SUB | next; affine/back-prefix boundaries exist; integrate exact historical witnesses, masks, metadata and cursor |
| N2 | MUL, Div, SDIV, Mod, SMOD, Exp, ADDMOD, MULMOD, SLT, SGT, ISZERO, AND, OR, XOR, NOT, SHL, SHR, SAR, SIGNEXTEND, BYTE, OFFSET | next; scalar/masked operation, shape/evaluation/Label success residual; OFFSET is not automatically affine ADD |
| N3 | EQ, LT, GT | next; common numerical provenance must imply compatible displacement; ordered comparisons need nonwrapping target closed endpoint; coincident zero-size distinct tags remain explicit |
| N4 | ASSIGN | exact immediate mixed paired-prefix extension checked in AssignProducer; includes opaque copies; ALLOCA preimage is N17 |
| N5 | PARAM | exact immediate mixed paired-prefix extension checked by ptr_paired_prefix_param (concretizePtrParamProducer); root empty-PT/equal-params and transported callee parameters handled, without supplied source success; normalization/universal dispatch remains open |
| N6 | INITIAL_FMP, BUMP, RETPC_PARAM | next; explicit FMP/return-PC relation and two-output BUMP residual; NOT in fn_ptr_ok exclusion list |
| N7 | MLOAD, ILOAD | next; D, masked load/taint and prefix attachment; ILOAD scalar-address syntax does not make its byte read disappear |
| N8 | MSTORE, MSTORE8, ISTORE | next; actual footprint, masked value bytes/taint/bookkeeping; MSTORE local boundaries do not prove entire family |
| N9 | MCOPY | next; D then ptr_mcopy_masked_content, actual operand/owner/placement/W integration |
| N10 | CALLDATACOPY, CODECOPY, DLOADBYTES, RETURNDATACOPY | next; .51 content conditional on operands/payload equality; derive these and OOB guard for returndata case |
| N11 | EXTCODECOPY | next; account-code payload, actual footprint/shared-state residual |
| N12 | SLOAD, SSTORE, TLOAD, TSTORE | next on OK; storage/transient masked observation/write residual; static-frame writes Abort |
| N13 | CALLER, CALLVALUE, ADDRESS, ORIGIN, GASPRICE, GAS, GASLIMIT, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, CHAINID, SELFBALANCE, BALANCE, BLOCKHASH, BASEFEE, CODESIZE, EXTCODESIZE, EXTCODEHASH, RETURNDATASIZE, BLOBHASH, BLOBBASEFEE, CALLDATASIZE, CALLDATALOAD, DLOAD | next; environment/scalar result/argument/taint residual; inspect actual GAS semantics, not equal memory lengths |
| N14 | SHA3, LOG | next on OK; D -> payload/hash/log/taint; LOG physical operand order/topics/static guard |
| N15 | CALL, STATICCALL | next on OK; .52 content requires WHOLE request read equality and exact shared fields; derive those (untainted byte equality alone insufficient absent taint_ok); MIN output footprint |
| N16 | DELEGATECALL, CREATE, CREATE2 | next on OK; request/read/outcomes/accounts/rollback/return values and actual effects residual; cannot rename CALL lemma |
| N17 | ALLOCA | immediate full certificate checked (E0441); normalized schema-restricted coverage checked by `ptr_paired_structural_prefix_normalize` in concretizePtrStructuralDispatch, retaining all explicit schema bridge premises |
| N18 | ASSERT, ASSERT_UNREACHABLE | next when condition true; derive scalar untainted condition equality; false condition aborts |
| J | JMP, JNZ, DJMP | block; successor/control/evaluation and PHI entry residual |
| C | INVOKE | call only; next explicitly excludes, not a terminator, IntRet converted to OK |
| R | RET | `ptr_paired_ret_prefix_immediate` (concretizePtrReturnPrefix) now constructs the complete immediate paired prefix from the exact successor_births antecedent: historical caller parameters transported through retained births, both stacks/saved/calls popped, ledger unchanged. Deleted-NOP normalization is checked by `ptr_paired_structural_prefix_normalize` under the explicit universal-schema bridges; exhaustive universal dispatch remains open. Root IntRet has no successor |
| X1 | MEMTOP, GETFMP, SETFMP, FMP_PARAM | raw next exists, source fn_ptr_ok excludes; transfer exclusion by actual stage preimage |
| X2 | DALLOCA | raw next exists, frozen no-DALLOCA excludes; transfer to output |
| X3 | DRET, RETFMP | raw ret exists, source fn_ptr_ok EXCLUDES; target preimage exclusion required |
| X4 | PHI | ordinary step Error; prefix PHIs atomic in B/J/C enters_block |
| X5 | NOP | source deleted-gap only; output preimage excludes retained NOP |
| T | RETURN, REVERT, STOP, SINK, SELFDESTRUCT, INVALID | Halt/Abort/Error, no departing event, but active observation still needs final static bound |

DRET's pack_dret_dynamic reads/writes and adopted cursor are not a forgotten
writer branch: ptrDisciplineScript.sml:120--139 explicitly excludes DRET,
RETFMP, GETFMP, SETFMP, FMP_PARAM, MEMTOP. DALLOCA separately excluded. Earlier
read audit's DRET residual should be retired by syntax/preimage inversion,
not by implementing a forbidden writer branch. INITIAL_FMP/BUMP/RETPC_PARAM
cannot be discarded with them.

Malformed operands/undefined eval, RETURNDATACOPY OOB, false assertions, static
writes/value CALL have no continuing transition in failing branches. There is
no chrono Halt/Abort/Error constructor. T opcodes can be final ACTIVE observations;
RETURN/REVERT memory bounds and revert-forward exemption are still obligations.
No equality of dead terminal payloads is needed just for continuation, but source
failure while target continues cannot be ignored. Default base Error includes
INVOKE (handled by run_defs); there is no extra unknown opcode constructor.

## Owner-relative X partition

For each actual nonempty successful memory write, divide selected read byte and
writer address into fixed or owned by source access_ok and historical operand
transport. Empty writes vacuous; requested CALL size is not actual MIN footprint.
For owned/owned compare TOKENS and allocation ids, not function names.

| Read / writer owner | Existing boundary | Residual implication from SAME I/H/W |
|---|---|---|
| fixed / fixed | identity map, initial sentinel or source last writer | scalar address and actual footprint equality; source suffix exclusion transfers by identity |
| fixed / owned | production reserved-interval separation | actual writer item/placement/size and footprint containment; fixed read's reserved interval |
| owned / fixed | fixed containment | derive write end <= lo and owned placement outside reserved region; fixed_region_reserved alone is not output geometry |
| owned / exact same (token,aid) | same-owner transport exclusion | historical and endpoint birth agreement, offsets and strict endpoints; transport source nonwrite for every writer family |
| owned / same token, different aid | local/local layout separation | BP write origin, source conflict/liveset, actual layout items and footprint containment |
| owned / writer strict descendant while read owner suspended | suspended-descendant/local-import separation | identify owner path/depth/lifetime at writer; imported placement equals original owner's placement |
| owned / writer strict ancestor | original-owner local/import separation, after rebasing | identify actual conflict supplier/view; descendant-local theorem has wrong direction by itself |
| owned / distinct non-ancestor tokens (completed siblings/repeated invocation) | no general disjoint-static-position theorem: static slots ARE reused | prove protected lifetime forces a simultaneous-stack separation case, or exclude this configuration from valid endpoint demand; token/function inequality is insufficient |

Executing descendant writing through imported pointer is classified by DESTINATION
owner, not executing callee. Retained births are not live demand. Returned owners
must be excluded from current valid demand or treated by explicit lifetime
reasoning. This is parent-level unresolved content, not a premise to insert in I.

## Source contracts used by this graph

Paths below abbreviate concretizePtr*Script.sml in this directory. Source lines
are the checked locations, not invented new exports. Earlier .18/.45 reports
retain the detailed support/protected-liveset/local exclusion signatures.

* ChronologicalHistory:29--71: exactly next/block/call/ret; :84--101 entry/snoc.
  StructuralTrace:11--48 root/gap/pair. Pair REQUIRES actual tagged source step
  AND actual target chrono step, equal inst ids, matched same/call/return depths
  (call additionally R b.po_fn bt.po_fn). Thus it cannot construct source success.
* StructuralTrace:105 `ptr_structural_trace_embedding`:
  `ptr_structural_trace R vs0 C Ct h a ht at done tokens registry births PT TG
  saved entries ==> LENGTH done+1=LENGTH ht /\ ptr_event_embedding h ht
  (done++[LENGTH h-1])`. :69 ownership projection preserves exact witnesses.
  :171 `ptr_structural_trace_entry_sound`: same premise implies
  `!t j. FLOOKUP entries t=SOME j ==> t<LENGTH h /\ j<LENGTH ht /\
  ?fn. FLOOKUP registry t=SOME fn /\ R fn (EL j ht).po_fn`.
  :226 sample_ownership only existential prefix witnesses, NOT historical
  transport or equality of tags with those in a paired derivation.
* StagePlacements:9 `ptr_stage_placements Ct positions` iff for all key,p,sz,
  `FLOOKUP positions key=SOME(p,sz) <=> ?g. MEM g Ct.ctx_functions /\
  MEM(key,p,sz) g.fn_mems_used`. :28 ptr_stage_placements_exists uses stage,
  NONE input eoms, shape, distinct ids and callee_first. :59 live_owner adds
  run-state/no-DALLOCA, source ownership, TG and numerical G lookups; concludes
  d<=stack depth, token at that depth, original registry owner/cache, actual
  output lookup, MEM(Allocation aid,p,sz) output.fn_mems_used and positions lookup.
* ValueTransport:98 `ptr_vars_transport_eval_all` is Label-aware evaluation;
  AffineTransport:162/188 and OwnedAffinePrefix:166/198/271 supply conditional
  actual affine back/aligned prefix extension. Their supplied ownership/value/
  metadata conditions are not arbitrary-opcode coverage.
* CopyContent:7 `ptr_mcopy_masked_content` exact signature schema:
  opcode MCOPY, operands [dop;sop;nop], source evals d,r,n, target dt,rt,n,
  `!i. i<w2n n /\ w2n r+i NOTIN tn.t_mem ==> read_byte(w2n r+i) s.vs_memory
  =read_byte(w2n rt+i) t.vs_memory` imply
  `?s' t'. step_inst_base inst s=OK s' /\ step_inst_base inst t=OK t' /\
  !i. i<w2n n /\ w2n d+i NOTIN mem_taint tn inst s s' ==>
  read_byte(w2n d+i) s'.vs_memory=read_byte(w2n dt+i) t'.vs_memory`.
  No disjointness assumption, no target exclusion conclusion.
* BufferCopyContent:14/32/50 ptr_calldatacopy_content/ptr_codecopy_content/
  ptr_dloadbytes_content: respective opcode, [dop;sop;nop], source eval d,r,n,
  target dt,r,n and equality of calldata/code/data-section payload imply
  `?s' t'. step_inst_base inst s=OK s' /\ step_inst_base inst t=OK t' /\
  !i. i<w2n n ==> read_byte(w2n d+i) s'.vs_memory=
  read_byte(w2n dt+i) t'.vs_memory`.
  :68 ptr_returndatacopy_content same with returndata equality AND
  `w2n r+w2n n<=LENGTH s.vs_returndata`; :87 success_bound derives this guard
  on target from evaluated target operands and actual target OK.
* ExternalCallContent:38 ptr_call_content: opcode CALL, seven operand evals
  (gas may differ; addr,value,az,rz equal; ao/ro relocate), one output,
  `read_memory (w2n ao) (w2n az) s=read_memory (w2n at) (w2n az) t`,
  equal call_ctx,accounts,transient,logs,pending_deletions,outcomes,requests,
  and nonstatic-value guard imply both actual OK steps, equal output lookup,
  returndata and all those updated shared fields, plus
  `!i. i<MIN(w2n rz)(LENGTH s'.vs_returndata) ==>
  read_byte(w2n ro+i) s'.vs_memory=read_byte(w2n rt+i) t'.vs_memory`.
  :74 ptr_staticcall_content drops value operand/guard and uses zero value/T;
  :105 ptr_call_success_nonabort derives static-value guard from target OK.
  This boundary deliberately does not require equal gas words.
* OperationalBytes: ptr_chrono_history_interval_byte_frame supplies source
  finite-interval framing. ptr_chrono_last_writer_agreement consumes BOTH
  exclusions and COMMON indices; .45's sampling/NOP framing adaptation is needed.
  It cannot be directly instantiated with unequal stuttering indices.

D0004: searched contract/concretizeStepStructureScript.sml. Reuse existing
concretize_positions_inst_id (:6), terminator/nonterminator (:13/:24), phi (:32),
nop (:63), inst_wf (:69), no_alloca (:119), blocks (:141), block_succs (:224),
var_operand (:237), entry_label (:245), cfg_edge (:255), reachable (:284).
Exact preimage (:99): `MEM bb (concretize_function_with_positions p fn).fn_blocks
/\ MEM i bb.bb_instructions ==> ?oldbb oldi. MEM oldbb fn.fn_blocks /\
MEM oldi oldbb.bb_instructions /\ i=concretize_inst_with_positions p oldi /\
i.inst_opcode<>NOP`. Labels (:91) equal. LedgerAlignment:105 already gives a
same-label target block and ptr_ledger_block_alignment for every source block.
No missing positions-rewrite fact and no duplicate lemma is proposed here.

## Review request / finite residual set

Residuals have names B,G,N1--N18,J,C,R,D,X as above, not new PLAN component IDs.
The parent needs ONE integration revision, not an open-ended opcode queue:

* Settle exact historical transcript restriction and original-owner placement
  interface, including completed activation/lifetime case in X.
* Specify shared-field/FMP relation strong enough for N6,N12--N16 and return.
  Do not substitute equal whole states or future-read equality.
* Prove D/X using historical evidence and actual production conflicts; W content
  successes reduce initializer cases but do not discharge a single suffix X.
* Compose source-success construction and cursor/PHI/call/return bookkeeping in
  the simultaneous induction. Terminal observations remain final bound consumers.

No residual may assume universal coverage, matching source success, or target
noninterference. Current interfaces do not close this specification. In
particular the exact H and shared-field predicates cannot responsibly be claimed
validated merely by writing down these macros. No frozen-theorem falsehood is
claimed; no unprovability evidence was produced.

Verification: source dispatch/signatures inspected read-only. Regression build
of CopyContent, BufferCopyContent and ExternalCallContent passed at session start
(TO_concretize_ptr-20261105T100526Z_m9607_t001). This report adds no SML or cheats.

## Shared-field boundary checkpoint (.56)

`concretizePtrSharedFieldsTheory` defines `ptr_shared_fields` independently
of memory, vars, params, cursor (`vs_current_bb`, `vs_inst_idx`, `vs_prev_bb`)
and allocation bookkeeping. Exact shared fields are: transient, accounts,
returndata, logs, outcomes, requests, pending_deletions, gas_readings,
immutables, call_ctx, tx_ctx, block_ctx, data_section, labels, code,
prev_hashes, fmp, call_entry_fmp, initial_fmp, return_pc_token, halted
(all with the `vs_` prefix). `vs_labels` is a shared lookup environment,
not the excluded execution cursor.

Checked interfaces: reflexivity; independent update_var stability;
target-success implies source-success for setup_callee with possibly
relocated argument lists; merge_callee_state compatibility; adopt_return_fmp
compatibility when both return adoption options are NONE. Setup needs
matching block nonemptiness and equality of the final argument token
(default 0w for empty args), NOT equality of the complete arguments.
Deriving this token equality from value transport remains an integration
obligation. Equal gas queues are intentional: NOP/ALLOCA removal does not
remove GAS observations.

Source audit (`venomExecSemanticsScript.sml:722-753`): INITIAL_FMP reads
`vs_initial_fmp` and performs one update_var. RETPC_PARAM requires a literal
operand but ignores its index value and reads `vs_return_pc_token`.
BUMP uses explicit evaluated base and size: first writes ptr_out=base,
then next_out=word_add base size; it neither reads nor changes FMP.
If the two output names coincide, the second write wins. Shared-field
stability therefore covers coincident outputs as well; equal/relocated
output VALUES remain with the separate value relation. No conditional
opcode wrapper or source simulation theorem is inferred from this audit.

## Demand lifetime / production conflict audit (C1.5.90.57)

This section supersedes the suggestion in the X table that numerical interval
presence is wholly missing. The audit outcome is localized unresolved interfaces,
not universal coverage and not a counterexample to StageStatic. No SML theorem
is added by this report. Checked prerequisite targets: ProtectedLivesets,
HistoricalPlacement and SharedFields (2026-11-05).

### Existing lifetime evidence and the SAME writer

Exact source signatures relevant to lifetime (all variables implicitly universally
quantified by the existing declarations):

* `ptr_source_ownership_live_prov` (SourceOwnership:520--523):
  `ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
   EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
   FLOOKUP TG v = SOME (token,aid) ==> MEM token tokens`.
  Saved provenance has the stronger suffix conclusion
  `MEM token (DROP (SUC n) tokens)` for `n < LENGTH saved` and
  `FLOOKUP (SND (EL n saved)) v = SOME (token,aid)` (same source:541--545).
  These are live-tag facts, not facts about all retained births.
* `ptr_chrono_endpoint_birth` (EndpointOrigin:58--72) takes
  `ptr_chrono_history vs0 ctx h endpoint`, empty initial allocas, no DALLOCA
  at every history index, `j < LENGTH h`, `d <= LENGTH (EL j h).po_stack`,
  and `FLOOKUP (ptr_bottom_state d (EL j h)).vs_allocas aid = SOME site`.
  Its conclusion is exactly
  `?i fuel sa'. i < j /\ LENGTH (EL i h).po_stack = d /\
   (EL i h).po_inst.inst_opcode = ALLOCA /\
   (EL i h).po_inst.inst_id = aid /\
   FLOOKUP (EL i h).po_state.vs_allocas aid = NONE /\
   step_inst fuel ctx (EL i h).po_inst (EL i h).po_state = OK sa' /\
   FLOOKUP sa'.vs_allocas aid = SOME site /\
   (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
   FLOOKUP (ptr_bottom_state d (EL (SUC i) h)).vs_allocas aid = SOME site`.
  Thus this is birth of the continuously present bottom-depth owner, not an
  arbitrary earlier activation with the same allocation id or function name.
* `ptr_endpoint_protected_history` (ProtectedHistory:31--55) already returns
  `?w. w + 1 < LENGTH h /\ ptr_chrono_write C x (EL w h) /\
   (!k. w <= k /\ k < LENGTH h ==>
     d <= LENGTH (EL k h).po_stack /\
     FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz) /\
     ~in_revert_forward (EL k h).po_fn (EL k h).po_state) /\
   (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write C x (EL k h)) /\
   ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
   ml_read_gen (Allocation aid) bp mems (ptr_owner_view d endpoint).cf_inst`.
  Its antecedent is precisely lines32--47 of that source: history, empty initial
  cache, shape/wf/reachable/SSA/fn_ptr_ok/inst_wf/no-DALLOCA, history access_ok,
  non-revert/non-ASSIGN endpoint, owner cache and positive byte bounds, untainted
  endpoint byte, selected Var read (or INVOKE), numerical provenance and owner BP.
  The proof obtains birth i then selects w with i<w; the cache/depth guard holds
  even at w, not only at w+1. This answers numerical lifetime positively.
* `ptr_endpoint_protected_livesets` (ProtectedLivesets:8--43) adds actual stage,
  per-function pass, observed-context and source discipline premises. Its exact
  output is
  `?w. w + 1 < LENGTH h /\ ptr_chrono_write C x (EL w h) /\
   (!k. w < k /\ k + 1 < LENGTH h ==> ~ptr_chrono_write C x (EL k h)) /\
   (!t. w < t /\ t < LENGTH h ==>
     ?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
       observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
       MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
            (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs)`.
  Its proof uses ProtectedHistory ONCE at lines48--49 and retains precisely that
  witness w. Its exported conclusion discards the depth/cache/non-revert and
  used/read seed conjuncts. Calling the two exports independently need not yield
  the same w. Recommended interface repair: strengthen THIS existing export
  in-place to retain those conjuncts, rather than create a synonym wrapper or
  assume equality of independently chosen writers. No repair is installed here.

### Exact token continuity candidate (unproved, no new constant)

The following is a candidate HOL statement using only existing constants and
inferred existing types; it is not claimed as a checked theorem:

```sml
!R vs0 C Ct h a ht at done tokens registry births PT TG saved entries H
 i j d tsj rj bj PTj TGj sj ej token.
 ptr_structural_transcript R vs0 C Ct h a ht at done tokens registry births
   PT TG saved entries H /\
 i <= j /\ j < LENGTH h /\
 (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
 EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
 EL (LENGTH (EL j h).po_stack - d) tsj = token ==>
 !k. i <= k /\ k <= j ==>
 ?tsk rk bk PTk TGk sk ek.
   EL k H = (tsk,rk,bk,PTk,TGk,sk,ek) /\
   EL (LENGTH (EL k h).po_stack - d) tsk = token
```

This is deliberately a continuity statement conditional on a numerical interval,
not conditional on target exclusion or future agreement. ProtectedHistory supplies
its interval with i=w and j=PRE(LENGTH h). HistoricalPlacement:66--90, specialized
at the demand endpoint, supplies d and the endpoint token equation from actual TG
and numerical G lookups, as well as actual output metadata. Transcript ownership
and adjacency use the SAME H (StructuralTranscript:92--96,126--131); no independently
generated ownership snapshots are permissible.

Reason to expect the candidate: `ptr_activation_tokens h a b tokens` is exactly
`LENGTH h :: tokens` on push, `TL tokens` on pop, otherwise `tokens`.
Bottom-depth indices are invariant under a push and under a pop above d; the
interval depth condition forbids popping the d owner. Root is token 0; each push
uses its new history index, strictly beyond all existing registry tokens
(ActivationChronology:108--113). Registry retention is not stack membership.
A popped token cannot be freshly pushed again: later history lengths increase.
This non-reappearance argument has NOT been exported as a theorem by the audited
interfaces; the continuity candidate is the smaller sufficient next boundary.

Consequences conditional on checking that boundary: a completed child cannot be
the current selected TG owner (live_prov); a later invocation uses a fresh token,
not the child's retained birth. Over the selected writer/read interval the demand
owner cannot be completed even temporarily. A writer destination owner obtained
from its actual live TG must therefore coexist with the demand owner at that
observation. Two coexisting stack activations are ancestor-comparable. Hence no
separation theorem for distinct nonancestor retained births is needed for this
owned-demand case. This does not exclude completed activations from the entire
history, only from this particular protected interval/destination classification.

### Actual production conflict matrix and premise provenance

| Destination relation at intervening source observation t | Actual supplier | Still to discharge, not new assumptions |
|---|---|---|
| Same (token,aid) | source suffix nonwrite + coherent birth/position + address/footprint transport | Same-token interval; paired write footprint containment and offsets for each writer family. No liveset separation is appropriate. |
| Same token, distinct aid | `ptr_owner_context_store_conflict`, then `ptr_output_local_local_separation` | For the SAME w: used seed, endpoint read seed, no-kill interval, and actual BP write-origin membership at t. Actual static items, output metadata, positive sizes, imported/local disjoint ids and pass witnesses must come from production, not arbitrary positions. |
| Demand owner ancestor of writer destination owner | `ptr_output_suspended_descendant_separation` | Demand owner's liveset at its suspended cursor from SAME-w protection; descendant live cache at t; convert bottom depths to n,k; actual ancestor pass/layout/import witnesses. The supplier gives the descendant imported item and separation, not equality with the global positions map automatically. |
| Demand owner descendant of writer destination owner | local/import separation with the shallower writer owner as local item, if its liveset can be supplied | Imported descendant cache/demand is available via StackImports/CallSeparation, but writer-only used_gen is NOT the read_gen required by `ptr_owner_context_liveset`. Need actual store-marking/BP write-origin at the shallower owner's current cursor, or a precise projected call-demand case when suspended. Merely swapping names in ProtectedLivesets does not supply this. |
| Distinct nonancestor / completed sibling / repeated invocation | exclude from coexisting live-owner case using interval continuity + live_prov | Birth retention and function/token inequality are insufficient. If writer is classified only by retained birth rather than live destination provenance, the classification itself is invalid. |

Exact consumer requirements explaining the remaining gap:

* OwnerConflict:105--128 `ptr_owner_context_store_conflict` requires the BP,
  callee-mems and sizes equations; history with `u<=t<=r<LENGTH h`; continuous d
  presence on [u,r]; owner function at u; wf and cfg correctness; `ml_used_gen a`
  at u, `ml_read_gen a` at r; no-kill on [t,r); and
  `MEM b (find_base_allocas_opt bp (inst_write_op (ptr_owner_view d (EL t h)).cf_inst))`.
  It returns BOTH `a` and `b` livesets containing the SAME owner cursor at t.
  This is stronger and more relevant than independently inventing writer liveness.
* LayoutOutput:135--151 `ptr_output_local_local_separation` needs fresh fn_eom,
  fn_ptr_ok, successful actual concretize call and actual fn_pass_step with
  `fn'=out.fpo_function`; static items for distinct a,b, positive sizes and both
  output metadata tuples; imported/local id disjointness; BOTH liveset lookups
  with one common `addr`. It concludes
  `reserved_intervals_disjoint (pa,sa) (pb,sb)`.
  LayoutOutput:70--86 local/import has the SAME production obligations but takes
  only a as local static item/output metadata and b from imported_mems_used.
  These conclusions are whole item separation, not actual-write exclusion.
* CallSeparation:8--39 `ptr_output_suspended_descendant_separation` takes actual
  stage/no-eom/shape/run-state/no-DALLOCA/distinct-id/callee-first; history at t;
  `stk=(EL t h).po_stack`, `n<LENGTH stk`, `k<=n`,
  `EL k (((EL t h).po_fn,(EL t h).po_state)::MAP (\f.(f.cf_fn,f.cf_state)) stk)
    =(desc,ds)` and `FLOOKUP ds.vs_allocas bid=SOME(db,sb)`;
  ancestor fn/addr are the n-th suspended frame's fn/cursor. It further needs
  observed-context/pass/success/static-item/output metadata/id-disjointness for
  the ancestor and its LOCAL item's liveset at addr. It returns
  `?pb. MEM (Allocation bid,pb,sb) (imported_mems_used observed.cu_context fn) /\
    reserved_intervals_disjoint (pa,sa) (pb,sb)`.
  Its proof derives imported membership and callee demand from the live descendant
  cache. It does NOT require a descendant writer to be the executing frame.

### Recommended semantic frontier / dependency ledger

First check bottom-token interval continuity on the accepted transcript, and
strengthen ProtectedLivesets in place to export its already-proved same-w interval
and seeds. These are finite interface repairs with premises from already-built
SOURCE histories. Neither requires constructing a future source step. Next audit
or prove the projected writer-conflict supplier for the descendant-demand /
ancestor-destination row above, retaining actual BP origins and call cursor cases.
Do not resume general opcode wrappers until that reverse-direction row is checked.

Premise provenance: frozen antecedent supplies source wf/SSA/reachable/discipline,
shape/no-DALLOCA/run-state/ids/schedule; stage decomposition supplies actual observed
pass/layout witnesses; accepted transcript supplies coherent historical ownership
and adjacency; endpoint TG+G and HistoricalPlacement supply live owner/depth/cache
and metadata; ProtectedHistory supplies w, interval, source nonwrite and seeds;
ProtectedLivesets supplies SAME-w liveset only after its interface is strengthened;
OwnerDemand supplies no-kill from protected source bytes; BP origins/store marking
must supply actual writer conflicts. Paired write content/footprint containment
and byte framing remain separate consumers. No target noninterference is yet proved.
Shared setup's final argument-token equality is also separate and unresolved;
equality of entire relocated argument vectors must not be introduced to solve it.

## Reverse ancestor-destination interface validation (C1.5.90.60)

Outcome: localized semantic supplier gap, NOT a proof of reverse exclusion.
No SML, speculative admission, positions-rewrite lemma, or executable change is
introduced. TokenInterval and the strengthened ProtectedLivesets discharge the
previous .57 continuity / same-w export recommendations; those are no longer
the missing boundaries below.

### Direction and cursor

At an intervening observation `a = EL t h`, let the demanded allocation belong
to a deeper live frame and the actual write destination belong to a shallower
live frame `f = EL n a.po_stack`. The shallower frame is necessarily suspended:
its instruction is INVOKE, NOT the currently executed store. Its production
cursor is `(f.cf_state.vs_current_bb,f.cf_state.vs_inst_idx)`. The demand owner's
cache is transported upward by StackImports, not by BP in the executing callee.

* StackImports:197--215 `ptr_frame_descendant_demand` supplies `ml_callee_gen
  (Allocation aid) mems f.cf_inst`, with actual stage, NONE eoms, shape/run-state,
  no-DALLOCA, distinct ids/callee-first, frame reachability, `n<LENGTH stk`,
  `k<=n`, the descendant `(owner,os)` at index k, its cache lookup, and the
  shallower owner's actual walk view. StackImports:218--237 supplies the
  corresponding imported tuple (add observed-context name equality).
* LivenessTransfer:16--26 makes callee_gen BOTH read_gen and used_gen. Applying
  OwnerConflict:55--71 with `u=t=r` at this SAME shallower cursor supplies the
  imported demand liveset (empty no-kill interval), exactly as done in
  CallSeparation:65--75. This part is an existing checked chain.
* LayoutOutput's local/import consumer still needs the shallower owner's LOCAL
  destination allocation liveset at that very cursor. CallSeparation does not
  supply it: its lines29--37 take the local liveset as an antecedent. Reversing
  the names in that theorem leaves precisely this antecedent unsolved.

### Store marking is not a suspended-call supplier

`ptr_active_write_liveset` (RetrospectiveLocal:8--19) has the exact interface

```sml
active_inst fn inst st /\
MEM a (find_base_allocas_opt bp (inst_write_op inst)) ==>
?xs. FLOOKUP (context_mem_livesets fuel ctx fn bp (cfg_analyze fn)) a = SOME xs /\
  MEM (st.vs_current_bb,st.vs_inst_idx) xs
```

It bypasses the need for a writer read seed when the write actually executes in
its allocation owner. It does NOT mark an ancestor's INVOKE for a descendant
store. OwnerConflict:105--128 has the same write-origin limitation in its final
antecedent. Thus even having both read/used seeds for the imported demand does
not make that store-conflict theorem applicable at the suspended ancestor.

BPOrigins:198--204 `ptr_bp_analyze_origins` goes from a BP member to membership
in `pointer_derived_vars fn (ptr_bp_alloc_roots fn aid)`. It is NOT runtime
provenance-to-BP completeness and cannot manufacture the ancestor call operand.
RuntimeGeneration:17--30 `ptr_production_operand_used_seed` goes the other way
for an already supplied Var operand and local derived membership, under
fn_ptr_ok, SSA, inst_wf, scan coverage and instruction membership. At an INVOKE,
its proof also yields operand_gen, hence read_gen by LivenessTransfer:20--21.
This would solve local liveness at `u=t=r`; the missing input is that ancestor
Var/local-derived witness, not a new liveness recurrence or a writer read seed.

### Smallest exposed semantic boundary (UNPROVED candidate)

The following is a precise proposed intermediate consumer, not a declared
constant/theorem and not a claim of checked derivability. All constants already
exist. It intentionally asks only for ancestor call-operand provenance/local
origin, not target separation, matching source success, or memory equality.
Here the positive birth and live token select the actual destination owner,
not an arbitrary retained birth or a same-named function.

```sml
ptr_source_ownership vs C h a tokens registry births PT TG saved /\
EVERY (fn_ptr_ok P) C.ctx_functions /\
EVERY ssa_form C.ctx_functions /\
EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
n < LENGTH a.po_stack /\ EL (SUC n) tokens = token /\
FLOOKUP TG v = SOME (token,bid) /\
FLOOKUP births (token,bid) = SOME (b,sz) /\ 0 < sz /\
FLOOKUP (EL n a.po_stack).cf_state.vs_allocas bid = SOME (b,sz) /\
inst_write_op a.po_inst = SOME (Var v) ==>
?u. MEM (Var u) (EL n a.po_stack).cf_inst.inst_operands /\
    FLOOKUP (EL n a.po_stack).cf_prov u = SOME (b,sz) /\
    u IN pointer_derived_vars (EL n a.po_stack).cf_fn
      (ptr_bp_alloc_roots (EL n a.po_stack).cf_fn bid)
```

This candidate is subject to strategist validation (including adequacy of its
antecedent); it is NOT a proposed new assumption on StageStatic. The current
source prefix and actual destination tag supply ownership, current TG and birth;
positive footprint containment supplies sz>0; live placement supplies the owner
cache/token; frozen source shape supplies the structural assumptions. It should
be proved from those sources, or corrected at that level before installation.

Premise-by-premise supplier ledger / remaining work:

| Boundary | Existing supplier | Exact limitation |
|---|---|---|
| Reachable current/saved frames | ownership history -> chrono reachability; owner_view_active | No target simulation needed. |
| Runtime variable supported by local-or-PARAM roots | ActivationSupport:121--139, FrameOrigins:5--11 | Support is closure over a UNION of local cache roots and PARAM roots; it does not select a PARAM chain or this owner's local bid. |
| One imported PARAM crosses one call | CallAncestry:41--59 | Requires `MEM (SOME site) PG` at that edge; concludes caller Var operand and numerical G lookup. It does not derive that membership from arbitrary derived runtime G, nor iterate it to the selected tagged owner. |
| Root classification | RootCover:7--12,36--59 | Local roots or `ptr_roots DIFF alloca_roots`; not membership in this specific bid's derived closure. Distinct local roots/cache uniqueness and exclusion of foreign PARAM origin still need semantic justification. |
| Tagged support | TaggedSupport:21--43 | Gives `v IN fn_pv P fn` / allowed PARAM index only, not local-bid closure at the selected ancestor. |
| BP origins/completeness | BPOrigins:198, ProductionCoverage:71, RuntimeGeneration:17 | Usable AFTER local-derived witness; BPOrigins direction alone is insufficient. |
| Imported deeper demand at same cursor | StackImports + OwnerConflict at singleton interval | Complete existing chain as above. |
| Actual layout, local items, positive sizes, observed/pass witnesses | HistoricalPlacement, StagePlacements, LayoutOutput | Keep original owner and production metadata; arbitrary positions or retained siblings are inadmissible. These do not solve ancestor operand origin. |

A possible proof route for the unproved boundary is to decompose finite derived
closure over frame roots, rule out local-cache origin in each strictly deeper
frame using positive active-owner geometry, extract PARAM membership, cross the
call with CallAncestry, and repeat until the selected owner; there rule out its
foreign PARAM and other local origins. No such iteration/origin-selection proof
was installed or credited in this diagnostic. In particular numerical site
aliasing at zero size is not solved by this route: the candidate explicitly
handles positive-byte destinations only. Zero-byte footprints require no byte
exclusion; zero-sized provenance elsewhere remains a separate integration issue.

Verification: holbuild passed OwnerConflict, BPOrigins, StackImports,
CallSeparation, TokenInterval, ProtectedLivesets (tool output
TO_concretize_ptr-20261105T100526Z_m9834_t001), then OwnerDemand,
RuntimeGeneration, RetrospectiveLocal, ActivationSupport, CallAncestry,
TaggedSupport (TO_concretize_ptr-20261105T100526Z_m9868_t001). No rebase break was
encountered. Universal prefix coverage and setup argument-token equality remain
blocked and are not conclusions of this audit.

## Checked reverse ancestor-destination supplier (.65)

`concretizePtrTaggedCallLivenessTheory` now supplies
`ptr_source_tagged_owner_call_liveset`: current source ownership, no DALLOCA,
selected suspended token `EL (SUC n) tokens = owner`, and current full-tag
lookup `FLOOKUP TG v = SOME(owner,aid)` give the production context liveset
for `Allocation aid` at that owner's suspended call cursor, under the stated
source function well-formedness/SSA/reachability/BP hypotheses. This uses
.64's exact tag-selected call operand, `ptr_production_operand_gen`, suspended
INVOKE/label shape, and the singleton interval of `ptr_owner_context_liveset`.
The history already includes its endpoint (`LENGTH h-1`). No allocation size
or numerical-site injectivity is used for that liveness fact.

`ptr_output_tagged_ancestor_destination_separation` composes this fact into
`ptr_output_suspended_descendant_separation`. It retains that theorem's actual
stage/observed-context/pass/layout/item/metadata, positive sizes, import-id
disjointness and descendant-cache premises, replacing the local liveset
premise by ownership at the exact supplied `EL t h` plus its tag and source
structural hypotheses. The conclusion is the same imported descendant tuple
and `reserved_intervals_disjoint (pa,sa) (pb,sb)`.

Dependency ledger: .64 -> production operand_gen -> suspended read/used gen
-> singleton owner liveset -> CallSeparation -> reverse-row layout separation.
This closes that source-side conflict supplier only: constructing the historical
ownership snapshots and relating an actual target write to the selected source
row still belong to universal prefix coverage. No target suffix exclusion,
future read equality, or matching source execution is established here.

## Checked ordinary-writer exact footprints (.66)

`concretizePtrExactWriteTransportTheory` supplies
`ptr_write_transport_owner_exact` and `ptr_write_transport_fixed_exact`.
Both use the same ordinary instruction, `mem_write_ops = SOME ops`, a finite
maximum size operand, label-aware variable transport, source destination/size
evaluations and scalar-empty size provenance/taint. The owned theorem uses
actual birth/position lookups and the closed source/target bounds; it gives
membership equivalence for every allocation-relative byte `k < sz`. The fixed
theorem uses scalar-empty destination provenance/taint and gives set equality.
Only CALL/STATICCALL/DELEGATECALL require equal post-returndata lengths, not
values. Other operand evaluations may carry different values or fail; the
option-valued transport supplies exactly matching success/failure. Finite
classification excludes DRET via the maximum-size premise.

Same-owner nonwrite follows directly by negating the checked membership
biconditional; maximum containment alone did not give this for truncated call
output writes. This interface assumes neither source step success nor target
suffix exclusion. Historical transport, production writer ownership, distinct
owner separation and universal source-prefix construction remain to integrate.

## Owned-demand ordinary-write integration (.67, checked conditional boundary)

E0306, commit a7457f6d1, completes the authorized conditional exclusion.
`ptr_demand_protected_token_interval` selects the original initializing writer
once. `ptr_demand_interval` packages those premises and the SAME w.
`ptr_demand_owner_layout` extracts actual production witnesses for either owner;
`ptr_demand_other_owner_separation` is Finalised and handles all equal/strict
bottom-depth orientations, including the actual Var write-use premise.
`ptr_demand_ordinary_write_exclusion` (DemandWriteExclusion:698-765) combines
fixed, identical-owner exact, and distinct-owner containment/separation rows.
No geometry premise is assumed by that consumer. Its fixed lower bound uses
`ptr_stage_placements_reserved_prefix`; its owned word endpoint input has a
checked supplier `ptr_stage_placements_strict_bound` (PlacementBounds:117-128).

This is NOT universal coverage. The consumer explicitly requires paired
historical value transport, classification and bounds, same labels, source
step_writes/chrono-write equivalence and paired CALL returndata lengths.
Zero-sized requests outside the numerical containment premises are caller cases.
No claim that structural_transcript alone supplies these semantic inputs is made.

## MCOPY architecture probe (.67.5)

### Actual dependency ledger (not specification macros)

Fix a SINGLE source observation A=EL j h and ownership snapshot
EL j H=(tsj,rj,bj,PTj,TGj,sj,ej). The source state is A.po_state, not a fresh
independent state. The target state t must be the paired prestate at its retained
aligned instruction. This pairing and its historical transport are still
**invariant data to construct**, not a theorem of structural_transcript.

1. **Definedness from target to source.** For the retained MCOPY with operands
   [dop;sop;nop], use `ptr_vars_transport_eval_all` (ValueTransport:98-110), same
   source/target labels, and `ptr_lookup_transport_some_right` (128-133) on EACH
   successful target evaluation. This yields three source values and their exact
   value-transport relations. No byte-content agreement is required. The scalar
   size is identical only after obtaining `op_prov TGj nop=NONE` and empty size
   taint, then `ptr_value_transport_scalar_empty` (37-42). Unlike definedness,
   numerical equality of the size is NOT automatic for an arbitrary tagged nop.
   Scalar/label operand cases must not be lost by only using eval for Var/Lit.

2. **Source discipline from this snapshot.** `ptr_structural_transcript_ownership`
   / `ptr_demand_interval_snapshot` supply ownership at A. Erasing the transcript
   supplies its actual source chronological history, whose reachability follows
   from `ptr_chrono_history_reachable` (ChronologicalHistory:103-113). Unfolding
   `ptr_discipline_def` (ptrDiscipline:625-635) gives BOTH access_ok and taint_ok
   at A. They are not assumed for the target. `taint_ok_def` (566-585), opcode
   MCOPY and operand membership force ALL THREE operand masks empty: MCOPY is
   not one of the allowed tainted-variable uses. Memory-read bytes may be tainted.
   `ptr_write_max_size_untainted` / `ptr_write_max_size_no_provenance` in
   WritePurity give the scalar-size interface once source fn_ptr_ok is available;
   source fn membership/wellformedness must be retained/derived from reachability.

3. **Requested-range classification, not actual-footprint bounds.**
   `ptr_source_write_classification` and `ptr_classified_write_range_def`
   (WriteClassification:47-104) give the MCOPY request (w2n d,w2n n), requiring
   all three source evaluations. For nonzero n outside revert forwarding,
   `access_ok_def` (ptrDiscipline:530-545) gives the fixed row if the numerical
   destination provenance is NONE and end<=lo; otherwise it supplies a Var
   destination with numerical (db,sb) and db<=w2n d, end<=db+sb. Exact historical
   erasure (`ptr_source_ownership_prov_erases`, SourceOwnership:300-306, plus
   `ptr_ledger_erases_def`/`ptr_owner_project_def`) produces the corresponding
   TGj tag and birth lookup; totality excludes a dangling tagged birth masquerading
   as numerical NONE. `ptr_transcript_historical_placement` gives this SAME live
   owner's coherent positions tuple. `ptr_stage_placements_strict_bound` gives
   pb+sb<dimword(:256) from stage/shape/NONE-eoms/callee-first and that lookup.
   These are existing checked suppliers; the consumer assembly from access_ok
   is not yet an exported checked lemma. No actual empty footprint implies a
   requested-range bound.

4. **Success and chronological correspondence.** MCOPY semantics in
   venomExecSemantics:639-647 succeeds whenever the three evaluations succeed;
   it returns OK(mcopy ... s). There is no memory-value test, fuel check,
   call-state check, or static-context prohibition in this branch.
   `step_inst_non_invoke` (1870-1876) lifts base execution to step_inst.
   Therefore SOURCE SUCCESS CAN BE CONSTRUCTED BEFORE READ AGREEMENT.
   Once success is known, `ptr_chrono_write_def` (ChronologicalHistory:132-137)
   reduces to requested-range membership for MCOPY, which is nonterminating and
   non-INVOKE. `step_writes_def` and `ptr_step_write_range`
   (WriteClassification:5-17) do not truncate MCOPY. Thus source actual footprint
   equals the requested footprint, and hence chrono_write, without requiring
   a new read-agreement premise or post-returndata equality. The exact adjacent
   source poststate still belongs to the same constructed source history.

5. **Masked content / ledger extension.** `ptr_mcopy_masked_content`
   (CopyContent:7-31) already proves paired base success and immediate postwrite
   masked byte equality FROM untainted old-read-byte agreement, all six operand
   evaluations, and a common size. It uses `mcopy_establishes_equiv`; do NOT
   re-prove opcode content. Upgrade with step_inst_non_invoke and determinism
   to the already chosen actual transitions. The read-agreement premise remains
   the genuine ledger/noninterference obligation: same-w exclusion for historical
   intervening writes plus immediate agreements at their matched initializing
   events. Structural history does not store those paired events/agreements.

### Edge-case and cycle audit

- n=0: scalar size equality makes both actual written ranges empty, regardless
  of operand addresses. Do not apply access_ok's nonzero implication or infer
  placement containment. Source success still requires all three operands defined.
  Zero bytes does not imply equality of whole poststates (memory expansion fields
  may change); only byte-content/footprint claims are vacuous.
- Revert forwarding: access_ok deliberately supplies no range bound there.
  For a protected owned demand's same-w interval the checked interval gives
  non-forwarding at each j; a more general dispatcher must keep the forwarding
  exception, not manufacture fixed/owned bounds.
- Tainted old source bytes: no equality required there. mem_taint/written_taint
  transfer masks to destination bytes; CopyContent uses that exact postwrite mask.
- Overlap: mcopy_def (venomExecSemantics:80-84) computes data from OLD memory,
  then writes. Neither a byte-by-byte evolving-memory copy nor nonoverlap is an
  admissible replacement. Existing CopyContent handles overlap.
- CALL contrast: its actual step_writes truncates requested length by post-return
  data length. That extra paired-outcome dependency is absent for MCOPY and is
  NOT solved by this probe.

### Finite dependency graph and smallest next semantic boundary

```
paired prestate transport + target operand evaluations + equal labels
  -> three defined source operands (+ exact value transport)
  -> source MCOPY OK (no memory agreement)
  -> source next observation can be constructed when its cursor is aligned
  -> source ptr_discipline access/taint facts at current observation
source size purity + value transport -> same requested size
source access + historical tags + stage positions/bounds
  -> fixed/owned classification (or zero-length/non-forwarding case)
source success + nontruncated MCOPY -> footprint/chrono equivalence
retained earlier paired transport/agreements + same-w interval
  -> conditional historical exclusion -> current untainted read agreement
current read agreement + existing CopyContent -> immediate masked write agreement
```

The first arrow through source success is the smallest missing named semantic
implication. The proposed exact HOL term is typechecked, NOT asserted, in
`concretizePtrMcopyArchitectureProbeScript.sml:8-26`. It quantifies typed births,
positions, TG, tn, source/target states, instruction and three operands/target
values, fuel and context, and concludes existential source values, all three
source evaluations/value relations and explicit successful step_inst. Its
antecedent is only MCOPY shape, ptr_vars_transport, equal labels, and three
successful target evaluations. In particular it has NO source OK, byte equality,
future exclusion, numerical range bound, read demand or independent ownership
witness premise. This does not by itself install a global invariant.

Directly consulted run-owned suppliers and the syntax-only probe were rebuilt
with holbuild (outputs m10853, m10865 and m10872). No scratch unproved theorem or specification
macro was installed. Universal source-prefix extension is still unproved.

## Installed-certificate induction contract review (C1.10.4)

This section supersedes the specification macros at the start of this file.
It is an architecture audit, NOT a HOL theorem or an authorization to migrate
production definitions. Checked against PairedPrefix:10-25,98-120, PairedFields:
11-119, StructuralTranscript:9-57 and OpaqueRetpc:7-105,231-250.

### Exact proposed coverage conclusion using the installed predicate

The following is the single candidate coverage contract, written with existing
constants only. It is deliberately NOT asserted: the installed sample relation
has the call/RETPC obstruction below. There is no hidden `Production` or
`Transport` macro in this contract, and no extra source-success hypothesis.

```sml
!rpolicy C Ct vs lo eom ht at.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C Ct /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom Ct = SOME eom /\ ptr_chrono_history vs Ct ht at ==>
  ?R local_positions positions h a done tokens registry births PT TG saved
    entries H calls W.
    ptr_paired_prefix R local_positions positions lo vs C Ct
      h a ht at done tokens registry births PT TG saved entries H calls W
```

Quantifier direction is essential: each target history is supplied; source
history, placement and all historical annotations are constructed. Existential
R/local_positions alone do not certify production lookup/metadata origin.
`ptr_paired_code` fixes blocks, entry label and ALLOCA local/global lookup
coherence, but its `R f g` is arbitrary. The eventual proof must choose R and
local_positions from the actual stage decomposition, not assume arbitrary R
has function-shape, output lookup or successful-layout properties.

This contract is NOT yet a validated induction invariant. In particular, do not
try to prove its step case with unchanged installed definitions: E0327 and the
OpaqueRetpc probes invalidate the proposed equal-token setup interface locally.
This is not a counterexample to the complete frozen theorem or even a complete
production counterexample to the displayed coverage contract.

### What the installed six conjuncts actually supply

| Installed clause / checked projection | Supplies | Does NOT supply |
|---|---|---|
| structural_transcript / ptr_paired_prefix_transcript | actual source and target histories via erasure; SAME per-source-index H snapshots and endpoint ownership | new source transition success; transport at arbitrary unmatched source indices |
| stage_placements / ptr_paired_prefix_placements | exact global metadata lookup table | local map coverage or actual successful pass witness on its own |
| paired_samples / ptr_paired_prefix_samples | at E[j]=EL j (done++[LENGTH h-1]), unrestricted vars transport and shared fields | mixed opaque relation; agreement of memory reads; arbitrary-index transport |
| paired_alignment / ptr_paired_prefix_alignment | paired code, NOP-gap cursor, params relation at those SAME samples | source instruction necessarily retained at current cursor; equal whole functions; target o1_fn_shape |
| paired_callers / ptr_paired_prefix_callers | exact suspended frames refer back to paired INVOKE samples and saved (PT,TG), with equal stack lengths | already-bound equal ordinary returns or post-return mixed vars |
| paired_writes / ptr_paired_prefix_writes | actual adjacent source/target write pairs, immediate postwrite masked byte equality, owner-relative rho, distinct departed target indices and coverage of nonempty ordinary SOURCE writes | target suffix exclusion; current read equality; completeness for target writes absent paired source classification |

`ptr_ledger_write_pair` records equality at source n+1 and target j+1, not at
E[j+1]. `ptr_paired_write_owner` uses H[n+1] birth/position lookups; this must be
reconciled with prewrite operand evidence in H[n], not silently replaced by
endpoint births. The fixed sentinel is a separate checked initial-origin fact,
not an owned-initial-memory equality clause. Birth retention is not live demand.

### Preservation obligations and acyclic dependency graph

Base: derive actual root function pair and local map from stage, source entry
success from target entry, and initial params/sample/caller/empty-write facts.
Production ALLOCA coverage checked in C1.10.1 excludes missing-map deletions;
combine that fact with the existing deleted-NOP boundary. It does not construct
source entry, sample transport or source NOP execution by itself.

Gap: PairedPrefix's checked gap theorem requires the actual tagged NOP step,
new sample, code/cursor/params facts and saved/stack preservation. Its list algebra
retains old samples/callers/W. It is not a theorem constructing those premises.
Normalize finitely after root, ordinary step, block entry, call and return.

Pair: construct the actual tagged source transition from EACH target next,
block, call or ret derivation, same id and corresponding depth change. Append
exact computed tokens/registry/births/PT/TG/saved/entries to H, freeze old endpoint
in done, extend W only at actual immediate write events, and normalize the new
endpoint. No source OK or target noninterference may be an input assumption.

```
frozen premises + actual stage decomposition
  -> production R/local maps + coverage + source shape/preimage exclusions
  -> root entry + finite NOP normalization -> certificate at target prefix 1
certificate at n + target transition
  -> SAME historical snapshot operands/definedness + source access/taint
  -> fixed/owned/zero/forwarding classification and source success guards
  -> read recovery [old W + SAME-w protected source interval + conditional X]
  -> actual source step and post-state transport/effects
  -> immediate masked write content + new W (where nonempty)
  -> transcript pair + callers/alignment/samples + finite NOP normalization
  -> certificate at n+1
certificate endpoint + static endpoint classification + max_live_eom adapter
  -> C1.7 output static access bound -> C1.8 frozen mem_inv packaging
```

For MCOPY, source OK precedes read recovery (no byte test). For external effects,
whole request equality and guards precede source OK; use only already-constructed
prefix reads. Neither branch may appeal to the n+1 certificate to construct n+1.

### Exhaustive consumer reconciliation and retained obligations

The dispatch N1-N18,J,C,R,X1-X5,T and owner-relative matrix above remain the
exhaustive partition, not a new opcode-wrapper queue. Their integration owners:

* C1.5.90 retains universal source-prefix existence, historical same-w read
  recovery and actual target write exclusion; C1.5.90.67's conditional ordinary
  write result is NOT unconditional coverage. Fixed reads require last fixed
  writer or initial sentinel plus interval framing; owned reads require selected
  initializing writer, continuous live owner and exact historical placement.
  Existing exact/containment separation handles fixed/fixed, mixed, same owner
  and coexisting distinct owners only after its operand/footprint premises are
  derived. No disjointness of completed sibling static slots is assumed.
* C1.6 retains preservation across N1-N18 and J/C/R, including masked reads,
  MSTORE/MSTORE8/ISTORE, MCOPY, all buffer copies/EXTCODECOPY, CALL/STATICCALL/
  DELEGATECALL/CREATE/CREATE2 effects, storage/transient/logs and two-output BUMP.
  Existing content and exact-footprint boundaries are conditional inputs, not
  constructed certificate steps. CALL output range is MIN with returndata;
  equal returned lengths/whole requests must be derived, never guessed.
* J and entry portions of B/C require matching successor/label evaluation,
  actual successful enters_block and parallel PHI selection from PRE-entry vars.
  Use existing StepStructure/StepRetpc/StepShape/StepCallChecks/StageShape facts;
  no duplicate rewrite lemma is needed. Cursor equality is not whole-block equality.
* C and R retain ordinary argument transport, callee lookup/setup/entry, saved
  caller bindings, token restoration and ordinary returned-value equality.
  RET discards LAST with FRONT; no runtime token-equality check exists. DRET/
  RETFMP are excluded, not implemented as additional writer branches.
* Zero-length requests have vacuous byte/footprint obligations but still require
  defined operand evaluation and source success. Do not infer a numerical bound
  from an empty actual footprint. Forwarding is a distinct access exemption;
  SAME-w protected owned intervals already exclude it where appropriate.
* C1.7 retains active terminal observations, including RETURN/REVERT, as well as
  every continuing prefix. No chrono Halt/Abort/Error successor exists, but that
  does not eliminate endpoint static_mem_ok obligations or revert forwarding.
  Fixed reserved endpoints and function endpoints must use the checked maximum
  interface; no old ctx_eom_bounded premise or alloca_next=0 is available.
* C1.8 remains blocked packaging only. No prefix diagnostic is its prerequisite
  semantic theorem. C1.5.90.40 (OwnedAffinePrefix) and ALL other retained C1.5.90,
  C1.6, C1.7 obligations/boundaries are preserved, not cancelled or reproved here.
  D0002 remains in force for every own-helper dependency rebuilt later. Today's
  two audited targets build cleanly; that is not a claim that every helper was
  rebuilt or that remaining CHEATs in the final dependency closure are solved.

### Required parent decision before simultaneous induction

Installed ptr_paired_sample STILL uses unrestricted ptr_vars_transport and
ptr_shared_fields, including equal vs_return_pc_token. ptr_paired_params still
uses ordinary argument transport, not a hidden opaque-token renaming. The checked
core/env/setup/merge/RETPC_PARAM probes in OpaqueRetpc are isolated only.

The parent must authorize an in-place certificate migration (or another justified
interface). The proposed mixed relation is exactly OpaqueRetpc:231-250:
non-retpc vars use lookup transport; retpc vars use own-token interpretation AND
synchronized undefinedness, with equal source/target retpc classification.
Core shared fields normalize ONLY the token, never memory/effects. Still unproved:
ordinary operand exclusion via opaque_use_ok; mixed ASSIGN and parallel PHI;
production source/target shape including metadata-only differences; mixed saved
caller/return binding; equal ordinary returned values. No pointer/opaque-tag
class disjointness is assumed. Old unrestricted transport lemmas remain valid
conditional boundaries and must not be weakened or dropped to force migration.

Requested scoped strategy review: replace/update the shallow C1.10 migration
subtree, preserving C1.5.90/C1.6/C1.7/C1.8 and all checked boundaries. Do not start
universal induction on the unchanged installed sample, and do not schedule
another opcode-by-opcode wrapper queue in place of this interface repair.

Verification: holbuild on concretizePtrPairedPrefixTheory and
concretizePtrOpaqueRetpcTheory passed (TO_concretize_ptr-20261105T174221Z_m11527_t001).
This audit introduces no HOL definition, theorem, duplicate lemma or admission.

## Mixed parallel-PHI boundary (C1.10.9)

`concretizePtrMixedPhiTheory.ptr_mixed_eval_phis` now derives source success
from target success for the same leading-PHI list, preserving mixed variables
under the actual `phis_prov` and `phis_taint` updates and preserving core shared
fields. It requires explicit predecessor equality (core shared fields provide
labels, not `vs_prev_bb`). The parallel recursion selects every operand in the
original prestate and applies head bindings after tail bindings, matching the
provenance and taint recursions even for repeated outputs. Own opaque tokens
remain independent; no arbitrary final-mask compatibility premise is added.

Still outstanding: production observation shape and source/target leading-PHI
correspondence, discharge of predecessor equality from paired cursor alignment,
ordinary return equality, byte/read recovery and universal source-prefix
construction. This local boundary is not a proof of the frozen static theorem.

## C1.5.90.67.21 — full chronological INVOKE integration audit

Artifact: `concretizePtrPairedCallSchemaScript.sml` contains a typechecked
quotation, NOT a theorem. Both that theory and PairedCallEntryTheory build.
The quotation states source call recovery, the immediate six-field certificate,
and subsequent NOP normalization. It assumes the actual target call constructor
and the static premises of `ptr_paired_invoke_entry`, not source success or a
post-call certificate.

### Computed witnesses (no independently chosen relocation)

Let b/bt be the exact observations in the quotation, copied from
ChronologicalHistory:48–59 and SourceOwnership:42–55. Source PG becomes
`MAP (op_prov a.po_prov) ops`; tagged PT becomes `MAP (op_prov TG) ops`;
both variable provenance maps become FEMPTY. Source taint becomes
`a.po_taint with t_var := FEMPTY`, NOT entry_taint (memory taint persists).
The saved tags are `(PT,TG)::saved`, not the callee parameter tags.
The activation token is LENGTH h; tokens and registry become
`LENGTH h::tokens` and `registry |+ (LENGTH h,f)` (ActivationChronology:5–16).
Births B are explicitly `ptr_birth_overlay (LENGTH h) b.po_state.vs_allocas births`.
setup_callee clears allocations; the accepted no-PHI entry identity gives
b.po_state.vs_allocas = FEMPTY. Hence B = births by birth_lift/overlay definitions
(ActivationBirths:8–15), not by a lifetime/freshness assumption.
The entries map gains `(LENGTH h,LENGTH ht)`; H appends exactly the new tuple.
done appends `LENGTH h - 1`.

### Six certificate fields and supplier recipe

| Field (`ptr_paired_prefix_def`:135–145) | Supplier / remaining assembly |
| --- | --- |
| transcript | `ptr_paired_invoke_entry` obtains f,args,cs,cs',i. Source active caller comes from ownership/history reachability, as in `ptr_owned_invoke_restrictions`. Expand observation projections to apply `ptr_tagged_chrono_step_call`; target step is given. `ptr_structural_transcript_pair` uses equal inst ids (positions id preservation), both pushed stacks, and R f g from paired code. Its computed tuple is exactly the schema tuple. |
| stage placements | unchanged C t and positions: reuse projection, no extension needed. |
| samples | `ptr_paired_samples_pair` freezes old endpoint and appends the new sample. Setup clears vars; `ptr_mixed_vars_setup` applies also with the actual caller taint with cleared t_var because mixed transport consults t_var only. `ptr_core_shared` comes from entry boundary. Overlay with empty allocation map changes no births. This is not equality of memories. |
| alignment | old j < LENGTH ht retain their code/cursor/params via EL_APPEND_EQN and the frozen former endpoint index. At j=LENGTH ht use selected paired code, entry cursor, and transported args as callee params. `ptr_args_transport_lengths` and setup params reduce the mask length required by `ptr_paired_params_def`. No new alignment semantic premise is needed. There is no exported alignment-pair lemma; this is list bookkeeping to be assembled, not a supplied theorem. |
| callers | push `(LENGTH h - 1,LENGTH ht - 1)::calls`. The new head frame is exactly the departing observation, on each side; LAST h=a, LAST ht=at and LAST H=old snapshot give ptr_paired_frame and saved tags. LENGTH ht=SUC(LENGTH done) makes new j=LENGTH ht-1 point to the newly appended done element. Old records use `ptr_paired_call_retained` and old callers at tail indices. `ptr_paired_callers_retained` alone is NOT applicable because stacks changed. No semantic caller transport assumption is needed; historical sample and alignment remain frozen. |
| writes | `ptr_paired_writes_pair` with extra=[] reuses ws. Its new-event coverage antecedent explicitly excludes INVOKE (PairedFields:217–229), so it is vacuous. Old actual write records use `ptr_paired_writes_retained`, including old post-event H entries. Separately, step_writes inst s bstate=[] for INVOKE follows from ptrDiscipline:267–274 and source_memory_write_ranges (codegenRel:131 ff; default [] branch). This call ENTRY does not execute callee writes, and must not be confused with a big-step INVOKE footprint. |

### Normalization and decision boundary

Apply `ptr_paired_prefix_normalize` (PairedPrefixProbe:339–353) to the
immediate certificate and fn_inst_wf f. It appends delta and snapshots,
retaining the computed tokens, registry, births, PT, TG, saved and entries.
It retains the PUSHED calls list and the SAME ws, not the original calls list.
The quotation includes both immediate and normalized certificates so no
assembly obligation can be hidden in normalization.

No unsupported semantic implication was found in this bounded call-entry audit.
The missing work is checked assembly: caller cons/list retention, the alignment
new-index split, clearing taint-variable projections and empty-birth-overlay
normalization. These are exact local consequences of definitions and accepted
interfaces, but are not certified by this quotation. Authorize a complete
INVOKE extension proof, not another conditional wrapper, before claiming them.
This does not resolve return restoration, callee body execution, historical
write exclusion, read recovery, or universal prefix coverage.

Disprove-first inspection: persistent memory taint is the main potential mismatch
with the entry boundary's entry_taint presentation. It is not silently reset here;
empty variable transport depends only on t_var. Imported pointer parameter tags
are preserved, and empty allocations do not erase retained ancestor births.

## C1.5.90.67.22 — checked chronological INVOKE integration

The former quotation in `concretizePtrPairedCallSchemaScript.sml` is now
`ptr_paired_invoke_prefix_normalize`, proved with precisely the audited
hypotheses and conclusions. It constructs source entry, the tagged step,
computed birth overlay, all six immediate certificate fields and subsequent
deleted-NOP normalization. Both PairedCallSchemaTheory and PairedJumpTheory
build cleanly. No source-success or successor-certificate premise was added.

The generic `ptr_paired_alignment_pair` has been moved from its local
PairedJump declaration into PairedPrefix and is reused by both consumers;
the earlier audit's assertion that no such lemma existed was incorrect.
Caller-cons assembly uses the actual departing observations, transcript LAST
snapshot and retained tail records; no additional caller helper was necessary.
Persistent memory taint is retained: only variable taint is cleared, and
`op_taint_def` discharges the entry-taint presentation mismatch. The write
ledger is unchanged; strict old event indices follow from event embedding,
and the new event is INVOKE, excluded by the write coverage definition.

This theorem covers call ENTRY only. Return restoration, callee execution,
read recovery, historical exclusion and universal prefix coverage remain
separate obligations; this checked assembly supplies none of them implicitly.

## 2026-11-06: installed-certificate sufficiency for X (.67.23)

**Result: a checked question and a supplier audit, NOT a proof of X.**
`concretizePtrPairedJumpSchemaScript.sml:51-76` now typechecks the owned-byte
question, in the existing acyclic schema theory. `holbuild` target
`concretizePtrPairedJumpSchemaTheory` passed (product output
TO_concretize_ptr-20261105T174221Z_m12860_t001). The first parse attempt used
`W`, which resolves to the combinator; renaming it `ws` fixed this. The quotation
introduces no theorem, constant, admission, invariant or oracle. All its free
variables are schematic/universally quantified in the proposed obligation.
The paired prefix and demand interval use exactly the same C,C',vs,h,endpoint,
ht,at,done,tokens,registry,births,PT,TG,saved,entries,H. It repeats the frozen
static antecedent (names witnessed explicitly), retains successful placement
`FLOOKUP positions (Allocation aid) = SOME (pa,sz)`, and asks, for
`w < EL q done /\ q < LENGTH done`, for
`pa+k NOTIN range_bytes (step_writes (EL q ht).po_inst
 (EL q ht).po_state (EL (SUC q) ht).po_state)`.
There is NO extra source-success, transport, exclusion or memory-equality premise.

### Indices and exact historical suppliers

Use n=EL q done, A=EL n h, T=EL q ht, Z=EL (SUC n) h,
U=EL (SUC q) ht, and destruct EL n H=(tsn,rn,bn,PTn,TGn,sn,en).
These are notation in this report, NOT new constants or fresh witness choices.

| Required fact at this use site | Actual supplier / missing implication |
|---|---|
| n+1<LENGTH h, q+1<LENGTH ht | Transcript erasure then `ptr_structural_trace_embedding` (StructuralTrace:105); strict event embedding of done++[LENGTH h-1]. No extra index restriction is needed. |
| w<n, same initializing writer, no later source write of b+k | DemandWriteExclusion:97-144 `ptr_demand_interval_def`, with the original w. No re-selection. |
| Interval owner presence, constant bottom-depth token, owner allocation | Same demand interval:138-144, from `ptr_demand_protected_token_interval`:25-93. Retained births alone are NOT the supplier. |
| Exact snapshot ownership at n, taint/access discipline | `ptr_structural_transcript_ownership`:92-96 and erasure/reachability; access already in demand interval:108; taint from ptr_discipline on reachable source observations. Use the same P obtained from ptr_discipline when constructing the interval; an arbitrary unrelated P is not a substitute. |
| Production destination placement and strict word bound | `ptr_transcript_historical_placement`, `ptr_stage_placements_strict_bound`; MCOPY assembly is already checked in HistoricalWriteClassification:7-64. This uses bn, not endpoint births. |
| Mixed pre-event variable transport | PairedPrefix:30-40 `ptr_paired_samples_mixed`, via `ptr_paired_prefix_samples`:180-187. Since q<LENGTH done, EL q (done++[LENGTH h-1])=n. |
| Labels, relevant shared fields | PairedPrefix:43-52 `ptr_paired_samples_core`; core/shared field projection. This does not equate memory or allocator metadata. |
| Unrestricted `ptr_vars_transport bn positions TGn A.po_taint A.po_state T.po_state` | **NOT supplied**, and not a valid consequence of mixed variables: opaque own return-PC tokens can differ. This is the first blocked application of `ptr_demand_ordinary_write_exclusion`:706 and `ptr_demand_mcopy_write_exclusion`:17. Do not add it to the quotation. |
| Transport of actual ordinary write operands | Available route, but not the interface used by the old exclusion theorem: `ptr_nonopaque_instruction_operands` (OpaqueRetpc:340-349), `ptr_mixed_vars_eval`:291-309 or paired_samples_eval_operands:54-73. Obtain opaque_use_ok from source shape, membership from the actual source history; ordinary writes are outside ASSIGN/PHI/RET/RETFMP/DRET. |
| Offset/size evals, size scalar and untainted, address fixed-or-owned classification | Historical source step already exists in the prefix, so source eval success is not a future-success premise here. `ptr_write_max_size_untainted`, `ptr_write_max_size_no_provenance`, actual reachability and fn_ptr_ok supply purity. HistoricalWriteClassification:7-64 supplies the MCOPY classification from these source evals and access_ok. Other ordinary families still require assembly with the same evidence. |
| Local/import production conflicts relative to later demanded owner | Checked conditional `ptr_demand_other_owner_separation` plus demand interval, exact snapshot and historical placement. No disjointness by sibling-token inequality is assumed. |
| Source chrono-write equivalence | ChronologicalHistory:132-149 and actual adjacent step; MCOPY instance HistoricalMcopyExclusion:73-78. Requested source ranges and actual step_writes differ for external CALL; handle its MIN rather than equating them blindly. |
| Target opcode/operands vs source instruction used by exclusion theorem | Existing production cursor/alignment and positions rewrite facts (reuse StepStructure/StepShape/StepCallChecks/StepRetpc/StageShape). Need historical event instantiation; equal ids by itself is insufficient. No duplicate structural theorem was introduced. |
| Immediate source poststate vs next normalized sample | Checked by StructuralTrace `ptr_structural_trace_nop_interval`, `ptr_structural_trace_gap_memory`, and `ptr_structural_trace_gap_returndata` (258-352). From structural_trace and q<LENGTH done, with n=EL q done and m=EL(SUC q)(done++[LENGTH h-1]), these give SUC n<=m<LENGTH h, NOP at each strict gap index, and equality of memory/returndata from SUC n to m. They do not equate cursors or whole states. |
| CALL post returndata lengths | Checked PairedPrefix `ptr_paired_samples_post_returndata` (55-67): structural_trace, paired_samples positions h ht done H, and q<LENGTH done imply source EL(SUC(EL q done)) returndata equals target EL(SUC q) returndata. LENGTH equality follows by congruence; no duplicate LENGTH theorem installed. Uses paired_samples_core at SUC q and the historical NOP gap bridge, not pre-CALL returndata. |
| W immediate equality / write ownership | PairedFields:91-114, PrefixLedger:16-29. Only source-to-target footprint inclusion, not reverse inclusion; only equality on source written bytes minus POST-taint. Even W's owner choice is a byte-map witness, not the historical instruction destination tag. It cannot supply suffix exclusion or exclude extra target writes. |

### Exact first missing semantic interface (not another invariant)

The installed certificate is not a direct client of the old exclusion signatures.
The gap is not solved by RET integration. The smallest durable repair to review
is **in-place** generalization of the write transport/exclusion interface, not a
new wrapper assuming unrestricted transport. The exact proposed quantified
replacement at the lowest exact-footprint boundary is:

Take `ptr_write_transport_owner_exact` (ExactWriteTransport:51-64), universally
quantified over its existing variables. Keep its conclusion and every premise
except `ptr_vars_transport births positions TG tn s t`. Replace that premise by:

```
ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
  (op_taint tn ops.iao_ofst)
  (eval_operand ops.iao_ofst s) (eval_operand ops.iao_ofst t) /\
ptr_lookup_transport births positions (op_prov TG sizeop)
  (op_taint tn sizeop) (eval_operand sizeop s) (eval_operand sizeop t) /\
(!op. IS_SOME (eval_operand op s) = IS_SOME (eval_operand op t))
```

This statement is an interface proposal, not installed or proved here. Offset
and size lookup transport come from mixed/nonopaque operand transport. The
last clause is presence parity, not value equality: even opaque variables have
presence parity in `ptr_mixed_vars_def`:259-263 (use
`ptr_mixed_vars_opaque_lookup`:280-289). Labels are already equal. The existing
proof at ExactWriteTransport:67-84 uses unrestricted transport ONLY to derive
these facts; the remaining exact interval proof is geometric. Its fixed-exact
sibling and containment consumers need the analogous in-place propagation,
not duplicate lemmas. This proposed supplier must still be formally proved and
its callers repaired by an authorized component. It is not credited as X.
For MCOPY in particular, operand-restricted transport of [dop;sop;nop] suffices;
no opaque return-PC value equality is needed. Source MCOPY success in the already
constructed historical prefix is available before X; the *new endpoint read*
success remains downstream of X. These are different uses of source success.

### Exhaustive chronological-footprint partition

ChronologicalHistory:29-72 has exactly next/block/call/ret; root is not a
transition. `step_writes` (ptrDiscipline:267-274) is an instruction footprint,
NOT automatically the set of all state changes of a chronological event.
`source_memory_write_ranges` (codegenRel:131-225) has exactly the nonempty
families listed below; all other opcodes return [].

| Event/family | Footprint and supplier obligation |
|---|---|
| ordinary next: MSTORE, MSTORE8, ISTORE | Fixed 32/1/32 range only when BOTH destination and value evaluate; mixed nonopaque eval parity and classified destination required. Actual source post differs only in cursor from chrono successor. |
| ordinary next: MCOPY, CALLDATACOPY, RETURNDATACOPY, DLOADBYTES, CODECOPY | Sized destination range only when destination/source/count evaluate; zero count has empty range. MCOPY conditional exclusion exists but still has old unrestricted signature. Copy content and source read success are not needed merely to classify an already executed historical footprint. |
| ordinary next: EXTCODECOPY | Same sized range, with additional addr evaluation guard. Include its presence parity, not just dst/count. |
| ordinary next: CALL, STATICCALL, DELEGATECALL | All operand evaluation guards, requested destination range clipped by MIN(requested size,LENGTH actual post returndata). Needs immediate-source/normalized-sample bridge above. Not an INVOKE entry. |
| ordinary next: every other opcode, including ALLOCA rewritten to ASSIGN and deleted NOP | source_memory_write_ranges=[]; allocas change taint/allocator, not a step_writes interval. Use existing rewrite facts to identify target opcode. |
| block entry JMP/JNZ/DJMP | step_writes=[]; enters_block/PHIs change variables, not memory. Accepted jump integration is not a memory exclusion proof for ordinary writes. |
| call entry INVOKE | step_writes=[] by opcode; setup/entry preserve memory. Do not substitute completed big-step INVOKE execution or a callee's later footprint. |
| return merge RET | step_writes=[]; merge keeps current callee memory, restores caller fields and binds outputs. There is no hidden rollback to saved caller memory. |
| return DRET | Syntactically can have multiple write ranges from dynamic return packing (codegenRel:212-223); NOT empty by being a terminator. Excluded by source fn_ptr_ok, then target production preimage. RETFMP also excluded by fn_ptr_ok (though its write ranges are []). This is a syntax exclusion, not ordinary-write consumer coverage. |
| root entry | No prior write; sentinel supplies identity agreement on x<lo only. |

### Fixed-byte path and dependency order

PairedFields:117-125 supplies `ptr_paired_initial_origin` and
`ptr_paired_initial_sentinel`: initial agreement on {x | x<lo}. For a current
untainted fixed read byte, one must still choose either that initial sentinel
(no source writer) or its last actual source writer and then exclude all later
target writes. W has immediate content for a selected ordinary writer, not
that choice or fixed-byte suffix exclusion. Fixed/fixed writes use exact
identity footprint matching; owned writes use allocation positions disjoint
from reserved intervals via fixed_region_reserved and production reservations.
`max_live_eom` bounds reserved ends for the final static consumer; it supplies
neither last-writer selection nor equality. The owned-byte quotation does not
assert this separate fixed-byte path is done.

Dependency verdict: SAME historical source prefix + access/taint + mixed
used-operand transport -> historical classification -> exact/contained target
footprint -> existing same-w geometry -> X over the existing prefix -> read
agreement -> new source step -> new W entry. The first non-applicable checked
consumer is the unrestricted transport premise; historical poststate/gap
assembly and external-call clipping remain explicit secondary bridges. No
universal source-prefix coverage is used to supply X, no new invariant was
installed, and no task falsehood is claimed. Stop this diagnostic here for
strategist selection of the next durable interface; do not append RET or a
queue of conditional opcode wrappers.

### C1.5.90.67.26 historical gap checkpoint

The source-only interval and two field bridges above, and the downstream
`ptr_paired_samples_post_returndata`, are checked without adding any premise
to the certificate. Their only event restriction is q<LENGTH done, so the
last departed event (whose next sample is the final history observation) is
included; the root with done=[] has no such event. NOP gaps may be empty.
The source theorem hypotheses are the actual structural trace, index bound,
and defining n/m equalities; the paired theorem additionally needs the actual
paired_samples predicate. No future source step or read equality is assumed.

This closes the immediate-poststate/normalized-sample field gap only.
Historical write classification for remaining ordinary families, source-success
supply for the MCOPY read consumer, fixed-byte exclusion, and universal target
prefix coverage remain unresolved. No CALL/RET simulation or global write
exclusion follows from these field equations alone.

### C1.5.90.67.27 requested-write classification generalization

HistoricalWriteClassification now exports `ptr_historical_write_classification`
in place of the MCOPY-only theorem (the old theorem is removed). It retains
stage, placement, transcript, historical index/snapshot, access_ok, taint_ok,
and non-forwarding premises. Its instruction-specific inputs are exactly
`mem_write_ops (EL j h).po_inst = SOME ops`, successful evaluation of
`ops.iao_ofst` to d, membership of `(w2n d,len)` in the source requested write
ranges, and len<>0. Its fixed/owned conclusion retains destination taint
purity in the fixed branch and exact provenance, historical destination tag,
production position, and strict word bound in the owned branch. A local
destination-purity fact uses taint_ok and mem_write_ops opcode cases; no new
purity premise was added.

HistoricalMcopyExclusion's existing `ptr_demand_mcopy_write_exclusion` keeps
its statement and now supplies the actual requested range and write-operand
record to this generic classifier. Both directly affected theories build.
There are no other SML imports/callers of these two theories in the current
source search. Earlier MCOPY-specific classification references in this
inventory describe the old interface and are superseded by this paragraph.

The generic requested-range boundary does not classify a clipped CALL actual
footprint as its requested length, nor classify zero-length ranges as bounded.
It does not construct source execution. Historical ordinary-event assembly
still needs exact event operands and footprints, immediate poststate fields
(where applicable), and the actual same-history access/taint suppliers.
MCOPY source-success for the read consumer, fixed-byte suffix exclusion,
and universal target-prefix coverage remain unresolved.

## Current universal-step checkpoint (.67.67, after exact MLOAD producer)

This section supersedes historical statements above that D/X, actual footprint
framing, writer retention, or owned/fixed byte recovery are still missing.
It does NOT certify universal coverage. Specification quotations are in
`concretizePtrUniversalStepSchemaScript.sml`; they typecheck without assertions,
cheats, definitions, or axioms. The two ML values are terms, NOT theorems.

### Common consumer and production bridge

`universal_normalized_step_schema` spells out the frozen antecedent (with a
chosen `names` witness), an existing normalized six-field paired prefix, actual
target chronological step, and static production bridges. Its conclusion
existentially supplies a nonempty finite source extension, all new ghost data,
write/call ledgers, and a normalized complete prefix at the actual target
successor. `done` grows by the departing source endpoint; snapshots grow by
exactly the source extension length. Source execution, post-state mixedness,
source memory agreement, and target suffix exclusion are NOT hypotheses.

The production bridges are deliberately explicit, not claimed to follow merely
from an arbitrary prefix: LIST_REL paired_code on context functions, code-name
preservation, source fn_inst_wf/retpc_shape_ok/opaque_use_ok/first_block_no_phi/
block wf/distinct labels/ALLOCA coverage, and target distinct labels. They are
static supplier obligations at the eventual stage consumer. `ptr_paired_code`
alone relates current function blocks and map entries; it is not a context-wide
stage decomposition or ALLOCA coverage theorem. In particular choosing R/lp and
proving the context-wide bridge from the frozen stage remains integration work.
The existing root and call producers use precisely this sort of static bridge.
These are NOT proposed added hypotheses to concretize_stage_static_mem.

### Exhaustive current supplier table

Rows N1--N18, J/C/R, X1--X5/T refer to the disjoint, exhaustive opcode sets in
the original dispatch table (lines 154--182). The four actual transition
constructors are next, block, call, ret in ChronologicalHistory lines 29--72;
root entry is a history constructor, not a fifth step. No error/halt event is
silently included in next. All theorem files below are run-owned helpers unless
explicitly qualified as contract suppliers.

| Event/family | Installed supplier and exact scope | Remaining consumer premise / status |
|---|---|---|
| Root B | PairedRoot: `ptr_paired_root`, `ptr_paired_root_normalized` | Full root certificate and normalization checked. Actual root inversion, matching production function, wf/no-PHI/coverage premises must be supplied from stage. Not an arbitrary-target-history theorem. |
| Source gap G | PairedPrefixProbe: `ptr_paired_prefix_gap_scan`, `ptr_paired_prefix_normalize` | Full six-field gap preservation checked; needs fn_inst_wf and current prefix. No opcode simulation missing for deleted NOPs. |
| N1 ADD/SUB | OwnedAffinePrefix: `ptr_affine_prefix_aligned_next`, `ptr_affine_owned_prefix` | Ownership/unrestricted variable-transport prefix, not a full mixed six-field certificate. Historical samples/callers/writes assembly and mixed input adaptation still required. |
| N2 scalar/masked arithmetic (entire original row) | AffineTransport and value/taint boundaries are conditional semantic ingredients | No full-prefix producer. Need exact success/selection and mask transport for each semantic family, not just result arithmetic. OFFSET stays in this row. |
| N3 EQ/LT/GT | ComparisonTransport: `ptr_comparison_eq_transport`, `ptr_comparison_lt_transport`, `ptr_comparison_gt_transport` | Conditional comparison values, with provenance/displacement and closed-end bounds. No full-prefix producer or universal derivation of its displacement premises. |
| N4 ASSIGN | AssignProducer: `ptr_paired_prefix_assign` | Exact immediate mixed paired-prefix extension checked with the MLOAD antecedent/conclusion, replacing only the source opcode. Target success constructs source success, including opaque return-PC copies; PairedNextAttach retains the full certificate. Source ALLOCA preimage goes to N17, not this row. No universal dispatch claimed. |
| N5 PARAM | ValueSelection selection boundaries; installed ptr_paired_params at endpoint | Actual PT/masks relation available; conditional selection still needs full mixed step/certificate assembly. |
| N6 INITIAL_FMP/BUMP/RETPC_PARAM | OpaqueRetpc: `ptr_mixed_vars_retpc_step_transport` for RETPC_PARAM | No full-prefix supplier for this row. BUMP/INITIAL_FMP not excluded by discipline; two-output/control-state semantics cannot be dropped. |
| N7 MLOAD | MloadProducer: `ptr_paired_prefix_mload` | Exact full immediate extension, arbitrary target chrono successor, frozen stage premises including max_live_eom, no extra source-success or read agreement premise. TG'=step_prov; other ghost maps and ws unchanged. Normalize afterward by PairedPrefixProbe. |
| N7 ILOAD | Conditional read/value interfaces only | Not covered by MLOAD theorem. Requires its own semantic read/taint mapping and certificate attachment. |
| N8 MSTORE | MstoreProducer: `ptr_paired_prefix_mstore` | Exact full immediate extension from current prefix and stage premises, arbitrary target chrono successor. Adds one actual ledger record; normalizer then applies. No source-success premise. |
| N8 MSTORE8/ISTORE | Existing byte-content/footprint boundaries only | Not covered by MSTORE's exact opcode hypothesis. Full mixed/write-ledger extension missing. |
| N9 MCOPY | McopyContent masked content; HistoricalMcopyExclusion conditional exclusion | Need mixed-compatible source success/read recovery consumer plus actual write record/certificate extension. The historical consumer's stronger transport hypothesis is not supplied by mixed variables. |
| N10 buffer copies | BufferCopyContent: conditional payload and returndata-bound content | No full-prefix producer; successful operand evaluation, exact payload/shared fields and RETURNDATACOPY guard must be derived, not assumed. |
| N11 EXTCODECOPY | Footprint/content ingredients | No full-prefix producer; account-code payload and complete shared-field preservation still consumers. |
| N12 SLOAD/SSTORE/TLOAD/TSTORE | Shared core and masked operand ingredients | No full-prefix producer. Successful static-frame branch inversion needed; memory read recovery does not itself prove storage equality. |
| N13 environment/scalar outputs | `ptr_paired_prefix_environment_read` in concretizePtrEnvironmentReadProducer proves the full immediate-prefix producer for CALLER, ADDRESS, CALLVALUE, ORIGIN, GASPRICE, CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, CALLDATASIZE and RETURNDATASIZE, using only actual target chronological success. | Remaining: GAS, SELFBALANCE, BALANCE, BLOCKHASH, CODESIZE, EXTCODESIZE, EXTCODEHASH, BLOBHASH, BLOBBASEFEE, CALLDATALOAD and DLOAD. No whole-row coverage; opaque environment facts are not unrestricted variable equality. |
| N14 SHA3/LOG | Owned/fixed read recovery plus conditional value/log ingredients | Need actual untainted payload and topics/static guard, exact effects and certificate assembly. No full producer. |
| N15 CALL/STATICCALL | ExternalCallContent conditional content, exact footprint clipping, post-returndata and core boundaries | Need whole request agreement derived from discipline/read recovery and actual outcomes/shared poststate. No full producer; clipped actual footprint is already available, not a new exclusion gap. |
| N16 DELEGATECALL/CREATE/CREATE2 | Existing request/footprint ingredients | No full producer. Distinct request/outcome/rollback semantics; cannot infer from CALL. |
| N17 ALLOCA -> ASSIGN | MixedAllocationPrefix: `ptr_paired_prefix_alloca_success`, `ptr_paired_prefix_alloca_immediate` (E0441); StructuralDispatch: `ptr_paired_structural_prefix_normalize` | Mixed fresh/cached success, retained births and full immediate six-field certificate checked. Normalized extension checked under exactly the universal-schema antecedent plus the ALLOCA/RET disjunction. Static production bridges remain explicit; not universal coverage. |
| N18 ASSERT/ASSERT_UNREACHABLE | Scalar/untainted restrictions from discipline are the intended suppliers | No full-prefix producer. Target continuing branch must force matching successful source condition. |
| J/JMP | PairedJump: `ptr_paired_jump_prefix_normalize` | Full normalized six-field extension checked. Static wf/retpc/coverage, actual target block-event premises and non-DALLOCA must be supplied/inverted. No assumed source success. |
| J/JNZ | PairedJump: `ptr_paired_jnz_prefix_normalize`; PairedJumpEntry: `ptr_owned_jnz_scalar` | Full normalized extension with explicit cond/yes/no syntax and scalar/nonopaque/empty-taint restrictions. Restriction supplier derives them from ownership+discipline+fn_ptr_ok+inst_wf+no-DALLOCA+opaque_use_ok; these must actually be matched in dispatch. Not unconditional coverage by itself. |
| J/DJMP | PHI-entry/cursor transport available | No full normalized producer; successor selection and scalar label-index restriction remain. |
| C/INVOKE | PairedCallSchema: `ptr_paired_invoke_prefix_normalize`, with InvokeArgs/CallEntry | Full immediate and normalized prefix checked; target decode/eval/lookup/setup/entry/event inversion and static context code bridge explicit. New token LENGTH h, registry and entries insertion, empty callee TG, saved (PT,TG) and call indices pushed, ws retained. Root/call entry uses no body execution. |
| R/RET | ReturnPrefix: `ptr_paired_ret_prefix_immediate` (E0456); StructuralDispatch: `ptr_paired_structural_prefix_normalize` | Actual source return, equal ordinary return values, historical saved-caller restoration, synchronized token/PT/TG/saved/calls pop and complete immediate certificate checked. Normalization derives resumed caller fn_inst_wf from actual successor history and context membership, without a new premise. All universal-schema static bridges remain explicit; root RET has no chronological successor. |
| X1 forbidden FMP family; X2 DALLOCA; X3 DRET/RETFMP | OperationalOpcodes: `ptr_stage_no_dret`, `ptr_stage_observation_no_dret`; contract positions preimages/no-ALLOCA/var-opcode facts | Syntax/discipline exclusions, not producers. Distinguish forbidden family from allowed N6; no-DALLOCA is separate task premise. Need dispatch contradiction at actual target preimage. |
| X4 PHI | Atomic production entry/PHI transport in MixedPhi and PairedEntry | No successful ordinary PHI next step. Already accounted for at B/J/C; not a residual opcode requiring ordinary simulation. |
| X5 NOP | Contract concretize_positions_nop; executed coverage/gap interfaces | Output NOP excluded via actual production preimage/coverage. Source-only deleted gaps handled by G. |
| T RETURN/REVERT/STOP/SINK/SELFDESTRUCT/INVALID | No continuing chronological step for halt/abort/error; successful terminal access uses eventual endpoint static bound | Not an extension branch. A reachable active terminal observation still needs memory access bound/revert-forward exemption; cannot delete it from final stage proof. |

### Historical structural priorities: ALLOCA and RET

The following selection and supplier ledger record the pre-E0441/E0456 audit.
Their missing immediate certificates and normalization are now discharged by
MixedAllocationPrefix, ReturnPrefix and StructuralDispatch as summarized in the
current table above and the closing checkpoint below. They are retained as
historical interface analysis, not current open obligations.

First precise unsupported implication selected (historically):
`mixed_allocation_success_schema` in UniversalStepSchema. It retains the frozen
stage assumptions plus the current actual prefix and normalized production
instruction correspondence, source ALLOCA opcode, source fn_inst_wf and
retpc_shape_ok, and actual target chronological successor. It concludes source
`step_inst 0 ... = OK s'`, a genuine tagged successor b at the adjacent source
cursor, the computed birth overlay B, retention of every old birth entry,
computed tagged TG', mixed variable transport, core sharing and actual paired
cursor at zt. It does not yet assert all six post-prefix fields. The quotation
is fully explicit, including existential witnesses, without executable macros.

Supplier ledger for this selected boundary:

* Endpoint source ownership and mixed/core sharing: PairedPrefix endpoint,
  transcript erasure and StructuralTrace ownership (already used by MLOAD).
* Actual source reachability, membership and cached-size equality:
  ChronologicalHistory reachability, AllocationSize `ptr_frame_sizes` and
  `ptr_alloca_inst_size`; normalized instruction activity/coverage from current
  cursor and contract rewrite/preimage. Source fn_inst_wf yields literal size
  and single output; source retpc_shape_ok forbids ALLOCA writing own retpc.
* Target next inversion: source ALLOCA rewrites to target ASSIGN on covered
  production path; it is not an arbitrary source ASSIGN. Actual target successor
  and cursor alignment give the next retained index and adjacent source activity.
* Fresh and cached source execution and owner tag: AllocationTransport contains
  the correct branch proof but its consumer requires ptr_vars_transport. Adapt
  this existing theorem in place, or provide the genuinely mixed semantic
  boundary, rather than assume unrestricted transport or duplicate it locally.
  Old nonopaque lookups should extend under retained births; opaque lookup
  presence/env are unchanged except the proven nonopaque allocation output.
* Birth retention: ActivationBirths `ptr_source_birth_caches_snoc_retained` and
  ownership extension, with the SAME HD tokens and actual allocation cache.
  Cached execution reuses its birth. This does not require fresh bases or
  vs_alloca_next=0. No new activation token or entry index is allocated here.
* Target ASSIGN changes no memory/core state; source ALLOCA changes allocator
  bookkeeping, which core deliberately does not equate. Use core boundary, not
  whole-state equality. Cursor advancement is separate from value updates.
* Then (later consumer) transcript/sample extension can use the new mixed
  endpoint; alignment/parameter/caller/W retention must be checked under the
  changed births and TG. Existing full MSTORE/MLOAD proofs do NOT supply this
  allocation-specific extension automatically.

This is a missing mixed semantic boundary plus later finite integration; the
audit has not found a necessary new invariant. That is a bounded conclusion,
not a proof of satisfiability of the proposed universal theorem.

RET is the next structural risk, not claimed solved by the ALLOCA quotation.
`ptr_mixed_return_bind` consumes already equal returned scalar lists and
adopt_fmp=NONE. Its input is saved caller mixedness, not callee endpoint mixedness.
The paired caller record must select the historical caller's PT/TG and current
memory taint, derive actual source RET and matching returned list from target
IntRet and source discipline, then bind/restack/cursor/normalize. `calls` and
`saved` must pop together; births and registry retain completed activations,
whereas tokens pop. Existing return-bind and retention lemmas cannot be renamed
as this whole theorem. No source return step or equal returned values should
be added as a hypothesis to a final return producer. Before authorizing that
integration the exact caller relation and memory-taint rebase should be inspected.

### Verification and scope

`holbuild(targets=["concretizePtrUniversalStepSchemaTheory"])` passed. This also
rebuilt AllocationTransport, OwnedAffinePrefix, OwnedAllocationPrefix, PairedEntry,
PairedCallEntry, PairedCallSchema, PairedJumpEntry and PairedJump on the current
base without dropping lemmas. MloadProducer separately passed at session start.
No semantic theorem was asserted here, and no frozen contract file was edited.
No new positions-rewrite lemma was proposed: all such needs use existing
concretizeStepStructure/StepShape/StepCallChecks/StepRetpc/StageShape imports.

## ALLOCA immediate certificate audit (allocCertificateAudit)

The earlier N17 success gap is now discharged by
`concretizePtrMixedAllocationPrefix.ptr_paired_prefix_alloca_success`
(lines 97–123): its antecedent and existential conclusion are exactly
`mixed_allocation_success_schema`. This covers fresh AND cached execution,
including zero size, without a zero allocator-frontier assumption.
`mixed_allocation_immediate_prefix_schema` adds only the immediate six-field
prefix conclusion under that SAME antecedent. It is a typechecked quotation,
not a theorem. `holbuild(targets=["concretizePtrUniversalStepSchemaTheory"])`
passed after its addition (TO_concretize_ptr-20261105T174221Z_m15721_t001).

Write `S = (tokens,registry,B,PT,TG',saved,entries)`. The candidate appends
`h++[b]`, `ht++[zt]`, `done++[LENGTH h-1]`, `H++[S]`, keeping calls and ws.
The following ledger distinguishes installed suppliers from assembly still
unproved. All field definitions are in PairedPrefix, lines 174–183.

| Field | Exact supplier interface and allocation match |
|---|---|
| transcript | StructuralTranscript pair rule, lines 33–56, consumes old transcript, `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved`, target `ptr_chrono_step C' at zt`, equal departing inst ids and the equal-stack-length disjunct. The tagged step is an explicit success conclusion. Source stack is unchanged by success; target stack is unchanged by ordinary ASSIGN event inversion. Existing contract rewrite id preservation gives equal ids. ActivationChronology tokens/registry definitions therefore reduce to tokens/registry, the entry conditional selects entries, and its computed overlay is exactly B. The rule appends S, not an altered copy of H. |
| placements | `ptr_stage_placements C' positions` is unchanged: C' and positions do not change. Project from old prefix. No new layout premise. |
| samples | `ptr_paired_samples_pair`: old samples AND `ptr_paired_sample positions b zt S` imply samples on the four appended lists. The new sample definition is exactly the success conclusion's mixed variables and core sharing. It uses B and TG' only at the new endpoint. |
| alignment | `ptr_paired_alignment_pair`: old samples, old alignment, `ptr_paired_code R lp positions b.po_fn zt.po_fn`, `ptr_paired_cursor lp b zt`, and `ptr_paired_params positions b zt S` imply appended alignment. Cursor is explicit in success. Code follows from endpoint code and b.po_fn=a.po_fn, with zt.po_fn=at.po_fn from ordinary target ASSIGN inversion. Params require the birth-extension implication specified below, plus unchanged source/target vs_params. The new TG' is irrelevant to ptr_paired_params. |
| callers | `ptr_paired_callers_retained`: old callers, `EVERY (\\n. n<LENGTH h) done`, `LENGTH done<LENGTH ht`, `LENGTH H=LENGTH h`, b.po_stack=a.po_stack and zt.po_stack=at.po_stack imply callers on arbitrary appended hs,ts,ds,snapshots with the same saved/calls. Length premises follow from old samples. Source stack is a success conclusion; target stack is ASSIGN inversion. No caller birth-map substitution is performed. |
| writes | `ptr_paired_writes_pair` (PairedFields lines 217–229) consumes old writes, `LENGTH H=LENGTH h`, positive source length, `LENGTH ht=SUC(LENGTH done)`, `EVERY (\\n. SUC n<LENGTH h) done`, the empty-or-singleton extra shape, EVERY new-write certificate on extra, and the departing nonempty-footprint implication. Choose extra=[]; EVERY and shape are trivial and ws++[]=ws. Structural trace embedding supplies the strict done bound. `LAST h=a` follows from source history. ALLOCA has `range_bytes(step_writes a.po_inst a.po_state b.po_state)={}`, so the implication is vacuous, regardless of fresh/cached allocation. No write equality or target exclusion premise is added. |

### Exact small missing transport boundary

No exported args birth-extension theorem was found in ValueTransport or
AllocationTransport. The precise desired implication (not an additional schema
premise, and not asserted here) is:

```sml
(!owner site. FLOOKUP births owner = SOME site ==>
  FLOOKUP B owner = SOME site) /\
ptr_args_transport births positions tags masks xs ys ==>
ptr_args_transport B positions tags masks xs ys
```

Installed `ptr_value_transport_birth_extension` has exactly the same lookup
retention antecedent plus `ptr_value_transport births positions tag mask x y`,
and concludes that value relation with B. `ptr_args_transport_def` is two
unchanged length equalities and
`LIST_REL (\\(tag,mask,x) y. ptr_value_transport births positions tag mask x y)
 (ZIP(tags,ZIP(masks,xs))) ys`. Thus LIST_REL monotonicity lifts the installed
value theorem; no new semantic invariant is indicated. The accepted success
supplier already concludes lookup retention for B. For paired params, the
PT=[]/equal-vs_params alternative is preserved directly; otherwise apply this
implication to unchanged PT, parameter lists and replicated empty masks.
ALLOCA/ASSIGN preserve vs_params, independently of the observation po_params
field (do not confuse these two). These operational projection facts remain
assembly obligations, not consequences of mixed variables alone.

### Audit verdict and scope

Immediate ALLOCA integration now appears standard constructor/list assembly
with one small reusable args-monotonicity boundary; no additional hypothesis
or change to the paired-prefix definition was identified. This verdict is NOT
a checked full-prefix theorem. In particular the quotation does not certify
its own premises or conclusion. Source execution and birth retention must be
obtained from the accepted success theorem, not assumed a second time.
`ptr_structural_transcript_append_prefix` preserves TAKE/EL of old H exactly;
all old samples, caller certificates and write certificates continue to use
their original snapshots. Neither B nor TG' may replace historical witnesses.
Normalization is a separate existing consumer. RET and other event families
were not advanced in this diagnostic; universal coverage is still unproved.
No positions-rewrite lemma or frozen contract file was added or edited.

## RET reconstruction audit (C1.5.90.67.returnAudit)

E0441 supersedes the preceding ALLOCA audit's unproved status: the exact
`ptr_paired_prefix_alloca_immediate` is now Finalised and built. It does not
establish universal coverage. `return_immediate_prefix_schema` in
UniversalStepSchema is a quotation ONLY, built/typechecked independently of
any proof. It repeats the production/static premises of
`universal_normalized_step_schema`, specializes the source opcode to RET,
and concludes actual source IntRet, successful caller binding, tagged return
and a complete one-event prefix. No source success, returned-value equality,
rebased caller mixedness or post-prefix is an antecedent.

### Actual semantics and first missing implication

* ChronologicalHistory lines 60–71 require a NONEMPTY stack, source IntRet,
  successful bind_outputs and an active caller continuation. RET with an empty
  stack has no chronological return successor. In step_inst_base lines 768–774,
  RET evaluates all operands, rejects NONE and SOME [], and returns FRONT of
  the nonempty value list with adopt_fmp=NONE and unchanged state. No comparison
  of the last operand with a return-PC token is performed. Thus empty-stack
  terminal return is not a new chronological-prefix event to simulate here.
* The positions rewrite of RET is unchanged by the existing contract
  `concretize_positions_unchanged`; contract structure/retpc/call-check/shape
  theories are already ancestors of UniversalStepSchema. No new rewrite fact
  is needed or introduced.
* Endpoint mixedness is NOT equality of all operands. The first missing checked
  semantic boundary is: from the production antecedent, current paired prefix,
  source RET, matching target instruction and actual target return, construct
  source `step_inst 0 C a.po_inst a.po_state = IntRet r a.po_state` with
  `r.iret_values = rt.iret_values` and both adoption fields NONE. Here rt is
  extracted from the actual target return, not supplied as a new assumption.
  This is a backward-success/equal-FRONT boundary, not an application of
  ptr_mixed_return_bind. It needs source discipline to forbid pointer-valued
  ordinary return operands (fn_ptr_ok/ptr_use_ok), and taint_ok to give empty
  operand taints. Tagged scalar provenance also needs to be discharged, not
  silently assumed. retpc_shape_ok/opaque_use_ok isolate the final opaque
  operand: its presence, rather than its value, must agree. Existing
  ptr_mixed_vars_eval_presence supplies per-operand presence; the existing
  ptr_mixed_vars_eval supplies transport of nonopaque operands, and
  ptr_value_transport_scalar_empty gives equality after scalar/empty-mask
  premises. Applying ptr_mixed_vars_eval_operands to the WHOLE RET list is
  invalid when its final operand is opaque. No installed theorem yet combines
  these facts into equal ordinary FRONT lists under these exact premises.
  NONE adoption is a RET computation on both sides; fn_ptr_ok excludes
  RETFMP/DRET elsewhere, but those opcodes are not this specialized schema.

### SAME historical snapshot, not current callee mixedness

Let `(n,j)=HD calls`, `f=HD a.po_stack`, `ft=HD at.po_stack` and
`(RPT,RTG)=HD saved`. PairedFields lines 62–78 give j<LENGTH done,
n=EL j done, saved caller frames equal to EL n h / EL j ht, INVOKE at both
indices, and saved tags equal to the PT/TG fields of the SAME `EL n H`.
Destructure that snapshot as `(tsn,rn,bn,PTn,TGn,sn,en)`. Then RPT=PTn and
RTG=TGn; PairedPrefix samples give precisely

```
ptr_mixed_vars bn positions TGn (EL n h).po_taint
  f.cf_fn ft.cf_fn f.cf_state ft.cf_state
```

at the saved call, NOT current callee mixedness. Caller cf_tvar is that
historical observation's t_var. At return, the new source taint is current
a.po_taint with t_var replaced by DRESTRICT f.cf_tvar outside the outputs.
The old snapshot's t_mem is NOT equated with current t_mem. This does not by
itself block mixed-variable restoration: ptr_mixed_vars_def uses only
op_taint tn (Var x), hence only t_var, not t_mem. A field-local taint replacement
is sufficient at this boundary. No memory equality or saved memory snapshot
is required for return binding.

The other required lift is bn -> current births (then the new overlay B).
`ptr_transcript_birth_retained` supplies lookup retention from historical n
to the last source index under no-DALLOCA. `ptr_value_transport_birth_extension`
supplies pointwise monotonicity. There is no ready mixed-vars historical-return
lift in the inspected interface: it must preserve opaque environments and
presence and use lookup monotonicity for ordinary variables. This is a small
precise boundary to prove, not permission to rewrite EL n H or map old H.
It should conclude mixedness of the SAVED caller states at current births
with caller t_var and current memory taint; it must retain exactly RPT/RTG.

### Return consumer and six-field supplier ledger

`ptr_mixed_return_bind` (OpaqueRetpc 691–714) consumes saved caller mixedness,
EVERY non-retpc outputs, equal returned lists, and NONE adoption on both sides.
It concludes equivalent binding failure and mixedness after successful binding
with DRESTRICT RTG and DRESTRICT caller t_var outside outs. The output condition
comes from `ptr_retpc_invoke_outputs`: caller retpc_shape_ok, historical INVOKE
membership, opcode INVOKE. Frame/call certificates identify that same INVOKE;
shape must come from caller context membership, not current callee shape.
Target binding success then implies source binding success, once the two
preceding semantic boundaries are proved.

| Field | Exact proposed supplier / remaining match |
| --- | --- |
| transcript | tagged return rule (SourceOwnership 56–70), then transcript pair rule with both stacks decreasing by one; ptr_activation_tokens pops, registry unchanged, entries unchanged; birth overlay uses resumed head token and restored caller vs_allocas |
| placements | retain historical stage placement witnesses and match caller code from its historical sample/context; do not invent fresh positions |
| samples | historical saved-caller mixedness lift, equal-FRONT RET boundary, ptr_mixed_return_bind, and merge/adopt core-sharing boundaries; new snapshot only uses current B and restored tags |
| alignment | saved INVOKE cursor and actual target successor must yield active source continuation after the saved index; an immediate NOP is allowed before common normalization. params come from saved caller vs_params, PTn and historical paired params lifted along retained births, not the callee's PT |
| callers | pop calls and saved in lockstep with stacks; all remaining certificates use unchanged (n,j) and unchanged old EL n H. Append/list retention is sufficient; no snapshot rebasing of remaining callers |
| writes | return is a terminator, not a memory-write event; keep ws and old certificates unchanged, discharge coverage using the terminator exclusion in paired_writes. No fictitious return write or new byte agreement |

The precise first gap is equal-FRONT source RET success. The next independent
interface gap is historical saved-caller mixedness at the new birth map; the
above lookup/taint analysis explains its likely proof without claiming it.
Caller continuation/cursor assembly and the other six fields remain unproved
consumers, not consequences of quotation typechecking. tokens become TL tokens;
PT becomes FST(HD saved), TG becomes DRESTRICT (SND(HD saved)) outside caller
outputs; saved/calls pop, registry/entries persist, births retain completed
activations. These transitions must be proved from the transcript semantics.

### ALLOCA normalization signature check only

The accepted immediate ALLOCA certificate matches the first premise of
`ptr_paired_prefix_normalize` directly with a=b and at=zt and the appended
histories/snapshot. The second premise is fn_inst_wf b.po_fn, obtained from
b.po_fn=a.po_fn and the ALLOCA schema's fn_inst_wf a.po_fn. Normalization appends
a source-only gap and snapshots, leaves target history/done and activation
fields unchanged, and obtains a non-NOP matched endpoint. Combining list
appends gives delta=[b]++gap and the analogous snapshot list, so delta is
nonempty. This is a signature match, NOT a new proved allocation-normalization
theorem. No extra allocation helper or universal claim was added in this audit.


## Checked normalized structural dispatch (C1.5.90.67.structuralDispatch)

`concretizePtrStructuralDispatch.ptr_paired_structural_prefix_normalize` is
Finalised and build-checked. It has exactly the antecedent of
`universal_normalized_step_schema`, augmented only by source opcode
ALLOCA or RET, and exactly its existential conclusion: nonempty source delta,
equal snapshot length, full appended paired prefix, non-NOP source endpoint
and actual positions-rewrite endpoint equation. It consumes the accepted
immediate certificates (ALLOCA E0441, RET E0456), then normalizes once. Resumed
caller well-formedness follows from actual successor history/context membership
and the existing global EVERY premise, not a new assumption.

This supersedes the open-status claims in both historical structural audits
above, including their quotation-only immediate certificates, equal-FRONT and
saved-caller transport gaps, and normalization-signature-only conclusion.
Old snapshots are retained unchanged; no memory equality, unrestricted variable
transport, source-success premise or new positions-rewrite fact is introduced.

The context-wide paired-code/name and source/target wf/shape/coverage bridges
listed in the common consumer section remain explicit hypotheses. Deriving them
from the frozen stage antecedent is still integration work. Exhaustive dispatch
is NOT proved: the table's N1--N6, ILOAD, MSTORE8/ISTORE, N9--N16, N18 and DJMP
still lack full producers; scalar JNZ restrictions and syntax exclusions must
still be matched at dispatch, and final terminal access bounds remain separate.
MLOAD/MSTORE immediate producers still require common normalization at their
consumer. No claim of universal target-prefix construction or of the frozen
static-memory theorem follows from restricted ALLOCA/RET coverage.

## Shared non-writing attachment (C1.5.90.67.nonwriteAttach)

`concretizePtrPairedNextAttach.ptr_paired_prefix_nonwrite_attach` now composes
sample/alignment extension, unchanged-stack caller retention and empty-write
ledger retention into one full immediate-prefix boundary. It consumes the actual
extended transcript and local endpoint sample/code/cursor/parameter relations;
it does not construct source execution or endpoint mixedness. Unchanged births,
tokens, registry, PT, saved entries and calls are intentional scope restrictions.
The existing exact MLOAD producer uses this boundary, with its statement and
actual-target-success-only execution premise unchanged. Its source-success,
transcript, mixedness and cursor proofs remain semantic obligations discharged
inside that producer, not added premises. This refactoring adds infrastructure,
not any additional opcode coverage or proof of the global static bridges.
