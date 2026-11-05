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
| N4 | ASSIGN | next; assignment back transport exists, distinguish ALLOCA preimage |
| N5 | PARAM | next; selection boundary conditional on PT/masks; integrate actual historical parameter relation |
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
| N17 | ALLOCA | source next versus target ASSIGN; fresh/cached prefix boundaries exist; production position/birth/taint/support integration |
| N18 | ASSERT, ASSERT_UNREACHABLE | next when condition true; derive scalar untainted condition equality; false condition aborts |
| J | JMP, JNZ, DJMP | block; successor/control/evaluation and PHI entry residual |
| C | INVOKE | call only; next explicitly excludes, not a terminator, IntRet converted to OK |
| R | RET | ret only with suspended caller; returned scalar values/bind/merge relation residual; root IntRet has no successor |
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
