# Ordinary dispatch closure audit (C2.local.dispatch.closureAudit)

Diagnostic only. No new theorem, definition, or assumption is installed by this
report. Existing accepted theorem statements remain unchanged. Paths below are
relative to venom/compiler unless stated otherwise.

## 1. Actual consumer, and the mismatch to resolve before assembly

There is **no current uniform ordinary-dispatch theorem in SML**. The assemble
component is a PLAN obligation, not a checked consumer. Its requested consumer
is the simultaneous normal-mode successor of the recursive reachability
invariant. Do not describe assembly as instantiation of an existing theorem.

The exact checked data interface is lowerDloadCoverageInvariantScript.sml:9-17:

```
ld_frame_data V U E L H AP BP AG BH tn un s t <=>
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  ld_shared_state tn un s t
```

The largest concrete normal-memory successor reference is
`ld_mcopy_certificate_backward`, lowerDloadCopyCertificateScript.sml:32-98.
Its exact pre/post clauses, not its name, are the template: source annotated
reachability, ptr_discipline, fn_ptr_ok, operand support, owned vars, supported
owners, strict word-range caps, disjoint sites, byte relation, shared state,
frame embedding, allocation account, all-support definedness, parameter and
variable selections, suspended allocation count, frame/stack bounds, frame
floor, live-source ownership, source/target extents, target live representation,
variable-taint bounds, and nonmemory-mask inclusion. It produces one source OK
witness and all those successor fields (with ld_step_prov and step_taint), plus
both memory-only footprints. It does NOT produce annotated successor reachability,
configured position alignment, gas equality, exact non-current storage agreement,
or the entry/call parameter-value envelope.

MLOAD: lowerDloadMloadProducerScript.sml:72-145 uses
`U = {v | v IN V /\ ~retpc_var fn v}` and produces the parameter envelope and
vars-only footprints, but not shared-state or floor/representation clauses.
MSTORE: lowerDloadStoreCertificateScript.sml:9-74 produces floor/representation
and memory-only footprints, but not shared state or parameter envelope.
MSTORE8: lowerDloadByteStoreCertificateScript.sml uses the same memory-only
certificate style. Thus none of these names means the *entire* recursive
consumer is closed. MCOPY's U premise also needs observable operand support;
all-support V definedness alone does not supply value agreement for return-PCs.

The common postcondition for future integration must be fixed by the strategist
before implementing more families. It must be a conjunction at the same source
successor, not several existential witnesses assumed equal without proof.
Determinism of step_inst can identify separately produced source witnesses at
identical fuel/context/instruction/state; it cannot identify witnesses using
unrelated fuel parameters or different source instructions.

## 2. Premise provenance (not additional hypotheses to invent)

* Source anchor membership and active instruction: ld_annotated_fn_member and
  ld_annotated_active_inst; fn_ptr_ok follows from the context-wide premise.
* Access and taint: ld_annotated_access_ok, ld_annotated_taint_ok from
  lowerDloadReachableDiscipline. access_ok applies only outside
  in_revert_forward; taint_ok's clean-read clause is gated by about_to_revert.
* Scalar provenance: ld_annotated_scalar_prov after ptr_use_ok/fn_ptr_ok excludes
  pointer use in the operand slot. ILOAD and ISTORE force *every* variable
  operand scalar (ptrDisciplineScript.sml:120-139).
* Operand taint: ld_taint_operand_clean and taint_ok. The exceptional store
  value and shifted value may be tainted; don't claim all operands clean.
* Operand values/definedness: ld_owned_operand_clean / ld_owned_operand_defined;
  require support in U. opaque_use_ok and ld_retpc_observable_operand bridge
  ordinary observable operands from V to U, as scalar certificate lines 135-142
  demonstrate. ASSIGN/RETPC copies must use their dedicated boundaries.
* Geometry: ld_fixed_live_write_footprint and access classification, instantiated
  with access_ok, owned selections, low/site byte relation, finite caps and
  separation. None derives the global geometry invariant from reachability alone.
* Floor: ld_vars_floor_representation_transport transports vars-only footprints;
  memory-only footprints preserve allocas/frontier directly. Accepted state
  footprint lemmas must be used instead of unfolding all certificate fields.
* Shared: ld_shared_state_vars_transport and ld_shared_state_memory_transport
  cover their named footprints and unchanged shared masks. ISTORE is NOT a
  memory-only effect. GAS is NOT vars-only (it consumes the gas stream).
* Global producer obligations, outside local dispatch: the reachable invariant
  must supply the parameter envelope, U/V support, all-support definedness,
  finite caps, supported-owner freshness and live separation/representation,
  allocation account, suspended stack bounds, saved embeddings and source
  annotations. No local successful step proves these initial premises.
* ld_shared_state_environment provides equal code, data section, calldata,
  returndata and contexts (lowerDloadSharedStateScript.sml:78-89). Code-image
  equality for ordinary CODECOPY is therefore an explicit checked field; the
  DLOAD macro's code_end image condition is a different obligation.
* Gas-stream equality and exact non-current storage/transient equality are
  separate companion invariants, absent from ld_shared_state. Every row needs
  their preservation; only the GAS producer currently explicitly returns the
  gas equality as part of its data interface.

## 3. Exhaustive opcode partition and closure matrix

Enumeration is venom/defs/venomInstScript.sml:23-68. Columns are source OK (S),
owned/provenance (O), shared-state (H), byte relation (B), geometry/account/floor
(G), reachable premise derivation (R). 'certificate' means the named checked
statement, with the omissions in section 1; 'partial' never means ready to
assemble. Nonordinary rows remain assigned to the named existing parent groups.

| Opcode partition | Existing support and open columns |
|---|---|
| ADD, SUB | ld_affine_certificate_backward: S/O/B/G and parameter envelope; H/floor/companions must be composed from footprints. R: ld_annotated_affine_prov/backward; pointer+Label exclusion is essential. |
| MUL, Div, Mod, SDIV, SMOD, Exp, ADDMOD, MULMOD, SLT, SGT, ISZERO, AND, OR, XOR, NOT | ld_clean_scalar_certificate_backward: S/O/B/G and envelope, not H/floor. ld_shared_state_vars_transport and ld_vars_floor_representation_transport supply those latter columns; companions still need one integration application. R checked by annotated clean scalar boundary. |
| SHL, SHR, SAR | ld_shift_certificate_backward: S/O/B/G and envelope; H/floor/companions compose by footprints. Shifted operand may be tainted; shift_taint rather than clean equality. |
| LT, GT, EQ | ld_compare_certificate_backward: S/O/B/G; checked same-nonempty-site comparison case. R uses access_ok positive-size comparison, not arbitrary pointer order preservation. H/floor/companions compose. |
| SIGNEXTEND, BYTE | ld_owned_byte_backward gives S/O conditional on scalar clean operands. Missing full footprint-based postcertificate and reachable operand derivation. H/B/G unchanged apart from output/provenance bookkeeping. |
| OFFSET | Semantics exec_pure2 word_add (venomExecSemantics:1039-1044), not covered by affine ADD/SUB list. ptr_use_ok disallows pointer operands; scalar clean boundary and full certificate missing. Label value agreement must use owned operand relation, not assume contexts equal. |
| ASSIGN | ld_assign_certificate_backward: S/O and old certificate fields; retain opaque return-PC handling. H/floor via footprints; companions/envelope integration. |
| PARAM | ld_param_certificate_backward; needs parameter-value envelope, not just LIST_REL selection. H/floor/companions via footprint. |
| RETPC_PARAM | ld_retpc_param_certificate_backward; opaque value need not equal. Preserve V-definedness separately from U-owned values. Companion integration remains. |
| GAS | ld_gas_frame_data_backward gives S/O/H and gas-stream equality including consumed tail; geometry/floor/B/envelope/other companions not in its conclusion. Use concrete ld_gas_backward footprint, never shared-state gas inference. |
| CALLER, ADDRESS, CALLVALUE, ORIGIN, GASPRICE, CHAINID, COINBASE, TIMESTAMP, NUMBER, PREVRANDAO, GASLIMIT, BASEFEE, BLOBBASEFEE, BLOCKHASH, BLOBHASH, CALLDATASIZE, CALLDATALOAD, RETURNDATASIZE, CODESIZE | ld_environment_read_backward gives common equal update; ld_owned_environment_read_backward gives S/O with scalar-clean premises. H/B/G and companions need common update transport; R scalar/taint/opaque support derivation missing from a full certificate. |
| BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODEHASH | Not in environment-read opcode list. Need account-observation equality and common update transport. Reuse observation argument in o1LowerDloadJointRead1Script.sml:10-34 (account_empty ignores storage); its ld_shared_agree premise is NOT ld_shared_state. Derive needed record observation via ld_shared_state_nonstorage, not duplicate a joint simulation. |
| SLOAD, TLOAD | ld_storage_read_backward gives masked result and exact paired updates; ld_owned_storage_read_backward S/O. Full H/B/G and companions missing; output can be tainted, so clean update theorem is insufficient. Keys scalar/clean by ptr_use_ok and taint_ok. |
| SSTORE, TSTORE | lowerDloadStorageWrite boundaries supply S/O/H effect pieces. Need complete same-witness B/G/envelope/gas/non-current-account companion transport. Successful target plus defined operands and equal call contexts excludes static abort; definedness alone does not. Store values can be tainted. |
| MLOAD | ld_mload_certificate_backward S/O/B/G/envelope; add H/floor/companions. R and range proof checked in producer. |
| MSTORE | ld_mstore_certificate_backward S/O/B/G/floor; add H from memory transport, envelope/companions. |
| MSTORE8 | ld_mstore8_certificate_backward analogous byte-write certificate; same missing integration companions. |
| MCOPY | ld_mcopy_certificate_backward S/O/H/B/G/floor. Need U support bridge, parameter-envelope and external companion preservation. Zero length is explicitly split in its geometry proof. |
| ILOAD | Executes mload, NOT finite immutable-map read (semantics:982). Same fixed 32-byte read range as MLOAD (memLocDefs:275-280); out_taint is mem_word_taint. General memory-read boundary can serve MLOAD/ILOAD, but current MLOAD theorem is opcode-specific and immutable. Missing S/O/B/G/H packaged certificate. Scalar address plus access_ok implies nonempty read ends <=lo: positive high access would require pointer provenance, contradiction. Hence identity low-byte relation suffices; no whole-memory equality needed. |
| ISTORE | Executes istore=mstore plus immutable bookkeeping. memLocDefs:203-208 is fixed 32-byte write; imm_taint updates map and memory taint must also transport. lowerDloadImmutableWrite supplies bookkeeping S/O/H pieces, NOT B/G. Scalar fixed address lies low by same access argument. Need combined byte/map successor footprint; do not apply memory-only shared transport to istore. |
| CALLDATACOPY, CODECOPY, RETURNDATACOPY, EXTCODECOPY | Missing full external-payload destination certificate. lowerDloadCleanCopy only covers DLOADBYTES/CODECOPY taint; ld_shared_payload_write gives byte overwrite interface, not execution/R/G. Dest may relocate; offset/size and EXTCODECOPY account address scalar clean. Equal payload from shared context/code/returndata/nonstorage account code. RETURNDATACOPY target OK entails offset+size <= LENGTH returndata; equality gives source guard. OOB is Abort, not ordinary next. Empty payload/zero size must not demand positive access. |
| SHA3 | Missing clean padded-slice consumer certificate S/O/H/B/G. taint_ok gives clean slice outside about_to_revert; SHA3 is never that exception. Address may relocate, size scalar clean; prove byte-list equality before applying Keccak, not hash injectivity. No state memory expansion occurs here (semantics:950-964). |
| LOG | Missing clean padded-slice effect certificate. Topics and size clean/scalar, offset may relocate. Metadata Lit topic_count and REVERSE rest ordering essential (semantics:1049-1073); successful target excludes static abort after definedness. Only vs_logs changes, not byte memory or shared fields; histories need not have been equal. R clean memory follows taint_ok. Zero length read equality is empty list, no site required. |
| ASSERT, ASSERT_UNREACHABLE | ld_guard_backward/prov/taint give identity successful state and annotation behavior. Need explicit identity certificate integration; failing guards are Abort/Error, no next successor. |
| NOP | OK identity (semantics:871); no automatic assumption outputs=[] authorized. step_taint/provenance treatment for arbitrary output metadata must be checked against shape, rather than treating annotation as identity from opcode alone. |
| PHI | Prefix handled by ld_phis_certificate_backward in control subtree. step_inst_base outside prefix is Error, so cannot be ordinary OK next. |
| ALLOCA | C2.allocation; ld_alloca_certificate_backward changes owner table/layout/account. Not ordinary fixed-E transport. |
| DALLOCA | C2.allocation responsibility: changes fmp/memory, pointer-root output; cannot classify as vars-only read or exclude by fn_ptr_ok (not excluded there). |
| DLOAD, DLOADBYTES | Configured multi-instruction macro responsibility of coverage; lowerDloadLoadCertificate / lowerDloadBytesProducer accepted boundaries. Not ordinary same-instruction dispatch. |
| INITIAL_FMP, BUMP | lowerDloadExplicitBase accepted execution/ownership boundaries; BUMP changes fmp. Full shared/data/companions must use specific fmp effect, not generic vars-only transport. Allocation/frame integration responsibility must be assigned explicitly. |
| JMP, JNZ, DJMP | C2.control; ld_jump_backward and frame transport do not give temporal block/PHI alignment by themselves. |
| INVOKE, RET | C2.calls; ld_annotated_call_pop reconstructs source completion from annotated terminal anchor plus saved setup. Not ordinary dispatch. |
| RETURN, REVERT, STOP, SINK, SELFDESTRUCT, INVALID | C2.terminal / actual observation and abort responsibilities; not ordinary nonterminator OK next. Revert forwarding and RETURNDATACOPY-to-REVERT exception belongs to suffix mode. |
| CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2 | C2.external; oracle selection/adoption, request read slices, return write window and storage masks. No ordinary dispatch closure claim from shared-state environment alone. |
| MEMTOP, DRET, GETFMP, SETFMP, RETFMP, FMP_PARAM | Excluded at reachable source instruction by fn_ptr_ok (ptrDiscipline:123-128). Requires annotated membership proof. MEMTOP is not simulated from byte relation. |

## 4. Exact small missing interface specifications (proposals, not proofs)

Use original names/relations only. The following schemas specify textual
instantiation, not new HOL definitions. They must be approved before source work.

### A. Common footprint completion, before new opcode families

First pin the exact integration postconjunction in the coverage component.
It is MCOPY lines 67-96, plus ld_frame_data V U ..., parameter envelope from
MLOAD lines 139-143, gas equality, exact non-current-account storage/transient
agreement, and unchanged saved/configured control fields where appropriate.
Its inputs are the corresponding preconjunction, the family's *proved* paired
step and precise footprint, plus that family's proved owned/provenance successor.
Do not assume post-byte relation for a memory writer or post-shared for a store.
A footprint completion theorem is transport only, not a backward execution
producer. It must not duplicate the accepted certificate statements.

The missing concrete account observation boundary is:
```
ld_shared_state tn un s t ==>
!a. (lookup_account a s.vs_accounts).balance =
      (lookup_account a t.vs_accounts).balance /\
    (lookup_account a s.vs_accounts).code =
      (lookup_account a t.vs_accounts).code /\
    account_empty (lookup_account a s.vs_accounts) =
      account_empty (lookup_account a t.vs_accounts)
```
Reuse existing ld_shared_state_nonstorage; check whether a direct corollary of
the sibling account-field boundary avoids a near-duplicate before adding it.

### B. One reusable padded-read boundary (SHA3 and LOG)

```
(!j. j<n ==> R (a+j) (b+j)) /\
DISJOINT X {q | a<=q /\ q<a+n} /\
ld_byte_rel R X Y (\q. read_memory q 1 s) (\q. read_memory q 1 t)
==>
TAKE n (DROP a s.vs_memory ++ REPLICATE n 0w) =
TAKE n (DROP b t.vs_memory ++ REPLICATE n 0w)
```
Check existing lowerDloadCopyReadback and sibling padded-read lemmas before
creating this signature; generalized existing readback is preferable.
Then reachable SHA3/LOG consumers use the exact MCOPY preconjunction (without
MCOPY opcode/shape premises), set opcode/operand shape appropriately, derive
clean source slice from taint_ok and transport address range using access_ok.
Their output is the common postconjunction from A with exact update/log footprint.
No clean-source-memory assumption may be added to the recursive invariant.

### C. One external payload overwrite family

Replace MCOPY opcode/shape lines 36-37 by membership in
[CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY], with its successful-step
shape derived from target OK. Keep all remaining geometric/data premises,
add opaque_use_ok fn and V-to-U observable support bridge if needed, and produce
MCOPY lines 66-98 plus A's companions/envelope. Payload equality is derived
inside the theorem from shared state (not assumed). Out-of-bounds return-data
branch is discharged from target OK; abort observations remain external/terminal.
Generalize the existing clean-copy taint lemma's opcode set in a new general
boundary without changing its accepted statement; do not duplicate its proof
once per copy opcode. Source witness must be the actual write_memory_with_expansion.

### D. Fixed-memory immutable integration

Do not change the old MLOAD/MSTORE theorem statements. A general fixed-read
backward core can replace opcode-specific *implementation duplication*, covering
[MLOAD; ILOAD] with 32-byte read and mem_word_taint result; the accepted MLOAD
consumer stays unchanged. For ILOAD's reachable consumer use MLOAD pre/post
clauses with opcode replaced, derive scalar address/low range internally and
add A's companions. ISTORE's consumer uses MSTORE clauses with opcode replaced,
BUT shared state and imm mask must be updated by existing immutable bookkeeping
boundary at the same concrete istore successor, and footprints allow both
vs_memory and vs_immutables changes. Its conclusion must include byte relation
and shared state simultaneously, not assume either of them.

### E. Residual nonmemory integration

Uniform common-update completion A serves SIGNEXTEND/BYTE/OFFSET, environment
and account reads, masked storage reads and existing scalar certificates; it
must allow masked unequal results for SLOAD/TLOAD. Reachable scalar/clean operand
proofs derive from source annotation + ptr_use_ok + taint_ok + opaque_use_ok,
not premises added to coverage. SSTORE/TSTORE, BUMP and GAS use separate precise
footprints; NOP/guards use their actual annotation update even for metadata.

## 5. Dependency order and decision requested

1. Coverage owns the authoritative complete pre/post conjunction and U/V support
   bridge; settle that interface before local integration. Current PLAN describes
   it, but no complete SML abbreviation/consumer exists. This is an ancestor
   interface issue, not another easy local family.
2. Footprint completion A and nonmemory integration E; reuse existing family
   boundaries and checked certificates. Do not copy old certificates wholesale.
3. Padded-read B and destination-copy C; immutable byte/map integration D.
4. Assign DALLOCA/INITIAL_FMP/BUMP explicitly to allocation versus local group;
   keep calls/control/external/terminal responsibilities unchanged.
5. Only then finite opcode dispatch assembly, followed by the single recursive
   reachability proof. Audit prose cannot lower its risk to mechanical.

Sanity build during audit: lowerDloadStorageReadTheory, lowerDloadExplicitBaseTheory,
lowerDloadStorageWriteTheory, lowerDloadImmutableWriteTheory all pass. No SML
source was edited during this diagnostic. Main frozen theorem remains open.
