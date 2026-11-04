# C1.9: LowerDload relocation specification audit

This is the accessible specification artifact for E0007, revised to make its pending conditions explicit. It is NOT a HOL definition, theorem, axiom, or claim of general preservation. No existing definition or statement is changed. The frozen theorem remains open. Authorization of definitions/proofs is a subsequent strategist decision.

## 1. Typed witnesses and normal relation candidate

All notation below is specification metalanguage; names such as R, V and Own are not installed constants.

```
Id = num # num                         (* frame occurrence, original inst_id *)
S : (Id, num # num # num) fmap          (* source base, target base, size *)
X : (Id, num # num) fmap                (* scratch generated aid, target base *)
H : (string, Id) fmap
HP : Id option list
PG : (num # num) option list
G : (string, num # num) fmap
Q : num set                            (* executed source DLOAD IDs, this owner *)
a : num                                (* active owner *)
W : (num # call_frame # venom_state #
     (string,Id) fmap # Id option list # num set) list
```

A W entry is `(owner, source suspended caller, target suspended caller, saved H, saved HP, saved Q)`. Source suspended callers are existing `call_frame` values; their source function, INVOKE instruction, state, parameter ghosts, provenance ghosts and variable taint are `cf_fn`, `cf_inst`, `cf_state`, `cf_params`, `cf_prov`, `cf_tvar`. Dynamic owner serials are fresh across returns: reused physical addresses do not reuse a serial. `W` projects to the source `stk` of `frame_reachable vs C stk PG G tn fn inst s`. Per-function supply witnesses come from `lower_dload_stage_lookup_supply`, not legacy arithmetic names.

### Erasure to existing source ghosts

```
FDOM H = FDOM G
!v id. FLOOKUP H v = SOME id ==>
  ?b c z. FLOOKUP S id = SOME (b,c,z) /\
          FLOOKUP G v = SOME (b,z)
LENGTH HP = LENGTH PG
LIST_REL
  (\h p. (h = NONE /\ p = NONE) \/
         ?id b c z. h = SOME id /\ p = SOME (b,z) /\
                    FLOOKUP S id = SOME (b,c,z)) HP PG
```

The same clauses relate each saved H/HP to its source caller's `cf_prov`/`cf_params`. Never recover an occurrence solely from source `(b,z)` equality when `z=0`.

### Value and availability clauses

For `h:Id option`, `m:num set`, `x y:bytes32`:

```
V NONE m x y <=> word_agree_except m x y
V (SOME id) m x y <=>
  ?b c z. FLOOKUP S id = SOME (b,c,z) /\
          y = x + n2w c - n2w b
```

For every original `v` in `fn_ir_vars fn`, source and target variable lookup have equal definedness. If both lookups yield `x,y` and `~retpc_var fn v`, require

```
V (FLOOKUP H v) (op_taint tn (Var v)) x y.
```

For `retpc_var fn v`, require definedness agreement only, not value agreement. Target fresh supply names are outside the original variable set. Require equal parameter-vector lengths and, for each `k < LENGTH s.vs_params`,

```
V (if k < LENGTH HP then EL k HP else NONE) {}
  (EL k s.vs_params) (EL k t.vs_params).
```

The fallback NONE matters: entry `PG=[]` need not have the length of arbitrary initial `vs_params`. Entry shape forbids PARAMs. Callee HP does have argument length.

### Ownership, allocation shape and credit

`owners = a :: MAP owner W` is ALL_DISTINCT. S and X entries belong to these owners only. In each active or suspended frame, original source ALLOCA lookup and target original-aid lookup correspond exactly via that owner's S entries:

```
FLOOKUP source.vs_allocas aid = SOME (b,z) <=>
  ?c. FLOOKUP S (owner,aid) = SOME (b,c,z) /\
      FLOOKUP target.vs_allocas aid = SOME (c,z).
```

Every S entry must occur in its owner's source lookup (no extra entries). The remaining target allocation lookups are exactly the size-32 scratch sites in X for that owner. Their aids are the actual supply-generated ALLOCA aids. Q and saved Q sets are exactly the X keys per owner, and contain only touched original DLOAD instruction IDs.

All nonempty source intervals of live occurrences are pairwise disjoint; the corresponding target intervals and all scratch target intervals are pairwise disjoint. Each is disjoint from `[0,lo)`. Zero-size intervals do not imply distinct bases. For S entries require `lo <= b`, `lo <= c`, `b+z < dimword(:256)`, `c+z < dimword(:256)`; each site's end is at most its owner's saved frontier. Scratch intervals have the analogous target bound. These are candidate invariants to prove, not new task hypotheses. DALLOCA need not be covered: `~ctx_has_dalloca C` is already in `o1_src_inv`.

```
k = CARD (FDOM X)
t.vs_alloca_next = s.vs_alloca_next + 32*k
```

On a call, no new X entries are created and both frontiers are inherited. On return, delete only the callee owner's S/X entries and restore suspended caller allocation metadata. A repeat DLOAD reuses X's generated aid; only first touch increments k. `k <= ctx_dload_count C` requires a proof using distinct active function names from `callee_first` and source instruction-ID distinctness. Existing conditional credit lemmas do not prove synchronization, uniqueness or this bound.

### Source-taint-indexed memory

```
(!i. i < lo /\ i NOTIN tn.t_mem ==>
     read_byte i s.vs_memory = read_byte i t.vs_memory) /\
(!id b c z j. FLOOKUP S id = SOME (b,c,z) /\ j < z /\
              b+j NOTIN tn.t_mem ==>
     read_byte (b+j) s.vs_memory = read_byte (c+j) t.vs_memory)
```

Use CURRENT SOURCE global tn, including caller bytes written by callees. No equality is demanded on scratch, free bytes or tainted source bytes. A fresh allocation's entire source interval is tainted by `new_site_bytes` even when the physical region was used by a previous frame. Thus new sites do not need equal uninitialized contents.

### Shared state

Equal fields: call/tx/block contexts, data section, labels, code, initial/current/call-entry FMP, previous hashes, halted, logs, outcomes, pending deletions and internal returndata. Current variable maps, parameters, control fields, allocation fields, return token, accounts, transient storage, immutables and requests are handled separately rather than equated wholesale.

For current account address A, accounts have equal nonstorage fields, and

```
!key. word_agree_except {j | (key,j) IN tn.t_stor}
        (s.vs_accounts A).storage key (t.vs_accounts A).storage key
```

where storage application is parenthesized as `((s.vs_accounts A).storage key)` and similarly on the target. Other accounts' storage is exact. Transient storage has the corresponding current-account clause using `tn.t_trans`, exact at other accounts. Immutables have equal domains and `word_agree_except {j | (key,j) IN tn.t_imm}` at each key. Requests satisfy `LIST_REL (request_agree_except D) s.vs_requests t.vs_requests`. These indices are NOT mapped memory addresses.

Terminal RETURN uses a terminal observation interface, not the ordinary relation: equal return-data lengths and agreement outside `ret_taint tn inst s`, then `taint_within`/`dead_wf` discharge `dead_result_rel`.

`vs_return_pc_token` is deliberately not equated. `setup_callee` sets it to LAST arguments (or 0w); the last argument could be a relocated pointer under the present syntactic assumptions. Its observation must remain opaque, as detailed below.

### Control and suspended callers

Source and target current/previous block labels agree. For source block bb at instruction index j and its block-input supply u, let

```
(pre,u1) = lower_dload_insts_supply u (TAKE j bb.bb_instructions).
```

The target boundary index is `LENGTH pre`. The block-input u is the supply after `lower_dload_blocks_supply` on preceding source blocks, and the corresponding target block comes from `lower_dload_block_supply u bb`. Supplied expansion output positions, not source j or legacy IDs, determine the next PC.

A saved tuple in W relates caller-local fields only: the saved source/target INVOKE PCs by this control boundary; saved lookup availability/value clauses with `cf_tvar`; saved parameter relation; allocation correspondence with owner; equal contexts and frame-local FMP fields. It does NOT require current shared state to equal the saved caller's shared state. Current mapped-memory and shared-state clauses use the active state and global tn. This permits a callee to update suspended caller-owned buffers. On return, `merge_callee_state` retains caller vars/params/control/allocation metadata and imports callee memory and other mutable shared fields; bind_outputs then removes output provenance and clears output variable taint as existing `frame_reachable_ret` specifies.

## 2. RETPC opacity: exact obligations

`RETPC_PARAM` reads `s.vs_return_pc_token` but `out_prov` returns NONE. Thus an ordinary no-provenance=>agreement invariant fails if the last argument is a pointer. This is a relation-interface issue, not a verified counterexample to the frozen theorem.

* Availability is still required for ALL original variables, including retpc_var. A successful RETPC_PARAM defines one output in both runs and needs no matching token value.
* ASSIGN of a retpc-derived Var has an output that is itself retpc_var by `copy_phi_var_assign`. Its input availability transfers success; its new value is exempt. If the output is not retpc_var, its input cannot be retpc_var by that same closure implication, so ordinary V is available.
* PHI is parallel. If the selected operand is retpc-derived, the output is retpc_var by `copy_phi_var_phi`; retain availability and exempt value. If the output is not retpc_var, no selected Var is retpc-derived; use ordinary V and old-H provenance. Successful source resolution implies target resolution from equal previous labels and operand availability. Non-Var selected operands are equal constants/labels. Ghost H uses old-H selection, independently of opacity.
* `opaque_use_ok` allows retpc-derived Vars only in ASSIGN, PHI, or as the unique final operand of RET. It prohibits observing them in SSTORE, JNZ, arithmetic, INVOKE arguments, memory sizes/addresses, etc.
* For a successful RET, eval_operands is SOME nonempty values in both runs by availability. Every FRONT operand excludes retpc-derived Vars by `retpc_use_ok`. Pointer Vars are prohibited in RET by `ptr_use_ok` (RET is neither preserving nor a memory op/comparison); tainted ordinary RET operands are prohibited by `taint_ok`. Thus FRONT operands are scalar untainted and ordinary V with NONE yields equality. The final token may differ and is discarded by FRONT. Both IntRet records have `iret_adopt_fmp=NONE`, since opcode is RET and DRET/RETFMP are excluded. `bind_outputs` therefore gets equal returned values.

All closure-to-live-evaluation implications above remain to be proved as boundary lemmas. In particular, source ghost presence must imply membership in syntactic `fn_pv P fn`; pointer-provenance variables must not silently be treated as scalar at RET. This is a pending ghost-coherence lemma, not an assumed fact.

## 3. Explicit initial witnesses and condition ledger

Initial witnesses: `S=X=H=FEMPTY`, `HP=PG=[]`, `G=FEMPTY`, `tn=entry_taint`, `W=[]`, owner `a=0`, `Q={}`, `k=0`, target input equal to source vs.

Definitionally discharged at equal input state: erasure, empty ownership/disjointness, empty site lookup correspondence, `k=0`, frontier credit equality, all byte equalities, equal parameters using NONE fallback, ordinary word agreement, shared field equality and request reflexivity. `o1_initial_state_ok` explicitly gives `vs_vars=FEMPTY`, `vs_memory=[]`, `vs_allocas=FEMPTY` and nonhalting. `ptr_discipline` supplies `lo <= vs.vs_alloca_next`. No initial parameter emptiness is assumed.

Pending for an actual checked initialization theorem: derive first source/target entry states and supply PC correspondence from context stage lookup; show first-block PHIs absent from shape; transport shared/control clauses through run_context entry updates; obtain source word-frontier bound at the first active raw-reachable state from `mem_inv raw_mem_ok`. The initial state predicate alone does NOT give this bound for an arbitrary state with no active instruction. No new premises may be added to the frozen statement to discharge these conditions.

## 4. Ten pending preservation interfaces

The following are requested lemma contracts, NOT proved facts. R abbreviates all normal clauses above, including the actual source reachability witness; PC means the supply boundary. `s+` denotes state with successor source index, target `t+` the successor expansion boundary, never the same numerical index by assumption.

1. **Supply/PC interface.** Hypotheses: `ir_supply_covers_fn u fn`, `lower_dload_function_supply u fn=(fn',u')`, source block lookup SOME bb and index j. Conclusion: matching target block lookup, block-input supply, and prefix expansion witness defining PC; original PHIs and labels unchanged, generated variables and IDs disjoint from all original names/IDs and each other. Block entry and INVOKE successor specializations must follow from the same interface, not duplicate lemmas.
2. **Operand interface.** Hypotheses: R and `eval_operand op s=SOME x`, op original and not a retpc-derived Var. Conclusion: `?y. eval_operand op t=SOME y /\ V (op witness H) (op_taint tn op) x y`. A separate availability projection covers ALL original operands including opaque ones, in both directions. Untainted scalar operands give equality; pointer addresses need bounded natural-offset conversion only at accesses/comparisons.
3. **Ghost/coherence interface.** Hypotheses: `frame_reachable vs C stk PG G tn fn inst s`, fn_ptr_ok/shape and R. Conclusions: G/PG erasure with chosen occurrences, G domains within fn_pv, and comparison/access witnesses of the same nonempty `(b,z)` identify the same occurrence through disjointness. Zero-size pair equality is never used to deduce occurrence equality. Establish the taint/provenance compatibility needed by arithmetic and return operands.
4. **Ordinary successful step.** Hypotheses: R, active_inst, source `fn_ptr_ok`, shape, access_ok/taint_ok, not forwarding, opcode neither INVOKE nor DLOAD/DLOADBYTES nor terminator, `step_inst n C inst s=OK s1`. Conclusion: matching target successful step and R at successor with source `step_prov PG G inst s1` / `step_taint inst s s1 tn`, appropriate new H/S/X. Fresh original ALLOCA adds exactly one occurrence and marks new source bytes tainted; repeated ALLOCA preserves its occurrence; no memory initialization requirement.
5. **PHI/block entry.** Hypotheses: related preentry states, matching blocks/previous labels and source `enters_block fn s s1`. Conclusion: target `enters_block fn' t t1` and R using `entry_prov fn s G` / `entry_taint_vars fn s tn`. H selection is parallel from OLD H, not an in-place sequential overwrite. Retpc availability/exemption follows Section 2.
6. **DLOAD/DLOADBYTES.** Hypotheses: R, source successful step, appropriate supply expansion, source dload_offset_ok/headroom and code_layout_valid. Conclusion: successful finite target expansion and R at successor. DLOAD introduces X iff first lookup NONE; repeats reuse scratch. Scratch intervals are disjoint from caller sites as well as current sites; its data equals source DLOAD through code-end/no-wrap facts. DLOADBYTES writes mapped destination bytes, not identity addresses by assumption.
7. **Call entry.** Hypotheses: R, decode_invoke SOME(nm,ops), matching function lookup, source eval args and setup_callee SOME cs. Conclusion: target eval args' and setup SOME ct; push `(a,cf,t,H,HP,Q)`; choose fresh owner; callee `H=FEMPTY`, `HP=MAP (op witness Hcaller) ops`, `Q={}`, source callee G=FEMPTY/PG=MAP op_prov; global tn retained except t_var=FEMPTY. Keep ALL suspended S/X entries; inherit frontier difference; establish token opacity rather than equality. Use existing setup failure conditions, not assumed call success on malformed functions.
8. **Internal return.** Hypotheses: R in callee, actual source successful RET/IntRet and output binding to saved caller. Conclusion: target IntRet with equal `iret_values`, both adopt NONE; target bind_outputs succeeds; merge shared callee state, restore caller allocation frontier and local H/HP, delete H/prov/variable-taint at outputs exactly as frame_reachable_ret; pop callee-owned S/X only. FRONT equality is proved as Section 2, not demanded as an input hypothesis. Writes through saved caller pointers remain covered by current tn memory clause.
9. **Terminal observation.** Hypotheses: R, source terminal step/trace and source `taint_within D C vs`, `dead_wf D`. Conclusion: a target terminal result satisfying `dead_result_rel D`; for ordinary Halt use final_taint/ret_taint and saved request snapshot bounds. For source Revert_abort the target must actually Abort Revert_abort; arbitrary Error or ExHalt is insufficient. No ordinary R is required of final RETURN/forwarding memory.
10. **Global credit/freshness.** Hypotheses: R, stage supply witnesses, source successful trace, `callee_first names C.ctx_functions`, source per-state headroom. Conclusions: original alloca lookup NONE synchronization, scratch cardinality increments exactly once per dynamic owner/source DLOAD ID, active owners have distinct function names, `CARD(FDOM X)<=ctx_dload_count C`, and target word-bound from source headroom plus frontier credit. On return rederive credit from restored saved caller metadata and reduced X. Existing local arithmetic equations are reusable but do not prove this global contract.

## 5. Conditional actual-Revert suffix contract

After exempt RETURNDATACOPY, drop all mapped-memory requirements. Candidate weaker suffix mode B retains: corresponding block/PC, definedness of all original variables, equality of nonpointer/non-retpc untainted scalar operands, current shared storage/transient/immutable agreement and request/log/outcome observations, and equal internal returndata LENGTH. Occurrence witnesses may still supply relocated pointer values, but their memory contents are irrelevant. ASSIGNs preserve availability and propagate equality or pointer/opaque class; REVERT only requires both operands defined, not equal memory contents.

Required suffix conclusion (schematic existing run_block argument order must be checked when formalizing):

```
R_before_copy /\ revert_forward_pair bb i j /\
PC_and_supply_block_correspondence /\
run_block fuel C bb s = Abort Revert_abort se
==>
?fuel' te. run_block fuel' C' bb' t = Abort Revert_abort te
```

For entry at the REVERT endpoint, B plus actual source Revert and matching wellformed operand shape/availability suffices. No-normal-return is NOT this contract.

Outstanding proof conditions:

* Use actual source successful COPY on a source Revert trace to establish `src_offset+w2n size <= LENGTH s.vs_returndata`. RDC OOB produces ExHalt, not Revert.
* Prove source/target src-offset and size equality from nonpointer/untainted scalar use restrictions and equal returndata length; then target COPY is successful. Destination may translate beyond its site; no bound is needed by operational RDC after this exemption.
* Actual source suffix success entails each intervening ASSIGN has one defined operand and one output. Transfer availability and typed value class along these assignments. Syntactic `resolve_block_assigns` equality alone is not a runtime-success theorem.
* Show source supply expansion leaves RDC/ASSIGN/REVERT unchanged (only PC prefix changes); transfer active indices and operand availability through the finite suffix.
* REVERT has exactly two defined operands in both runs and thus gives Revert_abort regardless of bytes copied or payload. Carry through internal call propagation without turning this into a normal return.

A syntactic revert_forward_pair can still Error on malformed/undefined ASSIGN or ExHalt on OOB COPY. Thus the contract is conditional on ACTUAL SOURCE Revert, not a claim every forwarding pair reverts. Taint exemptions about_to_revert and in_revert_forward differ: audit source taint restrictions across intervening ASSIGNs rather than treating every suffix byte-read as ordinary memory preservation.

## 6. Adversarial checks and evidence

These are definition-level audits, NOT checked counterexample theorems.

* Two zero-size allocations separated by DLOAD: equal source `(b,0)` may correspond to different target bases. H chooses Id; comparison is blocked by access_ok's `0<sz`, nonempty access cannot fit a zero-size interval. No address-based uniqueness used.
* Callee write through caller parameter: HP carries suspended caller's occurrence; current global tn and memory clauses cover that caller-owned site's changed bytes. Exact execution_frame equality is not suitable.
* Return then fresh call reusing region: stale source/target bytes may differ, but fresh source allocation taints its whole interval via new_site_bytes; until overwritten, observations are constrained by taint_ok and taint_within. Do not assert newly allocated memory is equal or zero.
* Repeated DLOAD in a loop: generated aid unchanged, idempotent exec_alloca, credit increments only on first touch. Need global touched-set/freshness proof, not a count of dynamic loop iterations.
* RETPC_PARAM followed by SSTORE would leak token, but opaque_use_ok prohibits it. A last pointer argument still defeats an overstrong ordinary variable relation, so the candidate includes an opaque exception.

Product evidence IDs:

- TO_ld_sim_v2-20261104T035000Z_m0105_t001: target build, no source changes; main cheat still present.
- TO_ld_sim_v2-20261104T035000Z_m0107_t001: ptr_roots, ptr_use_ok/fn_ptr_ok, provenance and parallel PHIs.
- TO_ld_sim_v2-20261104T035000Z_m0108_t001: frame_reachable stack rules, access_ok, taint_ok.
- TO_ld_sim_v2-20261104T035000Z_m0111_t001: setup_callee and merge_callee_state.
- TO_ld_sim_v2-20261104T035000Z_m0114_t001: exact forwarding syntax.
- TO_ld_sim_v2-20261104T035000Z_m0118_t001: new_site_bytes/mem_taint.
- TO_ld_sim_v2-20261104T035000Z_m0124_t001: RETPC_PARAM/PARAM/RET semantics.
- TO_ld_sim_v2-20261104T035000Z_m0130_t001: retpc_var closure and opaque_use_ok.
- TO_ld_sim_v2-20261104T035000Z_m0132_t001: o1_initial_state_ok.
- TO_ld_sim_v2-20261104T035000Z_m0135_t001: configured supply expansion.

No verified counterexample to the frozen theorem was obtained. All ten general preservation interfaces remain pending. This audit requests only review of specification completion; it does not authorize a broad relocation definition or the main simulation proof.
