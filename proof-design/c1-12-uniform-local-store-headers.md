# C1.12.3 — exact uniform local tuple-store interface proposal

## Status and requested decision

**Non-production proposal, not a proved or authorized interface.** No theorem,
logical definition, supplier edit, or frozen root edit is installed by this packet.
The proposed exports are:

* `bodyFullTupleLocalStore.tuple_local_store_uniform_full`;
* `bodyFullTupleLocalSequence.tuple_local_sequence_uniform_full`.

The sequence export has the **entire closed singleton formula as an antecedent**,
not an unexplained predicate and not an import of its proposed implementation.
This deliberately separates singleton execution from composition. Both formulas
below were parsed, typechecked as closed HOL `bool` terms, and created no theorem
in a temporary diagnostic theory. This certifies syntax, types and closure only.
It neither proves the formulas nor establishes that the frozen root can call them.
Implementation must wait for an exact-header ruling and the derivability decisions
listed below. Existing general callback/resource class approvals are not approval
of these complete new headers.

The scope is the successful local-store suffix of
`bodyFullAssignTuple.body_assign_tuple_locals_full`, whose statement is unchanged.
RHS exceptions, source target exceptions, shadow/gas composition and return-frame
assembly at that frozen root remain its owner's work, not consequences of this
suffix proposal. No `DISTINCT ids`, no source/destination disjointness, no no-DALLOCA
condition, no word-only restriction and no additional public premise is proposed.

## Evidence and imports

Prior investigation: `proof-design/c1-12-tuple-store-interface.md` (E0155).
Its six tests establish nil/cons alignment, repeated-name source sequencing and
conditional unread-value/frame/container transport. They do **not** establish the
singleton implementation or root-side staging premises. They are not repeated here.

The exact reproduction context for the two candidate terms is:

```sml
Theory bodyFullTupleHeaderTypecheck
Ancestors
  assignTuplePtrLocalSequence bodyFullMemoryFrames bodyMemoryDefs gasOutcomeFull
  tupleMemoryFrame tupleMemoryLayout vyperLookup vyperTyping
```

This is a known sufficient typechecking context, not a requirement to import the
old fixed-H execution tower into either implementation. Proposed production
imports for the singleton are the declarative/compiler/source types available
through `bodyPtrDefs`, `bodyFullPreds`, `stmtLowering`, `tupleLocalStoreProps`,
`tupleTargetStoreProps`, the concrete word leaf machinery, `bodyFullMemoryCopy`,
and the canonical bytestring execution supplier; add source/ghost frame libraries
as needed after the ruling. Proposed sequence imports are the declarative types,
`tupleLocalStoreProps`, `tupleTargetStoreProps`, `tupleMemoryFrame`,
`tupleMemoryLayout`, `assignTuplePtrUnread`/`assignTuplePtrUnreadBounds` and
`fragGasOriginPtr`; it must not import `bodyFullTupleLocalStore`.
These minimal production import lists have not themselves been built; the full
reproduction context above has. Do not copy foreign supplier proofs into either
new theory. The old fixed-H theorems are comparison material only.

Typechecking evidence:

* Prior build: `TO_assignment_cases-L0059-20261116T201002809072Z_m0013_t001`.
* Closed-boolean check: `TO_assignment_cases-L0059-20261116T201002809072Z_m0014_t004`.
* Session-resume build of the unchanged temporary theory:
  `TO_assignment_cases-L0059-20261116T201002809072Z_m0018_t001`.

## Complete candidate formulas

The following ML quotations are the complete candidate HOL statements. The ML
names are **terms**, not named theorems or definitions. To state the future
singleton theorem, use the body of `singleton_candidate`; to state the sequence
theorem, expand `^singleton_candidate` to that same complete universally quantified
formula. The antiquotation shown here performs exactly that expansion, before HOL
parses the implication; it does not introduce a logical predicate or an assumption
export. All variables, including `DF`, `st0`, `lo`, and the reference invariant
state `es0`, are quantified.

```sml
val singleton_candidate : term = ``
  !DF lo d explicit ctx func PG cenv cx st0 tops env0 es0
   ty g tv v src sw sa sb es es' s G tn.
  compile_tuple_store_all cenv [ty] [g] [Var src] sa = ((),sb) /\
  assign_tuple_targets cx g v es = (INL (),es') /\
  (?id p sz vt entry. g = BaseTarget (NameTarget id) /\
    lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vt /\ (is_word_type vt = is_word_type ty) /\
    (if is_word_type ty then store_lays_out tv entry.type v else
      (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\
      value_has_type entry.type v /\
      type_memory_bytes cenv ty = type_memory_size tv /\
      type_memory_bytes cenv vt = type_memory_size entry.type /\
      0 < type_memory_size entry.type /\
      type_memory_size entry.type + 64 < dimword(:256))) /\
  value_has_type tv v /\ val_wf tv v /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env0 es0 /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\ (is_word_type ty ==> sw = typed_val_to_w256 tv v) /\
  (~is_word_type ty ==> ptr_covers G tn src s (type_memory_size tv)) /\
  ptr_val_ok cx ty v (Var src) G tn s /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    es'.storage_trace = es.storage_trace /\
    (!tail. assign_tuple_targets cx g v (es with gas_obs := tail) =
      (INL (),es' with gas_obs := tail)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    return_buf_frame d cenv sb t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    ((t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem) \/
     ?id dst dsz written. local_region cenv es.scopes s id dst dsz /\
       written <= type_memory_size tv /\ written <= dsz /\
       (!i. ~(dst <= i /\ i < dst+written) ==>
         mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
         (i IN tn'.t_mem <=> i IN tn.t_mem))) /\
    (!c0 e0 sa0 s0. alloca_frame c0 e0 sa0 s0 cenv es s ==>
      alloca_frame c0 e0 sa0 s0 cenv es' t) /\
    (!H. valid_horizon cx st0 H es'.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx es' t /\
      ghost_inv_at (DF H) lo d cenv cx es' G' tn' t)
``;

val sequence_candidate : term = ``
  ^singleton_candidate ==>
  !DF lo d explicit ctx func PG cenv cx st0 tops env0 es0
   gs tys tvs vs ops addr b sz sa sb es es' s G tn.
  compile_tuple_store_all cenv tys gs ops sa = ((),sb) /\
  assign_tuple_target_list cx gs vs es = (INL (),es') /\
  LENGTH gs = LENGTH tys /\ LENGTH tys = LENGTH tvs /\
  LENGTH tvs = LENGTH vs /\ LENGTH ops = LENGTH vs /\
  EVERY (\op. ?x. op = Var x /\ not_fresh_at sa x) ops /\
  local_ptrs_reserved cenv sa /\ values_have_types tvs vs /\ tuple_val_wf vs tvs /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!i. i < LENGTH gs ==>
    ptr_val_ok cx (EL i tys) (EL i vs) (EL i ops) G tn s /\
    ?w. eval_operand (EL i ops) s = SOME w /\
      (if is_word_type (EL i tys) then w = typed_val_to_w256 (EL i tvs) (EL i vs)
       else w2n w = addr + SUM (MAP type_memory_size (TAKE i tvs))) /\
      (!p. ~is_word_type (EL i tys) /\ EL i ops = Var p ==>
        ptr_covers G tn p s (type_memory_size (EL i tvs)))) /\
  (!i. i < LENGTH gs ==>
    ?id p cap vt entry. EL i gs = BaseTarget (NameTarget id) /\
      lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
      cenv.ce_var_type id = SOME vt /\ (is_word_type vt = is_word_type (EL i tys)) /\
      (if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs) else
        (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
        evaluate_type (get_tenv cx) vt = SOME entry.type /\
        value_has_type entry.type (EL i vs) /\
        type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
        type_memory_bytes cenv vt = type_memory_size entry.type /\
        0 < type_memory_size entry.type /\
        type_memory_size entry.type + 64 < dimword(:256))) /\
  (!i. i < LENGTH tys ==> evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)) /\
  b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region cenv es.scopes s name b sz)) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env0 es0 /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    dead_lo_ok H (DF H) lo cenv cx /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    es'.storage_trace = es.storage_trace /\
    (!tail. assign_tuple_target_list cx gs vs (es with gas_obs := tail) =
      (INL (),es' with gas_obs := tail)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    return_buf_frame d cenv sb t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!c0 e0 sa0 s0. alloca_frame c0 e0 sa0 s0 cenv es s ==>
      alloca_frame c0 e0 sa0 s0 cenv es' t) /\
    ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
     (?name. local_region cenv es'.scopes t name b sz)) /\
    (!H. valid_horizon cx st0 H es'.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
      stmt_state_rel H ctx func cenv cx es' t /\
      ghost_inv_at (DF H) lo d cenv cx es' G' tn' t)
``;

val _ = if null (free_vars singleton_candidate) andalso
           null (free_vars sequence_candidate) andalso
           type_of singleton_candidate = Type.bool andalso
           type_of sequence_candidate = Type.bool
        then print "C1.12.3: both closed candidate headers typecheck as bool; no theorem created.\n"
        else raise Fail "candidate header is open or not boolean";
```

## Premise provenance and outstanding root derivability

Status key: **existing** means a source interface/argument is present, not that a
new full theorem has been proved; **open** means a precise derivation is still
required before the root can use the proposal. No open row is an assumed new root
hypothesis. References are paths under `lowering/` on the inspected receiver.

| Candidate premise(s) | Source/provenance | Status and exact obligation |
| --- | --- | --- |
| Singleton compiler equation; sequence compiler equation | `tupleLocalStoreProps.tuple_store_local_step` (74ff); `assignTuplePtrLocalContract.tuple_local_compatible_singleton_code_ptr`; E0155 cons probe | Existing decomposition. Root must extract the actual suffix from its one RHS lowering, not compile an unrelated fragment. |
| Singleton/list successful source equation | `tupleTargetStoreProps`, `tupleLocalStoreProps.assign_tuple_target_list_local_cons` (152ff); E0155 repeated-local test | Existing inversion. Root's conditional target-full premise is discharged with actual RHS eval/read witnesses. Successful suffix is only one branch of full outcome. |
| Lengths, `tys/tvs/vs` typing and evaluated types | `bodyMemAssignTupleLocals` (58-65) uses `tuple_locals_source_types`, `evaluate_type_TupleT_cases`; (80-88) derives runtime component typing | Existing source-type route. Full root must transport it through actual RHS eval/read; that adaptation is open. |
| Local compatibility existential, word `store_lays_out` | Exact comparison interface `assignTuplePtrLocalContract` (83-94), `assignTuplePtrLocalSequence` (26-37); root typechecking/local hypotheses; `tuple_target_local_ptr`, `tuple_target_local_lays_out` used in `bodyMemAssignTupleLocals` (72-85) | Existing candidate shape. Derive ALL nonword size, bytestring compatibility and `< dimword` clauses from root typing/body metadata, not merely word layout. Open at the full suffix. |
| `body_inv`, reference `expr_sim_inv` | Frozen root carries these directly | Direct input. `es0` is the root reference state, not a claim that a post-write `expr_sim_inv` holds. Stable metadata can be extracted once; dynamic relation comes from the all-H bundle. |
| `not_fresh_at`, reserved local/return pointers, saved operands | Compiler freshness/monotonicity and tuple extraction; same premises in `assignTuplePtrLocalSequence` (15-18) | Existing compiler route. Need explicit tuple snapshot/load lowering decomposition and freshness at each actual intermediate compiler state. Open join. |
| Component `ptr_val_ok`, word encoding, nonword `ptr_covers`, exact offset | Old sequence input (19-25); `tupleMemoryLayout.tuple_in_memory_element`, `tuple_element_interval`, `tuple_element_footprint`; staged tuple representation | Open full RHS/staging join. The root must expose ONE tuple allocation/local container and saved operands from its actual path; generic `expr_post` alone is not this entire conjunction. |
| `b <= addr`, tuple-size bound, allocation OR local-region container | Old sequence (38-40); `tupleMemoryFrame.tuple_container_write_position` (66-78) | Open root container derivation. Do not assert fresh/disjoint staging unconditionally: an existing local container is allowed. Must establish this ownership alternative and size bound after RHS/staging. |
| `storage_trace_domain` and all-H `stmt_state_rel`, `dead_lo_ok`, `ghost_inv_at` | Full RHS/unwrap/staging and statement-fragment entry conditions | Open uniform join. `st0` is the source trace origin throughout. Source local writes preserve trace; that equality aligns head/tail valid horizons. It is not valid to change `st0` at each write without proof. |
| `return_buf_frame`, allocation history, actual conditional FMP | Canonical full judgment/entry/staging resources; `stmt_state_rel_allocas_below_fmp` at a witnessed valid H | FMP must be supplied at the actual stepped state, never inferred from `alloca_inv`. `storage_trace_domain` provides the witnessed-H route when needed before path selection. Preservation of return-buffer frame/history by every bytestring/fixed leaf is open. |
| `fn_has_code`, instruction IDs, current block/index, not halted | Root fragment environment and compiler decomposition | Existing entry interface. Need subfragment code containment and actual endpoint alignment, including any generated bytestring blocks. |
| Complete singleton formula (sequence only) | Proposed independent export above | Explicit conditional interface, NOT a root assumption. Root can eliminate it only after actual authorized singleton producer integrates. |

## Postcondition provenance and use

| Candidate postcondition | Intended implementation/source evidence | Consumer use and remaining proof |
| --- | --- | --- |
| `?t G' tn'. ... !H ...` | Concrete MSTORE/MCOPY/bytestring execution, with deterministic ghost updates chosen BEFORE H | Essential full suffix interface. `tuple_local_compatibility_callback_ptr` (80-116) cannot supply it by repeated fixed-H invocation. |
| Same storage trace and all-tail source equation | Local assignment changes containing scope only; `tupleLocalStoreProps.assign_tuple_target_list_local_cons` and E0155 | Allows one trace/domain and exact H to persist through induction and the gas-observation adapter. All-tail statement still requires proof for the singleton and list. |
| Normal compiler endpoint, allocation map/next unchanged | `assignTuplePtrLocalSingleton` word/bytes/fixed code cases; concrete store frame | Continuation/Q and allocation-history transport. Next/history additions are NOT already conclusions of the fixed-H callback. Verify for every concrete opcode. |
| Conditional actual FMP at endpoint | Unchanged allocation map/next plus unchanged FMP memory (where required), or suitable full state relation | Canonical normal-Q resource. Allocation-map equality alone does NOT justify FMP preservation; actual FMP-memory/return-frame reasoning must be checked for each leaf. |
| Return-buffer frame | Reserved return pointers, bounded local writes and state relation local backing/region separation | Needed by root frame return rule and next singleton. Exact derivation from current premises is open, especially bytestring-generated code. Do not silently add a buffer disjointness hypothesis. |
| Saved variable value/provenance/taint equality | Same clauses in `tuple_local_compatible_head_path_ptr` (49-50) and callback (107-108) | Tail operands and local pointer preservation; new arbitrary-lo origin-path proof still needed. |
| Storage/transient/immutable taint equality | `body_full_memory_copy_path` (35); exact concrete MSTORE/bytestring updates | Supports old ghost/frame observations. Bytestring export must be checked for these exact clauses; typechecking does not prove them. |
| Bounded local memory/taint write with `written <= size tv` and destination capacity | Callback (110-115), singleton head (36-54) | Key unread-component invariant. Sequence need not return a single bounding region for all writes; it consumes each head bound before recursing. |
| Old allocation frame retained | `assignTuplePtrSequential.tuple_head_alloca_frame_ptr` (60-92); E0155 transport test | Re-establishes root's original allocation frame after list, including repeated target names. Source scope-domain equality needed by this proof is derivable from source assignment, not a hidden callback premise. |
| Allocation/local container retained (sequence) | `tupleMemoryFrame.tuple_container_transport` (134-152), E0155 | Root/tail ownership. Repeated writes change entry values but not scope domains or reserved local pointers. |
| Arbitrary-lo origin path, output state relation and `ghost_inv_at` | New singleton path proof and origin-path composition at common actual endpoint | Root full normal result. Fixed-H `gas_path_ptr D 0` / `ghost_inv H d` is NOT this interface. `explicit` is passed unchanged; no implicit reset to zero. |

## Word/nonword derivation plan, without implementation credit

1. **Word:** invert the singleton compile equation to its actual MSTORE and use
   the source containing-scope update. The deterministic concrete store and taint
   update give a candidate endpoint before H. `bodyFullAssignLocalTail` (57-145)
   is the existing arbitrary-lo ghost/origin-edge example, but its Assign/RHS code
   premise is different: do not instantiate it as if it were singleton tuple code,
   copy its theorem under a new name, or transfer that owner's work. Use canonical
   low-level store leaves and prove this code boundary only after exact approval.
2. **Fixed nonword:** compatibility forces `vt = ty` outside bytestrings. The
   compiler takes the flat copy branch. `body_full_memory_copy_path` (11-40) has
   the desired existential-before-`!D` order and permits overlapping MCOPY.
   Derive source/destination coverage, robust representation, frontier/no-wrap
   bounds from the dynamic relation and `ptr_val_ok`/coverage premises at a
   witnessed H. Finish state/source and arbitrary-lo ghost observations at that
   same endpoint. These derivations, including return frame/history, are open.
3. **Bytestring:** different source/destination capacities are permitted explicitly.
   `assignTuplePtrLocalSingleton` (81-95) and
   `tuple_local_bytes_compatible_head_ptr` show the fixed-H code/extent route;
   canonical `compile_store_bytestring_inst_seq_ptr`,
   `store_bytestring_run_exact` and `compile_store_bytestring_body_mem_ok` are the
   intended execution/memory boundaries. On this inspected branch the inst-seq
   export's visibility is a separate canonical owner intake (C1.31/D0022), not
   work for this lane. Current `bodyFullMemoryStore` (32-33) still asks for
   source/destination disjointness: it does not prove the alias-permitting header
   above. D0016's approved memory companion work belongs to its existing owner;
   consume actual integrated delivery or use canonical exact bytestring leaves,
   never assume the supplier has already changed.

## Why the unread/alias invariant is not an assumed snapshot miracle

The sequence uses the old well-tested invariant shape rather than claiming every
original RHS component remains forever represented. Word values are saved in
variables. For a nonword unread index `i`, its operand points to
`addr + SUM (MAP type_memory_size (TAKE i tvs))`. Its footprint ends no later than
`b+sz`. At a head with slot size `elem`, the bounded-write post has
`written <= elem` and `written <= dsz`. From local pointer relations,
`alloca_inv` and the actual allocation/local container,
`tuple_container_write_position` derives `dst <= addr` or disjointness of the
whole container and destination. Therefore the head's destination interval cannot
reach the unread suffix starting at `addr+elem`. The same exterior condition
protects memory taint, not just bytes. `tuple_sequential_value_frame_ptr` (13-45)
then transports unread `ptr_val_ok`; existing pointer coverage transport must also
be instantiated for the next head. E0155 checks the conditional value/frame/
container part, not every full induction obligation.

Repeated identifiers `[id;id]` use the source entry after the first update. Type,
assignability and scope-domain layout are stable under the update (see
`tupleLocalStoreProps.lookup_scopes_write_local_type` and
`assignTuplePtrLocalContract.tuple_local_compatibility_scope_ptr`). No DISTINCT
restriction is needed. The tuple may itself occupy that local's container; a
write to its beginning may destroy consumed prefix data, but the size/position
argument protects unread suffix data. Overlapping MCOPY is atomic snapshot copy
for its single head; **that alone does not protect later heads**. The container
and unread-interval argument does. Bytestring compatibility must retain
`written <= type_memory_size tv` even when destination capacity differs.

The root-side unresolved question is precise: can its actual RHS evaluation,
unwrap, staging and component extraction produce all saved words, robust nonword
representations/coverage and that one container/size bound *at the same ordinary
state and ghosts before H*? The memory-only root demonstrates the source typing
route, but is not a certificate of this full property. Neither independent S1 and
pointer paths nor a separate fresh buffer witness can be spliced in after the
fact. If the root needs an additional staging/snapshot step, it must be the
already-compiled step and must preserve this same-path ordering. No new Stage
header or frozen root premise is proposed.

## Exact ruling / derivability questions to settle before implementation

1. Approve or amend AS WRITTEN both complete headers above, including reference
   metadata inputs, arbitrary `lo`, witnessed trace/domain, endpoint-before-H,
   return frame/history, conditional actual FMP and bounded write clauses. The
   sequence is conditional on the complete singleton statement, not an authorized
   assumption in the root. New headers require this ruling under TASK.
2. Confirm the root-side SAME-path staged-container and per-component compatibility
   derivation outlined above, or identify the exact existing producer which
   supplies each open matrix row. In particular do not equate matching tuple type
   with robust RHS encoding/coverage, or capacity with actual written extent.
3. Confirm that return-buffer frame, allocation history, allocation-next equality
   and conditional actual FMP follow from these premises for all three concrete
   store branches. If not, revise this proposal before producer work; do not add
   an ad-hoc public guard or use bare `alloca_inv` as FMP evidence.
4. Keep producer ownership separate: C1.12.4 implements singleton only after the
   ruling; C1.12.5 implements callback-parametric sequence without importing it;
   C1.12.2 alone assembles the frozen root. MemoryStore/canonical bytestring
   supplier intake remains its current owners' work. No producer/root proof
   continuity credit is requested by this diagnostic completion.

A negative answer to a derivability question here is a design question, not a
verified counterexample or an external-precondition finding. This packet ends at
the exact-header authorization checkpoint and records the open gaps honestly.
