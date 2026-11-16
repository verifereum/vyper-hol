# C1.12.1: local tuple recursion and tail-resource probe

## Scope and result

Source base: `a9dc90977bdc7d641b58171917e7041ec3f901cc` (L0058).
No production SML, definitions, root headers, or supplier contracts were changed.
The temporary `bodyFullTupleLocalProbeTheory` passed ordinary holbuild with all six tests below:
`TO_assignment_cases-L0058-20261116T190255092638Z_m0025_t001`.
The temporary script is removed after preserving its complete reproducible text here; it is not a proposed producer or imported helper.

**The probe does not qualify the frozen root.** Nil/cons alignment and conditional head-post resource transport are checked. Obtaining that head post under exactly the frozen root assumptions, with a uniform ordinary endpoint and ghosts before H, remains unresolved. No theorem falsehood or omitted public premise is asserted.

## Exact state threaded through recursion

Compiler nil is `((),st)`; source nil is `(INL (),es)`. Compiler cons extracts `sm` after the actual MSTORE or `compile_store_memory` head, and passes `sm` to the remaining compiler. Source cons updates the containing scope to
`pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest`
and passes that state to the remaining source stores. In particular, `[id;id]` performs its second lookup/write in the first write's resulting state, not in the initial state. No DISTINCT assumption is justified or needed for these unfoldings.

The checked head-post transport test retains:

* `ptr_val_ok` of one unread saved operand, provided its saved variable/provenance/taint is unchanged and a bounded local write leaves its unread window untouched;
* the older `alloca_frame`, using preserved reserved pointers and scope domains;
* the tuple's allocation/local-region container at the successor, using allocation-map monotonicity and the same scope-domain/pointer preservation.

The bound for an unread non-word operand is
`addr + elem <= w2n w /\ w2n w + val_footprint tv v <= b + sz`.
Writes have `written <= elem` and `written <= dsz`. Container/local-region aliasing is allowed. The existing `tuple_container_write_position`/`tuple_unread_value_frame_ptr` machinery used inside `tuple_sequential_value_frame_ptr` handles that case; no extra source/destination disjointness is introduced. These bounds are conditional premises of the checked transport test, NOT facts proved here from the root.

## Precise remaining interface gap

`assignTuplePtrLocalContract.tuple_local_compatibility_callback_ptr` (80-116) supplies a singleton store only from a **fixed H**, `ghost_inv H d`, `~ctx_has_dalloca ctx`, returning `?t G' tn'` with `gas_path_ptr D 0 ...`. `assignTuplePtrSequential.tuple_store_sequential_path_ptr` (94-163) consumes that interface and likewise returns its endpoint/ghosts after H. It transports the component representations, old allocation frame and saved variables, but has no uniform joint endpoint theorem. Source evidence: `TO_assignment_cases-L0058-20261116T190255092638Z_m0026_t001` and `..._m0021_t002`.

The needed step is one ordinary compiled successor and ghosts selected BEFORE every valid-horizon observation, for the singleton tuple-store code, followed by the same uniform property for the remaining stores. It must retain arbitrary `lo`/`ghost_inv_at D lo d`, conditional actual FMP (not inferred from alloca_inv), allocation history, and the component/frame/container facts tested here. Merely applying the fixed-H result once per horizon gives `!H. ?t G' tn'. ...`, not the required `?t G' tn'. !H. ...`.

`bodyFullAssignLocalTail.body_assign_local_word_full_store` (57-145) is a relevant existing deterministic MSTORE example: its endpoint and taint are explicitly given, with arbitrary-lo `gas_origin_ptr_edge` and `ghost_inv_at`. However its code premise is `stmt_env ... (Assign ... e)` plus the RHS lowering decomposition; it is not directly the singleton `compile_tuple_store_all` code premise. It is word-only, while the frozen local tuple root permits non-word locals. This observation is design input, not authority to duplicate or change that owner's producer.

Therefore the planned root assembly C1.12.2 is not yet de-risked by this probe. A strategist/owner must choose and authorize a joint sequential-store interface at its natural existing producer boundary (including non-word stores), or another uniform endpoint argument. No new helper header is installed by this report. No old ptr tower is ported.

## Reproduction

Create temporary `lowering/bodyFullTupleLocalProbeScript.sml` with the following contents and run `holbuild(targets=["bodyFullTupleLocalProbeTheory"])`. The final checked build above used exactly this text. Remove that temporary file afterwards. Existing supplier qualification is separately recorded in the component episode.

```sml
(* Temporary interface tests for C1.12.1; not a production supplier. *)
Theory bodyFullTupleLocalProbe
Ancestors
  tupleLocalStoreProps tupleTargetStoreProps assignTuplePtrSequential tupleMemoryFrame
  stmtLowering compileEnv vyperInterpreter vyperState vyperValue vyperLookup
  emitHelper list finite_map

Theorem probe_compiler_nil:
  compile_tuple_store_all ce [] (MAP (BaseTarget o NameTarget) []) [] st = ((),st)
Proof
  simp[compile_tuple_store_all_def,comp_return_def]
QED

Theorem probe_source_nil:
  assign_tuple_target_list cx [] [] es = (INL (),es)
Proof
  simp[Once evaluate_def,return_def]
QED

Theorem probe_compiler_local_cons:
  compile_tuple_store_all ce (ty::tys)
    (MAP (BaseTarget o NameTarget) (id::ids)) (op::ops) sa = ((),sb) /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  ce.ce_var_type id = SOME vt /\ (is_word_type vt = is_word_type ty) ==>
  ?sm. (if is_word_type ty then emit_void MSTORE [Var p;op]
         else compile_store_memory ce op (Var p) vt ty) sa = ((),sm) /\
    compile_tuple_store_all ce tys (MAP (BaseTarget o NameTarget) ids) ops sm = ((),sb)
Proof
  simp[MAP,combinTheory.o_THM] >> (MATCH_ACCEPT_TAC tupleLocalStorePropsTheory.tuple_store_local_step)
QED

Theorem probe_source_local_cons:
  assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) (id::ids))
    (v::vs) es = (INL (),ef) ==>
  ?pre sc entry rest.
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest)
      = (INL (),ef)
Proof
  strip_tac >> drule assign_tuple_target_list_local_cons >> metis_tac[]
QED

(* Repeated identifiers are not removed or assumed distinct.  The tail
   performs its lookup in the state resulting from the preceding write. *)
Theorem probe_repeated_local:
  assign_tuple_target_list cx
    (MAP (BaseTarget o NameTarget) [id;id]) [v;w] es = (INL (),ef) ==>
  ?em. assign_tuple_targets cx (BaseTarget (NameTarget id)) v es = (INL (),em) /\
       assign_tuple_targets cx (BaseTarget (NameTarget id)) w em = (INL (),ef)
Proof
  simp[MAP,combinTheory.o_THM,assign_tuple_target_list_cons,probe_source_nil] >>
  rpt strip_tac >> Cases_on `r` >> gvs[] >>
  Cases_on `r` >> gvs[]
QED

(* Fixed-endpoint head-post test.  No distinct-name or destination/source
   disjointness premise: a bounded write in a local region is enough. *)
Theorem probe_head_post_tail_resources:
  ptr_val_ok cx ty v (Var p) G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  alloca_inv s /\ local_ptrs_rel func ce es.scopes s /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region ce es.scopes s name b sz)) /\
  b <= addr /\
  (~is_word_type ty ==> !w. eval_operand (Var p) s = SOME w ==>
     addr + elem <= w2n w /\ w2n w + val_footprint tv v <= b + sz) /\
  alloca_frame c0 e0 sa0 s0 ce es s /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\ local_ptrs_reserved ce sm /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
  op_taint tn' (Var p) = op_taint tn (Var p) /\
  (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
  ((t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem) \/
   ?id dst dsz written. local_region ce es.scopes s id dst dsz /\
     written <= elem /\ written <= dsz /\
     (!i. ~(dst <= i /\ i < dst+written) ==>
       mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
       (i IN tn'.t_mem <=> i IN tn.t_mem))) ==>
  ptr_val_ok cx ty v (Var p) G' tn' t /\
  alloca_frame c0 e0 sa0 s0 ce em t /\
  ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region ce em.scopes t name b sz))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (irule tuple_sequential_value_frame_ptr >>
      qexistsl_tac [`G`,`addr`,`b`,`ce`,`elem`,`func`,`s`,`es.scopes`,`sz`,`tn`,`tv`] >>
      simp[]) >>
  conj_tac
  >- (irule tuple_head_alloca_frame_ptr >>
      qexistsl_tac [`es`,`s`,`sm`] >> simp[] >> metis_tac[]) >>
  irule tuple_container_transport >>
  qexistsl_tac [`s`,`sm`,`es.scopes`] >> simp[] >> metis_tac[]
QED
```
