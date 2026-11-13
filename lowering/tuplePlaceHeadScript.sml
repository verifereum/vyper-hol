(* A head certificate protects outstanding aggregates, not consumed word slots.
   Ownership, operand values, and memory representation are separate fields. *)
Theory tuplePlaceHead
Ancestors
  tuplePlacePrefix tuplePlaceBorrowStore abiEncoderSourceTransport
  tupleMemoryFrame exprSimCopy valueEncodingProofs valueEncodingProps vyperTypeDefaults list
Libs monadsyntax

Definition tuple_place_head_def:
  tuple_place_head ctx func cenv cx es lo cs tys ltys ltvs vs elems
      (w:256 word) i s <=>
    stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    LENGTH elems = LENGTH ltys /\ LENGTH ltvs = LENGTH ltys /\
    i <= LENGTH ltys /\ EVERY (\op. ?x. op = Var x) elems /\
    (!x. MEM (Var x) elems ==> not_fresh_at cs x) /\
    local_ptrs_reserved cenv cs /\ values_have_types ltvs vs /\ tuple_val_wf vs ltvs /\
    tuple_place_snapshot cenv cx es lo cs.cs_next_id tys ltys ltvs w s /\
    (!j. i <= j /\ j < LENGTH ltys ==> ?v.
      eval_operand (EL j elems) s = SOME v /\
      if is_word_type (EL j ltys) then
        v = typed_val_to_w256 (EL j ltvs) (EL j vs)
      else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) /\
    (!j. i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
      val_in_memory (EL j ltvs) (EL j vs)
        (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) s.vs_memory)
End

Theorem tuple_place_head_intro:
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = cs.cs_current_bb /\ s.vs_inst_idx = LENGTH cs.cs_current_insts /\
  LENGTH elems = LENGTH ltys /\ LENGTH ltvs = LENGTH ltys /\
  EVERY (\op. ?x. op = Var x) elems /\
  (!x. MEM (Var x) elems ==> not_fresh_at cs x) /\
  local_ptrs_reserved cenv cs /\ values_have_types ltvs vs /\ tuple_val_wf vs ltvs /\
  tuple_place_snapshot cenv cx es lo cs.cs_next_id tys ltys ltvs w s /\
  tuple_in_memory vs ltvs (w2n w) s.vs_memory /\
  (!j. j < LENGTH ltys ==> ?v. eval_operand (EL j elems) s = SOME v /\
    if is_word_type (EL j ltys) then v = typed_val_to_w256 (EL j ltvs) (EL j vs)
    else w2n v = w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) ==>
  tuple_place_head ctx func cenv cx es lo cs tys ltys ltvs vs elems w 0 s
Proof
  strip_tac >> simp[tuple_place_head_def] >> rpt strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule abi_encoder_tuple_memory >> simp[] >>
  gvs[values_have_types_LIST_REL, LIST_REL_EL_EQN]
QED

Theorem tuple_place_assignment_prefix_head:
  !ctx func cenv cx es es1 tys ltys ltvs vs sa su sl ss op staged elems sv s0 e.
    expr_type e = TupleT tys /\ lowered_value_type cenv e = TupleT ltys /\
    value_has_type (TupleTV ltvs) (ArrayV (TupleV vs)) /\
    evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
    LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) ltys ltvs /\
    expr_post ctx func cenv cx e es sa su s0 es1 (ArrayV (TupleV vs)) op sv /\
    (!x. op = Var x ==> not_fresh_at su x) /\ sa.cs_next_id <= su.cs_next_id /\
    (if is_memory_view e /\ EXISTS (\t. ~is_word_type t) ltys /\
        0 < type_memory_size_list ltvs then
       do buf <- compile_alloc_buffer (type_memory_bytes cenv (TupleT ltys));
          emit_void MCOPY [buf.buf_operand; op;
            Lit (n2w (type_memory_bytes cenv (TupleT ltys)))];
          comp_return buf.buf_operand od
     else comp_return op) su = (staged,sl) /\
    compile_tuple_load_all cenv staged ltys 0 sl = (elems,ss) /\
    cs_extends sl ss /\ fn_has_code su sl func /\ fn_has_code sl ss func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv su /\
    ~sv.vs_halted /\ sv.vs_current_bb = su.cs_current_bb /\
    sv.vs_inst_idx = LENGTH su.cs_current_insts ==>
    ?t w. tuple_place_head ctx func cenv cx es1 sa.cs_next_id ss
      tys ltys ltvs vs elems w 0 t /\
      (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x sv) /\
      (!aid entry. FLOOKUP sv.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      gas_marked_path F ctx func sv 0 (OK t)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_place_assignment_prefix_path >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >> irule tuple_place_head_intro >>
  simp[] >> gvs[LIST_REL_EL_EQN]
QED

(* Consumer of the local-frame conjunct of tuple_place_equal_value_run_frame.
   The frame is at the SAME endpoint t as correctness and gas.  scopes-domain
   equality, not unchanged source entries, reconstructs the live region. *)
Theorem tuple_place_head_borrow_frame:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  MAP FDOM ee.scopes = MAP FDOM ff.scopes /\
  local_region cenv ee.scopes s name b len /\
  b <= a /\ a + type_memory_size tv <= b + len /\
  evaluate_type (get_tenv cx) (EL i tys) = SOME dtv /\ ltys = tys /\
  (loc = LocMemory ==> a + type_memory_size tv <= w2n w \/
    w2n w + type_memory_size dtv <= a) /\
  (!name b len a n dtv. local_region cenv ee.scopes s name b len /\
    b <= a /\ a+n <= b+len /\
    evaluate_type (get_tenv cx) (EL i ltys) = SOME dtv /\
    (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
    mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
  val_in_memory tv v a s.vs_memory /\ val_wf tv v ==>
  val_in_memory tv v a t.vs_memory /\ local_region cenv ff.scopes t name b len
Proof
  strip_tac >> conj_tac
  >- (irule val_in_memory_mem_agree >> simp[] >>
      qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
      sym_tac >> first_x_assum irule >> metis_tac[]) >>
  `local_region cenv ee.scopes t name b len` by
    (drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  drule local_region_scopes_domain >> metis_tac[]
QED

(* PREMISE LEDGER -- interface probe, NOT a certification of store readiness.

   Initialization:
   tuple_place_assignment_prefix_head has EXACTLY the antecedent of
   tuple_place_assignment_prefix_path.  LIST_REL supplies the length equality;
   abi_encoder_tuple_memory projects outstanding element representations.
   The head records i and original TAKE i offsets, not a shrinking tuple.
   All future elements retain operand values; only aggregate elements retain
   bytes.  The snapshot certificate alone never implies val_in_memory.

   Pointer step (target_post):
   - old loaded operand values: tuple_place_target_operand; head's EVERY Var
     excludes labels, and freshness is in the head.  Transport freshness to
     the pointer endpoint needs compiler monotonicity for compile_get_target_ptr.
   - destination operand/typing and state relation: target_post_def.
   - old allocation lookup: target_post_def.  Its byte frame additionally needs
     aid < pointer-start.cs_next_id and nonlocal separation of the whole owner;
     owned snapshot supplies these once the index bound is transported.
   - borrowed bytes: tuple_place_pure_target_scopes and
     tuple_place_pure_target_borrow_bytes.  Reconstruct local regions using
     copy_buffer_local_region_frame and local_region_scopes_domain, not entry
     equality.  local_path_at is static in cenv,cx.
   - static call safety for reachable-target geometry:
     tuple_place_rhs_empty_call_safe / tuple_place_rhs_target_call_safe.

   Store step (tuple_place_value_run_frame, or equal_value_run_frame):
   - head source operand freshness: head plus compiler monotonicity; pointer
     destination freshness: target_post.  Positive type_slot_size, paired
     evaluation, widening and lengths: tuple_place_type_facts (root typing).
   - value_has_type: head values_have_types projected at the same index.
     expr_val_rel: loaded word equation OR outstanding aggregate memory;
     still requires element evaluation and val_wf projection, not ownership.
   - source end <= vs_alloca_next: REMAINING derived bridge from snapshot
     containment + alloca_inv (owned) or local_ptrs_rel (borrowed), and
     per-element prefix-sum bounds.  This is not an explicit head field.
   - separation from ALL allocations with store-start.cs_next_id <= aid:
     REMAINING derived bridge.  Owned case should use distinct allocation ids
     and alloca_inv disjointness.  Borrowed case needs ALLOCA site/output
     provenance and not_local_ptr to use local_ptrs_rel_alloca_disjoint;
     local_region by itself does not supply those site facts.
     expr_val_at_alloca_disjoint is related, but asks for the instruction and
     its output/nonlocal witnesses and refers to val_footprint, not simply
     the tuple's full capacity.  Do not silently add this separation to head.
   - memory destination + type_memory_size dtv + 64 < dimword: REMAINING
     margin bridge. tuple_place_memory_end_bound proves only end < dimword;
     the frozen root's size+64 bound alone does not add the destination base.
   - type_alloc_ok dty for widened storage: tuple_place_rhs_element_alloc_ok
     from original expr_body_pre; keep this static fact across the fold.
   - widened memory separation: owned snapshot nonlocal separation plus
     actual destination containment, NOT arbitrary place_ptr_rel separation.
     Borrowed snapshot has ltys=tys, hence EL i ltys=EL i tys; the widening
     side condition disappears in tuple_place_equal_value_run_frame.
   - borrowed destination separation: tuple_place_borrow_destination_apart
     using ACTUAL evaluated typed target, call safety and full local extent.
     tuple_place_head_borrow_frame checks consumption of the resulting local
     slice frame and region reconstruction at the runner's endpoint.
   - source invariant after write: tuple_place_write_inv; retain actual
     runtime_place_typed/storage_place_region and source write equation.
     Scope-domain preservation and compiler monotonicity must be threaded.

   Outcome: initialization and frame consumption are checked, but a uniform
   store fold is NOT yet authorized by this candidate invariant.  The three
   REMAINING numeric/provenance bridges above require explicit proofs (or
   a justified tighter runner interface) before claiming readiness.  No new
   hypotheses have been added to the frozen root or the prefix theorem.
*)

(* CURRENT RUNNER APPLICABILITY AUDIT (C1.3.4.3.8).
   This supersedes the runner-selection and REMAINING items in the older
   ledger above. It is a diagnostic, not a new theorem or head hypothesis.

   Notation used ONLY in this comment:
     H = tuple_place_head ctx func cenv cx es lo sp tys ltys ltvs vs elems w0 i s0
     R = assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
         evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
         evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs)
     P = target_post ctx func cenv cx es sp sa s0 ee (PlaceR p)
           (Type (EL i tys)) (dst,SOME loc,SOME (EL i tys)) s
     E = eval_base_place cx bt es = (INL (PlaceR p),ee)
     S = supported_target_pure tops bt /\ well_typed_target env bt (EL i tys) /\
         target_indices_pre cenv cx env bt /\ call_evaluation_safe cx []
     C = compile_get_target_ptr compile_expr cenv bt sp =
           ((dst,SOME loc,SOME (EL i tys)),sa)
     K = cs_extends sp sa
     sty = EL i ltys; dty = EL i tys; stv = EL i ltvs; dtv = EL i tvs
     v = EL i vs; op = EL i elems
     N = type_memory_size_list ltvs
     A j = w2n w0 + SUM (MAP type_memory_size (TAKE j ltvs))
   The root also supplies its two size+64 inequalities at nonword indices,
   acyclic metadata, conditional CapMcopy, and the ORIGINAL expr_body_pre.
   All implications below require i < LENGTH tys. Names H/R/P/E/S/C/K are
   textual abbreviations, not predicates added to the HOL development.

   COMMON PREMISES, WITH PRODUCERS
   - Index and evaluation: tuple_place_type_facts R gives lengths, both EL
     evaluations, assignable dty, widening sty->dty and positive destination
     slot count. arg_type_fits_tuple_layouts additionally gives indexwise
     arg_type_fits. aggregateEvaluatedLayout.arg_type_fits_word_type gives
     word(sty) <=> word(dty). For a word destination type_widens_to_word gives
     sty=dty, hence stv=dtv by the paired evaluations.
   - value_has_type stv v: H.values_have_types via values_have_types_LIST_REL
     and LIST_REL_EL_EQN. Destination value typing follows from
     type_widens_to_value_has_type when needed. val_wf comes from the EL
     projection of H.tuple_val_wf; it is distinct from source value typing.
   - expr_val_rel cx sty v op s: H supplies eval at s0 and aggregate bytes.
     tuple_place_target_operand transports eval under P (H.EVERY Var excludes
     Label). Pending aggregate bytes must be transported by the OWNED or
     BORROWED pointer frame below; expr_val_rel_def then reconstructs the
     relation at s. No ownership assertion is used to produce source values.
   - Destination eval, place_ptr_rel, destination freshness, stmt_state_rel:
     P by target_post_def, at the same s. LocMemory/Storage/Transient follows
     by place_ptr_rel case analysis; PlaceR excludes HashMapRef stores.
   - Source operand freshness and local_ptrs_reserved: H, K, not_fresh_at_mono
     and local_ptrs_reserved_next_var. C yields K using
     externalEntryShape.compile_get_target_ptr_expr_labels. K also supplies
     next_id monotonicity for the owner age. Subsequent store extension and
     fn_has_code slices must come from actual tuple-store code decomposition.
   - expr_sim_inv at ee: eval_base_place_sim_inv after tuple_place_target_ready,
     or aug_place_base_inv from source inv, target_indices_pre and E. This is
     NOT a conjunct of target_post. Root-type agreement demanded by all store
     runners follows from aug_place_entry_type_agrees at ee (s'=s there).
   - storage_place_region: adapt E to eval_target_place and use
     vyperStoragePlaceProvenance.eval_target_place_region. This does not need
     an allocation-age assertion. Runtime destination typing for write_inv
     uses eval_target_place_runtime_facts under source invariants and S.
   - write_place = (INL (),ff) is the actual successful source branch, not a
     consequence of P. Code equations, fn_has_code, fn_inst_ids_distinct and
     control/halted facts are actual compilation/gas-path inputs; H's control
     at sp is NOT control at sa. The pointer execution must supply the latter.
   - Static call safety: tuple_place_rhs_empty_call_safe from original RHS
     expr_body_pre. S follows at every iteration from root EVERY/LIST_REL;
     it does not require re-establishing RHS expr_body_pre after a write.

   WORD BRANCH
   place_store_word_run needs exactly its emit_void equation, destination
   eval/place/freshness, is_word_type dty, expr_val_rel at dty, source inv,
   acyclic metadata, reserved locals, storage region, root agreement, evaluated
   destination/value typing, state relation, successful write, code and
   control facts. All are listed above; it needs NO CapMcopy, source extent,
   allocation containment, size margin or source operand freshness premise.
   For suffix framing select tuple_place_word_run_frame instead, with
     a=w2n w0, n=N
   and destination separation for the whole snapshot. Its extra premise is
     loc=LocMemory ==> w2n w0+N <= w2n dw \/ w2n dw+type_memory_size dtv <= w2n w0.
   OWNED/BORROWED separation below supplies this even when element i is a word.
   One chosen WHOLE tuple frame protects all outstanding elements; do not
   combine multiple existential word runs for separate element slices.
   If EVERY is_word_type ltys holds, no byte frame is needed after loading.

   OWNED AGGREGATE BRANCH
   Select tuple_place_owned_value_run_frame (NOT tuple_place_value_run_frame).
   Its code equation includes the actual dynamic-array stride pair, dty/sty,
   and src_loc; retain them from compile_tuple_store_all decomposition.
   Apart from common premises, the exact additional requirements are:
   (1) CapMcopy: nonword sty plus the word-equivalence fact yields EXISTS
       nonword ltys, discharging the frozen conditional capability.
   (2) Positive source size and source size+64<D: respectively
       tuple_place_element_source_positive and the frozen ltvs inequality,
       using word equivalence to meet its nonword DESTINATION guard.
   (3) Strict source end<D and old allocation containing that source:
       the original owned witness, P allocation preservation, K age and
       abi_encoder_prefix_sum_bound give aid<sa.next_id, b<=A i and
       A i+size(stv)<=b+len. alloca_inv from P.state_rel bounds b+len by
       s.alloca_next, and alloca_room bounds that frontier strictly by D.
   (4) Strict memory destination end<D: tuple_place_memory_end_bound using
       the actual write, root agreement and P. NO destination-end+64 needed.
   (5) Positive destination size and destination size+64<D: assignability
       with slot_count_of_memory_size (or equal-layout positivity) and the
       frozen tvs inequality. Positive destination slot count is type_facts.
   (6) type_alloc_ok cenv dty on widened non-bytes storage: obtain once via
       tuple_place_rhs_element_alloc_ok at ORIGINAL RHS expr_body_pre and
       carry as a static indexed fact. It is not implied by H alone.
   (7) The conditional widened-memory source/destination separation follows
       from the full owner's nonlocal separation and actual target containment
       tuple_place_memory_coordinates (or memory_place_live_region).
       Restrict this whole-region separation to element i. No separation
       from arbitrary future allocations is a consumer premise any longer.
   Returns one endpoint with correctness, gas, variables, allocations,
   control and universal old-allocation byte slices. For every pending j,
   its slice lies in the SAME old owner; use the same witness, not a new run.

   BORROWED EQUAL-LAYOUT AGGREGATE BRANCH
   H's borrowed alternative supplies ltys=tys, hence sty=dty and ltvs=tvs.
   Memory: select tuple_place_equal_memory_run_frame. Its premises are:
   nonword ty; compile_assign_value at ty/ty, word flag F and actual arr;
   destination eval/place; both freshness facts; evaluated ty/value typing;
   expr_val_rel; 0<size(tv) and size(tv)+64<D; source inv; reserved locals;
   source-containing LOCAL REGION OR OLD ALLOCATION; state_rel; actual write;
   root agreement; code/distinctness; and control/halted facts.
   Containment is A i in [b,b+len] from the borrowed tuple and prefix bound.
   Positivity/margin are the common indexed facts. This runner needs neither
   destination-end+64 nor universal newer-allocation separation, nor an
   unconditional CapMcopy premise. Its local and old-allocation byte frames
   share its correctness endpoint. Destination separation is needed only
   to CONSUME these frames for pending snapshots, not to run the equal copy.
   Storage/transient: select tuple_place_equal_storage_run_memory for
   !et n. dty<>ArrayT et (Dynamic n), otherwise tuple_place_equal_dyn_run_memory.
   Their common premises are loc=Storage or Transient, same-layout code with
   the exact stride pair, destination eval/place, both freshness facts,
   widening dty->dty, evaluated type/value typing, expr_val_rel, CapMcopy,
   inv/acyclic/reserved/storage region, source end<=s.alloca_next for nonwords,
   positive destination slot count, state_rel/write, code/distinctness/control.
   Source frontier is bodyMemoryDefs.body_local_region_frontier plus prefix
   containment. Self-widening is from the paired fit, not a new root premise.
   Their SAME correctness endpoint has total memory identity. No new equal
   storage execution theorem is missing. A small dispatch boundary may combine
   these ALTERNATIVES, but must not use obsolete equal_value_run_frame, which
   still demands the invalid stronger margin and arbitrary-future-id premise.

   EXACT RESIDUAL BRIDGES (proposed implications; NOT proved by this comment)
   B1: H /\ R /\ P /\ E /\ S /\ C /\ K /\ expr_sim_inv cenv cx env es ==>
       source operand equations and all pending aggregate representations
       from H hold at s, and tuple_place_snapshot ... ee ... sa.next_id ... s.
       Use tuple_place_target_allocation for an owner and
       tuple_place_pure_target_borrow_bytes for a borrow; local-region
       equivalence is wb_frame_local_regions with scope-domain equality.
       Prove owner nonlocal separation at ee by the REVERSE region equivalence,
       not merely forward transport of the one borrowed local.
   B2: The antecedent of B1 plus an OWNED alternative (aid,b,len) ==>
       aid<sa.next_id /\ FLOOKUP s.allocas aid=SOME(b,len) /\
       b<=A i /\ A i+size(stv)<=b+len /\ A i+size(stv)<D.
       These are containment/age/arithmetic consequences, not new invariants.
   B3: The antecedent of B1 plus OWNED alternative and the actual destination
       place_ptr_rel at LocMemory ==> b+len<=w2n dw \/
       w2n dw+size(dtv)<=b. Use actual memory target local coordinates.
   B4: The antecedent of B1 plus BORROWED alternative (name,b,len,k) with
       w2n w0=b+k ==> w2n w0+N<=w2n dw \/ w2n dw+size(dtv)<=w2n w0
       for LocMemory. tuple_place_local_path_extent and
       tuple_place_borrow_destination_apart supply the geometry. The latter
       expects eval_base_place cx bt ee=(INL(PlaceR p),ee), not E as written.
       Candidate adapter: supported_target_pure tops bt /\ E ==> ee=es.
       targetPlaceLive.nested_pop_eval_base_pure_state proves this from
       EVERY pure_expr (target_indices bt); a supported-purity-to-semantic-
       purity adapter is still to be checked/proved (scope equality alone
       is not full state equality). Do not silently instantiate ee=es.
   B5: The antecedent of B1 plus branch certificate and the frozen indexed
       size bounds ==> the selected runner's exact arithmetic/containment
       antecedents (enumerated above), including CapMcopy and type_alloc_ok
       only on the branches that demand them. This is not the legacy universal
       readiness contract. Post-store snapshot reconstruction additionally
       needs MAP FDOM ee.scopes=MAP FDOM ff.scopes from the actual write;
       tuple_place_head_borrow_frame already consumes that equality.

   ZERO/ALL-WORD COVERAGE
   At a valid consumer index tuple_place_element_source_positive and the TAKE
   prefix bound imply N>0; ZERO snapshot cannot occur under R. At an aggregate
   index EVERY is_word_type ltys is impossible. Thus OWNED or BORROWED covers
   every aggregate consumer without a zero-storage runner. With all-word
   layout only loaded operand equations matter. No claim of positive layout
   is based merely on gs<>[], and no empty-layout experiment is a root
   counterexample. No new execution primitive is required by this audit;
   B1--B5 and the purity adapter remain proof work, not asserted consequences
   of a passing build of the still unfinished root.
*)
