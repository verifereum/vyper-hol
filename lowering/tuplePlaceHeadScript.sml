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
