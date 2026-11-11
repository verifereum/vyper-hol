(* Boundary probes for a tuple snapshot across place evaluation. *)
Theory tuplePlaceSnapshot
Ancestors
  loweringPosts valueEncodingProps valueEncodingProofs
  venomExecSemantics venomState compileEnv placeMemoryCopyEffect
  tupleStageProps exprLoweringProps localPtrsProps emitHelper
Libs
  monadsyntax

Theorem tuple_place_target_frame:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s ==>
  wb_frame cenv es es' sa s0 s
Proof
  simp[target_post_def, wb_frame_def] >> metis_tac[]
QED

Theorem tuple_place_target_operand:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!lbl. op <> Label lbl) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def] >>
  simp[target_post_def] >> metis_tac[]
QED

Theorem tuple_place_target_allocation:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!n lb lsz. local_region cenv es.scopes s0 n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  simp[target_post_def] >> metis_tac[]
QED

(* The unchanged-entry clause includes dynamic-array length words. *)
Theorem tuple_place_target_unchanged_local:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  local_region cenv es.scopes s0 n b sz /\
  lookup_scopes n es'.scopes = lookup_scopes n es.scopes ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  simp[target_post_def, locals_kept_def] >> metis_tac[]
QED

(* A typed-copy effect, unlike stmt_state_rel alone, protects a snapshot.
   This applies to dynamic length words and zero-sized types as well. *)
Theorem tuple_place_copy_snapshot:
  typed_copy_effect ctx func sa sb s t d n /\
  val_in_memory tv v b s.vs_memory /\ val_wf tv v /\
  (b + type_memory_size tv <= d \/ d + n <= b) ==>
  val_in_memory tv v b t.vs_memory
Proof
  strip_tac >> irule val_in_memory_mem_agree >> simp[] >>
  qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[] >>
  sym_tac >> irule typed_copy_effect_bytes >> metis_tac[]
QED

(* The tuple envelope includes unused capacity, even for a short dynamic
   child. Bytes/string children alone instead have a live footprint. *)
Theorem tuple_place_dynamic_slack_probe:
  val_footprint (ArrayTV (BaseTV BoolT) (Dynamic 4))
    (ArrayV (DynArrayV [BoolV T])) = 160 /\
  val_footprint (TupleTV [ArrayTV (BaseTV BoolT) (Dynamic 4)])
    (ArrayV (TupleV [ArrayV (DynArrayV [BoolV T])])) = 160 /\
  val_footprint (TupleTV [BaseTV (BytesT (Dynamic 64))])
    (ArrayV (TupleV [BytesV []])) = 96 /\
  val_footprint (BaseTV (BytesT (Dynamic 64))) (BytesV []) = 32
Proof
  EVAL_TAC
QED

Theorem tuple_place_empty_layout_probe:
  type_memory_size (TupleTV [TupleTV []]) = 0 /\
  val_footprint (TupleTV [TupleTV []])
    (ArrayV (TupleV [ArrayV (TupleV [])])) = 0
Proof
  EVAL_TAC
QED

(* Unlike expr_tuple_memory_owned this retains allocation age and nonlocal
   separation, and permits an empty layout without inventing an owner. *)
Theorem tuple_place_expr_owned_snapshot:
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  expr_val_own cenv cx (TupleT tys) sa sb es
    (ArrayV (TupleV vs)) op s /\
  eval_operand op s = SOME w ==>
  type_memory_size_list tvs = 0 \/
  ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
    (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
      b + sz <= lb \/ lb + lsz <= b)
Proof
  strip_tac >>
  qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_own_def, is_word_type_def] >>
  simp[val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
  metis_tac[]
QED

(* A producer test at the exported run interface. No positivity assumption:
   even a zero-byte stage has an allocation id. The gas-path variant in
   tupleAssignPrefix is local, so this is not yet a prefix gas contract. *)
Theorem tuple_place_stage_owned_probe:
  (do buf <- compile_alloc_buffer sz;
      emit_void MCOPY [buf.buf_operand; op; Lit (n2w sz)];
      comp_return buf.buf_operand od) sa = (staged,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= sz /\ sz < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. eval_operand staged t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    stmt_state_rel ctx func cenv cx es t /\
    (!n lb lsz. local_region cenv es.scopes t n lb lsz ==>
      w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
    (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s = r)
Proof
  strip_tac >> drule_all tuple_stage_copy_run >>
  disch_then (qx_choosel_then [`t`, `w`] strip_assume_tac) >>
  drule_all tuple_stage_copy_parts >>
  disch_then (qx_choosel_then [`sx`, `sm`, `p`] strip_assume_tac) >>
  `MEM (mk_inst sx.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (irule loweringHaltTheory.emit_inst_fn_member >>
     qexists `sm` >> simp[]) >>
  `not_local_ptr cenv es.scopes p` by
    (gvs[local_ptrs_reserved_def, not_local_ptr_def] >> metis_tac[]) >>
  qexistsl [`t`, `w`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `alloca_inv t /\ local_ptrs_rel func cenv es.scopes t` by
        gvs[stmt_state_rel_def, state_rel_def] >>
      qpat_x_assum `sx = _` SUBST_ALL_TAC >>
      drule_at (Pat `MEM _ _`) local_ptrs_rel_alloca_disjoint >>
      simp[venomInstTheory.mk_inst_def] >>
      disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
      simp[regions_disjoint_def]) >>
  metis_tac[]
QED

Theorem tuple_place_all_word_probe:
  EVERY is_word_type [BaseT BoolT; BaseT BoolT] /\
  type_memory_size (TupleTV [BaseTV BoolT; BaseTV BoolT]) = 64
Proof
  EVAL_TAC
QED

(* The ordinary post permits a local-backed result as well as an owned
   allocation. Keep that alternative explicit until staging is selected. *)
Theorem tuple_place_expr_snapshot_cases:
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  expr_val_at cenv cx (TupleT tys) sa sb es
    (ArrayV (TupleV vs)) op s /\
  eval_operand op s = SOME w ==>
  type_memory_size_list tvs = 0 \/
  (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
    b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
    (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
      b + sz <= lb \/ lb + lsz <= b)) \/
  (?n b sz. local_region cenv es.scopes s n b sz /\
    b <= w2n w /\ w2n w + type_memory_size_list tvs <= b + sz /\
    local_val_at cenv cx n (w2n w - b) (TupleTV tvs) (ArrayV (TupleV vs)))
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, is_word_type_def, val_footprint_def,
       valueEncodingTheory.type_memory_size_def] >> metis_tac[]
QED
