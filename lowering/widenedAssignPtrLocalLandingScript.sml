(* Existing-local landing is independent of the copy's control-flow cursor. *)
Theory widenedAssignPtrLocalLanding
Ancestors assignBasePtrLocalSemantic assignBasePtrScopePost
  bodyPtrMakeArrayCopyStateFrame typedMemoryCopy bodyPtrDefs
  exprLoweringProps loweringStateRelDefs localPtrsProps compileEnv venomState finite_map
  valueEncoding valueEncodingDefs vyperState ptrDiscipline pred_set

Theorem widened_local_write_state_post:
  !ctx fn cenv cx es s t sa id p sz dst pre sc entry rest v n.
    stmt_state_rel ctx fn cenv cx es s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME dst /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\
    n <= sz /\ n <= type_memory_size entry.type /\
    typed_copy_state_frame sa (w2n dst) n s t /\
    val_wf entry.type v /\ val_in_memory entry.type v (w2n dst) t.vs_memory ==>
    stmt_state_rel ctx fn cenv cx
      (es with scopes := pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = t with <|vs_current_bb := s.vs_current_bb;
    vs_prev_bb := s.vs_prev_bb; vs_inst_idx := s.vs_inst_idx|>` >>
  `typed_copy_state_frame sa (w2n dst) n s u` by
    fs[Abbr `u`, typed_copy_state_frame_def, lookup_var_def] >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_prev_bb = s.vs_prev_bb /\
   val_in_memory entry.type v (w2n dst) u.vs_memory` by simp[Abbr `u`] >>
  drule_all assign_base_local_write_state_post >>
  simp[Abbr `u`, literal_stmt_state_rel_cursor]
QED

(* The source write and both target-side invariants use this one endpoint. *)
Theorem widened_local_write_landing_ptr:
  !ctx fn cenv cx es es' s t sa id p sz dst pre sc entry rest v n
    d G tn Gf tf.
    stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
    write_place cx (MemoryPlace id []) v es = (INL (),es') /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME dst /\ local_ptrs_reserved cenv sa /\
    local_region cenv es.scopes s id (w2n dst) sz /\
    n <= sz /\ n <= type_memory_size entry.type /\
    typed_copy_state_frame sa (w2n dst) n s t /\ val_wf entry.type v /\
    (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
      val_in_memory entry.type v (w2n dst) m) /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    (!i. ~(w2n dst <= i /\ i < w2n dst+n) ==>
      (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
    stmt_state_rel ctx fn cenv cx es' t /\ ghost_inv d cenv cx es' Gf tf t
Proof
  rpt gen_tac >> strip_tac >>
  `es' = es with scopes := pre ++
    (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest` by
    (drule stmtSimAssignStoreTheory.write_place_local >> simp[] >> metis_tac[]) >>
  `val_in_memory entry.type v (w2n dst) t.vs_memory` by
    metis_tac[mem_agree_outside_def] >>
  `local_ptrs_rel fn cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `stor_taint_ok cx tf t` by
    fs[ghost_inv_def, stor_taint_ok_def, typed_copy_state_frame_def,
       venom_state_component_equality] >>
  `!i. ~(w2n dst <= i /\ i < w2n dst+n) ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >> conj_tac >- (
      fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      first_x_assum irule >> decide_tac) >> metis_tac[]) >>
  drule_all assign_base_local_scope_ghost_post >> strip_tac >>
  drule_all widened_local_write_state_post >> simp[]
QED

(* Frame composition allows the write to intersect the original frame,
   provided its newly tainted bytes were already tainted at expression entry. *)
Theorem widened_local_ghost_kept_write_frame:
  !cenv es sa sb G0 tn0 s0 G tn Gf tf writes.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sb x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
    tf.t_mem INTER writes SUBSET tn0.t_mem ==>
    ghost_kept cenv es sa G0 tn0 s0 Gf tf
Proof
  rpt gen_tac >> strip_tac >>
  `!i. i IN tf.t_mem ==> i IN tn.t_mem \/ i IN tn0.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i IN writes` >>
     fs[SUBSET_DEF, IN_INTER] >> metis_tac[]) >>
  fs[ghost_kept_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  metis_tac[]
QED
