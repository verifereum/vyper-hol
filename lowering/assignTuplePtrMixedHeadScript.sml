(* Common head interface for the sequential mixed-target store induction.
   The write alternative exposes only its bounding local region; no
   disjointness between destinations is required. *)
Theory assignTuplePtrMixedHead
Ancestors
  assignTuplePtrStoreHead assignTuplePtrFixedSingleton assignTuplePtrNonlocal
  tupleTargetStoreProps tupleLocalStoreRun bodyPtrDefs exprSimProps
  ptrDiscipline venomExecSemantics venomState compileEnv context
  valueEncodingProps exprLoweringProps stmtSimDeclStore

Theorem tuple_target_mixed_head_path_ptr:
  compile_tuple_store_all cenv [ty] [g] [Var src] sa = ((),sb) /\
  assign_tuple_targets cx g v es = (INL (),es') /\
  tuple_target_aligned cenv cx g ty tv /\
  tuple_target_layout es.scopes g ty tv v /\
  value_has_type tv v /\ val_wf tv v /\
  (~is_word_type ty ==> type_memory_size tv + 64 < dimword (:256)) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa src /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  lookup_var src s = SOME sw /\
  (is_word_type ty ==> sw = typed_val_to_w256 tv v) /\
  (~is_word_type ty ==> ptr_covers G tn src s (type_memory_size tv)) /\
  ptr_val_ok cx ty v (Var src) G tn s /\ ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    stmt_state_rel ctx func cenv cx es' t /\ ghost_inv d cenv cx es' G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      op_taint tn' (Var x) = op_taint tn (Var x) /\ FLOOKUP G' x = FLOOKUP G x) /\
    (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==> FLOOKUP t.vs_allocas aid = SOME bs) /\
    ((t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem) \/
     ?id dst sz. local_region cenv es.scopes s id dst sz /\ type_memory_size tv <= sz /\
       (!i. ~(dst <= i /\ i < dst + type_memory_size tv) ==>
         mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
         (i IN tn'.t_mem <=> i IN tn.t_mem))) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `?id. g = BaseTarget (NameTarget id)`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      Cases_on `is_word_type ty`
      >- suspend "word" >> gvs[] >>
      drule_all tuple_target_local_aggregate_head_path_ptr >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
      disj2_tac >> qexistsl_tac [`id`, `w2n dw`, `sz`] >> simp[]) >>
  `!id. g <> BaseTarget (NameTarget id)` by metis_tac[] >>
  `is_word_type ty` by metis_tac[tuple_target_aligned_nonlocal_word] >>
  `eval_operand (Var src) s = SOME (typed_val_to_w256 tv v) /\
   op_taint tn (Var src) = {} /\ (!x. Var src = Var x ==> not_fresh_at sa x)` by
    fs[eval_operand_def, ptr_val_ok_def] >>
  drule_all tuple_target_nonlocal_head_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]
QED

Resume tuple_target_mixed_head_path_ptr[word]:
  `eval_operand (Var src) s = SOME (typed_val_to_w256 tv v) /\
   (!x. Var src = Var x ==> not_fresh_at sa x)` by simp[eval_operand_def] >>
  drule_all tuple_target_local_word_head_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `type_memory_size tv = 32` by
    (fs[tuple_target_aligned_local, tuple_target_layout_local] >>
     metis_tac[typed_word_store]) >>
  `entry.type = tv` by fs[tuple_target_layout_local] >>
  `32 <= sz` by metis_tac[] >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  disj2_tac >> qexistsl_tac [`id`, `w2n dw`, `sz`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Finalise tuple_target_mixed_head_path_ptr
