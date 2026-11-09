(* Single-target paths with a physical source type distinct from the target. *)
Theory tupleWidenedTargetStore
Ancestors
  tupleWidenedLocalStore bodyMemAssignTupleTargetsStore tupleTargetStoreProps
  stmtLowering exprLoweringProps compileEnv venomState placeMemoryCopyEffect
  tupleMemoryFrame exprSimProps valueEncodingProofs localPtrsProps

Theorem tuple_word_source_code[local]:
  is_word_type sty /\ is_word_type dty ==>
  compile_tuple_store_all ce [sty] [g] [op] sa =
  compile_tuple_store_all ce [dty] [g] [op] sa
Proof
  strip_tac >> Cases_on `g` >> simp[compile_tuple_store_all_def] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def, FUN_EQ_THM] >>
  pairarg_tac >> simp[] >>
  rpt (CASE_TAC >> simp[])
QED

Theorem tuple_target_widened_head_path_mem:
  compile_tuple_store_all cenv [sty] [g] [op] sa = ((),sb) /\
  assign_tuple_targets cx g v es = (INL (),es') /\
  tuple_target_aligned cenv cx g dty dtv /\
  tuple_target_layout es.scopes g dty dtv v /\
  (is_word_type sty = is_word_type dty) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type stv v /\ val_wf stv v /\
  value_has_type dtv v /\ val_wf dtv v /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  (if is_word_type sty then eval_operand op s = SOME (typed_val_to_w256 dtv v)
   else ?sw. eval_operand op s = SOME sw /\
     val_in_memory stv v (w2n sw) s.vs_memory /\
     w2n sw + type_memory_size stv < dimword (:256) /\
     w2n sw + type_memory_size stv <= s.vs_alloca_next /\
     type_memory_size dtv + 64 < dimword (:256) /\
     cenv.ce_target CapMcopy /\
     (!id entry p sz dw.
       g = BaseTarget (NameTarget id) /\ lookup_scopes id es.scopes = SOME entry /\
       FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME dw ==>
       w2n dw + type_memory_size dtv < dimword (:256) /\
       (dty <> sty /\ ~is_bytestring_type dty ==>
         w2n sw + type_memory_size stv <= w2n dw \/
         w2n dw + type_memory_size dtv <= w2n sw))) /\
  local_ptrs_reserved cenv sa /\ (!x. op = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ return_buf_frame d cenv sa s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\ stmt_state_rel ctx func cenv cx es' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ return_buf_frame d cenv sb t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    (!n. OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es'.scopes) =
         OPTION_MAP (\e. (e.type,e.assignable)) (lookup_scopes n es.scopes)) /\
    (t.vs_memory = s.vs_memory \/ ?id p sz entry dw.
      g = BaseTarget (NameTarget id) /\ lookup_scopes id es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME dw /\
      (!a len. a + len <= w2n dw \/
        w2n dw + (if is_word_type dty then 32 else type_memory_size dtv) <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory))
Proof
  strip_tac >> Cases_on `is_word_type sty`
  >- (`compile_tuple_store_all cenv [dty] [g] [op] sa = ((),sb)` by
        metis_tac[tuple_word_source_code] >>
      qpat_x_assum `compile_tuple_store_all cenv [sty] _ _ _ = _` kall_tac >>
      drule tuple_target_store_head_path_mem >>
      disch_then irule >> simp[] >> metis_tac[]) >>
  drule_all tuple_target_assignment_scope_frame >> strip_tac >>
  `?id. g = BaseTarget (NameTarget id)` by
    metis_tac[tuple_target_aligned_nonlocal_word] >>
  pop_assum strip_assume_tac >> gvs[] >>
  gvs[tuple_target_aligned_local, tuple_target_layout_local] >>
  drule_all tuple_target_local_assignment >> strip_tac >>
  `?dw. lookup_var p s = SOME dw /\
    w2n dw + type_memory_size entry.type <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `w2n dw + type_memory_size entry.type < dimword (:256) /\
   (dty <> sty /\ ~is_bytestring_type dty ==>
      w2n sw + type_memory_size stv <= w2n dw \/
      w2n dw + type_memory_size entry.type <= w2n sw)` by simp[] >>
  drule tuple_local_widened_memory_path >>
  disch_then (drule_at (Pat `find_containing_scope _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var p s = _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `cenv.ce_var_type id = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP cenv.ce_vars id = _`)) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  fs[typed_copy_effect_def] >> metis_tac[]
QED

(* A destination may be larger than a source member; frame the owned envelope. *)
Theorem tuple_target_widened_source_memory:
  stmt_state_rel ctx func cenv cx es s /\
  tuple_target_layout es.scopes g dty dtv v /\
  (is_word_type dty ==> type_memory_size dtv = 32) /\
  (!id dst dsz. local_region cenv es.scopes s id dst dsz ==>
     regions_disjoint b sz dst dsz) /\
  b <= addr /\ addr + type_memory_size_list tvs <= b + sz /\
  tuple_in_memory vs tvs addr s.vs_memory /\ tuple_val_wf vs tvs /\
  (t.vs_memory = s.vs_memory \/ ?id p dsz entry dw.
    g = BaseTarget (NameTarget id) /\ lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) dsz) /\ lookup_var p s = SOME dw /\
    (!a len. a + len <= w2n dw \/
      w2n dw + (if is_word_type dty then 32 else type_memory_size dtv) <= a ==>
      mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory)) ==>
  tuple_in_memory vs tvs addr t.vs_memory
Proof
  strip_tac >- simp[] >>
  gvs[tuple_target_layout_local] >>
  `type_memory_size entry.type <= dsz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[] >> metis_tac[]) >>
  `regions_disjoint b sz (w2n dw) dsz` by
    (first_x_assum irule >> simp[local_region_def] >> metis_tac[]) >>
  `mem_bytes_at addr (type_memory_size_list tvs) t.vs_memory =
   mem_bytes_at addr (type_memory_size_list tvs) s.vs_memory` by
    (first_x_assum irule >> fs[regions_disjoint_def] >>
     Cases_on `is_word_type dty` >> gvs[] >> decide_tac) >>
  irule (cj 5 val_in_memory_mem_agree_proof) >> metis_tac[]
QED

Theorem tuple_owned_source_region_frame:
  local_ptrs_rel func cenv scopes s /\ local_ptrs_reserved cenv sa /\
  MAP FDOM scopes = MAP FDOM scopes' /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid bs. FLOOKUP s.vs_allocas aid = SOME bs ==>
     FLOOKUP t.vs_allocas aid = SOME bs) /\
  ((?aid. FLOOKUP s.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region cenv scopes s name b sz)) /\
  (!name lb len. local_region cenv scopes s name lb len ==>
     regions_disjoint b sz lb len) ==>
  ((?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz)) \/
   (?name. local_region cenv scopes' t name b sz)) /\
  (!name lb len. local_region cenv scopes' t name lb len ==>
     regions_disjoint b sz lb len)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (irule tuple_container_transport >> goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
  irule local_region_frame >> metis_tac[]
QED
