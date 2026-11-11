(* Equal-layout stores retain borrowed local bytes at their correctness endpoint. *)
Theory tuplePlaceBorrowStore
Ancestors
  tuplePlaceValueFrame tuplePlaceMemoryFrame
  placeStore placeStoreStorage placeStoreSlots placeMemoryStateRebuild placeStoreMemory placeMemoryStoreEffect
  vyperTypeArgFits exprSimProps valueEncodingProps vyperTyping
  stmtSimDefs exprSimHypsDefs loweringPosts venomState stmtLowering exprLowering
  compileEnv vyperInterpreter vyperState vyperValue vyperTypeSystem
  fragGasPath fragGasMode arithmetic exprLoweringProps stmtSimStoreCopy
  typedMemoryCopy

Theorem tuple_place_equal_storage_run_memory:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty dty (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) dty dty /\
    evaluate_type (get_tenv cx) dty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx dty v op s /\ cenv.ce_target CapMcopy /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (~is_word_type dty ==> !sw. eval_operand op s = SOME sw ==>
       w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_memory = s.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  Cases_on `is_word_type dty` >- suspend "word" >>
  drule_all place_store_storage_compile >> simp[] >>
  strip_tac >> suspend "equal"
QED

Resume tuple_place_equal_storage_run_memory[word]:
  rename1 `evaluate_type _ dty = SOME stv` >>
  drule_all place_store_storage_compile >> simp[] >> strip_tac >>
  `eval_operand op s = SOME (typed_val_to_w256 stv v)` by fs[expr_val_rel_def] >>
  drule_all place_store_emit_slot_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w (w2n root+delta)) writes
      (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
       (n2w (w2n root+delta+i)) (typed_val_to_w256 stv v) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. typed_val_to_w256 stv v`]
       (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> rpt strip_tac >> drule_all place_store_word_live_copy >>
     disch_then (qspecl_then [`get_storage cx ee tr`, `root+n2w delta`, `b`] mp_tac) >>
     simp[AC ADD_ASSOC ADD_COMM]) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func s 0 (OK t)` >>
  `t.vs_memory = s.vs_memory` by
    (unabbrev_all_tac >> Cases_on `tr` >> simp[tstore_def, sstore_def]) >>
  qexists_tac `t` >> simp[] >> reverse conj_tac
  >- (unabbrev_all_tac >> Cases_on `tr` >> simp[tstore_def, sstore_def, lookup_var_def]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >> simp[] >> unabbrev_all_tac >>
  simp[stmt_state_rel_inst_idx, GSYM wordsTheory.word_add_n2w,
       wordsTheory.n2w_w2n, wordsTheory.WORD_ADD_COMM]
QED

Resume tuple_place_equal_storage_run_memory[equal]:
  rename1 `evaluate_type _ dty = SOME stv` >>
  fs[expr_val_rel_def] >>
  `val_in_memory stv v (w2n w) s.vs_memory` by metis_tac[] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `w2n w + type_memory_size stv < dimword (:256)` by
    (first_x_assum (qspec_then `w` mp_tac) >> simp[] >> strip_tac >> fs[] >> decide_tac) >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  qspecl_then [`cenv`, `op`, `dst_op`, `dty`, `tr`, `sa`, `sb`, `stv`, `func`, `s`,
      `w`, `w2n root + delta`, `ctx`, `cx`, `env`, `ee`, `mid`, `var_name`, `keys`,
      `root`, `tv`, `path`, `delta`, `writes`, `v`] mp_tac
    place_store_slots_suffix_run >>
  (impl_tac >- (fs[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Finalise tuple_place_equal_storage_run_memory

(* The equal-layout companion of tuple_place_value_run_frame. Both byte
   clauses refer to the same t as the source write correctness result. *)
Theorem tuple_place_equal_value_run_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty stv v sa sb.
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty dty (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) dty dty /\
    evaluate_type (get_tenv cx) dty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx dty v op s /\ cenv.ce_target CapMcopy /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type dty ==> !sw. eval_operand op s = SOME sw ==>
       w2n sw + type_memory_size stv <= s.vs_alloca_next /\
       !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
         w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==> !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!aid b len a n dtv. aid < sa.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= a /\ a+n <= b+len /\
        evaluate_type (get_tenv cx) dty = SOME dtv /\
        (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory) /\
      (!name b len a n dtv. local_region cenv ee.scopes s name b len /\
        b <= a /\ a+n <= b+len /\
        evaluate_type (get_tenv cx) dty = SOME dtv /\
        (loc = LocMemory ==> a+n <= w2n w \/ w2n w+type_memory_size dtv <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `loc = LocMemory`
  >- suspend "memory" >>
  Q.SUBGOAL_THEN `loc = LocStorage \/ loc = LocTransient` assume_tac
  >- (Cases_on `p` >> gvs[place_ptr_rel_def] >>
      rename1 `slot_loc tr` >> Cases_on `tr` >> gvs[slot_loc_def]) >>
  `~is_word_type dty ==> !sw. eval_operand op s = SOME sw ==>
       w2n sw + type_memory_size stv <= s.vs_alloca_next` by metis_tac[] >>
  drule_all tuple_place_equal_storage_run_memory >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Resume tuple_place_equal_value_run_frame[memory]:
  Cases_on `is_word_type dty`
  >- suspend "memory_word" >>
  drule_all (SRULE [] (Q.INST [`sty` |-> `dty`]
    (SPEC_ALL tuple_place_memory_forward_frame))) >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule memory_place_write_stmt_state >>
     goal_assum (drule_at (Pat `val_in_memory _ _ _ t.vs_memory`)) >>
     qexistsl_tac [`dty`, `ee`, `env`, `p`, `r`, `s`, `sa`] >>
     gvs[] >> conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!aid b len a n. _ ==> mem_bytes_at _ _ _ = _` irule >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!name b len a n. local_region _ _ _ _ _ _ /\ _ ==> _` irule >>
  metis_tac[]
QED

Resume tuple_place_equal_value_run_frame[memory_word]:
  gvs[] >>
  `emit_void MSTORE [dst_op; op] sa = ((),sb)` by
    gvs[compile_assign_value_def] >>
  `eval_operand op s = SOME (typed_val_to_w256 stv v)` by fs[expr_val_rel_def] >>
  qabbrev_tac `u = mstore (w2n w) (typed_val_to_w256 stv v) s` >>
  `stmt_state_rel ctx func cenv cx ff u` by
    (Cases_on `p`
     >- (gvs[place_ptr_rel_def, slot_loc_def] >> Cases_on `b` >> gvs[])
     >- (rename1 `MemoryPlace id path` >>
         unabbrev_all_tac >> irule place_store_word_memory_state >>
         qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
         qpat_assum `place_ptr_rel _ _ _ _ _ _ _` (irule_at Any) >>
         qpat_assum `evaluate_type _ dty = _` (irule_at Any) >> simp[]) >>
     gvs[place_ptr_rel_def, slot_loc_def]) >>
  `gas_marked_path F ctx func s 0 (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
   (!x. lookup_var x u = lookup_var x s) /\
   u.vs_allocas = s.vs_allocas /\ ~u.vs_halted /\
   u.vs_current_bb = sb.cs_current_bb /\
   SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (irule place_store_emit_run >> simp[Abbr `u`] >>
     qexistsl_tac [`dst_op`, `LocMemory`, `op`, `sa`, `w`,
                    `typed_val_to_w256 stv v`] >> simp[]) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def] >> conj_tac >>
  rpt strip_tac >> gvs[] >> simp[Abbr `u`] >>
  irule mstore_mem_bytes_at_disjoint >>
  drule_all abiValueEncodingTheory.abi_word_type_size >> simp[]
QED
Finalise tuple_place_equal_value_run_frame
