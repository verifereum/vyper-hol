Theory assignPlaceBytesStore
Ancestors
  placeStoreStorage stmtSimStoreCopy exprLoweringProps
  words arithmetic list rich_list

(* Capacity-sized copies may wrap on dead source words.  Keep the actual
   word-address semantics here; only live reads are later unwrapped. *)
Theorem assign_place_memory_to_slots_wrapped_path:
  (if tr then compile_memory_to_transient else compile_memory_to_storage)
    src dst n sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
          (mload (w2n (sw + n2w j * 32w)) s) q) s (COUNT_LIST n) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_word_copy_loop src dst n LocMemory
     (if tr then LocTransient else LocStorage) F sa = (result,sb)` by
    (Cases_on `tr` >> gvs[contextTheory.compile_memory_to_transient_def,
                          contextTheory.compile_memory_to_storage_def]) >>
  drule place_store_copy_boundary >> strip_tac >> gvs[] >>
  drule_all place_store_copy_framed_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  drule place_store_copy_frame_observations >> strip_tac >> simp[] >>
  gvs[store_copy_frame_def, store_copy_prefix_def] >>
  Cases_on `tr` >> simp[]
QED

(* A live byte forces the start of its word below the live footprint end;
   it does not force the end of that rounded word below the footprint. *)
Theorem assign_place_live_word_start:
  !st base len i cap b off.
  w2n (lookup_storage (n2w base) st) = len /\
  i < 1 + word_size cap /\ b < 32 /\
  ~dyn_bytes_dead st base cap (base+i) b /\
  off + 32 + len < dimword (:256) ==>
  off + 32*i < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `i = 0` >- simp[] >>
  gvs[loweringStateRelDefsTheory.dyn_bytes_dead_def] >>
  `i <= word_size cap` by decide_tac >>
  `base < base+i /\ base+i <= base + word_size cap` by decide_tac >>
  gvs[] >>
  `32*i = 32*(i-1) + 32` by decide_tac >>
  gvs[] >> decide_tac
QED

Theorem assign_place_wrapped_memory_leaf_run:
  (if tr then compile_memory_to_transient else compile_memory_to_storage)
    src dst n sa = (result,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  n < dimword (:256) /\ local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\ n <= type_slot_size tv /\
  (!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    i < n /\
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mload (w2n (sw + n2w i * 32w)) s) T)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx
        (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all (BETA_RULE (Q.INST
    [`rd` |-> `\i. mload (w2n (sw + n2w i * 32w)) s`]
    (SPEC_ALL place_store_encoded_leaf_state))) >> strip_tac >>
  drule_all assign_place_memory_to_slots_wrapped_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  qpat_x_assum `start = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
    AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM,
    arithmeticTheory.ADD_COMM]
QED

Theorem assign_place_bytes_live_start:
  !tv v off k writes st cap i b.
    (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (case v of BytesV bs => off+32+LENGTH bs < dimword (:256)
             | StringV str => off+32+LENGTH str < dimword (:256) | _ => F) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+i) b ==>
    off+32*i < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, vyperStorageTheory.encode_value_def,
      loweringStateRelDefsTheory.dead_bytes_def, vyperValueTheory.type_slot_size_def] >>
  drule (SRULE [AC ADD_ASSOC ADD_COMM] place_store_dyn_bytes_header) >>
  disch_then (qspecl_then [`k`, `st`] mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  gvs[loweringStateRelDefsTheory.dyn_bytes_dead_def]
QED

Theorem assign_place_bytestring_wrapped_live_copy:
  !tv v (sw:bytes32) s k writes st src_cap dst_cap i b.
    (tv = BaseTV (BytesT (Dynamic dst_cap)) \/ tv = BaseTV (StringT dst_cap)) /\
    well_formed_type_value tv /\ value_has_type tv v /\
    val_in_memory tv v (w2n sw) s.vs_memory /\
    (case v of BytesV bs => LENGTH bs <= src_cap /\
                              w2n sw+32+LENGTH bs < dimword (:256)
             | StringV str => LENGTH str <= src_cap /\
                              w2n sw+32+LENGTH str < dimword (:256) | _ => F) /\
    src_cap <= dst_cap /\ encode_value tv v = SOME writes /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+i) b ==>
    i < 1 + word_size src_cap /\
    EL b (word_to_bytes
      (lookup_storage (n2w (w2n k+i)) (apply_writes k writes st)) T) =
    EL b (word_to_bytes (mload (w2n (sw + n2w i * 32w)) s) T)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `case v of BytesV bs => LENGTH bs <= src_cap
           | StringV str => LENGTH str <= src_cap | _ => F` by
    (Cases_on `v` >> gvs[]) >>
  `case v of BytesV bs => w2n sw+32+LENGTH bs < dimword (:256)
           | StringV str => w2n sw+32+LENGTH str < dimword (:256) | _ => F` by
    (Cases_on `v` >> gvs[]) >>
  `w2n sw+32*i < dimword (:256)` by
    (irule assign_place_bytes_live_start >> metis_tac[]) >>
  drule_all place_store_bytestring_live_copy >> strip_tac >>
  `w2n (sw + n2w i * 32w) = w2n sw + 32*i` by
    (rewrite_tac[wordsTheory.word_mul_n2w] >>
     simp_tac (srw_ss()) [wordsTheory.word_add_def, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_PLUS, arithmeticTheory.MOD_MOD] >>
     `w2n sw + i*32 < dimword (:256)` by metis_tac[MULT_COMM] >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.LESS_MOD, MULT_COMM]) >>
  simp[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem assign_place_wrapped_memory_suffix_run:
  (if n <= 1 then
     ?loaded sm. emit_op MLOAD [src] sa = (loaded,sm) /\
       emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sm = ((),sb)
   else ?r. (if tr then compile_memory_to_transient else compile_memory_to_storage)
       src dst n sa = (r,sb)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  0 < n /\ n < dimword (:256) /\ n <= type_slot_size tv /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  (!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    i < n /\
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mload (w2n (sw + n2w i * 32w)) s) T)) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `n <= 1`
  >- suspend "load"
  >> qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all assign_place_wrapped_memory_leaf_run >> metis_tac[]
QED
Resume assign_place_wrapped_memory_suffix_run[load]:
  `n = 1` by decide_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all place_store_load_emit_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
      (n2w (start+i)) (mload (w2n (sw + n2w i * 32w)) s) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST
       [`rd` |-> `\i. mload (w2n ((sw:bytes32) + n2w i * 32w)) s`]
       (SPEC_ALL place_store_encoded_leaf_state))) >>
     metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  (reverse conj_tac >-
    (qpat_x_assum `store_copy_normalize s t = _` mp_tac >>
     Cases_on `tr` >>
     simp[store_copy_normalize_def, venomStateTheory.tstore_def,
          venomStateTheory.sstore_def, venomStateTheory.venom_state_component_equality])) >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (FOLDL _ _ _)` mp_tac >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  simp[wordsTheory.WORD_MULT_CLAUSES, wordsTheory.WORD_ADD_0]
QED
Finalise assign_place_wrapped_memory_suffix_run

Theorem assign_place_bytes_storage_run:
  (loc = LocStorage \/ loc = LocTransient) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  compile_assign_value cenv dst loc src (is_word_type dty) src_loc dty sty
    NONE (type_memory_bytes cenv dty) sa = ((),sb) /\
  eval_operand dst s = SOME k /\ eval_operand src s = SOME sw /\
  place_ptr_rel cenv cx s (PlaceR p) k (SOME loc) (Type dty) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + val_footprint stv v < dimword (:256) /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  storage_place_region cx p /\ stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    alloca_frame cenv ee sa s cenv ff t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type dty /\ (!et n. dty <> ArrayT et (Dynamic n))` by
    (Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[compileEnvTheory.is_bytestring_type_def, compileEnvTheory.is_word_type_def] >>
     rename1 `BaseT (BytesT bd)` >> Cases_on `bd` >>
     gvs[compileEnvTheory.is_bytestring_type_def, compileEnvTheory.is_word_type_def]) >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all place_store_bytestring_representation >>
  disch_then (qx_choose_then `src_cap` (qx_choose_then `dst_cap`
    (map_every assume_tac o CONJUNCTS))) >>
  `0 < type_slot_size dtv` by
    (gvs[vyperValueTheory.type_slot_size_def]) >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `type_memory_bytes cenv sty = 32 * (1 + word_size src_cap)` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `case v of BytesV bs => LENGTH bs <= src_cap /\
                              w2n sw+32+LENGTH bs < dimword (:256)
           | StringV str => LENGTH str <= src_cap /\
                              w2n sw+32+LENGTH str < dimword (:256) | _ => F` by
    (gvs[] >> Cases_on `v` >>
     gvs[loweringPostsTheory.val_footprint_def, vyperTypingTheory.value_has_type_def]) >>
  `1 + word_size src_cap <= type_slot_size dtv` by
    (gvs[vyperValueTheory.type_slot_size_def] >>
     metis_tac[exprSimHypsTheory.word_size_monotone]) >>
  `1 + word_size src_cap < dimword (:256)` by suspend "count" >>
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `(case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) = NONE` by
    (Cases_on `dty` >> gvs[compileEnvTheory.is_bytestring_type_def]) >>
  qpat_assum `(case dty of ArrayT _ _ => _ | _ => _) = NONE`
    (fn meta => qpat_assum `~is_word_type dty`
      (fn word => drule_all (SRULE [meta,word] place_store_storage_compile))) >>
  simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `alloca_frame cenv ee sa s cenv final _` >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       stmt_state_rel ctx func cenv cx final t /\
       (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
       t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by suspend "suffix" >>
  qexists_tac `t` >> simp[] >>
  irule stmtSimDefsTheory.alloca_frame_of_mem_frame >>
  simp[Abbr `final`, vyperStorageBackendTheory.set_storage_scopes] >>
  qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]
QED
Resume assign_place_bytes_storage_run[count]:
  `dst_cap < dimword (:256)` by
    gvs[vyperTypingTheory.well_formed_type_value_def] >>
  `src_cap < dimword (:256)` by decide_tac >>
  `word_size src_cap < dimword (:256) - 1` by
    (simp[vfmConstantsTheory.word_size_def, arithmeticTheory.DIV_LT_X] >>
     simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
     qpat_x_assum `src_cap < dimword (:256)` mp_tac >>
     simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> decide_tac) >>
  decide_tac
QED
Resume assign_place_bytes_storage_run[suffix]:
  unabbrev_all_tac >>
  qpat_x_assum `n2w (w2n root+delta) = root+n2w delta`
    (fn th => rewrite_tac[GSYM th] >> assume_tac th) >>
  irule assign_place_wrapped_memory_suffix_run >>
  simp[] >> (conj_tac >- metis_tac[]) >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = SOME sw`)) >>
  qexistsl_tac [`dst`, `word_size src_cap + 1`, `v`] >>
  simp[ADD_COMM] >> (reverse conj_tac >- metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `w2n (root+n2w delta) = _`
    (fn addr => irule (SIMP_RULE (srw_ss()) [addr, AC ADD_ASSOC ADD_COMM]
      (Q.INST [`k` |-> `root+n2w delta`]
        (SPEC_ALL assign_place_bytestring_wrapped_live_copy)))) >>
  simp[] >> qexistsl_tac [`dst_cap`, `dtv`, `v`] >>
  simp[AC ADD_ASSOC ADD_COMM] >>
  (conj_tac >- metis_tac[]) >>
  qpat_x_assum `case v of BytesV _ => _ /\ _ | StringV _ => _ | _ => _` mp_tac >>
  Cases_on `v` >> simp_tac (srw_ss()) [AC ADD_ASSOC ADD_COMM]
QED
Finalise assign_place_bytes_storage_run
