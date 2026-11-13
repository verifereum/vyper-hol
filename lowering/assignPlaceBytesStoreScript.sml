Theory assignPlaceBytesStore
Ancestors
  placeStoreSlots placeStoreStorage stmtSimStoreCopy exprLoweringProps
  compileEnv venomState venomInst venomExecSemantics valueEncodingProps
  fragGasMode context words arithmetic list rich_list
Libs
  stepInstBaseLib

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
  `compile_word_copy_loop_op src dst (Lit (n2w n)) LocMemory
     (if tr then LocTransient else LocStorage) F sa = (result,sb)` by
    (Cases_on `tr` >> gvs[contextTheory.compile_memory_to_transient_def,
                          contextTheory.compile_memory_to_storage_def,
                          contextTheory.compile_word_copy_loop_def]) >>
  mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
                  `ctor` |-> `F`, `u` |-> `result`,
                  `s0` |-> `s`, `b` |-> `sw`, `k` |-> `dw`]
    (INST [mk_var ("count", ``:operand``) |-> ``Lit (n2w n)``]
      placeStoreCopyPathTheory.place_store_runtime_copy_path)) >>
  (impl_tac >- (Cases_on `tr` >> simp[eval_operand_def] >> metis_tac[])) >>
  strip_tac >>
  qexists_tac `t` >> simp[] >>
  drule placeStoreCopyPathTheory.place_store_copy_frame_observations >>
  strip_tac >> simp[] >>
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

(* Kept local here while placeStoreSlots' public interface is frozen.  This
   is store_slots_bytes_count_path's statement and proof, unchanged. *)
Theorem assign_place_bytes_count_path[local]:
  compile_bytestring_word_count src sa = (cnt,sm) /\
  eval_operand src s = SOME sw /\
  mem_word_at (w2n sw) s.vs_memory = n2w L /\
  L + 63 < dimword (:256) /\ fn_has_code sa sm func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
      eval_operand cnt u = SOME (n2w (1 + word_size L)) /\
      u.vs_memory = s.vs_memory /\
      (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s u) /\
      ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
      u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
  simp[compile_bytestring_word_count_def, comp_bind_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MLOAD [src] sa = (loaded,a)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [loaded; Lit 63w] a = (sum,b)` >>
  `ci_mono sa a /\ ci_mono a b /\ ci_mono b sm` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sm func` by
    (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
                                  cs_extends_trans]) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
       eval_operand loaded t = SOME (n2w L) /\
       t.vs_memory = s.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame sa off len s t) /\
       ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
       t.vs_inst_idx = LENGTH a.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[src]`, `MLOAD`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_read1_def, GSYM mem_word_at_eq_mload]) >>
  suspend "rest"
QED
Resume assign_place_bytes_count_path[rest]:
  `?r. gas_marked_path F ctx func t 0 (OK r) /\
       eval_operand sum r = SOME (n2w (L + 63)) /\
       r.vs_memory = t.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame a off len t r) /\
       ~r.vs_halted /\ r.vs_current_bb = b.cs_current_bb /\
       r.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[loaded; Lit 63w]`, `ADD`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, GSYM wordsTheory.word_add_n2w]) >>
  `(n2w (L + 63):bytes32) >>> 5 = n2w (1 + word_size L)` by
    (once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
     simp[Excl "w2n_11", wordsTheory.w2n_lsr, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD, vfmConstantsTheory.word_size_def] >>
     qspec_then `L + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     qspec_then `L + 63` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     rpt strip_tac >>
     `(L + 31) DIV 32 + 1 < dimword (:256)` by intLib.ARITH_TAC >>
     simp[arithmeticTheory.LESS_MOD] >> intLib.ARITH_TAC) >>
  `?u. gas_marked_path F ctx func r 0 (OK u) /\
       eval_operand cnt u = SOME (n2w (1 + word_size L)) /\
       u.vs_memory = r.vs_memory /\
       (!off len. typedMemoryCopy$typed_copy_state_frame b off len r u) /\
       ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
       u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (irule place_store_emit_op_path >> simp[] >>
     qexistsl_tac [`[Lit 5w; sum]`, `SHR`] >>
     simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `t` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  rpt gen_tac >>
  metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_trans,
            typedMemoryCopyTheory.typed_copy_state_frame_mono]
QED
Finalise assign_place_bytes_count_path

Theorem assign_place_bytes_storage_run:
  (loc = LocStorage \/ loc = LocTransient) /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  compile_assign_value cenv dst loc src (is_word_type dty) src_loc dty sty
    (type_memory_bytes cenv dty) sa = ((),sb) /\
  eval_operand dst s = SOME k /\ eval_operand src s = SOME sw /\
  place_ptr_rel cenv cx s (PlaceR p) k (SOME loc) (Type dty) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + val_footprint stv v < dimword (:256) /\
  type_memory_size stv < dimword (:256) /\
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
  `n2w (w2n root+delta) = root+n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n] >>
  `compile_store_slots cenv src dst dty tr sa = ((),sb)` by
    (qpat_assum `~is_word_type dty` (fn word =>
       drule_all (SRULE [word] placeStoreSlotsTheory.place_store_storage_compile)) >>
     simp[] >> strip_tac >> gvs[]) >>
  `?len. mem_word_at (w2n sw) s.vs_memory = n2w len /\
     (!j. MEM j (MAP FST writes) <=> j < 1 + word_size len) /\
     len <= src_cap` by suspend "encoding" >>
  `len + 63 < dimword (:256) /\
   1 + word_size len < dimword (:256)` by suspend "count" >>
  `is_abi_dynamic cenv.ce_struct_fields dty` by
    (qpat_x_assum `is_bytestring_type dty` mp_tac >>
     Cases_on `dty` >> simp[compileEnvTheory.is_bytestring_type_def,
                              compileEnvTheory.is_abi_dynamic_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[compileEnvTheory.is_bytestring_type_def,
          compileEnvTheory.is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     simp[compileEnvTheory.is_bytestring_type_def,
          compileEnvTheory.is_abi_dynamic_def]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def, comp_bind_def,
       comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count src sa = (cnt,sm)` >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `ci_mono sa sm /\ (!x. cnt = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[contextTheory.compile_bytestring_word_count_def, comp_bind_def] >>
     pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     conj_tac
     >- (fs[ci_mono_def] >>
         metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh]) >>
  rename1 `compile_word_copy_loop_op _ _ _ _ _ _ sm = (res,sb)` >>
  `ci_mono sm sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_word_copy_loop_op,
              pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  drule_all assign_place_bytes_count_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand src u = SOME sw /\
   eval_operand dst u = SOME (root+n2w delta)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_operand] >>
  `!x. src = Var x \/ dst = Var x \/ cnt = Var x ==>
       not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `u.vs_call_ctx = s.vs_call_ctx /\ u.vs_allocas = s.vs_allocas /\
   store_copy_normalize s u = s /\
   (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)` by
    (first_x_assum (qspecl_then [`0`,`0`] mp_tac) >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
          store_copy_normalize_def, venomStateTheory.venom_state_component_equality] >>
     metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx ee u` by
    (irule place_store_normalized_stmt_state >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
     qexists_tac `s` >> simp[]) >>
  mp_tac (Q.INST [`loc` |-> `if tr then LocTransient else LocStorage`,
                  `ctor` |-> `F`, `s0` |-> `u`, `sa` |-> `sm`,
                  `b` |-> `sw`, `k` |-> `root+n2w delta`,
                  `n` |-> `1 + word_size len`]
    (INST [mk_var ("count", ``:operand``) |-> mk_var ("cnt", ``:operand``),
           mk_var ("u", ``:string``) |-> mk_var ("res", ``:string``)]
      placeStoreCopyPathTheory.place_store_runtime_copy_path)) >>
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >>
  strip_tac >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr
      (apply_writes (root+n2w delta) writes (get_storage cx ee tr)))
    (store_copy_normalize u t)` by suspend "semantic" >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x u` by
    (fs[store_copy_frame_def] >>
     metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh]) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr
      (apply_writes (root+n2w delta) writes (get_storage cx ee tr))) t` by
    (irule place_store_normalized_stmt_state >>
     goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
     qexists_tac `u` >> simp[]) >>
  drule placeStoreCopyPathTheory.place_store_copy_frame_observations >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by metis_tac[] >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       gas_marked_path_then)) >> qexists_tac `u` >> simp[]) >>
  `alloca_frame cenv ee sa s cenv
    (set_storage cx ee tr
      (apply_writes (root+n2w delta) writes (get_storage cx ee tr))) t` by
    (irule stmtSimDefsTheory.alloca_frame_of_mem_frame >>
     simp[vyperStorageBackendTheory.set_storage_scopes] >>
     qexistsl_tac [`ctx`, `cx`, `func`] >> simp[]) >>
  qexists_tac `t` >> simp[]
QED
Resume assign_place_bytes_storage_run[count]:
  `word_size len <= word_size src_cap` by
    metis_tac[exprSimHypsTheory.word_size_monotone] >>
  `src_cap <= 32 * word_size src_cap` by
    (simp[vfmConstantsTheory.word_size_def] >>
     `(src_cap+31) MOD 32 < 32` by simp[] >>
     qspec_then `src_cap+31` mp_tac
       (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
     decide_tac) >>
  `32 * (1 + word_size src_cap) < dimword (:256)` by metis_tac[] >>
  qpat_x_assum `32 * (1 + word_size src_cap) < dimword (:256)` mp_tac >>
  qpat_x_assum `src_cap <= 32 * word_size src_cap` mp_tac >>
  qpat_x_assum `len <= src_cap` mp_tac >>
  qpat_x_assum `word_size len <= word_size src_cap` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  rpt strip_tac >> intLib.ARITH_TAC
QED
Resume assign_place_bytes_storage_run[encoding]:
  qexists_tac `case v of BytesV bs => LENGTH bs
                      | StringV str => LENGTH str | _ => 0` >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def,
      valueEncodingDefsTheory.val_in_memory_def,
      vyperStorageTheory.encode_value_def] >>
  drule vyperEncodeDecodeTheory.encode_dyn_bytes_slots_keys >> strip_tac >>
  simp[]
QED
Resume assign_place_bytes_storage_run[semantic]:
  markerLib.RESUME_TAC >> Cases_on `tr` >>
  qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [store_copy_frame_def, store_copy_prefix_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  qpat_x_assum `n2w _ = root+n2w delta`
    (fn th => rewrite_tac[GSYM th] >> assume_tac th) >>
  pure_rewrite_tac[wordsTheory.word_add_n2w] >>
  drule_at (Pat `declared_storage_region _ _ _ _ = _`)
    placeStoreSlotsTheory.place_store_encoded_leaf_state_sparse >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (fn th => irule (PURE_REWRITE_RULE [COND_CLAUSES] (BETA_RULE (Q.INST
    [`rd` |-> `\i. mload (w2n ((sw:bytes32) + n2w i * 32w)) u`]
    (SPEC_ALL th))))) >>
  asm_rewrite_tac[] >>
  asm_simp_tac bool_ss [rich_listTheory.MEM_COUNT_LIST, AC ADD_ASSOC ADD_COMM] >>
  (conj_tac >- (
  rpt gen_tac >> strip_tac >>
  qpat_assum `w2n _ = _`
    (fn addr => drule_at (Pat `encode_value _ _ = _`)
      (cj 2 (SIMP_RULE (srw_ss()) [addr, AC ADD_ASSOC ADD_COMM]
        (Q.INST [`k` |-> `root+n2w delta`, `s` |-> `u`]
          (SPEC_ALL assign_place_bytestring_wrapped_live_copy))))) >>
  disch_then irule >> asm_rewrite_tac[] >>
  qexistsl_tac [`dst_cap`, `src_cap`] >>
  asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  fs[vyperValueTheory.type_slot_size_def, AC ADD_ASSOC ADD_COMM])
QED
Finalise assign_place_bytes_storage_run
