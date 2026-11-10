Theory placeRelayoutStorageFrame
Ancestors
  placeStoreStorage placeDynStoragePath placeDynStorageEmptyPath
  placeDynStoreState placeDynExecutionLayout placeDynLayout
  vyperTyping vyperValue valueEncoding valueEncodingProps
Libs monadsyntax

Theorem place_relayout_typed_storage_suffix_framed_run:
  (if type_memory_size tv <= 32 then
     ?loaded sm. emit_op MLOAD [src] sa = (loaded,sm) /\
       emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sm = ((),sb)
   else ?r. (if tr then compile_memory_to_transient else compile_memory_to_storage)
       src dst (type_memory_size tv DIV 32) sa = (r,sb)) /\
  type_memory_size tv = 32 * type_slot_size tv /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved cenv sa /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `!i b. i < type_slot_size tv /\ b < 32 /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
      start tv (start+i) b ==>
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (mload (w2n sw+32*i) s) T)` by
    (rpt strip_tac >> irule place_store_memory_live_at >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`tv`, `v`] >> pure_asm_rewrite_tac[] >> simp[]) >>
  Cases_on `type_memory_size tv <= 32`
  >- suspend "load"
  >> suspend "loop"
QED
Resume place_relayout_typed_storage_suffix_framed_run[loop]:
  `type_slot_size tv < dimword (:256)` by decide_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  mp_tac (Q.INST [`n` |-> `type_slot_size tv`, `result` |-> `r`]
    (SPEC_ALL place_store_memory_leaf_run)) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Resume place_relayout_typed_storage_suffix_framed_run[load]:
  `type_slot_size tv = 1` by decide_tac >>
  fs[IgnAsm `start = _`] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[fragExecTheory.cs_appends_emit_helpers, fragExecTheory.cs_appends_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all place_store_load_emit_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
     Cases_on `tr` >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def, venomStateTheory.venom_state_component_equality,
          venomStateTheory.sstore_def, venomStateTheory.tstore_def]) >>
  `stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\u i. (if tr then tstore else sstore)
      (n2w (start+i)) (mload (w2n sw) s) u) s (COUNT_LIST 1))` by
    (irule (BETA_RULE (Q.INST [`rd` |-> `\i. mload (w2n (sw:bytes32)) s`]
      (SPEC_ALL place_store_encoded_leaf_state))) >>
     conj_tac >- metis_tac[] >> reverse conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     simp[] >> qexists_tac `v` >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at Any) >> simp[] >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >> gvs[]
QED
Finalise place_relayout_typed_storage_suffix_framed_run

Theorem place_relayout_dyn_storage_suffix_framed_run:
  compile_dynarray_to_storage src dst (type_slot_size etv)
    (32 * type_slot_size etv) (loc = LocTransient) mid = ((),sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  fn_has_code mid sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at mid x) /\
  eval_operand src q = SOME pw /\ eval_operand dst q = SOME w /\
  ~q.vs_halted /\ q.vs_current_bb = mid.cs_current_bb /\
  q.vs_inst_idx = LENGTH mid.cs_current_insts /\
  place_ptr_rel cenv cx q (PlaceR p) w (SOME loc) (Type dty) /\
  expr_sim_inv cenv cx env ee /\ storage_place_region cx p /\
  (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
  evaluate_type (get_tenv cx) dty = SOME (ArrayTV etv (Dynamic n)) /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\
  value_has_type (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs)) /\
  val_in_memory (ArrayTV etv (Dynamic n)) (ArrayV (DynArrayV vs))
    (w2n pw) q.vs_memory /\
  w2n pw + type_memory_size (ArrayTV etv (Dynamic n)) < dimword (:256) /\
  stmt_state_rel ctx func cenv cx ee q /\
  write_place cx p (ArrayV (DynArrayV vs)) ee = (INL (),ff) /\
  local_ptrs_reserved cenv mid ==>
  ?t. gas_marked_path F ctx func q 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x q) /\
    t.vs_memory = q.vs_memory /\ t.vs_allocas = q.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `mload (w2n pw) q = n2w (LENGTH vs)` by
    (drule place_dyn_memory_header >>
     simp[venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def]) >>
  `LENGTH vs < dimword (:256)` by
    gvs[well_formed_type_value_def, value_has_type_def] >>
  `type_slot_size etv = 1 ==> 32 * type_slot_size etv = 32` by simp[] >>
  `~q.vs_call_ctx.cc_static` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ q` mp_tac >>
     pure_rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def,
                      loweringStateRelDefsTheory.state_rel_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `?t. gas_marked_path F ctx func q 0 (OK t) /\
       (!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x q) /\
       store_copy_normalize q t =
         (if loc = LocTransient then tstore else sstore) w (n2w (LENGTH vs))
           (place_dyn_prefix loc pw w (type_slot_size etv)
             (32 * type_slot_size etv) q (LENGTH vs)) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (Cases_on `LENGTH vs = 0`
     >- (`mload (w2n pw) q = 0w` by simp[] >>
         drule_all place_dyn_storage_empty_path >>
         disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `t` >>
         gvs[place_dyn_prefix_eqs]) >>
     `type_slot_size etv < dimword (:256)` by
       (gvs[well_formed_type_value_def, value_has_type_def,
            type_slot_size_def] >>
        `0 < n` by (Cases_on `n` >> gvs[]) >>
        `type_slot_size etv <= n * type_slot_size etv` by simp[] >>
        qpat_x_assum `n * type_slot_size etv + 1 <= _` mp_tac >>
        qpat_x_assum `type_slot_size etv <= n * type_slot_size etv` mp_tac >>
        decide_tac) >>
     drule_all place_dyn_storage_path >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     qexists_tac `t` >> Cases_on `loc` >> gvs[]) >>
  `w2n pw + 32 * (1 + n * type_slot_size etv) <= dimword (:256)` by
    (qpat_assum `w2n pw + type_memory_size _ < _` mp_tac >>
     pure_rewrite_tac[cj 1 valueEncodingPropsTheory.type_memory_size_slots,
                      vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `store_copy_normalize q t =
    (if loc = LocStorage then sstore else tstore) w
      (n2w (w2n (n2w (LENGTH vs):bytes32)))
      (place_dyn_prefix loc pw w (type_slot_size etv)
        (32 * type_slot_size etv) q (w2n (n2w (LENGTH vs):bytes32)))` by
    (Cases_on `loc` >> gvs[]) >>
  `stmt_state_rel ctx func cenv cx ff t` by
    (irule place_dyn_normalized_write_state >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     qexistsl_tac [`dty`, `ee`, `env`, `p`] >> gvs[]) >>
  `t.vs_memory = q.vs_memory /\ t.vs_allocas = q.vs_allocas` by
    (qpat_assum `store_copy_normalize q t =
       (if loc = LocTransient then _ else _) _ _ _` mp_tac >>
     Cases_on `loc = LocTransient` >>
     gvs[stmtSimStoreCopyTheory.store_copy_normalize_def,
          venomStateTheory.venom_state_component_equality,
          place_dyn_prefix_fields, venomStateTheory.sstore_def,
          venomStateTheory.tstore_def]) >>
  qexists_tac `t` >> simp[]
QED
