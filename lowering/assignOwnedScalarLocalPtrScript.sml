(* Actual scalar local stores preserve a disjoint saved tuple allocation. *)
Theory assignOwnedScalarLocalPtr
Ancestors
  aggregateLocalStorePtr assignTuplePtrLocalWordRuntime assignTuplePtrLocalContract
  assignTupleStoreResourcesPtr tupleTargetStoreProps tupleLocalStoreRun
  stmtSimAugAssign stmtSimDeclStore bodySim exprSimHypsDefs exprSimProps
  exprSimLayoutTransport bodyPtrIfExpLayout exprLoweringProps
  supportedTypes vyperTypeArgFits vyperPlaceWriteSoundness vyperTypeSystem
  vyperTyping vyperTypeEnv vyperState vyperLookup compileEnv context emitHelper loweringPosts
  bodyPtrDefs loweringStateRelDefs typedMemoryCopy venomMemDefs
  venomState valueEncoding valueEncodingDefs finite_map arithmetic words list

Theorem scalar_local_saved_window_store_ptr:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_target env (NameTarget id) dty /\
  runtime_place_writable cx es (MemoryPlace id []) /\
  supported_scalar_type sty /\ supported_scalar_type dty /\ arg_type_fits sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  compile_tuple_store_all cenv [sty] [BaseTarget (NameTarget id)] [Var src] sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_val_ok cx sty v (Var src) G tn s /\ not_fresh_at sa src /\
  lookup_var src s = SOME sw /\
  (is_word_type sty ==> sw = typed_val_to_w256 stv v) /\
  (~is_word_type sty ==> ptr_covers G tn src s (type_memory_size stv) /\
    own_base <= w2n sw /\ w2n sw+type_memory_size stv <= own_base+own_size) /\
  own_base+own_size < dimword (:256) /\
  (!b sz. local_region cenv es.scopes s id b sz ==>
    own_base+own_size <= b \/ b+sz <= own_base) ==>
  ?fin Hf tf t.
    write_place cx (MemoryPlace id []) v es = (INL (),fin) /\
    stmt_state_rel ctx func cenv cx fin t /\ ghost_inv d cenv cx fin Hf tf t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Hf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\
    (!i. own_base <= i /\ i < own_base+own_size ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem ==> i IN tn.t_mem)) /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Hf tf (OK t)

Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP env.var_types id = SOME dty` by
    gvs[well_typed_target_def,type_place_target_NameTarget,AllCaseEqs()] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  rename1 `FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` >>
  `entry.type = dtv` by
    (qpat_assum `!entry. lookup_scopes id es.scopes = SOME entry ==> _`
      (fn th => mp_tac (MATCH_MP (Q.SPEC `entry` th)
        (ASSUME ``lookup_scopes id es.scopes = SOME entry``))) >>
     qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv`
       (fn th => REWRITE_TAC [th]) >> simp[]) >>
  `cenv.ce_var_type id = SOME dty` by
    (qpat_assum `expr_sim_inv cenv cx env es`
      (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> cenv.ce_var_type id = SOME ty`
       drule >> simp[]) >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  rename1 `find_containing_scope id es.scopes = SOME (pre,sc,entry,rest)` >>
  `entry.assignable` by fs[runtime_place_writable_def] >>
  `?dw. lookup_var p s = SOME dw` by
    (fs[stmt_state_rel_def,state_rel_def,local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `type_memory_size dtv <= sz` by metis_tac[] >>
  `is_word_type dty = is_word_type sty` by metis_tac[compatible_word_type] >>
  drule_all tuple_local_compatible_singleton_code_ptr >> strip_tac >>
  qabbrev_tac `fin = es with scopes :=
    pre ++ (sc |+ (id,entry with <|value := v; popped := []|>))::rest` >>
  `write_place cx (MemoryPlace id []) v es = (INL (),fin)` by
    (simp[Abbr `fin`] >> irule tuple_target_local_write_safe >> asm_rewrite_tac[]) >>
  `(!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x)` by
    fs[ret_pc_ok_def] >>
  `op_taint tn (Var src) = {}` by fs[ptr_val_ok_def,ptr_mem_ok_def] >>
  `own_base+own_size <= w2n dw \/ w2n dw+sz <= own_base` by metis_tac[] >>
  `!i. own_base <= i /\ i < own_base+own_size ==>
    ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv)` by
    (rpt strip_tac >> decide_tac) >>
  (Cases_on `is_word_type sty`
   >- suspend "word" >>
   suspend "memory")
QED

Resume scalar_local_saved_window_store_ptr[word]:
  markerLib.RESUME_TAC >>
  `supported_word_type sty` by
    (fs[supported_scalar_type_def] >>
     Cases_on `sty` >> fs[supported_string_type_def] >>
     Cases_on `b` >> fs[supported_string_type_def,is_word_type_def] >>
     Cases_on `b'` >> fs[supported_string_type_def,is_word_type_def]) >>
  `sty = dty` by metis_tac[ifexp_supported_word_fits_eq] >>
  `stv = dtv` by metis_tac[optionTheory.SOME_11] >>
  `store_lays_out stv entry.type v` by metis_tac[store_lays_out_typed] >>
  `type_memory_size dtv = 32` by metis_tac[word_tv_memory_size] >>
  `eval_operand (Var src) s = SOME (typed_val_to_w256 stv v)` by
    fs[eval_operand_def] >>
  `emit_void MSTORE [Var p;Var src] sa = ((),sb)` by fs[] >>
  drule_all tuple_local_word_runtime_head_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx fin t /\ ghost_inv d cenv cx fin G tn' t` by
    gvs[Abbr `fin`] >>
  `!i. own_base <= i /\ i < own_base+own_size ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `~(w2n dw <= i /\ i < w2n dw+32)` by metis_tac[] >>
     metis_tac[]) >>
  qexistsl_tac [`fin`,`G`,`tn'`,`t`] >> asm_rewrite_tac[] >>
  metis_tac[]
QED

Resume scalar_local_saved_window_store_ptr[memory]:
  markerLib.RESUME_TAC >>
  `compile_store_memory cenv (Var src) (Var p) dty sty sa = ((),sb)` by fs[] >>
  `own_base <= w2n sw /\ w2n sw+type_memory_size stv <= own_base+own_size` by
    metis_tac[] >>
  `w2n sw+type_memory_size stv < dimword (:256)` by
    decide_tac >>
  `w2n dw+type_memory_size dtv <= w2n sw \/
    w2n sw+type_memory_size stv <= w2n dw` by decide_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n sw) m` by
    (fs[ptr_val_ok_def,ptr_mem_ok_def,eval_operand_def] >> metis_tac[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_def] >> strip_tac >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `type_widens_to (get_tenv cx) sty dty` by
    fs[type_widens_to_def,well_formed_type_def] >>
  mp_tac (Q.INST [`tenv` |-> `get_tenv cx`,`a` |-> `sa`,`b` |-> `sb`,
    `fn` |-> `func`,`D` |-> `cx_dead cx`,`es'` |-> `fin`]
    (SPEC_ALL aggregate_local_store_framed_ptr)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`Hf`,`tf`,`t`] strip_assume_tac) >>
  `t.vs_allocas = s.vs_allocas` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  `!i. own_base <= i /\ i < own_base+own_size ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tf.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv)` by metis_tac[] >>
     conj_tac
     >- (fs[typed_copy_state_frame_def,typed_copy_frame_def] >>
         first_assum irule >> decide_tac) >>
     metis_tac[]) >>
  qexistsl_tac [`fin`,`Hf`,`tf`,`t`] >> asm_rewrite_tac[] >>
  metis_tac[]
QED

Finalise scalar_local_saved_window_store_ptr

Theorem owned_scalar_local_tuple_store_ptr:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_target env (NameTarget id) dty /\
  runtime_place_writable cx es (MemoryPlace id []) /\
  supported_scalar_type sty /\ supported_scalar_type dty /\ arg_type_fits sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv dty = type_memory_size dtv /\
  compile_tuple_store_all cenv [sty] [BaseTarget (NameTarget id)] [Var src] sa = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ret_pc_ok cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ptr_val_ok cx sty v (Var src) G tn s /\ not_fresh_at sa src /\
  lookup_var src s = SOME sw /\
  (is_word_type sty ==> sw = typed_val_to_w256 stv v) /\
  (~is_word_type sty ==> ptr_covers G tn src s (type_memory_size stv) /\
    own_base <= w2n sw /\ w2n sw+type_memory_size stv <= own_base+own_size) /\
  FLOOKUP s.vs_allocas aid = SOME (own_base,own_size) /\ aid < sa.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    own_base+own_size <= b \/ b+sz <= own_base) ==>
  ?fin Hf tf t.
    write_place cx (MemoryPlace id []) v es = (INL (),fin) /\
    stmt_state_rel ctx func cenv cx fin t /\ ghost_inv d cenv cx fin Hf tf t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Hf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)) /\
    FLOOKUP t.vs_allocas aid = SOME (own_base,own_size) /\
    (!i. own_base <= i /\ i < own_base+own_size ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tf.t_mem ==> i IN tn.t_mem)) /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn s 0 Hf tf (OK t)


Proof
  strip_tac >>
  `own_base+own_size < dimword (:256)` by
    (`alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
     `own_base+own_size <= s.vs_alloca_next` by
       metis_tac[alloca_inv_def,alloca_next_valid_def] >>
     drule alloca_room_next_lt >> decide_tac) >>
  mp_tac (Q.INST [`PG` |-> `PG`] (SPEC_ALL scalar_local_saved_window_store_ptr)) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  disch_then (qx_choosel_then [`fin`,`Hf`,`tf`,`t`] strip_assume_tac) >>
  qexistsl_tac [`fin`,`Hf`,`tf`,`t`] >> asm_rewrite_tac[]
QED
