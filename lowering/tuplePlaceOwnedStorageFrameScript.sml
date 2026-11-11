Theory tuplePlaceOwnedStorageFrame
Ancestors
  tuplePlaceValueStorageFrame allocaSiteResource stmtSimDefs exprSimHypsDefs
  loweringPosts venomState stmtLowering exprLowering compileEnv loweringStateRelDefs
  vyperInterpreter vyperState vyperValue vyperTypeSystem arithmetic

Theorem tuple_place_owned_storage_run_frame:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty (type_memory_bytes cenv dty) sa = ((),sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
       evaluate_type (get_tenv cx) dty = SOME dtv ==>
       type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= w2n w \/
       w2n w + type_memory_size dtv <= w2n sw \/ sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0. p = MemoryPlace id path /\
       lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
       0 < type_memory_size stv /\ type_memory_size stv + 64 < dimword (:256) /\
       w2n sw + type_memory_size stv < dimword (:256) /\
       ?aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
         aid < sa.cs_next_id /\ b <= w2n sw /\
         w2n sw + type_memory_size stv <= b+len) /\
    (loc = LocMemory ==> !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       w2n w + type_memory_size dtv < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
       0 < type_memory_size dtv /\ type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
       type_alloc_ok cenv dty) /\
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
      (!aid b len a n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
        b <= a /\ a+n <= b+len ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `~is_word_type sty ==> !sw. eval_operand op s = SOME sw ==>
     w2n sw + type_memory_size stv <= s.vs_alloca_next /\
     !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
       w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw` by
    (ntac 3 strip_tac >>
     qpat_x_assum `~is_word_type sty ==> !sw. _ ==> 0 < _ /\ _`
       (drule_all_then strip_assume_tac) >>
     conj_tac >- (drule_all alloca_site_registered_below >> decide_tac) >>
     rpt strip_tac >> `aid <> aid'` by decide_tac >>
     `b + len <= b' \/ b' + sz <= b` by
       metis_tac[alloca_inv_def, allocas_non_overlapping_def] >> decide_tac) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `env`, `ee`, `ff`, `s`, `p`, `w`, `loc`,
      `dst_op`, `op`, `src_loc`, `dty`, `sty`, `stv`, `v`, `sa`, `sb`] mp_tac
    tuple_place_value_storage_run_frame >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
  simp[]
QED
