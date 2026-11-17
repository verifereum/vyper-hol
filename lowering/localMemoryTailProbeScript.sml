(* The memory-source branch, including the original RHS/target frames. *)
Theory localMemoryTailProbe
Ancestors
  localMemoryJointPostProbe localMemoryPrefixProbe localMemoryTransportProbe
  localMemoryRhsProbe targetPurePostTransport bodySimFull bodySim bodyPtrDefs
  stmtSimDefs exprSimHypsDefs exprSimMemDefs loweringPosts exprLoweringProps
  loweringStateRelDefs compileEnv context stmtLowering exprLowering
  freshWrites venomState vyperState words list arithmetic

Theorem memory_assignment_joint_tail:
  vv_post (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) u /\
  target_post H ctx func cenv cx mid sm st u ee
    (PlaceR (MemoryPlace id path)) (Type ty) (Var xd,SOME LocMemory,ann) z /\
  ee = mid with <|gas_obs := gs; outcomes := os; requests := rq;
    logs := lg; storage_trace := trace|> /\
  ~expr_has_effect e /\ post_value_type cenv e = ty /\
  lowered_value_type cenv e = ty /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\ 0 < type_memory_size tv /\
  read_result cx raw mid = (INL v,mid) /\ value_has_type tv v /\
  ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) mid G1 tn1 u /\
  ptr_buf_ok cenv e (Var xs) G1 u /\
  vv_store_bound cx ty ty mid raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) u /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path))
    (Var xd,SOME LocMemory,ann) G2 tn2 z /\
  ghost_inv_at D lo d cenv cx ee G2 tn2 z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 u G2 tn2 /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  local_ptrs_reserved cenv st /\ not_fresh_at sm xs /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= st.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= st.cs_next_id /\
  u.vs_alloca_next <= z.vs_alloca_next /\
  lookup_scopes id ee.scopes = SOME entry /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  (!t0. cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  dead_lo_ok H D lo cenv cx /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  unwrap_value cenv (LocatedValue ty (mk_ptr (Var xs) LocMemory)) st = (op,su) /\
  compile_assign_value cenv (Var xd) LocMemory op F (SOME LocMemory) ty ty
    bytes su = ((),sb) /\
  write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  ~z.vs_halted /\ z.vs_current_bb = st.cs_current_bb /\
  z.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) ==>
  ?t Gf tf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G2,tn2) [] (OK t,Gf,tf) /\
    stmt_state_rel H ctx func cenv cx ff t /\
    ghost_inv_at D lo d cenv cx ff Gf tf t /\
    alloca_frame cenv es sa s0 cenv ff t /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
        off+sz <= b \/ b+sz' <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_storage_live H cx (LocatedValue ty (mk_ptr (Var xs) LocMemory)) mid u` by
    fs[vv_post_def] >>
  `!x. vv_operand (LocatedValue ty (mk_ptr (Var xs) LocMemory)) = Var x ==>
    not_fresh_at sm x` by simp[vv_operand_def,mk_ptr_def] >>
  `!l. vv_operand (LocatedValue ty (mk_ptr (Var xs) LocMemory)) <> Label l` by
    simp[vv_operand_def,mk_ptr_def] >>
  drule_all target_saved_post_transport >> strip_tac >>
  `wb_frame cenv mid mid sm u z` by
    (gvs[target_post_def,wb_frame_def,locals_kept_def,popped_kept_def] >>
     metis_tac[]) >>
  drule_all memory_rhs_store_resources >> strip_tac >>
  `lookup_var xs z = lookup_var xs u` by
    (fs[target_post_def] >> metis_tac[]) >>
  drule_all target_saved_memory_ptr_transport >> strip_tac >>
  `read_result cx raw ee = (INL v,ee)` by
    simp[SRULE [] target_saved_read_oracles] >>
  `ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) ee G2 tn2 z /\
   vv_store_bound cx ty ty ee raw
     (LocatedValue ty (mk_ptr (Var xs) LocMemory)) z` by
    (simp[ptr_vv_ok_def,vv_store_bound_def,mk_ptr_def,
       SRULE [] target_saved_read_oracles] >>
     gvs[ptr_vv_ok_def,vv_store_bound_def,mk_ptr_def]) >>
  `not_fresh_at st xs` by metis_tac[not_fresh_at_mono] >>
  mp_tac (Q.INST [`rhs_origin` |-> `ee`,`start` |-> `sa`,`rhs0` |-> `z`,
    `target_origin` |-> `mid`,`cut` |-> `sm`,`target0` |-> `u`,
    `es` |-> `ee`,`s` |-> `z`,`sa` |-> `st`,`G` |-> `G2`,`tn` |-> `tn2`,
    `es0` |-> `es`]
    (SPEC_ALL memory_posts_store_joint)) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all rhs_target_store_allocation_posts >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tf`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
