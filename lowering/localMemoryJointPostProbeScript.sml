(* Actual RHS/target posts supply the staged joint subpath-store suffix. *)
Theory localMemoryJointPostProbe
Ancestors
  localMemoryStoreStagedProbe localMemoryTargetProbe localMemoryRhsProbe
  bodyFullMemoryFrames bodyPtrDefs stmtSimDefs bodySimFull bodySim
  exprSimHypsDefs loweringPosts exprLoweringProps loweringStateRelDefs
  compileEnv context stmtLowering exprLowering venomState vyperState
  words list arithmetic

Theorem memory_posts_store_joint:
  vv_post (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx e rhs_origin start sa rhs0 es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  post_value_type cenv e = ty /\ lowered_value_type cenv e = ty /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  read_result cx raw es = (INL v,es) /\ value_has_type tv v /\
  ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory)) es G tn s /\
  ptr_buf_ok cenv e (Var xs) G s /\
  vv_store_bound cx ty ty es raw
    (LocatedValue ty (mk_ptr (Var xs) LocMemory)) s /\
  target_post H ctx func cenv cx target_origin cut sa target0 es
    (PlaceR (MemoryPlace id path)) (Type ty) (Var xd,SOME LocMemory,ann) s /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path))
    (Var xd,SOME LocMemory,ann) G tn s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  lookup_scopes id es.scopes = SOME entry /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  (!t0. cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es0 /\
  dead_lo_ok H D lo cenv cx /\ 0 < type_memory_size tv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  unwrap_value cenv (LocatedValue ty (mk_ptr (Var xs) LocMemory)) sa = (op,su) /\
  compile_assign_value cenv (Var xd) LocMemory op F (SOME LocMemory) ty ty
    bytes su = ((),sb) /\
  write_place cx (MemoryPlace id path) v es = (INL (),ff) /\
  local_ptrs_reserved cenv sa /\ not_fresh_at sa xs /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
  ?t Gf tf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf) /\
    stmt_state_rel H ctx func cenv cx ff t /\
    ghost_inv_at D lo d cenv cx ff Gf tf t /\
    alloca_frame cenv es sa s cenv ff t /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s n b sz' ==>
        off+sz <= b \/ b+sz' <= off) /\
      off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all memory_rhs_store_resources >> strip_tac >>
  `op = Var xs /\ su = sa` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  qpat_x_assum `su = sa` SUBST_ALL_TAC >>
  drule_all memory_target_store_resources >> strip_tac >>
  rename1 `mem_path_offset entry.type path = SOME (k,tvtgt)` >>
  `tvtgt = tv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tvtgt = tv` SUBST_ALL_TAC >>
  `0 < cap` by
    (drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >> decide_tac) >>
  `stmt_state_rel H ctx func cenv cx es s` by fs[vv_post_def] >>
  `lo <= w2n bw` by
    (drule_all body_full_local_region_lower_bound >> simp[]) >>
  `lo <= w2n dw` by decide_tac >>
  mp_tac (Q.INST [`start` |-> `start`,`s` |-> `s`,`sa` |-> `sa`,
    `xs` |-> `xs`,`xd` |-> `xd`,`sw` |-> `sw`,`dw` |-> `dw`,
    `bw` |-> `bw`,`p` |-> `p`,`cap` |-> `cap`,`k` |-> `k`,
    `entry` |-> `entry`,`tv` |-> `tv`,`ty` |-> `ty`,
    `H` |-> `H`,`D` |-> `D`,`G` |-> `G`,`tn` |-> `tn`]
    (SPEC_ALL staged_memory_subpath_store_joint)) >>
  impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED
