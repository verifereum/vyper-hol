(* The actual compiler value may carry a buffer field or bytestring annotation. *)
Theory localMemoryArbitraryRhsProbe
Ancestors
  localMemoryCanonicalProbe localMemoryTailProbe bodyPtrDefs loweringPosts
  exprSimMemDefs exprLowering compileEnv context venomState

Theorem memory_assignment_joint_memory_rhs:
  p.ptr_location = LocMemory /\ p.ptr_operand = Var xs /\
  vv_post (H0:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sm s0 mid raw
    (LocatedValue source_ann p) u /\
  target_post H0 ctx func cenv cx mid sm st u ee
    (PlaceR (MemoryPlace id path)) (Type ty) (Var xd,SOME LocMemory,ann) z /\
  ee = mid with <|gas_obs := gs; outcomes := os; requests := rq;
    logs := lg; storage_trace := trace|> /\
  ~expr_has_effect e /\ post_value_type cenv e = ty /\
  lowered_value_type cenv e = ty /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes cenv ty = type_memory_size tv /\ 0 < type_memory_size tv /\
  read_result cx raw mid = (INL v,mid) /\ value_has_type tv v /\
  ptr_vv_ok cx ty raw (LocatedValue source_ann p) mid G1 tn1 u /\
  ptr_buf_ok cenv e (Var xs) G1 u /\
  vv_store_bound cx ty ty mid raw
    (LocatedValue source_ann p) u /\
  target_ptr_ok cenv (PlaceR (MemoryPlace id path))
    (Var xd,SOME LocMemory,ann) G2 tn2 z /\
  ghost_inv_at D0 lo d0 cenv cx ee G2 tn2 z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 u G2 tn2 /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
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
  dead_lo_ok H0 D0 lo cenv cx /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  unwrap_value cenv (LocatedValue source_ann p) st = (op,su) /\
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
    (!D.
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,G2,tn2) [] (OK t,Gf,tf)) /\
    (!(H:(bool # 256 word # type_value) list # num list) D d.
      stmt_state_rel H ctx func cenv cx ee z /\
      ghost_inv_at D lo d cenv cx ee G2 tn2 z ==>
      stmt_state_rel H ctx func cenv cx ff t /\
      ghost_inv_at D lo d cenv cx ff Gf tf t) /\
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
  drule_all memory_vv_canonical_post >>
  disch_then (qspec_then `st` strip_assume_tac) >>
  `ptr_vv_ok cx ty raw (LocatedValue ty (mk_ptr (Var xs) LocMemory))
     mid G1 tn1 u /\
   vv_store_bound cx ty ty mid raw
     (LocatedValue ty (mk_ptr (Var xs) LocMemory)) u` by
    (mp_tac (Q.INST [`p` |-> `p`,`xs` |-> `xs`,`cx` |-> `cx`,
       `ty` |-> `ty`,`ann` |-> `source_ann`,`lt` |-> `ty`,`raw` |-> `raw`,
       `es` |-> `mid`,`G` |-> `G1`,`tn` |-> `tn1`,`s` |-> `u`]
       (SPEC_ALL memory_vv_canonical_resources)) >> simp[]) >>
  `unwrap_value cenv (LocatedValue ty (mk_ptr (Var xs) LocMemory)) st = (op,su)` by
    (gvs[unwrap_value_def,mk_ptr_def,comp_return_def]) >>
  drule_all memory_assignment_joint_effect >> simp[]
QED
