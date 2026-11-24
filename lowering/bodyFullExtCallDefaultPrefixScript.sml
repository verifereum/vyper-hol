(* Successful nonword default materialization up to, but not including, the
   store. The child has already selected its physical and shadow endpoints;
   the suffix here uses their explicit-site classification, but adds no marks. *)
Theory bodyFullExtCallDefaultPrefix
Ancestors
  bodyFullExtCallDefaultAlloc bodyFullExtCallDefaultUnwrap fragGasOriginPtr
  bodyPtrIfExpAllocCompiler abiBuiltinAllocation loweringShapeRules
  loweringPosts vyperStorageFootprint exprLoweringProps ptrDiscipline
  freshWrites words finite_map
Libs ctorCopyObservationLib

val default_prefix_entry = ``
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_alloc_buffer (type_memory_bytes cenv (lowered_value_type cenv e)) sm = (buf,sn) /\
  unwrap_value cenv vv sn = (op,sc) /\
  fn_has_code sm sn func /\ fn_has_code sn sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  type_memory_size ltv < dimword (:256) /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~is_word_type (post_value_type cenv e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  type_memory_bytes cenv (post_value_type cenv e) = type_memory_size ptv /\
  type_memory_size ptv < 2**64 /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME ltv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ltv /\
  (post_value_type cenv e = lowered_value_type cenv e \/
   is_bytestring_type (post_value_type cenv e) /\
   is_bytestring_type (lowered_value_type cenv e)) /\
  (!v. read_result cx tv ee = (INL v,ee) ==>
       value_has_type ptv v /\ value_has_type ltv v) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 ==> ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
       ptr_buf_ok cenv e p.ptr_operand G s) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q dw v z G' tn' sw.
    buf.buf_operand = Var q /\
    read_result cx tv ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z) /\
    ghost_kept_at lo cenv es sa Gi ti s0 G' tn' /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
         FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP z.vs_allocas aid = SOME entry) /\
    alloca_history func z /\ allocas_from lo z /\ lo <= z.vs_alloca_next /\
    s.vs_alloca_next <= z.vs_alloca_next /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    z.vs_alloca_next < dimword (:256) /\
    z.vs_labels = s.vs_labels /\ ~z.vs_halted /\
    z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    not_fresh_at sc q /\ lookup_var q z = SOME dw /\
    ptr_covers G' tn' q z (type_memory_size ltv) /\
    FLOOKUP z.vs_allocas sm.cs_next_id = SOME (w2n dw,type_memory_size ltv) /\
    FLOOKUP G' q = SOME (w2n dw,type_memory_size ltv) /\
    MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size ltv))] [q])
        (fn_insts func) /\
    w2n dw + type_memory_size ltv <= z.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes z name b len ==>
       regions_disjoint (w2n dw) (type_memory_size ltv) b len) /\
    eval_operand op z = SOME sw /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    ptr_mem_ok cx (post_value_type cenv e) v op G' tn' z /\
    value_has_type ltv v /\ val_wf ltv v /\
    (!mem. mem_agree_outside tn'.t_mem z.vs_memory mem ==>
         val_in_memory ltv v (w2n sw) mem) /\
    (type_memory_size ltv <> 0 ==>
       (?x. op = Var x /\ ptr_covers G' tn' x z (type_memory_size ltv)) /\
       w2n sw + type_memory_size ltv <= z.vs_alloca_next) /\
    (val_footprint ptv v = 0 \/
     regions_disjoint (w2n dw) (type_memory_size ltv) (w2n sw) (val_footprint ptv v))``;

val prefix_alloc_law = ctorCopyObservationLib.close_except
  ["R","ctx","func","sm","sn","buf","explicit","PG"]
  (ctorCopyObservationLib.observe "s" "u" NONE (concl extcall_default_alloc_cut));
val prefix_unwrap_law = fst (dest_imp (snd (dest_imp
  (concl extcall_default_unwrap_store_entry_observed))));
val (default_prefix_pre,default_prefix_post_observed) = dest_imp
  (ctorCopyObservationLib.observe "s" "z" NONE default_prefix_entry);

Theorem extcall_default_prefix_store_entry_observed:
  ^default_prefix_pre ==>
  ^prefix_alloc_law ==> ^prefix_unwrap_law ==>
  (!p q r. R p q /\ R q r ==> R p r) ==>
  ^default_prefix_post_observed
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_alloc_buffer (type_memory_size ltv) sm = (buf,sn)` by
    (qpat_assum `type_memory_bytes cenv (lowered_value_type cenv e) = _`
       (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id < sn.cs_next_id` by
    (drule abi_builtin_alloc_buffer_shape >> simp[emit_op_eq] >> strip_tac >> gvs[]) >>
  disch_then drule_all >>
  disch_then (qx_choosel_then [`q`,`dw`,`u`,`Ga`,`ta`]
    (map_every assume_tac o CONJUNCTS)) >>
  `vv_post (storage_trace_horizon ee.storage_trace)
       ctx func cenv cx e es sa sm s0 ee tv vv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     (impl_tac >- fs[storage_trace_domain_def]) >> simp[]) >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[]) >>
  disch_then (mk_asm "unwrap") >>
  mp_tac (Q.INST [`n` |-> `type_memory_size ltv`]
    extcall_default_unwrap_store_entry_observed) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  asm_x "unwrap" (fn law => disch_then (mp_tac o C MATCH_MP law)) >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`,`sw`]
    (map_every assume_tac o CONJUNCTS)) >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at sn x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x z = _ /\ _`
       (qspec_then `x` (strip_assume_tac o UNDISCH)) >> simp[]) >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP z.vs_allocas aid = SOME entry` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME entry` by simp[] >>
     qpat_assum `wb_frame cenv ee ee sn u z`
       (mp_tac o MATCH_MP (cj 2 (iffLR wb_frame_def))) >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `s.vs_alloca_next <= z.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size ltv))] [q])
       (fn_insts func)` by
    (`stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee s` by
       (qpat_assum `vv_post _ ctx func cenv cx e es sa sm s0 ee tv vv s`
          (mp_tac o MATCH_MP (cj 1 (iffLR vv_post_def))) >> simp[]) >>
     drule_all compile_alloc_buffer_raw_step >> simp[] >> strip_tac >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,G',tn') /\
       expr_post H ctx func cenv cx e es sa sc s0 ee v op z /\
       ghost_inv_at (DF H) lo d cenv cx ee G' tn' z` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (u,Ga,ta) _ _ /\ _`
       (qspec_then `H` (strip_assume_tac o UNDISCH)) >> simp[] >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Ga,ta)`
       (qspec_then `DF H` (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`u`,`Ga`,`ta`,`[]`,`OK z`,`G'`,`tn'`] mp_tac) >> simp[]) >>
  disch_tac >> qexistsl [`q`, `dw`, `v`, `z`, `G'`, `tn'`, `sw`] >>
  conj_tac >- (first_x_assum irule >> qexists_tac `u` >> simp[]) >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem extcall_default_prefix_store_entry:
  ^default_prefix_entry
Proof
  disch_then (mp_tac o MATCH_MP
    (Q.INST [`R` |-> `\p q. T`] extcall_default_prefix_store_entry_observed)) >>
  BETA_TAC >> REWRITE_TAC [] >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC extcall_default_alloc_cut)) >>
  (impl_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC bodyFullUnwrapTheory.unwrap_value_origin_ptr)) >>
  disch_then ACCEPT_TAC
QED
