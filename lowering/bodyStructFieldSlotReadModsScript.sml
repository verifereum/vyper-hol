(* Materialize a linked StructLit field from storage or transient storage.
   The scratch allocation belongs to the post-ADD cursor, not the VV cursor. *)
Theory bodyStructFieldSlotReadMods
Ancestors
  bodyPtrMakeArrayMemoryFrame bodyCopySlotRhsEndpointMods bodyCopyMaterializedRhsPostMods
  appendStorageGhostPtr exprSimUnwrap
  bodyFullPostsMods allocLimits bodyFullShadowBodyInv bodyPtrDefs exprSimStorageCopy
  bodyCopyReadPhysicalTypeMods exprPtrUnwrapStorageShape exprOperandVar
  exprLoweringProps exprSimHyps exprSimHypsDefs exprSimFullBundleProps
  stateRelProj wordArgsPtr exprSimWordArgs exprSimProps valueTypingMemoryProps
  loweringPosts loweringStateRelDefs freshWrites fragGasOriginPtr
  allocaSiteResource vyperTypeArgFits vyperStorageFootprint
  vyperEvalExprPreservesScopesDom representationCleanPtr abiDecodeStaticProps
  vyperInterpreter vyperState venomState venomInst context finite_map words list arithmetic

Theorem slot_field_layout_at_read[local]:
  compile_expr ce ty e si = (LocatedValue tag p,sm) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  vv_post_mods H ctx func ce cx e es si sn entry ee tv (LocatedValue tag p) s ==>
  ?v rt. read_result cx tv ee = (INL v,ee) /\
    lowered_value_type ce e = expr_type e /\ post_value_type ce e = expr_type e /\
    tag = expr_type e /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
    type_memory_bytes ce (expr_type e) = type_memory_size rt /\
    type_memory_size rt < 2 ** 64 /\ value_has_type rt v /\ val_wf rt v
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac compile_storage_lowered_value_type >>
  drule_then assume_tac post_value_type_lowered >>
  `tag = expr_type e /\ ?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[vv_post_mods_def, vv_holds_mods_def, vv_holds_def, storage_holds_def] >>
     metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all copy_read_physical_type_gas_obs_mods >> strip_tac >>
  `alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
  drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def] >> strip_tac >>
  qexists `rt` >>
  qpat_assum `lowered_value_type ce e = _` (fn th => fs[th,value_has_type_memory_wf])
QED

(* The slot reader uses one scratch site; expose its linked posts and physical
   write window at the same endpoint as the arbitrary-dead-set counted path. *)
Theorem slot_field_read_endpoint[local]:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_expr ce ty e si = (LocatedValue tag p,sm) /\
  unwrap_value ce (LocatedValue tag p) sn = (op,su) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sn su func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce si /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si sn entry ee tv (LocatedValue tag p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue tag p) ee G tn s /\
  ghost_kept_at lo ce es si Gi ti entry G tn /\
  ~s.vs_halted /\ expr_sim_full_endpoint func sn entry s ==>
  ?v z Gf tf rt w scratch.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es si su entry ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es si Gi ti entry Gf tf /\
    wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
    ~z.vs_halted /\ expr_sim_full_endpoint func su s z /\
    sn.cs_next_id < su.cs_next_id /\ sn.cs_next_var < su.cs_next_var /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    lowered_value_type ce e = expr_type e /\
    value_has_type rt v /\ val_wf rt v /\
    op = Var scratch /\ not_fresh_at su scratch /\
    eval_operand op z = SOME w /\ ptr_covers Gf tf scratch z (type_memory_size rt) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!aid b len. aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size rt) b len) /\
    pure_frame ce func ee sn s z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac slot_field_layout_at_read >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `si.cs_next_id <= sn.cs_next_id /\ si.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists `si` >> asm_rewrite_tac[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by
    (drule (cj 1 compiler_compile_var) >> simp[vv_operand_def] >>
     metis_tac[not_fresh_at_mono]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_then strip_assume_tac expr_sim_full_endpoint_fields >>
  mp_tac (Q.INST [`t` |-> `tag`,`sc` |-> `su`,`sm` |-> `sn`,
                 `sa` |-> `si`,`entry` |-> `entry`, `explicit` |-> `explicit`,
                 `PG` |-> `PG`] copy_slot_rhs_endpoint_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choosel_then [`scratch`,`w`,`mid`,`buf`,`u`,`z`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "post"
QED

Resume slot_field_read_endpoint[post]:
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es si su entry ee v op z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
    ghost_kept_at lo ce es si Gi ti entry Gf tf /\
    FLOOKUP z.vs_allocas sn.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    not_fresh_at su scratch /\
    wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_x_assum `op = Var scratch` SUBST_ALL_TAC >>
     mp_tac (Q.INST [`D` |-> `DF H`, `nb` |-> `type_memory_size rt`,
                    `sa` |-> `si`, `sm` |-> `sn`, `sb` |-> `su`,
                    `H` |-> `H`, `s0` |-> `entry`, `root` |-> `scratch`,
                    `vv` |-> `LocatedValue tag p`]
       (INST_TYPE [alpha |-> ``:256``] copy_materialized_rhs_post_mods)) >>
     asm_rewrite_tac[LESS_EQ_REFL] >> strip_tac >> asm_rewrite_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `pure_frame ce func ee sn s z` by
    (irule pure_frame_fresh_alloca >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
         qpat_assum `!name b len. local_region ce ee.scopes s name b len ==> _`
           (drule_then ACCEPT_TAC)) >>
     qexistsl [`w2n w`,`sn.cs_next_id`,`[Lit (n2w (type_memory_size rt))]`,
               `[scratch]`,`type_memory_size rt`] >>
     asm_rewrite_tac[LESS_EQ_REFL] >> simp[regions_disjoint_def] >>
     rpt strip_tac >> qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
     decide_tac) >>
  qpat_x_assum `op = Var scratch` SUBST_ALL_TAC >>
  qpat_x_assum `scratch = STRING _ _` kall_tac >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`rt`,`w`,`scratch`] >>
  asm_rewrite_tac[expr_sim_full_endpoint_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED

Finalise slot_field_read_endpoint[local]

Theorem slot_field_prefix_cells[local]:
  literal_prefix_ok cells tn s /\
  EVERY (\(tv,v,p,k). addr <= p /\ p+k <= addr+off) cells /\ off <= cap /\
  mem_bytes_at addr cap z.vs_memory = mem_bytes_at addr cap s.vs_memory /\
  (!i. addr <= i /\ i < addr+cap /\ i IN tf.t_mem ==> i IN tn.t_mem) ==>
  literal_prefix_ok cells tf z
Proof
  strip_tac >> irule literal_prefix_transport >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac literal_prefix_lookup >>
  `addr <= p /\ p+k <= addr+off` by
    (qpat_assum `EVERY _ cells`
       (qspec_then `(tv,v,p,k)` mp_tac o REWRITE_RULE[EVERY_MEM]) >> simp[]) >>
  `mem_bytes_at p k z.vs_memory = mem_bytes_at p k s.vs_memory` by
    (irule mem_bytes_at_bytewise >> rpt strip_tac >>
     irule mem_bytes_at_eq_byte >> qexistsl [`addr`,`cap`] >> simp[] >> decide_tac) >>
  gen_tac >> disch_tac >> irule robust_val_in_memory_shrinking_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`tn.t_mem`,`tf.t_mem`,`s.vs_memory`,`z.vs_memory`,`k`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem slot_field_old_result_frame[local]:
  wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
  aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (addr,cap) /\
  (!name b n. local_region ce ee.scopes s name b n ==> addr+cap <= b \/ b+n <= addr) ==>
  mem_bytes_at addr cap z.vs_memory = mem_bytes_at addr cap s.vs_memory /\
  (!i. addr <= i /\ i < addr+cap /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  simp[wb_frame_def,ghost_kept_at_def] >> strip_tac >> conj_tac
  >- (qpat_assum `!a off sz. _ ==> mem_bytes_at off sz _ = _`
        (qspecl_then [`aid`,`addr`,`cap`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!a off sz i. _ ==> i IN tn.t_mem`
    (qspecl_then [`aid`,`addr`,`cap`,`i`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC
QED

Theorem struct_field_slot_read_mods:
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  compile_expr ce ty e si = (LocatedValue tag p,sm) /\
  unwrap_value ce (LocatedValue tag p) sn = (op,su) /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id /\
  fn_has_code sn su func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce si /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at si x) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es si sn entry ee tv (LocatedValue tag p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue tag p) ee G tn s /\
  ghost_kept_at lo ce es si Gi ti entry G tn /\
  ~s.vs_halted /\ expr_sim_full_endpoint func sn entry s /\
  aid < sn.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (addr,cap) /\
  (!name b n. local_region ce ee.scopes s name b n ==> addr+cap <= b \/ b+n <= addr) /\
  EVERY (\(tv,v,b,n). addr <= b /\ b+n <= addr+cap) cells /\ literal_prefix_ok cells tn s /\
  not_fresh_at sn root /\ ptr_covers G tn root s cap /\
  not_fresh_at sn dst /\ ptr_covers G tn dst s field_size ==>
  ?v z Gf tf rt w.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es si su entry ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es si Gi ti entry Gf tf /\
    ~z.vs_halted /\ expr_sim_full_endpoint func su s z /\
    cs_extends sn su /\ sn.cs_next_id < su.cs_next_id /\
    ~is_word_type (lowered_value_type ce e) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    lowered_value_type ce e = expr_type e /\ value_has_type rt v /\ val_wf rt v /\
    eval_operand op z = SOME w /\ op_taint tf op = {} /\
    (?scratch. op = Var scratch /\ not_fresh_at su scratch /\
      ptr_covers Gf tf scratch z (type_memory_size rt)) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    w2n w + type_memory_size rt <= z.vs_alloca_next /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (w2n w + val_footprint rt v <= addr \/ addr+cap <= w2n w) /\
    wb_frame ce ee ee sn s z /\ ghost_kept_at lo ce ee sn G tn s Gf tf /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!old b. FLOOKUP s.vs_allocas old = SOME b ==> FLOOKUP z.vs_allocas old = SOME b) /\
    literal_prefix_ok cells tf z /\ ptr_covers Gf tf root z cap /\
    ptr_covers Gf tf dst z field_size /\ pure_frame ce func ee sn s z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac unwrap_value_extends >>
  mp_tac slot_field_read_endpoint >>
  asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`v`,`z`,`Gf`,`tf`,`rt`,`w`,`scratch`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then strip_assume_tac slot_field_old_result_frame >>
  `literal_prefix_ok cells tf z` by
    (irule slot_field_prefix_cells >> qexistsl [`addr`,`cap`,`cap`,`s`,`tn`] >> simp[]) >>
  `w2n w + val_footprint rt v <= addr \/ addr+cap <= w2n w` by
    (qpat_assum `!a b len. _ ==> regions_disjoint _ _ b len`
       (qspecl_then [`aid`,`addr`,`cap`] mp_tac) >> simp[regions_disjoint_def] >>
     `val_footprint rt v <= type_memory_size rt` by simp[val_footprint_le] >> decide_tac) >>
  `ptr_covers Gf tf root z cap /\ ptr_covers Gf tf dst z field_size` by
    (conj_tac >> irule ptr_covers_old_transport >> qexistsl [`G`,`s`,`sn`,`tn`] >>
     simp[] >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `op_taint tf op = {}` by
    (qpat_assum `op = Var scratch` SUBST1_TAC >>
     qpat_assum `ptr_covers Gf tf scratch z _`
       (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ptr_covers_def])) >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`rt`,`w`] >> asm_rewrite_tac[] >>
  qexists_tac `scratch` >> asm_rewrite_tac[]
QED
