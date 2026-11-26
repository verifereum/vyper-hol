(* Materialize the selected nonword arm at the actual unwrap cursor k.
   The earlier expression compilation ends at sm; a widening destination
   can already have been allocated between sm and k. *)
Theory bodyIfExpArmUnwrapMods
Ancestors
  bodyCopyMaterializedRhsPostMods bodyCopySlotRhsEndpointMods
  bodyCopyRuntimeRhsRunMods bodyCopyCtorRhsRunMods bodyLocalCopyPhysicalRhsMods
  bodyCopyReadPhysicalTypeMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyPtrAttributeSource exprSimAttribute exprPtrUnwrapStorageShape exprSimCopy
  exprOperandVar exprLoweringProps fragExec freshWrites stateRelProj
  exprBodyPreProps exprBodyPreTypingProps allocLimits typedMemoryCopy
  valueTypingMemoryProps bodyPtrIfExpCopyInputs exprSimMemorySource valueCopyBytes
  loweringPosts ptrDiscipline bodyPtrDefs fragGasOriginPtr exprSimWordArgs
  bodyFullHashKeccakFixed exprLowering compileEnv exprSimHyps exprSimHypsDefs
  exprSimStorageCopy
  vyperEvalExprPreservesScopesDom vyperStorageFootprint
  vyperInterpreter vyperState venomState context words finite_map arithmetic

(* At a valid horizon the raw linked post witnesses the actual source read,
   including when its location is code belonging to an imported module. *)
Theorem ifexp_raw_post_read[local]:
  vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv s ==>
  ?v. read_result cx tv ee = (INL v,ee)
Proof
  simp[vv_post_mods_def] >> strip_tac >> Cases_on `vv`
  >- fs[vv_holds_mods_def,vv_holds_def] >>
  rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
  >- fs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  fs[vv_holds_mods_def] >> drule_then strip_assume_tac attribute_vv_holds_read_operand >> simp[]
QED

Theorem ifexp_located_tag[local]:
  vv_post_mods H ctx func ce cx e es sa k s0 ee tv (LocatedValue tag p) s ==>
  p.ptr_location <> LocCalldata /\
  (tag = post_value_type ce e \/
   p.ptr_location = LocMemory /\ is_bytestring_type tag /\
   is_bytestring_type (post_value_type ce e))
Proof
  simp[vv_post_mods_def,vv_holds_mods_def,vv_holds_def] >>
  Cases_on `p.ptr_location` >> simp[] >> metis_tac[]
QED

Theorem ifexp_immutable_nonwrap[local]:
  immutable_holds ce cx tag tv w ee s /\
  evaluate_type (get_tenv cx) tag = SOME rt ==>
  w2n w + type_memory_size rt < dimword (:256)
Proof
  rw[immutable_holds_def,sub_layout_def] >>
  `off + k < dimword (:256)` by decide_tac >>
  `rt = tvt` by fs[] >>
  simp[w2n_n2w,LESS_MOD] >> decide_tac
QED

val entry = ``
  compile_expr ce ty e sa = (vv,sm) /\
  unwrap_value ce vv k = (op,sb) /\
  sm.cs_next_var <= k.cs_next_var /\ sm.cs_next_id <= k.cs_next_id /\
  fn_has_code k sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!tag x. vv = StackValue tag x ==> ptr_buf_ok ce e x G s) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory rt v (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = k.cs_current_bb /\
  s.vs_inst_idx = LENGTH k.cs_current_insts /\ alloca_history func s``;

val result = ``
  ?v z Gf tf pt rt w.
    read_result cx tv ee = (INL v,ee) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx e es sa sb s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\
    ptr_buf_ok ce e op Gf z /\ expr_store_bound cx (post_value_type ce e) v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\ s.vs_alloca_next <= z.vs_alloca_next /\
    ~is_word_type (post_value_type ce e) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
    eval_operand op z = SOME w /\ op_taint tf op = {} /\
    (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= z.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (0 < type_memory_size rt ==>
      ?r. op = Var r /\ not_fresh_at sb r /\ ptr_covers Gf tf r z (type_memory_size rt)) /\
    (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
    (!x cap. not_fresh_at k x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap) /\
    wb_frame ce ee ee k s z /\ ghost_kept_at lo ce ee k G tn s Gf tf /\
    ((sb = k /\ z = s /\ Gf = G /\ tf = tn /\ op = vv_operand vv /\
      vv_at ce cx (post_value_type ce e) sa k ee tv
        (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) s /\
      (!id path. tv = PlaceR (MemoryPlace id path) ==>
        vv_place_ptr ce cx ee s tv
          (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)))) \/
     (k.cs_next_id < sb.cs_next_id /\ post_value_type ce e = lowered_value_type ce e /\
      FLOOKUP z.vs_allocas k.cs_next_id = SOME (w2n w,type_memory_size rt) /\
      lo <= w2n w /\ (!id path. tv <> PlaceR (MemoryPlace id path)) /\
      (!aid b len. aid < k.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size rt) b len)))``;

Theorem ifexp_identity_raw_location[local]:
  vv_post_mods H ctx func ce cx e es sa k s0 ee tv vv s /\
  ~is_word_type (post_value_type ce e) /\
  ((?tag. vv = StackValue tag op) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\ p.ptr_operand = op)) ==>
  vv_at ce cx (post_value_type ce e) sa k ee tv
    (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)) s /\
  (!id path. tv = PlaceR (MemoryPlace id path) ==>
    vv_place_ptr ce cx ee s tv
      (LocatedValue (post_value_type ce e) (mk_ptr op LocMemory)))
Proof
  simp[vv_post_mods_def] >> strip_tac >>
  (conj_tac
   >- (gvs[vv_at_def,mk_ptr_def,expr_val_at_def] >>
       rpt strip_tac >> first_x_assum drule >> simp[local_place_at_def] >>
       metis_tac[])) >>
  rpt gen_tac >> strip_tac >>
  gvs[vv_at_def,vv_place_ptr_mods_def,vv_place_ptr_def,mk_ptr_def]
QED

Theorem ifexp_identity_physical[local]:
  expr_post_mods H ctx func ce cx e es sa k s0 ee v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type rt v ==>
  ?w. eval_operand op s = SOME w /\ op_taint tn op = {} /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem
Proof
  strip_tac >>
  `?w. eval_operand op s = SOME w` by fs[expr_post_mods_def,expr_post_def,expr_val_rel_def] >>
  qexists `w` >>
  `op_taint tn op = {} /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory pt v (w2n w) mem)` by
    fs[ptr_val_ok_def,ptr_mem_ok_def] >> simp[] >> rpt strip_tac >>
  metis_tac[bytestring_val_in_memory_transfer,optionTheory.SOME_11]
QED

val identity_shape = ``
  ((?tag. vv = StackValue tag op) \/
   (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory /\
      ~is_word_type tag /\ p.ptr_operand = op))``;

val typed_read = ``
  read_result cx tv ee = (INL v,ee) /\
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  value_has_type pt v /\ value_has_type rt v /\ val_wf rt v``;

Theorem ifexp_identity_cut:
  ^entry /\ ^typed_read /\ ^identity_shape /\ op = vv_operand vv /\
  ptr_buf_ok ce e op G s ==> ^result
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sb s0 ee v op s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (drule_then strip_assume_tac) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule (cj 3 (REWRITE_RULE [IMP_CONJ_THM] local_copy_rhs_identity_unwrap_mods)) >>
     asm_rewrite_tac[] >> qexistsl [`G`,`k`,`tn`,`tv`,`vv`] >>
     qpat_x_assum `op = vv_operand vv` SUBST_ALL_TAC >> asm_rewrite_tac[]) >>
  drule_all local_copy_rhs_identity_unwrap_mods >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `sb = k` SUBST_ALL_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac ifexp_identity_physical >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
    fs[expr_post_mods_def,expr_post_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  qpat_assum `!r y. evaluate_type _ (lowered_value_type ce e) = SOME r /\ _ ==> _`
    (drule_all_then assume_tac) >>
  `w2n w + type_memory_size rt < dimword (:256)` by
    (Cases_on `type_memory_size rt = 0` >- simp[w2n_lt] >> decide_tac) >>
  qexistsl [`v`,`s`,`G`,`tn`,`pt`,`rt`,`w`] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  simp[cj 1 gas_origin_ptr_path_rules,wb_frame_refl,wordArgsPtrTheory.ghost_kept_at_refl] >>
  conj_tac >- suspend "cover" >>
  suspend "location"
QED

Resume ifexp_identity_cut[cover]:
  strip_tac >>
  `type_memory_size rt <= type_memory_bytes ce (lowered_value_type ce e)` by simp[] >>
  drule_all ptr_buf_ok_read_covers >> strip_tac >>
  qexists `p` >> simp[] >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
  metis_tac[not_fresh_at_mono]
QED

Resume ifexp_identity_cut[location]:
  qpat_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any (qspec_then `op` mp_tac) ifexp_identity_raw_location) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >> simp[]
QED

Finalise ifexp_identity_cut[local]

(* These are projections of one physical run, not a second allocation or
   a second copy. In particular the literal ALLOCA witness is what lets the
   linked post theorem transfer allocation separation for every owner. *)
val copy_resources = ``
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf)) /\
  ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func z /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  k.cs_next_id < sb.cs_next_id /\ k.cs_next_var < sb.cs_next_var /\
  w2n w + type_memory_size rt < dimword (:256) /\
  root = STRING #"%" (toString k.cs_next_var) /\
  MEM (mk_inst k.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
  exec_alloca (mk_inst k.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root])
    s (n2w (type_memory_size rt) : bytes32) = OK u /\
  FLOOKUP u.vs_allocas k.cs_next_id = SOME (w2n w,type_memory_size rt) /\
  copy_static z = copy_static u /\ LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP z.vs_allocas aid = SOME b) /\
  (!aid b len. aid < k.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n w) (type_memory_size rt) b len) /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size rt <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!j. j < w2n w \/ w2n w+type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem) /\
  z.vs_accounts = s.vs_accounts /\ z.vs_transient = s.vs_transient /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_immutables = s.vs_immutables /\
  z.vs_data_section = s.vs_data_section /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  eval_operand op z = SOME w /\ op = Var root /\ ptr_covers Gf tf root z (type_memory_size rt) /\
  (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n w) mem)``;

Theorem ifexp_materialized_cut[local]:
  ^entry /\ ^typed_read /\ ^copy_resources /\
  post_value_type ce e = lowered_value_type ce e /\
  (!id path. tv <> PlaceR (MemoryPlace id path)) ==> ^result
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac (cj 1 compile_expr_grows) >>
  `sa.cs_next_id <= k.cs_next_id /\ sa.cs_next_var <= k.cs_next_var` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `pt = rt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `pt = rt` SUBST_ALL_TAC >>
  `type_memory_size rt < dimword (:256)` by decide_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func ce cx e es sa sb s0 ee v op z /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z /\
    ghost_kept_at lo ce es sa Gi ti s0 Gf tf /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\ ptr_buf_ok ce e op Gf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\
    FLOOKUP z.vs_allocas k.cs_next_id = SOME (w2n w,type_memory_size rt) /\
    lo <= w2n w /\ w2n w + type_memory_size rt <= z.vs_alloca_next /\ not_fresh_at sb root /\
    wb_frame ce ee ee k s z /\ ghost_kept_at lo ce ee k G tn s Gf tf /\
    (!x cap. not_fresh_at k x /\ ptr_covers G tn x s cap ==> ptr_covers Gf tf x z cap)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
     qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
     match_mp_tac (Q.INST [`nb` |-> `type_memory_size rt`, `sm` |-> `k`]
       copy_materialized_rhs_post_mods) >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee z` by
    fs[expr_post_mods_def,expr_post_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  `op_taint tf op = {}` by
    (qpat_assum `op = Var root` SUBST1_TAC >>
     qpat_assum `ptr_covers Gf tf root z _`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >> simp[NoAsms]) >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qpat_x_assum `op = Var root` SUBST_ALL_TAC >>
  qexistsl [`v`,`z`,`Gf`,`tf`,`rt`,`rt`,`w`] >>
  asm_rewrite_tac[] >> simp[]
QED

Theorem ifexp_arm_nonword_unwrap_mods:
  ^entry ==> ^result
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac ifexp_raw_post_read >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by simp[bind_def] >>
  drule_all copy_read_physical_type_gas_obs_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`pt`,`rt`] strip_assume_tac))) >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue tag p` >>
  drule_then (CONJUNCTS_THEN2 assume_tac assume_tac) ifexp_located_tag >>
  `~is_word_type tag` by metis_tac[is_bytestring_word_type] >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >>
  suspend "copy"
QED

Resume ifexp_arm_nonword_unwrap_mods[stack]:
  rename1 `unwrap_value ce (StackValue tag src) k = (op,sb)` >>
  `src = op` by fs[unwrap_value_def,comp_return_def] >>
  qpat_x_assum `src = op` SUBST_ALL_TAC >>
  match_mp_tac (Q.INST [`vv` |-> `StackValue tag op`] ifexp_identity_cut) >>
  asm_rewrite_tac[] >> simp[vv_operand_def]
QED

Resume ifexp_arm_nonword_unwrap_mods[memory]:
  `p.ptr_operand = op` by fs[unwrap_value_def,comp_return_def] >>
  match_mp_tac (Q.INST [`vv` |-> `LocatedValue tag p`] ifexp_identity_cut) >>
  asm_rewrite_tac[] >> simp[vv_operand_def] >>
  qpat_assum `!tag' p'. LocatedValue tag p = LocatedValue tag' p' /\ _ ==> _`
    (qspecl_then [`tag`,`p`] mp_tac) >> gvs[]
QED

Resume ifexp_arm_nonword_unwrap_mods[copy]:
  `tag = post_value_type ce e` by metis_tac[] >>
  `lowered_value_type ce e = expr_type e` by
    (drule_all compile_nonmemory_lowered_value_type >> simp[]) >>
  `post_value_type ce e = lowered_value_type ce e` by
    simp[post_value_type_lowered] >>
  `pt = rt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `pt = rt` SUBST_ALL_TAC >>
  `type_memory_bytes ce tag = type_memory_size rt` by metis_tac[] >>
  `type_memory_size rt < 2 ** 64` by
    (`alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce k` by
    (drule (cj 1 compile_expr_grows) >> strip_tac >>
     irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[] >> decide_tac) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at k x` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[vv_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  `!id path. tv <> PlaceR (MemoryPlace id path)` by
    (qpat_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >> fs[vv_at_def]) >>
  `?z Gf tf root w u. ^copy_resources` suffices_by
    (disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`]
       (map_every assume_tac o CONJUNCTS)) >>
     match_mp_tac (Q.INST [`vv` |-> `LocatedValue tag p`,`pt` |-> `rt`]
       ifexp_materialized_cut) >> asm_rewrite_tac[]) >>
  Cases_on `p.ptr_location = LocCode`
  >- (
    `ce.ce_is_ctor ==> ?val. read_result cx tv ee = (INL val,ee) /\
      !t w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME t /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size t <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory t val (w2n w) mem)` by
      (qpat_assum `ce.ce_is_ctor /\ vv_location _ = _ ==> _` mp_tac >>
       pure_rewrite_tac[vv_location_def,vv_operand_def] >> asm_rewrite_tac[]) >>
    qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
      (mp_then Any mp_tac local_copy_raw_code_source_mods) >>
    disch_then (qspecl_then [`v`,`tn`,`rt`,`lo`,`G`] mp_tac) >>
    (impl_tac >- asm_rewrite_tac[]) >>
    disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac
        (qx_choosel_then [`owner`,`tops`,`src`] (map_every assume_tac o CONJUNCTS))))) >>
    `evaluate_type (get_tenv cx) tag = SOME rt` by metis_tac[] >>
    drule_all_then assume_tac ifexp_immutable_nonwrap >>
    `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee s` by
      fs[vv_post_mods_def] >>
    drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
    Cases_on `ce.ce_is_ctor`
    >- (
      `type_memory_size rt < dimword (:256)` by decide_tac >>
      qpat_assum `ce.ce_is_ctor ==> w2n src + _ <= lo /\ _` (drule_then strip_assume_tac) >>
      drule_all (Q.INST [`sc` |-> `sb`, `sb` |-> `k`] copy_ctor_rhs_endpoint_mods) >>
      disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >>
      disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS)) >>
      `!j. j < w2n w \/ w2n w + type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by
        (rpt gen_tac >> strip_tac >> first_x_assum (drule_then (fn th => simp[th]))) >>
      qexistsl [`z`,`Gf`,`tf`,`root`,`w`,`u`] >> asm_rewrite_tac[]) >>
    `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
    qpat_assum `~ce.ce_is_ctor ==> _ /\ _` (drule_then strip_assume_tac) >>
    drule_all (Q.INST [`sc` |-> `sb`, `sm` |-> `k`] copy_runtime_rhs_endpoint_mods) >>
    disch_then (qspecl_then [`explicit`,`PG`,`G`] mp_tac) >>
    disch_then (qx_choosel_then [`z`,`Gf`,`tf`,`root`,`w`,`u`] (map_every assume_tac o CONJUNCTS)) >>
    `!j. j < w2n w \/ w2n w + type_memory_size rt <= j ==> j IN tf.t_mem ==> j IN tn.t_mem` by simp[] >>
    qexistsl [`z`,`Gf`,`tf`,`root`,`w`,`u`] >> asm_rewrite_tac[]) >>
  `(p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
    ?z Gf tf root w u. ^copy_resources` suffices_by
    (disch_then irule >> Cases_on `p.ptr_location` >> fs[]) >>
  disch_tac >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size rt` by metis_tac[] >>
  mp_tac (Q.INST [`t` |-> `tag`,`sc` |-> `sb`,`sm` |-> `k`,`entry` |-> `s0`]
    copy_slot_rhs_endpoint_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`root`,`w`,`mid`,`buf`,`u`,`z`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`z`,`Gf`,`tf`,`root`,`w`,`u`] >> asm_rewrite_tac[]
QED

Finalise ifexp_arm_nonword_unwrap_mods
