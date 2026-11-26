(* The reason middle uses the physical slot runner only in the slot case. *)
Theory bodyReasonNoncodeUnwrapMods
Ancestors
  bodyFullUnwrapSlotPost exprSimCopy exprOperandVar wordArgsPtr fragGasOriginPtr
  exprSimMemDefs exprSimWordArgs exprSimProps exprLowering loweringPosts loweringStateRelDefs bodyPtrDefs
  valueEncodingProps valueEncodingTyping valueCopyBytes vyperStorageFootprint
  freshWrites context compileEnv ptrDiscipline venomInst venomState venomMemDefs
  arithmetic words finite_map

Theorem reason_noncode_unwrap_normalized_from_slot_run_mods:
  ((?t a. vv = StackValue t a) \/
   (?t p. vv = LocatedValue t p /\
      (p.ptr_location = LocMemory \/ p.ptr_location = LocStorage \/
       p.ptr_location = LocTransient))) /\
  ~is_word_type (post_value_type ce e) /\
  unwrap_value ce vv sb = (op,sc) /\ fn_has_code sb sc func /\
  local_ptrs_reserved ce sb /\ fn_inst_ids_distinct func /\ alloca_history func sh /\
  ~sh.vs_halted /\ sh.vs_current_bb = sb.cs_current_bb /\
  sh.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
  type_memory_size rt < 2**64 /\ read_result cx tv ee = (INL v,ee) /\
  value_has_type rt v /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee sh) /\
  vv_holds ce cx (post_value_type ce e) tv vv ee sh /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv sh /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee Gh tnh sh /\
  allocas_from lo sh /\ lo <= sh.vs_alloca_next /\
  (!t p. vv = LocatedValue t p /\
     (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\ ~is_word_type t /\
     unwrap_value ce (LocatedValue t p) sb = (op,sc) /\ fn_has_code sb sc func /\
     local_ptrs_reserved ce sb /\ fn_inst_ids_distinct func /\ alloca_history func sh /\
     ~sh.vs_halted /\ sh.vs_current_bb = sb.cs_current_bb /\
     sh.vs_inst_idx = LENGTH sb.cs_current_insts /\
     (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
     evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
     type_memory_bytes ce (post_value_type ce e) = type_memory_size rt /\
     type_memory_size rt < 2**64 /\ read_result cx tv ee = (INL v,ee) /\
     storage_trace_domain cx st0 ee.storage_trace /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee sh) /\
     t = post_value_type ce e /\
     (?key. eval_operand p.ptr_operand sh = SOME key /\
        storage_holds cx (p.ptr_location = LocTransient) t tv key ee sh) /\
     allocas_from lo sh /\ lo <= sh.vs_alloca_next /\
     ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue t p) ee Gh tnh sh ==>
     ?root dst mid buf u z Gf tf.
       op = Var root /\ not_fresh_at mid root /\
       compile_alloc_buffer (type_memory_size rt) sb = (buf,mid) /\
       buf.buf_operand = Var root /\ fn_has_code sb mid func /\
       MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_size rt))] [root]) (fn_insts func) /\
       sb.cs_next_var <= mid.cs_next_var /\ sb.cs_next_id < sc.cs_next_id /\
       (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,tnh) [] (OK z,Gf,tf)) /\
       ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\ z.vs_inst_idx = LENGTH sc.cs_current_insts /\
       alloca_history func z /\ sh.vs_alloca_next <= z.vs_alloca_next /\ allocas_from lo z /\
       eval_operand op z = SOME dst /\ ptr_covers Gf tf root z (type_memory_size rt) /\
       lo <= w2n dst /\ w2n dst + type_memory_size rt < dimword (:256) /\
       w2n dst + type_memory_size rt <= z.vs_alloca_next /\
       val_wf rt v /\
       (!mem. mem_agree_outside tf.t_mem z.vs_memory mem ==> val_in_memory rt v (w2n dst) mem) /\
       FLOOKUP u.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
       FLOOKUP z.vs_allocas sb.cs_next_id = SOME (w2n dst,type_memory_size rt) /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u) /\
       u.vs_memory = sh.vs_memory /\ copy_static z = copy_static u /\
       copy_static z = copy_static (buffer_allocation_fields sh sb.cs_next_id (type_memory_size rt)) /\
       (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x sh) /\
       (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
       (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x sh /\
         FLOOKUP Gf x = FLOOKUP Gh x /\ op_taint tf (Var x) = op_taint tnh (Var x)) /\
       (!aid ent. FLOOKUP sh.vs_allocas aid = SOME ent ==>
         FLOOKUP u.vs_allocas aid = SOME ent /\ FLOOKUP z.vs_allocas aid = SOME ent) /\
       (!aid b len. aid < sb.cs_next_id /\ FLOOKUP sh.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
       (!name b len. local_region ce ee.scopes u name b len ==>
         regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
       (!name b len. local_region ce ee.scopes sh name b len ==>
         regions_disjoint (w2n dst) (type_memory_size rt) b len) /\
       LENGTH sh.vs_memory <= LENGTH z.vs_memory /\
       (!off len. off+len <= w2n dst \/ w2n dst+type_memory_size rt <= off ==>
         mem_bytes_at off len z.vs_memory = mem_bytes_at off len sh.vs_memory) /\
       (!i. ~(w2n dst <= i /\ i < w2n dst+type_memory_size rt) /\ i IN tf.t_mem ==> i IN tnh.t_mem) /\
       tf.t_stor = tnh.t_stor /\ tf.t_trans = tnh.t_trans /\ tf.t_imm = tnh.t_imm) ==>
  ?z Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sh,Gh,tnh) [] (OK z,Gf,tf)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z) /\
    wb_frame ce ee ee sb sh z /\ ghost_kept_at lo ce ee sb Gh tnh sh Gf tf /\
    (!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x sh) /\
    (!x n. not_fresh_at sb x /\ ptr_covers Gh tnh x sh n ==> ptr_covers Gf tf x z n) /\
    expr_val_rel cx (post_value_type ce e) v op z /\
    ptr_val_ok cx (post_value_type ce e) v op Gf tf z /\
    expr_store_bound cx (post_value_type ce e) v op z /\ val_wf rt v /\
    (!x. op = Var x ==> not_fresh_at sc x) /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
    allocas_from lo z /\ sh.vs_alloca_next <= z.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (drule compiler_unwrap_value_var >> Cases_on `vv` >> fs[vv_operand_def]) >>
  `val_wf rt v` by (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
    first_assum ACCEPT_TAC) >>
  Cases_on `vv`
  >- suspend "stack" >> suspend "located"
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[stack]:
  qpat_x_assum `!t p. _` kall_tac >>
  gvs[unwrap_value_def, comp_return_def, vv_holds_def, ptr_vv_ok_def] >>
  qexistsl_tac [`sh`,`Gh`,`tnh`] >>
  simp[cj 1 gas_origin_ptr_path_rules, wb_frame_refl, ghost_kept_at_refl] >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, expr_store_bound_def]
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[located]:
  rename1 `unwrap_value ce (LocatedValue t p) sb = _` >>
  qpat_x_assum `(?t a. _ = StackValue t a) \/ _` mp_tac >>
  simp[] >> disch_tac >>
  Cases_on `p.ptr_location = LocMemory`
  >- suspend "memory" >> suspend "slot"
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[memory]:
  qpat_x_assum `!t p. _` kall_tac >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `w` strip_assume_tac)) >>
  `~is_word_type t` by metis_tac[is_bytestring_word_type] >>
  gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def] >>
  qexistsl_tac [`sh`,`Gh`,`tnh`] >>
  simp[cj 1 gas_origin_ptr_path_rules, wb_frame_refl, ghost_kept_at_refl, ptr_val_ok_def] >>
  rpt conj_tac >>
  FIRST [rename1 `expr_val_rel _ _ _ _ _` >> simp[expr_val_rel_def] >> qexists_tac `w` >> simp[],
    qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
    simp[vv_store_bound_def, expr_store_bound_def]]
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[slot]:
  qpat_assum `p.ptr_location <> LocMemory` (fn nh =>
    qpat_x_assum `p.ptr_location = LocMemory \/ _`
      (assume_tac o SIMP_RULE (srw_ss()) [nh])) >>
  `t = post_value_type ce e /\
   (?key. eval_operand p.ptr_operand sh = SOME key /\
      storage_holds cx (p.ptr_location = LocTransient) t tv key ee sh)` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `p.ptr_location = LocStorage \/ _` strip_assume_tac >>
     simp[vv_holds_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sb x` by fs[vv_operand_def] >>
  `~is_word_type t` by simp[] >>
  qpat_x_assum `!t p. _` (qspecl_then [`t`,`p`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (REFL_TAC >> NO_TAC) >> qexists_tac `key` >> pure_asm_rewrite_tac[] >> simp[NoAsms])) >>
  disch_then (qx_choosel_then [`root`,`dst`,`mid`,`buf`,`u`,`z`,`Gf`,`tf`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "frames"
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[frames]:
  qpat_x_assum `copy_static z = copy_static (buffer_allocation_fields _ _ _)` kall_tac >>
  qabbrev_tac `nb = type_memory_size rt` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee z` by
    (rpt strip_tac >> irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n dst`,`mk_inst sb.cs_next_id ALLOCA [Lit (n2w nb)] [root]`,`u`,`sb`,`nb`] >>
     asm_simp_tac (srw_ss()) [mk_inst_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!name b len. local_region _ _ u name b len ==> _` (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `wb_frame ce ee ee sb sh z` by
    (irule unwrap_slot_copy_wb_frame >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     reverse conj_tac >- (rpt gen_tac >> disch_tac >>
       qpat_assum `!aid ent. FLOOKUP sh.vs_allocas aid = SOME ent ==> _`
         (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
     qexistsl_tac [`nb`,`w2n dst`] >>
     conj_tac >- (rpt gen_tac >> disch_tac >>
       qpat_assum `!name b len. local_region _ _ sh name b len ==> _` (drule_then mp_tac) >>
       simp[loweringStateRelDefsTheory.regions_disjoint_def] >> tautLib.TAUT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!id b len. _ ==> regions_disjoint _ _ _ _` (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> tautLib.TAUT_TAC) >>
  `ghost_kept_at lo ce ee sb Gh tnh sh Gf tf` by suspend "ghost" >>
  suspend "values"
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[ghost]:
  simp[ghost_kept_at_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!id b len. _ ==> regions_disjoint _ _ _ _` (drule_all_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
      qpat_assum `!i. ~(_ <= i /\ _) /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!name b len. local_region _ _ sh name b len ==> _` (drule_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
  qpat_assum `!i. ~(_ <= i /\ _) /\ _ ==> _` irule >> simp[] >> decide_tac
QED

Resume reason_noncode_unwrap_normalized_from_slot_run_mods[values]:
  `val_in_memory rt v (w2n dst) z.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `expr_val_rel cx (post_value_type ce e) v op z` by
    (simp[expr_val_rel_def] >> qexists_tac `dst` >> simp[]) >>
  `val_store_size rt v <= nb` by simp[Abbr `nb`, val_store_size_le] >>
  `expr_store_bound cx (post_value_type ce e) v op z` by
    (simp[expr_store_bound_def] >> decide_tac) >>
  `ptr_val_ok cx (post_value_type ce e) v op Gf tf z` by
    (qpat_assum `ptr_covers Gf tf root z _`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     `lookup_var root z = SOME dst` by
       (qpat_assum `op = Var root` (fn eq =>
          qpat_assum `eval_operand op z = SOME dst`
            (ACCEPT_TAC o REWRITE_RULE [eq, eval_operand_def]))) >>
     `w = dst` by (qpat_x_assum `lookup_var root z = SOME w` mp_tac >> simp[]) >>
     qpat_x_assum `w = dst` SUBST_ALL_TAC >>
     simp[ptr_val_ok_def, ptr_mem_ok_def] >> decide_tac) >>
  qexistsl_tac [`z`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x. not_fresh_at sb x ==> lookup_var x z = lookup_var x sh /\ _`
    (drule_then strip_assume_tac) >> fs[ptr_covers_def]
QED

Finalise reason_noncode_unwrap_normalized_from_slot_run_mods
