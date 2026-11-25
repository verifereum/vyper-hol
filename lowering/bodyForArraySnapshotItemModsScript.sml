(* Reached snapshot element: run the address slice and then the typed copy. *)
Theory bodyForArraySnapshotItemMods
Ancestors
  bodyForArraySnapshotAddressFrameMods bodyForArraySnapshotMemoryCopyMods
  bodyForArraySnapshotQualifiedCopyMods bodyForArraySnapshotFrameMods
  bodyFullForArrayRound bodyFullForFacts bodyAssignNameLinkedSetup bodyInvCodeProps
  bodyFullPathHistory fragGasOriginPtrLoop exprLoweringProps loweringShapeDefs
  exprSimHypsDefs exprSimCopy vyperTypeSystem vyperState vyperStorageFootprint
  bodyForArrayHeaderMods bodyForRangeHeaderMods bodyMemBopRestWordPath
  stateRelProj fragExec compileEnv words arithmetic

Theorem snapshot_copy_posts[local]:
  typed_copy_state_frame saCopy (w2n dw) n u z /\ n <= cap /\
  tf.t_imm = tu.t_imm /\ tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\
  (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tu.t_mem)) /\
  (!x. not_fresh_at saCopy x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
      op_taint tf (Var x) = op_taint tu (Var x)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf)) /\
  (!op. copy_old_operand saAddr op ==> eval_operand op u = eval_operand op s /\
      op_prov Gu op = op_prov G op /\ op_taint tu op = op_taint tn op) /\
  ci_mono saAddr saCopy /\ ci_mono sa saAddr /\ ci_mono saLen saAddr /\
  local_ptrs_reserved c saCopy /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  immutable_frame_mods func c cx ee u /\
  ret_pc_ok c sa u /\ return_buf_frame d c sa u /\ return_buf_sep d c ee u /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gu tu u /\
  for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tu u /\
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) ee Gu tu u /\
  lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func c cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d c cx ee Gu tu u) ==>
  (!op. copy_old_operand saAddr op ==> eval_operand op z = eval_operand op s /\
      op_prov Gf op = op_prov G op /\ op_taint tf op = op_taint tn op) /\
  for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
  for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gf tf z /\
  for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tf z /\
  immutable_frame_mods func c cx ee z /\
  ret_pc_ok c sa z /\ return_buf_frame d c sa z /\ return_buf_sep d c ee z /\
  allocas_from lo z /\ lo <= z.vs_alloca_next /\
  !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf) /\
    stmt_state_rel H ctx func c cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d c cx ee Gf tf z
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  `alloca_inv u` by drule_then ACCEPT_TAC rest_word_state_alloca_inv >>
  `alloca_history func u` by
    fs[for_array_outer_frame_mods_def,bodyForRangeHeaderModsTheory.range_outer_frame_mods_def] >>
  `alloca_history func z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] _` (qspec_then `DF H0` assume_tac) >>
     drule_all_then ACCEPT_TAC body_full_path_alloca_history) >>
  `!x. not_fresh_at sa x ==> not_fresh_at saCopy x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `!x. not_fresh_at saLen x ==> not_fresh_at saCopy x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func c cx ee z /\ immutable_frame_mods func c cx ee z /\
    ghost_inv_at_mods (DF H) lo d c cx ee Gf tf z /\
    ret_pc_ok c sa z /\ return_buf_frame d c sa z /\ return_buf_sep d c ee z /\
    allocas_from lo z /\ lo <= z.vs_alloca_next /\
    for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gf tf z /\
    for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tf z /\
    for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
    (!op. copy_old_operand saCopy op ==> eval_operand op z = eval_operand op u /\
        op_prov Gf op = op_prov Gu op /\ op_taint tf op = op_taint tu op)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     irule for_array_snapshot_frame_mods >>
     qpat_assum `typed_copy_state_frame _ _ _ _ _` (irule_at Any) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `!op. copy_old_operand saAddr op ==> copy_old_operand saCopy op` by
    metis_tac[ci_mono_def,copy_old_operand_mono] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!op. copy_old_operand saAddr op ==> _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!op. copy_old_operand saAddr op ==> copy_old_operand saCopy op`
        (drule_then assume_tac) >>
      qpat_assum `!op. copy_old_operand saCopy op ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  asm_rewrite_tac[] >> gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then strip_assume_tac) >>
  asm_rewrite_tac[] >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED

Theorem for_array_snapshot_item_mods:
  for_nonslot_layout (c,id,typ,e,sty,bd,ret_ty,loop_body) (func,shadow_func)
    (sa,vv,saExpr,shadow_sa,shadow_saExpr,loc,len_op,saLen)
    (bc,saD,saA,xd,cap,inst.inst_id)
    (entry,cond,bod,incr,exit,idx,invalid,valid,dv,next_var)
    (saAddr,stride,off_op,sm,sum_op,sn,addr,saCopy,sbCopy)
    (sbBody,sj,sb,shadow_sbCopy,shadow_sbBody) /\
  contract_inv mods exps ctx c cx /\
  well_typed_iterator env typ (Array e) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV tv bd) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\ a::rs = DROP k vs /\
  (!lbl. vv_operand vv <> Label lbl) /\
  s.vs_inst_idx = LENGTH saAddr.cs_current_insts /\
  lookup_var idx s = SOME (n2w k) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ fn_inst_ids_distinct func /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    for_array_header_mods mods DF lo d ctx func c cx env id st0
      (es0,sa,s0,G0,tn0) (em,saExpr,saLen,q,tq) (xd,dw,cap,inst.inst_id)
      vs (vv_operand vv,bw,len_op,idx) bod (\_ _ _ _ _ _. T) H (a::rs) ee G tn s) /\
  ((loc = LocMemory /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) m) /\
    ptr_mem_ok cx (ArrayT typ bd) (ArrayV av) (vv_operand vv) Gq tq q /\
    eval_operand (vv_operand vv) q = SOME bw /\
    op_prov G (vv_operand vv) = op_prov Gq (vv_operand vv) /\
    (0 < type_memory_size (ArrayTV tv bd) ==>
      (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
         aid < saExpr.cs_next_id /\ b <= w2n bw /\
         w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz) \/
      (?name b sz. local_region c ee.scopes s name b sz /\ b <= w2n bw /\
         w2n bw + type_memory_size (ArrayTV tv bd) <= b + sz))) \/
   (loc = LocCode /\ op_prov G (vv_operand vv) = NONE /\
    w2n bw + type_memory_size (ArrayTV tv bd) < dimword (:256) /\
    (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo /\
      !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) m) /\
    (~c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= LENGTH s.vs_data_section /\
      val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) s.vs_data_section))) ==>
  ?v z Gf tf.
    read_result cx a ee = (INL v,ee) /\ value_has_type tv v /\ val_wf tv v /\
    (!m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory tv v (w2n dw) m) /\
    z.vs_current_bb = sbCopy.cs_current_bb /\
    z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\ ~z.vs_halted /\
    lookup_var idx z = SOME (n2w k) /\
    FLOOKUP Gf idx = FLOOKUP G idx /\ op_taint tf (Var idx) = op_taint tn (Var idx) /\
    eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) s /\
    eval_operand len_op z = eval_operand len_op s /\
    (!x. not_fresh_at saLen x ==>
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
    for_array_item_mods c sa saExpr (xd,dw,cap,inst.inst_id) ee Gf tf z /\
    for_array_outer_frame_mods ctx func c sa es0 s0 G0 tn0 ee Gf tf z /\
    for_array_capture_frame_mods c (em,saExpr,saLen,q,tq) ee tf z /\
    immutable_frame_mods func c cx ee z /\
    ret_pc_ok c sa z /\ return_buf_frame d c sa z /\ return_buf_sep d c ee z /\
    allocas_from lo z /\ lo <= z.vs_alloca_next /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gf,tf) /\
      stmt_state_rel H ctx func c cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d c cx ee Gf tf z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `a::rs = DROP k vs` (strip_assume_tac o MATCH_MP DROP_EQ_CONS o SYM) >>
  qhdtm_x_assum `for_nonslot_layout`
    (strip_assume_tac o REWRITE_RULE [for_nonslot_layout_def]) >>
  `sty = typ` by fs[well_typed_iterator_def] >>
  qpat_x_assum `sty = typ` SUBST_ALL_TAC >>
  `evaluate_type (get_tenv cx) (ArrayT typ bd) = SOME (ArrayTV tv bd)` by
    fs[] >>
  Q.SUBGOAL_THEN `loc = LocMemory \/ loc = LocCode` assume_tac
  >- (qpat_assum `(loc = LocMemory /\ _) \/ (loc = LocCode /\ _)` DISJ_CASES_TAC >> fs[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_header_mods mods DF lo d ctx func c cx env id st0 _ _ _ vs _ bod _ H _ ee G tn s`
    (qspec_then `H0` (drule_then (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def]))) >>
  `type_memory_bytes c typ = type_memory_size tv` by
    drule_all_then ACCEPT_TAC assign_name_memory_bytes_mods >>
  `stride = type_memory_size tv /\ type_memory_size tv <= cap` by
    (qpat_assum `loc = LocMemory \/ loc = LocCode` DISJ_CASES_TAC >>
     fs[elem_size_in_location_def,is_slot_addressed_def]) >>
  `ci_mono saLen saAddr /\ ci_mono sa saAddr` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= saAddr.cs_next_var /\ saLen.cs_next_var <= saAddr.cs_next_var` by
    fs[ci_mono_def] >>
  `!x. not_fresh_at saLen x ==> not_fresh_at saAddr x` by
    metis_tac[not_fresh_at_mono] >>
  `copy_old_operand saAddr (vv_operand vv) /\ copy_old_operand saAddr len_op` by
    (simp[copy_old_operand_def] >> metis_tac[]) >>
  `(case bd of Fixed _ => sum_op = off_op /\ sn = sm
      | Dynamic _ => emit_op ADD [Lit 32w;off_op] sm = (sum_op,sn))` by
    (qpat_assum `loc = LocMemory \/ loc = LocCode` DISJ_CASES_TAC >>
     Cases_on `bd` >> fs[word_scale_def,is_slot_addressed_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func c cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d c cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> for_array_header_mods mods DF lo d ctx func c cx env id st0 _ _ _ vs _ bod _ H _ ee G tn s`
       (drule_then (strip_assume_tac o REWRITE_RULE [for_array_header_mods_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "address"
QED

Resume for_array_snapshot_item_mods[address]:
  `s.vs_current_bb = saAddr.cs_current_bb` by simp[] >>
  qpat_assum `copy_old_operand saAddr (vv_operand vv)`
    (assume_tac o REWRITE_RULE [copy_old_operand_def]) >>
  mp_tac (Q.INST [`base_op` |-> `vv_operand vv`, `aid` |-> `inst.inst_id`]
    for_array_snapshot_address_frame_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`out`,`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at saCopy xd` by metis_tac[ci_mono_def,not_fresh_at_mono] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `alloca_inv u` by drule_then ACCEPT_TAC rest_word_state_alloca_inv >>
  `u.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H0 ctx func c cx ee u`
       (mp_tac o MATCH_MP stmt_state_rel_alloca_room) >>
     disch_then (ACCEPT_TAC o MATCH_MP (SPEC_ALL alloca_room_next_lt))) >>
  suspend "copy"
QED

Resume for_array_snapshot_item_mods[copy]:
  qpat_x_assum `addr = Var out` SUBST_ALL_TAC >>
  unabbrev_all_tac >>
  Q.SUBGOAL_THEN
    `?v n z Gf tf.
      EL k vs = Value v /\ value_has_type tv v /\ val_wf tv v /\ n <= cap /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gf,tf)) /\
      ~z.vs_halted /\ z.vs_current_bb = sbCopy.cs_current_bb /\
      z.vs_inst_idx = LENGTH sbCopy.cs_current_insts /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==> val_in_memory tv v (w2n dw) m) /\
      typed_copy_state_frame saCopy (w2n dw) n u z /\
      tf.t_imm = tu.t_imm /\ tf.t_stor = tu.t_stor /\ tf.t_trans = tu.t_trans /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==> (i IN tf.t_mem <=> i IN tu.t_mem)) /\
      (!x. not_fresh_at saCopy x ==> FLOOKUP Gf x = FLOOKUP Gu x /\
        op_taint tf (Var x) = op_taint tu (Var x)) /\
      lookup_var xd z = SOME dw /\ ptr_covers Gf tf xd z cap`
    (qx_choosel_then [`v`,`n`,`z`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS))
  >- (qpat_x_assum `loc = LocMemory \/ loc = LocCode` kall_tac >>
      qpat_x_assum `(loc = LocMemory /\ _) \/ (loc = LocCode /\ _)`
        (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
      >- suspend "memory" >>
      suspend "qualified") >>
  suspend "post"
QED

Resume for_array_snapshot_item_mods[memory]:
  `compile_iter_elem_copy c (Var out) (Var xd) (type_memory_size tv)
     LocMemory F typ typ saCopy = ((),sbCopy)` by fs[is_slot_addressed_def] >>
  `acyclic_struct_metadata c.ce_struct_fields` by
    drule_then ACCEPT_TAC contract_inv_acyclic_struct_metadata >>
  qhdtm_assum `expr_sim_inv_mods`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func c cx ee u`
    (mp_then Any (mp_tac o SPEC_ALL)
      (Q.INST [`ty` |-> `typ`, `xs` |-> `out`, `G` |-> `Gu`, `tn` |-> `tu`,
        `Gc` |-> `Gq`, `tc` |-> `tq`, `capture` |-> `q`,
        `base_op` |-> `vv_operand vv`, `aidItem` |-> `inst.inst_id`,
        `delta` |-> `(case bd of Fixed _ => 0 | Dynamic _ => 32) + k * type_memory_size tv`]
        for_array_snapshot_memory_copy_mods)) >>
  (impl_tac >- suspend "memory_input") >>
  disch_then (qx_choosel_then [`v`,`n`,`z`,`Gf`,`tf`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`n`,`z`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED

Resume for_array_snapshot_item_mods[memory_input]:
  asm_rewrite_tac[]
QED

Resume for_array_snapshot_item_mods[qualified]:
  `compile_iter_elem_copy c (Var out) (Var xd) (type_memory_size tv)
     LocCode F typ typ saCopy = ((),sbCopy)` by
    fs[is_slot_addressed_def,elem_size_in_location_def] >>
  qpat_assum `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func c cx ee u`
    (mp_then Any (fn th =>
      qpat_assum `ghost_inv_at_mods _ lo d c cx ee Gu tu u`
        (mp_then Any (mp_tac o SPEC_ALL) th))
      (Q.INST [`ty` |-> `typ`, `dty` |-> `typ`, `sty` |-> `typ`,
        `stride` |-> `type_memory_size tv`, `G` |-> `Gu`, `tn` |-> `tu`,
        `sa` |-> `saCopy`, `saOuter` |-> `sa`, `sb` |-> `sbCopy`,
        `capacity` |-> `cap`, `aid` |-> `inst.inst_id`]
        for_array_snapshot_qualified_copy_mods)) >>
  (impl_tac >- suspend "qualified_input") >>
  disch_then (qx_choosel_then [`v`,`raw`,`z`,`Gf`,`tf`,`words`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`v`,`32*words`,`z`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED

Resume for_array_snapshot_item_mods[qualified_input]:
  asm_rewrite_tac[]
QED

Resume for_array_snapshot_item_mods[post]:
  mp_tac snapshot_copy_posts >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `copy_old_operand saAddr (Var idx)` by simp[copy_old_operand_def] >>
  qpat_assum `!op. copy_old_operand saAddr op ==> eval_operand op z = _ /\ _`
    (qspec_then `Var idx` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
       [venomStateTheory.eval_operand_def,ptrDisciplineTheory.op_prov_def]))) >>
  `!x. not_fresh_at saLen x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `copy_old_operand saAddr (Var x)` by simp[copy_old_operand_def] >>
     qpat_assum `!op. copy_old_operand saAddr op ==> eval_operand op z = _ /\ _`
       (qspec_then `Var x` (drule_then strip_assume_tac)) >>
     fs[ptrDisciplineTheory.op_prov_def]) >>
  `a = Value v` by
    (qpat_assum `EL k vs = a` (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`v`,`z`,`Gf`,`tf`] >>
  asm_rewrite_tac[read_result_def,return_def] >>
  conj_tac
  >- (qpat_assum `!op. copy_old_operand saAddr op ==> eval_operand op z = _ /\ _`
        (qspec_then `vv_operand vv` (drule_then (strip_assume_tac))) >> simp[]) >>
  qpat_assum `!op. copy_old_operand saAddr op ==> eval_operand op z = _ /\ _`
    (qspec_then `len_op` (drule_then strip_assume_tac)) >> simp[]
QED

Finalise for_array_snapshot_item_mods
