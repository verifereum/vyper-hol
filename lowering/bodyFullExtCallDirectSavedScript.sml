Theory bodyFullExtCallDirectSaved
Ancestors
  bodyFullExtCallTupleStores bodyFullExtCallSavedOperand bodyFullExtCallDirectUnwrap
  bodyFullExtCallPosTransport exprOperandVar freshWrites fragExec exprSimHypsDefs
  exprLoweringProps exprSimHyps vyperTyping valueEncodingDefs
  targetPurePostTransport exprBopSimProps stateRelProj
  loweringPosts loweringStateRelDefs bodyPtrDefs fragGasOriginPtrDead
  vyperStorageFootprint compileEnv exprLowering context venomState freshWrites
Libs horizonTypeLib pureFrameLib

(* Each later row reads the same saved value at its actual unwrap cut.
   Its original allocation interval is independent of the frame cutoff. *)
Theorem extcall_direct_saved_advance:
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  read_result cx raw ee = (INL v,ee) /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (vv_location saved = SOME LocMemory ==> ~is_word_type ty) /\
  (!tag p. saved = LocatedValue tag p ==> tag = ty) /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
       ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at front x) /\
  (!l. vv_operand saved <> Label l) /\
  ss.cs_next_var <= front.cs_next_var /\ ss.cs_next_id <= front.cs_next_id /\
  local_ptrs_reserved ce front /\
  wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s Gnext tt /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  stmt_state_rel H ctx func ce cx ee t /\ ghost_inv_at (DF H) lo d ce cx ee Gnext tt t /\
  vv_storage_live H cx saved ee s /\ dead_lo_ok H (DF H) lo ce cx ==>
  vv_holds ce cx ty raw saved ee t /\ vv_at ce cx ty si ss ee raw saved t /\
  ptr_vv_ok cx ty raw saved ee Gnext tt t /\ vv_store_bound cx ty ty ee raw saved t /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
       ptr_buf_ok ce e (vv_operand saved) Gnext t) /\
  (!(hz:(bool # bytes32 # type_value) list # num list).
    vv_storage_live hz cx saved ee s ==> vv_storage_live hz cx saved ee t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee s`
    (assume_tac o CONJUNCT1 o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `vv_holds ce cx ty raw saved ee t /\ vv_at ce cx ty si ss ee raw saved t /\
    ptr_vv_ok cx ty raw saved ee Gnext tt t /\ vv_store_bound cx ty ty ee raw saved t /\
    ((case saved of StackValue tag op0 => ~is_word_type ty
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
         ptr_buf_ok ce e (vv_operand saved) Gnext t)` by
    (mp_tac (Q.INST [`origin` |-> `si`,`end_st` |-> `ss`,`cut` |-> `front`,
       `fn` |-> `func`, `H` |-> `H`, `q` |-> `t`,`Gq` |-> `Gnext`,`tq` |-> `tt`,`D` |-> `(DF:((bool # bytes32 # type_value) list # num list) -> dead) H`]
       (horizonTypeLib.at_horizon_named "H" extcall_tuple_saved_entry)) >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `vv_holds ce cx ty raw saved ee s`
    (strip_assume_tac o MATCH_MP target_saved_operand_exists) >>
  `!x w. not_fresh_at front x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    fs[wb_frame_def] >>
  `!w. eval_operand (vv_operand saved) s = SOME w ==>
    eval_operand (vv_operand saved) t = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`front`,`s`] >> simp[]) >>
  irule target_saved_storage_live_frame >>
  qexists_tac `s` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem extcall_saved_code_value[local]:
  vv_location saved = SOME LocCode /\
  (!tag p. saved = LocatedValue tag p ==> tag = ty) ==>
  ?p. saved = LocatedValue ty p /\ p.ptr_location = LocCode
Proof
  Cases_on `saved` >> simp[vv_location_def] >> metis_tac[]
QED

(* Keep Stage 1's saved value and provenance through the encoder's own
   cursor and address arithmetic, then materialize at the actual unwrap. *)
Theorem extcall_direct_restore_saved_from_posts:
  restore_copy_posts P (DF,lo,d,explicit,ctx,func,PG) ce cx st0 ee e /\
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  ss.cs_next_var <= front.cs_next_var /\ ss.cs_next_id <= front.cs_next_id /\
  front.cs_next_var <= su.cs_next_var /\ local_ptrs_reserved ce front /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gu tu u) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  wb_frame ce ee ee front s u /\ ghost_kept_at lo ce ee front G tn s Gu tu /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  unwrap_value ce saved su = (src,sb) /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  alloca_history func u /\ ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?z Gz tz.
    P su sb u z /\ pure_frame ce func ee su u z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gz tz z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
    expr_store_bound cx ty v src z /\ (~is_word_type ty ==> ptr_buf_ok ce e src Gz z) /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
      lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)) /\
    wb_frame ce ee ee su u z /\ ghost_kept_at lo ce ee su Gu tu u Gz tz /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    (~is_word_type ty ==> expr_val_at ce cx ty si ss ee v src z \/
                          expr_val_at ce cx ty su sb ee v src z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  `!x. vv_operand saved = Var x ==> not_fresh_at ss x` by
    metis_tac[extcall_saved_operand_not_fresh] >>
  `!x. vv_operand saved = Var x ==> not_fresh_at front x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. vv_operand saved = Var x ==> not_fresh_at su x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(vv_location saved = SOME LocMemory ==> ~is_word_type ty) /\
    (!tag p. saved = LocatedValue tag p ==> tag = ty)` by
    (qpat_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
     Cases_on `saved` >> simp_tac (srw_ss()) [vv_location_def] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  mp_tac (Q.INST [`t` |-> `u`, `Gnext` |-> `Gu`, `tt` |-> `tu`,
    `H` |-> `hz`] extcall_direct_saved_advance) >>
  impl_tac
  >- (asm_rewrite_tac[] >> qpat_assum `!H. dead_lo_ok H (DF H) lo ce cx`
      (ACCEPT_TAC o Q.SPEC `hz`)) >>
  strip_tac >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    vv_storage_live H cx saved ee u /\ ghost_inv_at (DF H) lo d ce cx ee Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!hz. vv_storage_live hz cx saved ee s ==> _`
       (qspec_then `H` MATCH_MP_TAC) >>
     first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `(?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ compile_expr ce (expr_type e) e si = (saved,sm) /\
        (!x. p.ptr_operand = Var x ==> not_fresh_at sm x))` ASSUME_TAC
  >- (qpat_assum `(?tag op0. saved = StackValue tag op0) \/ _` mp_tac >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac (DISJ_CASES_THEN strip_assume_tac))
     >- (disj1_tac >> metis_tac[])
     >- (disj2_tac >> disj1_tac >> metis_tac[]) >>
     disj2_tac >> disj2_tac >> qexists_tac `p` >> asm_rewrite_tac[] >>
     qpat_assum `compile_expr ce (expr_type e) e si = (vv,sm)`
       (mp_then (Pos hd) mp_tac (cj 1 compiler_compile_var)) >>
     strip_tac >> simp[vv_operand_def] >> metis_tac[vv_operand_def]) >>
  `ce.ce_is_ctor /\ vv_location saved = SOME LocCode ==>
    !w. eval_operand (vv_operand saved) u = SOME w ==>
      w2n w + type_memory_size tv <= lo /\
      (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
        val_in_memory tv v (w2n w) mem)` by
    (strip_tac >> gen_tac >> disch_tac >>
     mp_tac extcall_saved_code_value >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `code_p` strip_assume_tac) >>
     `vv_holds ce cx ty raw (LocatedValue ty code_p) ee u /\
      eval_operand code_p.ptr_operand u = SOME w` by
       metis_tac[vv_operand_def] >>
     mp_tac (Q.INST [`cenv` |-> `ce`, `entry` |-> `ee`, `p` |-> `code_p`, `G` |-> `Gu`,
       `tn` |-> `tu`, `H` |-> `(hz:(bool # bytes32 # type_value) list # num list)`,
       `D` |-> `(DF:((bool # bytes32 # type_value) list # num list) -> dead) hz`]
       (horizonTypeLib.at_horizon_named "H" extcall_request_saved_ctor_read)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       TRY REFL_TAC >> TRY (qexists_tac `raw` >> asm_rewrite_tac[]) >>
       TRY (qpat_assum `!H. dead_lo_ok H (DF H) lo ce cx` (ACCEPT_TAC o Q.SPEC `hz`)) >>
       POP_ASSUM_LIST (K ALL_TAC) >> NO_TAC) >>
     disch_then (qspecl_then [`tv`,`w`] mp_tac) >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`fn` |-> `func`, `rt` |-> `tv`, `t` |-> `u`,
    `G` |-> `Gu`, `tn` |-> `tu`] extcall_direct_saved_unwrap_from_posts) >>
  impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >>
  asm_rewrite_tac[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem extcall_direct_restore_saved_pure:
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ sm.cs_next_var <= su.cs_next_var /\ sm.cs_next_id <= su.cs_next_id /\
  ss.cs_next_var <= front.cs_next_var /\ ss.cs_next_id <= front.cs_next_id /\
  front.cs_next_var <= su.cs_next_var /\ local_ptrs_reserved ce front /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee Gu tu u) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  wb_frame ce ee ee front s u /\ ghost_kept_at lo ce ee front G tn s Gu tu /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  unwrap_value ce saved su = (src,sb) /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  alloca_history func u /\ ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
  u.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?z Gz tz.
    pure_frame ce func ee su u z /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d ce cx ee Gz tz z) /\
    expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\
    expr_store_bound cx ty v src z /\ (~is_word_type ty ==> ptr_buf_ok ce e src Gz z) /\
    alloca_history func z /\ u.vs_alloca_next <= z.vs_alloca_next /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at su x ==>
      lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
      op_taint tz (Var x) = op_taint tu (Var x)) /\
    wb_frame ce ee ee su u z /\ ghost_kept_at lo ce ee su Gu tu u Gz tz /\
    (!x. src = Var x ==> not_fresh_at sb x) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    (~is_word_type ty ==> expr_val_at ce cx ty si ss ee v src z \/
                          expr_val_at ce cx ty su sb ee v src z)
Proof
  mp_tac (Q.INST [`P` |-> `\a b s t. T`] extcall_direct_restore_saved_from_posts) >>
  simp_tac bool_ss [bodyFullExtCallDelayedSlotTheory.restore_copy_posts_true]
QED

Theorem extcall_direct_restore_saved =
  pureFrameLib.drop_frame extcall_direct_restore_saved_pure
