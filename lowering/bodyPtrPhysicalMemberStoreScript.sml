(* Physical child layouts may also widen into a declared container member. *)
Theory bodyPtrPhysicalMemberStore
Ancestors
  bodyPtrPhysicalChildStore assignRelayoutCaller vyperTypeSystem
  bodyPtrMakeArrayConsOutcome bodyPtrPhysicalChildAdd bodyPtrPhysicalStoreFrame
  bodyPtrPhysicalChildInputs bodyPtrMakeArrayChildUnwrap
  bodyPtrMakeArrayConsBind bodyPtrMakeArrayConsSource
  bodyPtrMakeArrayPositiveBytes bodyPtrMakeArrayConsLayout bodyPtrMakeArrayConsInvariant
  bodyPtrMakeArrayChildren bodyPtrPhysicalChildUnwrap exprSimAggregateChildren
  bodyPtrDefs bodyPtrPreds bodySim exprSimHyps exprSimHypsDefs loweringPosts
  exprLowering exprLoweringProps exprOperandVar exprPtrUnwrapFacts emitHelperProps
  compileEnv context freshWrites fragGasPath fragGasPathPtr fragExec
  exprSimWordArgs wordArgsPtr vyperState vyperInterpreter vyperValue
  vyperTypeSystem vyperTypeValues valueEncoding valueEncodingProps
  venomState ptrDiscipline finite_map list pair words
  assignBasePtrBoundary loweringStateRelDefs exprSimProps
  aggregateStorePtr typedMemoryCopy bodyPtrSubscriptSeamTupleLayoutBridge


Theorem literal_cons_typed_member_endpoint_physical:
  body_inv tops ctx ce cx /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) dty (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ evaluate_type (get_tenv cx) dty = SOME tv /\
  arg_type_fits (expr_type e) dty /\
  val_wf tv v /\ value_has_type tv v /\ k = type_memory_bytes ce dty /\
  off+k <= capacity /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ lookup_var root s = SOME (n2w addr) /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (addr,capacity) /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn /\
  (pure ==> ~expr_has_effect e) ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    literal_loop_frame pure ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es' sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono si sm` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono su sb` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
  `ci_mono si sn /\ ci_mono si su /\ ci_mono si sb /\
   cs_extends sm sb /\ cs_extends sn sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code si sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\ local_ptrs_reserved ce su` by
    metis_tac[compiler_ci_mono_reserved] >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sm p` by
    metis_tac[cj 1 compiler_compile_var] >>
  `not_fresh_at sn dst` by
    (drule emitted_insts_emit_op >> simp[not_fresh_at_def] >> metis_tac[]) >>
  `expr_sim_inv ce cx env esi` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce dty = type_memory_size tv` by
    (drule_all expr_sim_inv_memory_size >> simp[]) >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by simp[type_widens_to_def, vyperTypeSystemTheory.well_formed_type_def] >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type (expr_type e)` by metis_tac[type_widens_from_bytestring] >>
  drule literal_loop_frame_allocation >> strip_tac >>
  `stmt_state_rel ctx func ce cx esi s0` by
    metis_tac[literal_loop_frame_runtime] >>
  `stmt_state_rel ctx func ce cx es' s` by fs[vv_post_def] >>
  `addr+capacity < dimword(:256)` by
    (
      `FLOOKUP s.vs_allocas aid = SOME (addr,capacity)` by
        (fs[vv_post_def, wb_frame_def] >> metis_tac[]) >>
      `s.vs_alloca_next < dimword(:256)` by
        (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
      fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
      qpat_x_assum `!aid base sz. FLOOKUP _ _ = SOME _ ==> _` drule >> decide_tac) >>
  `addr < dimword(:256)` by decide_tac >>
  `w2n (n2w addr : bytes32) + off < dimword(:256)` by
    (simp[] >> decide_tac) >>
  `op_taint tn (Var root) = {}` by fs[ptr_covers_def] >>
  `lowered_value_type ce e = post_value_type ce e` by
    metis_tac[bodyPtrSubscriptSeamTupleLayoutBridgeTheory.aggregate_lowered_post_type] >>
  `~is_word_type (post_value_type ce e)` by
    (
      `expr_sim_inv ce cx env esi /\ well_typed_expr env e` by
        fs[expr_body_pre_def] >>
      drule_all post_value_type_widens >> strip_tac >>
      metis_tac[return_source_word_widens_eq]) >>
  `!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s` by metis_tac[] >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_var <= su.cs_next_var /\
   si.cs_next_id <= su.cs_next_id /\ su.cs_next_var <= sb.cs_next_var /\
   su.cs_next_id <= sb.cs_next_id` by fs[ci_mono_def] >>
  drule_all (Q.INST [`n` |-> `k`] literal_physical_child_add_unwrap) >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `z` (qx_choose_then `H` (qx_choose_then `tm` strip_assume_tac)))) >>
  drule_all literal_loop_frame_materialized >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx) esi = (INL v,es')` by
    simp[bind_def] >>
  `post_value_type ce e = lowered_value_type ce e` by metis_tac[] >>
  drule_all literal_physical_source_inputs >> strip_tac >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) dty` by
    metis_tac[assignRelayoutCallerTheory.type_widens_to_trans] >>
  `~is_word_type (lowered_value_type ce e)` by metis_tac[] >>
  qpat_x_assum `lowered_value_type ce e = post_value_type ce e` kall_tac >>
  `w2n (n2w addr + n2w off : bytes32) = addr+off` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `!name p n. local_region ce es'.scopes z name p n ==>
      p+n <= addr+off \/ addr+off+k <= p` by
    (rpt strip_tac >>
     `addr+capacity <= p \/ p+n <= addr` by
       (fs[literal_loop_frame_def] >> metis_tac[]) >> decide_tac) >>
  `~is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[type_widens_from_bytestring] >>
  `expr_val_at ce cx (lowered_value_type ce e) si su es' v op z` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `k = type_memory_size tv` by metis_tac[] >>
  `FLOOKUP z.vs_allocas aid = SOME (addr,capacity)` by
    fs[literal_loop_frame_def] >>
  `addr <= addr+off /\ addr+off+type_memory_size tv <= addr+capacity` by
    decide_tac >>
  `w2n sw + type_memory_size stv < dimword(:256) /\
   (w2n sw + type_memory_size stv <= addr+off \/
    addr+off+k <= w2n sw)` by
    (mp_tac (Q.INST [`dty` |-> `dty`, `dtv` |-> `tv`, `tv` |-> `stv`,
       `sty` |-> `lowered_value_type ce e`, `sa` |-> `si`, `sb` |-> `su`,
       `es` |-> `es'`, `s` |-> `z`, `dw` |-> `(n2w addr+n2w off : 256 word)`, `did` |-> `aid`,
       `b` |-> `addr`, `k` |-> `capacity`]
       (INST_TYPE [alpha |-> ``:256``] aggregate_physical_source_slot_bounds)) >>
     (impl_tac >-
       (asm_simp_tac std_ss [] >> qx_genl_tac [`name`, `aa`, `nn`] >> strip_tac >>
        qpat_x_assum `!name p n. local_region ce es'.scopes z name p n ==>
          p+n <= addr+off \/ addr+off+k <= p`
          (qspecl_then [`name`, `aa`, `nn`] mp_tac) >>
        asm_simp_tac std_ss [] >> decide_tac)) >>
     asm_simp_tac std_ss []) >>
  `w2n (n2w addr+n2w off : bytes32) + type_memory_size tv < dimword(:256)` by
    (asm_simp_tac std_ss [] >> decide_tac) >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sn p` by
    metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `!p. op = Var p ==> not_fresh_at su p` by
    (rpt strip_tac >> drule compiler_unwrap_value_var >>
     disch_then (qspec_then `p` mp_tac) >> simp[] >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  `not_fresh_at su dst` by metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at su p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at su p)` by
    metis_tac[not_fresh_at_mono] >>
  `val_footprint tv v <= k` by
    (qpat_x_assum `k = type_memory_size tv` SUBST1_TAC >>
     irule val_footprint_le >> first_assum ACCEPT_TAC) >>
  `acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `op_taint tm (Var dst) = {}` by fs[ptr_covers_def] >>
  `ptr_covers H tm dst z (type_memory_size tv)` by metis_tac[] >>
  mp_tac (Q.SPECL [`ce`, `get_tenv cx`, `ctx`, `D`, `PG`,
    `dty`, `lowered_value_type ce e`, `tv`, `stv`, `v`]
    aggregateStorePtrTheory.compile_store_memory_aggregate_counted_ptr) >>
  (impl_tac >-
    (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`su`, `sb`, `dst`, `op`,
    `(n2w addr+n2w off : bytes32)`, `sw`, `func`, `H`, `tm`, `z`] mp_tac) >>
  (impl_tac >-
    (asm_simp_tac std_ss [] >> metis_tac[])) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `z2` strip_assume_tac))) >>
  qpat_assum `w2n (n2w addr+n2w off : bytes32) = addr+off`
    (fn th => full_simp_tac std_ss [th]) >>
  `literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es' sb G2 tn2 z2
      (cells ++ [(tv,v,addr+off,type_memory_size tv)]) (off+type_memory_size tv) /\
   literal_prefix_ok (cells ++ [(tv,v,addr+off,type_memory_size tv)]) tn2 z2` by
    (mp_tac (Q.INST [`es` |-> `es'`, `sa` |-> `su`, `G` |-> `H`,
       `tn` |-> `tm`, `s` |-> `z`, `H` |-> `G2`, `tm` |-> `tn2`, `t` |-> `z2`,
       `k` |-> `type_memory_size tv`] literal_typed_loop_store_frame) >>
     (impl_tac >- (asm_simp_tac std_ss [] >> rpt conj_tac >> metis_tac[])) >>
     disch_then ACCEPT_TAC) >>
  (qexistsl_tac [`z2`, `G2`, `tn2`] >> conj_tac
   >- (irule (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then |> SRULE []) >>
       qexistsl_tac [`H`, `z`, `tm`] >> simp[]) >>
   conj_tac >> first_assum ACCEPT_TAC)
QED
