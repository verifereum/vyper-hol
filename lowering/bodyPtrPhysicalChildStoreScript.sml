(* Physical source layouts at the literal child-store boundary. *)
Theory bodyPtrPhysicalChildStore
Ancestors
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


Theorem literal_cons_aggregate_endpoint_physical:
  body_inv tops ctx ce cx /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ value_has_type tv v /\ k = type_memory_bytes ce (expr_type e) /\
  off+k <= capacity /\
  ~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e) /\
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
  drule_all literal_cons_compiler_stages >> strip_tac >>
  drule_all literal_annotation_slot >> strip_tac >>
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
    (mp_tac (Q.INST [`dty` |-> `expr_type e`, `dtv` |-> `tv`, `tv` |-> `stv`,
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
  `val_footprint tv v <= k` by metis_tac[] >>
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
    `expr_type e`, `lowered_value_type ce e`, `tv`, `stv`, `v`]
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

Theorem literal_cons_bytes_endpoint_physical:
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ value_has_type tv v /\ k = type_memory_bytes ce (expr_type e) /\
  off+k <= capacity /\
  ~is_word_type (expr_type e) /\ is_bytestring_type (expr_type e) /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ lookup_var root s = SOME (n2w addr) /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (addr,capacity) /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
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
  `post_value_type ce e = expr_type e` by
    (irule loweringPostsTheory.post_value_type_bytestring >> first_assum ACCEPT_TAC) >>
  drule_all literal_cons_compiler_stages >> strip_tac >> drule literal_loop_frame_allocation >> strip_tac >>
  drule_all literal_annotation_slot >> strip_tac >> drule_all literal_bytes_runtime_slot >> strip_tac >>
  qmatch_asmsub_abbrev_tac `val_store_size tv v = n` >>
  `0 < k /\ n <= k /\ n < dimword(:256)` by
    (gvs[Abbr `n`, wordsTheory.dimword_def] >> decide_tac) >>
  `stmt_state_rel ctx func ce cx esi s0` by metis_tac[literal_loop_frame_runtime] >>
  `off < capacity /\ op_taint tn (Var root) = {}` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def] >> decide_tac) >>
  `si.cs_next_var <= sm.cs_next_var /\ si.cs_next_var <= su.cs_next_var /\
   si.cs_next_id <= su.cs_next_id /\ su.cs_next_var <= sb.cs_next_var /\
   su.cs_next_id <= sb.cs_next_id` by gvs[ci_mono_def] >>
  `n+off <= capacity` by decide_tac >>
  `addr < dimword(:256) /\ addr+off < dimword(:256)` by decide_tac >>
  `w2n (n2w addr : bytes32)+off < dimword(:256) /\ off+n <= capacity` by
    (simp[] >> decide_tac) >>
  mp_tac (Q.INST [`sb` |-> `su`, `out` |-> `dst`,
    `a` |-> `(n2w addr : 256 word)`] literal_physical_child_add_unwrap) >>
  (impl_tac >- (asm_simp_tac std_ss [] >> metis_tac[])) >> strip_tac >>
  drule_all literal_loop_frame_materialized >> strip_tac >>
  `w2n (n2w addr + n2w off : bytes32) = addr+off` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `?a. eval_operand op z = SOME a /\ op_taint tm op = {}` by
    (gvs[bodyPtrDefsTheory.ptr_val_ok_def, expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `ptr_mem_ok cx (expr_type e) v op H tm z` by
    gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `?src. op = Var src /\ ptr_covers H tm src z n` by
    (irule exprPtrUnwrapFactsTheory.ptr_mem_ok_read_covers >>
     simp[] >> qexistsl [`cx`, `expr_type e`, `tv`, `v`] >> simp[]) >>
  `lookup_var src z = SOME a` by gvs[venomStateTheory.eval_operand_def] >>
  `!p. vv_operand vv = Var p ==> not_fresh_at sn p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `not_fresh_at su src` by
    (drule compiler_unwrap_value_var >>
     disch_then (qspec_then `src` mp_tac) >> simp[] >>
     Cases_on `vv` >> gvs[contextTheory.vv_operand_def]) >>
  `not_fresh_at su dst` by metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `(!p. not_fresh_at fr p ==> not_fresh_at su p) /\
   (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at su p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at su p)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_TRANS]) >>
  `?z' H' tm'.
    gas_path_ptr D 0 ctx func PG H tm z 0 H' tm' (OK z') /\
    literal_loop_frame pure ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es' sb H' tm' z' (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm' z'` by
    (irule literal_bytes_loop_store >> simp[] >>
     qexistsl [`a`, `n2w addr + n2w off`, `dst`, `su`, `src`,
       `lowered_value_type ce e`, `expr_type e`] >> gvs[Abbr `n`]) >>
  qexistsl [`z'`, `H'`, `tm'`] >> gvs[] >>
  irule (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then |> SRULE []) >>
  qexistsl [`H`, `z`, `tm`] >> simp[]
QED

Theorem literal_cons_endpoint_physical:
  body_inv tops ctx ce cx /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ value_has_type tv v /\ k = type_memory_bytes ce (expr_type e) /\
  off+k <= capacity /\
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
  strip_tac >> Cases_on `is_word_type (expr_type e)`
  >- (`post_value_type ce e = expr_type e` by simp[] >>
      `ptr_vv_ok cx (expr_type e) raw vv es' G tn s` by metis_tac[] >>
      drule_all literal_annotation_slot >> strip_tac >>
      `k = 32 /\ off+32 <= capacity` by metis_tac[] >>
      drule_all literal_cons_word_endpoint >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >> gvs[]) >>
  `!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s` by metis_tac[] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (`post_value_type ce e = expr_type e` by simp[] >>
      `ptr_vv_ok cx (expr_type e) raw vv es' G tn s` by metis_tac[] >>
      drule_all literal_cons_bytes_endpoint_physical >> simp[]) >>
  drule_all literal_cons_aggregate_endpoint_physical >> simp[]
QED

Theorem literal_cons_outcome_ptr_physical:
  body_inv tops ctx ce cx /\
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  literal_loop_frame pure ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  k = type_memory_bytes ce (expr_type e) /\ off+k <= capacity /\
  (pure ==> ~expr_has_effect e) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee H tm z. ?v. res = INL v /\ value_has_type tv v /\
      literal_loop_frame pure ctx func ce cx d root aid addr capacity
        ees fr sf Gf tnf ee sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
      literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z)
    (\res ee gt r. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_cons_compiler_stages >> strip_tac >>
  drule literal_loop_frame_runtime >> strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  drule_all post_value_type_widens >> strip_tac >>
  `~is_word_type (expr_type e) ==> ~is_word_type (post_value_type ce e)` by
    metis_tac[return_source_word_widens_eq] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >>
  disch_then drule_all >> strip_tac >>
  irule literal_result_bind_outcome_ptr >>
  qexists `\raw ee H tm z.
    vv_post ctx func ce cx e es si sm s0 ee raw vv z /\
    z.vs_current_bb = sm.cs_current_bb /\ z.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d ce cx ee H tm z /\ ptr_vv_ok cx (post_value_type ce e) raw vv ee H tm z /\
    (!t arg. vv = StackValue t arg /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok ce e arg H z) /\
    (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand H z) /\
    ghost_kept ce es si G0 tn0 s0 H tm` >>
  conj_tac >- suspend "normal" >> suspend "child"
QED

Resume literal_cons_outcome_ptr_physical[child]:
  drule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >> disch_then irule >>
  simp[] >> rpt strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >> metis_tac[]
QED

Resume literal_cons_outcome_ptr_physical[normal]:
  rpt gen_tac >> strip_tac >> fs[] >>
  `ee with gas_obs := [] = ee` by
    (simp[vyperStateTheory.evaluation_state_component_equality]) >>
  drule literal_marked_child_materialises >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_expr cx e marked = _` >>
  `literal_loop_frame pure ctx func ce cx d root aid addr capacity
     ees fr sf Gf tnf marked si G0 tn0 s0 cells off` by
    (gvs[Abbr `marked`, literal_loop_frame_def, bodyPtrDefsTheory.ghost_inv_def,
        bodyPtrDefsTheory.ghost_kept_def, exprSimWordArgsTheory.wb_frame_gas_obs] >>
        metis_tac[]) >>
  `ghost_kept ce marked si G0 tn0 s0 G tn` by
    (gvs[Abbr `marked`, bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  `expr_body_pre ce cx env e marked` by simp[Abbr `marked`] >>
  `lookup_var root t = SOME (n2w addr)` by
    (gvs[literal_loop_frame_def, vv_post_def] >> metis_tac[]) >>
  `ptr_covers G tn root t capacity /\ FLOOKUP G root = SOME (addr,capacity)` by
    (gvs[literal_loop_frame_def, bodyPtrDefsTheory.ghost_kept_def,
         bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryComposePtrTheory.gas_marked_exec_ptr_def] >>
     metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal]) >>
  `off+k <= capacity` by decide_tac >>
  drule_at (Pat `eval_expr _ _ _ = _`) literal_cons_endpoint_physical >>
  disch_then (drule_at (Pat `literal_loop_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >> simp[] >>
  disch_tac >>
  `?z H tm. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 H tm (OK z) /\
     literal_loop_frame pure ctx func ce cx d root aid addr capacity
       ees fr sf Gf tnf ee sb H tm z
         (cells ++ [(tv,v',addr+off,type_memory_bytes ce (expr_type e))])
         (off+type_memory_bytes ce (expr_type e)) /\
     literal_prefix_ok (cells ++ [(tv,v',addr+off,type_memory_bytes ce (expr_type e))]) tm z` by
    (qpat_x_assum `!pg dead. ?z H tm. gas_path_ptr dead 0 ctx func pg G tn t 0 H tm (OK z) /\ _`
       (fn th => POP_ASSUM_LIST (K (simp[] >> metis_tac[th])))) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  qexists `[]` >> disj1_tac >>
  qexistsl [`INL v'`, `ee`, `H`, `tm`, `OK z`] >> gvs[]
QED
Finalise literal_cons_outcome_ptr_physical
