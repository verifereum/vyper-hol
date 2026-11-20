(* Joint postconditions for the memory raw-call continuation. *)
Theory bodyFullRawCallFinishPost
Ancestors emitHelperProps[qualified,ignore_grammar] compileEnv[qualified,ignore_grammar] rich_list[qualified,ignore_grammar] ptrDiscipline[qualified,ignore_grammar] bodyPtrIfExpAllocFrame[qualified,ignore_grammar]
  bodyFullRawCallFinishJoint bodyFullRawCallZero bodyFullRawCallBytes
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimRawCall exprSimMemDefs stateRelProj
  exprSimProps valueEncoding valueTypingMemoryProps loweringPosts
  vfmConstants context vyperState venomMemDefs exprSimRawCallCalldata
  exprSimHash exprLowering exprLoweringProps loweringHalt fragExec fragExecMem instIdxIndep
  words list emitHelper venomInst

Libs
  monadsyntax

(* Both ownership and the store bound come from the row of this very run. *)
Theorem raw_call_tuple_live_row_post[local]:
  storage_well_formed_on cx es (FST H) /\ expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
  eval_operand result t = SOME w /\
  FLOOKUP t.vs_allocas ti = SOME (w2n w,64 + ((n+31) DIV 32)*32) /\
  sf.cs_next_id <= ti /\ ti < sb.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
    w2n w + (64 + ((n+31) DIV 32)*32) <= lb \/ lb + lsz <= w2n w) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n bytes)]) /\
  val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    v (w2n w) t.vs_memory /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
    es (Value v) vv t /\
  vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv t
Proof
  strip_tac >>
  `type_memory_size (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) =
     64 + ((n+31) DIV 32)*32` by
    (simp[type_memory_size_def, word_size_def] >> decide_tac) >>
  `w2n w + (64 + ((n+31) DIV 32)*32) <= t.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >>
     simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  conj_asm1_tac
  >- (simp[] >> metis_tac[raw_call_tuple_post]) >>
  conj_tac
  >- (qpat_assum `vv = _` SUBST1_TAC >>
      qpat_assum `post_value_type cenv e = _` SUBST1_TAC >>
      qpat_assum `lowered_value_type cenv e = _` SUBST1_TAC >>
      irule vv_store_bound_capacity >> simp[mk_ptr_def] >>
      qexistsl_tac [`H`,`cenv`,`ctx`,`es0`,`func`,`s0`,`sf`,`sb`] >> gvs[mk_ptr_def]) >>
  `val_wf (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) v` by
    (simp[valueEncodingDefsTheory.val_wf_def, type_memory_size_def, listTheory.LENGTH_TAKE_EQ] >>
     qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def] >> decide_tac) >>
  drule val_footprint_le >> strip_tac >>
  gvs[vv_own_def, mk_ptr_def, read_result_def, return_def] >>
  disj1_tac >> qexistsl_tac [`ti`,`w2n w`,`64 + ((n+31) DIV 32)*32`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* Obtain the one physical run before quantifying over the horizon. The
   universal relation is obtained by determinism of run_inst_seq, not by
   selecting a different witness in the postcondition at each horizon. *)
Theorem raw_call_positive_tuple_endpoint[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel H0 ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n data) pre).vs_memory /\
  s.vs_returndata = data /\
  tn.t_mem = old_tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE n data)} /\
  w2n ro = w2n w + 32 /\ LENGTH data < dimword (:256) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n data)]) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (!i. w2n w + 32 <= i /\ i < w2n w + 32 + LENGTH (TAKE n data) ==>
    i NOTIN tn.t_mem) /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      !H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
          storage_well_formed_on cx es (FST H) ==>
        vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv (t with vs_inst_idx := LENGTH
          sb.cs_current_insts) /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
            es (Value v) vv (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
          vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv (t with vs_inst_idx := LENGTH
            sb.cs_current_insts)
Proof
  strip_tac >>
  conj_tac
  >- (drule_all raw_call_positive_suffix_mem_ok >> simp[]) >>
  drule_all raw_call_positive_payload_cut >> strip_tac >>
  conj_tac >- metis_tac[] >>
  `LENGTH s.vs_returndata < dimword (:256)` by simp[] >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_nonrevert_positive_run) >>
  disch_then drule_all >> disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms, Excl "vv_post_inst_idx"] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_nonrevert_positive_run) >>
  disch_then drule_all >> strip_tac >>
  rename1 `stmt_state_rel H ctx func cenv cx es t'` >>
  `t' = t` by
    (qpat_x_assum `run_inst_seq _ s = OK t'` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u` by
    simp[Abbr `u`, stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx] >>
  `!name lb lsz. local_region cenv es.scopes u name lb lsz <=>
                 local_region cenv es.scopes t name lb lsz` by
    simp[Abbr `u`, loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def] >>
  irule raw_call_tuple_live_row_post >> simp[] >>
  qexistsl_tac [`data`,`result`,`ti`,`tw`] >>
  gvs[Abbr `u`, hash_eval_operand_inst_idx] >> first_assum ACCEPT_TAC
QED

(* The tuple's length-store cut uses the same runtime witness for the ghost
   sequence as for the state and writeback frame. *)
Theorem raw_call_tuple_length_cut[local]:
  emit_op RETURNDATASIZE [] sa = (z,s1) /\
  emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
  compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
  emit_void MSTORE [Var x;cap] s3 = ((),s4) /\
  0 < n /\ n < dimword (:256) /\
  64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  safe_operand sa (Var x) /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
  sf.cs_next_var <= sa.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= alloc.inst_id /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
  allocas_from lo s ==>
  ?u G1 tn1.
    run_inst_seq (emitted_insts sa s4) s = OK u /\
    stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa s4) s G1 tn1) /\
    ptr_covers G1 tn1 x u (32 + ((n+31) DIV 32)*32) /\
    (!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) mem) /\
    tn1.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v u = lookup_var v s /\ FLOOKUP G1 v = FLOOKUP G v /\
      op_taint tn1 (Var v) = op_taint tn (Var v)) /\
    (u with vs_vars := s.vs_vars) =
      mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s
Proof
  strip_tac >>
  `eval_operand (Var x) s = SOME w` by simp[venomStateTheory.eval_operand_def] >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  `w2n w <= w2n w /\ w2n w + 32 <= w2n w + (32 + ((n+31) DIV 32)*32)` by decide_tac >>
  drule_all raw_call_output_prefix_ready >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es u` by fs[] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_alloca_room) >>
     simp[alloca_room_def] >> decide_tac) >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by decide_tac >>
  `lookup_var x s = SOME (n2w (w2n w))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    qpat_assum `stmt_state_rel H ctx func cenv cx es s`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  drule_all bodyFullRawCallTupleLengthTheory.raw_call_tuple_length_checked >>
  disch_then (qspecl_then [`func`,`PG`] strip_assume_tac) >>
  rename1 `ptr_covers G1 tn1 x u _` >>
  qexistsl_tac [`u`,`G1`,`tn1`] >> simp[]
QED

(* Apply row separation at the current state.  Transport old local regions
   forward using only the SOME-lookups preserved by wb_frame. *)
Theorem raw_call_tuple_wb_row_exclusions[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (b,k) /\
  sf.cs_next_id <= alloc.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es0 es sf s0 s /\ allocas_from lo s ==>
  lo <= b /\
  (!name a m i. local_region cenv es.scopes s name a m /\ a <= i /\ i < a+m ==>
     ~(b <= i /\ i < b+k)) /\
  (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
     aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k)) /\
  (!name a m i. local_region cenv es0.scopes s0 name a m /\ a <= i /\ i < a+m ==>
     ~(b <= i /\ i < b+k))
Proof
  strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `!aid a m. FLOOKUP s.vs_allocas aid = SOME (a,m) /\ aid < alloc.inst_id ==>
     a+m <= b \/ b+k <= a` by
    (rpt strip_tac >> `aid <> alloc.inst_id` by decide_tac >>
     fs[alloca_inv_def,venomMemDefsTheory.allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`aid`,`alloc.inst_id`] mp_tac) >> simp[]) >>
  conj_tac >- metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `!name a m i. local_region cenv es.scopes s name a m /\ a <= i /\ i < a+m ==>
     ~(b <= i /\ i < b+k)` by
    (rpt strip_tac >> drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  conj_tac
  >- (rpt (gen_tac ORELSE disch_tac) >> fs[] >>
      rename1 `FLOOKUP s0.vs_allocas aid = SOME (a,m)` >>
      `FLOOKUP s.vs_allocas aid = SOME (a,m)` by metis_tac[] >>
      `aid < alloc.inst_id` by decide_tac >>
      `a+m <= b \/ b+k <= a` by metis_tac[] >> decide_tac) >>
  rpt (gen_tac ORELSE disch_tac) >> fs[] >>
  rename1 `local_region cenv es0.scopes s0 name a m` >>
  `local_region cenv es.scopes s name a m` by
    (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sf`,`es0.scopes`] >> simp[]) >>
  metis_tac[]
QED

Theorem raw_call_tuple_length_ghost_frame[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (b,k) /\ 32 <= k /\
  sf.cs_next_id <= alloc.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es0 es sf s0 s /\ allocas_from lo s /\
  sf.cs_next_var <= sa.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!v. not_fresh_at sa v ==>
    lookup_var v u = lookup_var v s /\ FLOOKUP G1 v = FLOOKUP G v /\
    op_taint tn1 (Var v) = op_taint tn (Var v)) /\
  (u with vs_vars := s.vs_vars) = mstore b len s /\
  tn1.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
  tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G1 tn1 /\
  (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
       ghost_inv_at D lo dep cenv cx es G1 tn1 u)
Proof
  strip_tac >> drule_all raw_call_tuple_wb_row_exclusions >> strip_tac >>
  `!i. b <= i /\ i < b+32 ==> i < b+k` by decide_tac >>
  `!v. not_fresh_at sf v ==>
    lookup_var v u = lookup_var v s /\ FLOOKUP G1 v = FLOOKUP G v /\
    op_taint tn1 (Var v) = op_taint tn (Var v)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables` by
    (qpat_assum `(u with vs_vars := _) = _` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality, venomStateTheory.mstore_def]) >>
  `u.vs_memory = (mstore b len s).vs_memory` by
    (qpat_assum `(u with vs_vars := _) = _`
      (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >> simp[]) >>
  qabbrev_tac `R = {i | b <= i /\ i < b+32}` >>
  `!i. i NOTIN R ==> mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (simp[Abbr `R`] >> rpt strip_tac >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!i. i NOTIN R /\ i IN tn1.t_mem ==> i IN tn.t_mem` by simp[Abbr `R`] >>
  `!i. i < lo ==> i NOTIN R` by (simp[Abbr `R`] >> decide_tac) >>
  `!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> i NOTIN R` by (simp[Abbr `R`] >> metis_tac[]) >>
  `!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> i NOTIN R` by
    (simp[Abbr `R`] >> metis_tac[]) >>
  `!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> i NOTIN R` by (simp[Abbr `R`] >> metis_tac[]) >>
  drule bodyFullRawCallTupleWriteFrameTheory.raw_call_tuple_write_frame >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`tn1`,`u`,`dep`,`R`,`G1`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* The ALLOCA cut uses the very step which creates the tuple row. *)
Theorem raw_call_tuple_alloc_cut[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  compile_alloc_buffer k sa = (buf,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ k < dimword (:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\ lo <= s.vs_alloca_next /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sf x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sf x) ==>
  ?p u b.
    buf.buf_operand = Var p /\ not_local_ptr cenv es.scopes p /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) (fn_insts func) /\
    emitted_insts sa sb = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]] /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s = OK u /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    stmt_state_rel H ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,k) /\ b + k < dimword (:256) /\
    lookup_var p u = SOME (n2w b) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p])
      u) (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn) /\
      (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
           ghost_inv_at D lo dep cenv cx es (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p])
             u) (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn) u) /\
      ptr_covers (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) u) (step_taint (mk_inst
        sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn) p u k
Proof
  strip_tac >> drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `p` (qx_choose_then `u` strip_assume_tac)) >>
  drule_all bodyPtrIfExpAllocSourceTheory.compile_alloc_buffer_raw_resources >> strip_tac >>
  `wb_frame cenv es0 es sf s0 u` by
    (irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
     qexistsl_tac [`s`,`es.scopes`,`sa`] >> simp[]) >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]]` by
    gvs[emitted_insts_def, DROP_PREFIX] >>
  `not_local_ptr cenv es.scopes p` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `sa` >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  drule_all allocationPtrTheory.alloca_step_site >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  `lookup_var p u = SOME (n2w b)` by fs[venomStateTheory.eval_operand_def] >>
  `STRING #"%" (toString sa.cs_next_var) = p` by gvs[] >>
  qexistsl_tac [`p`,`u`,`b`] >>
  simp[run_inst_seq_def] >>
  conj_tac
  >- (drule_all bodyFullRawCallTupleAllocFrameTheory.raw_call_tuple_alloc_kept_at >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule bodyFullAllocGenericTheory.compile_alloc_buffer_ghost_frame_at >>
      metis_tac[]) >>
  drule_all allocationPtrTheory.alloca_step_ptr_covers >> simp[]
QED

(* A new tuple row does not invalidate pointers into the old bytes row. *)
Theorem raw_call_tuple_alloc_transport[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) (fn_insts func) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s = OK u /\
  p = STRING #"%" (toString sa.cs_next_var) /\ k < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  FLOOKUP s.vs_allocas aid = SOME (a,len) /\ val_wf tv v /\ val_footprint tv v <= len /\
  safe_operand sa (Var x) /\ ptr_covers G tn x s len /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v a mem) ==>
  allocas_from lo u /\ ptr_covers (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn) x u len /\
    (!op. safe_operand sa op ==> eval_operand op u = eval_operand op s /\
         op_taint (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn) op = op_taint tn op) /\
    (!mem. mem_agree_outside (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn).t_mem
      u.vs_memory mem ==> val_in_memory tv v a mem) /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn [(mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p])] (s with
      vs_inst_idx := j) (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) u) (step_taint
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]) s u tn))
Proof
  strip_tac >> simp[] >>
  `!op z. safe_operand sa op /\ op = Var z ==> z <> p` by
    (simp[exprSafeOperandTheory.safe_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  conj_tac
  >- (irule frameActivationSeparationTheory.allocas_from_step >>
      qexistsl_tac [`ctx`,`0`,`mk_inst sa.cs_next_id ALLOCA [Lit (n2w k)] [p]`,`s`] >>
      simp[venomExecSemanticsTheory.step_inst_non_invoke, venomInstTheory.mk_inst_def]) >>
  `x <> p` by metis_tac[] >>
  conj_tac
  >- (drule_all allocationPtrTheory.alloca_step_old_ptr_covers >> simp[]) >>
  conj_tac
  >- (rpt strip_tac
      >- (irule allocationPtrTheory.alloca_step_operand_preserved >> metis_tac[])
      >> irule bodyPtrIfExpAllocSourceTheory.alloca_step_operand_taint >> metis_tac[]) >>
  conj_tac
  >- (`a + len <= s.vs_alloca_next` by
        (drule stmt_state_rel_local_ptrs_alloca >>
         simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
         first_x_assum drule >> simp[]) >>
      `!i. a <= i /\ i < a + val_footprint tv v ==> i < s.vs_alloca_next` by decide_tac >>
      (metis_tac[bodyPtrIfExpAllocFrameTheory.alloca_step_robust_below_frontier])) >>
  rpt gen_tac >> simp[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := j)` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _` mp_tac >>
     simp[NoAsms, ptrDisciplineTheory.allocas_below_fmp_def] >> tautLib.TAUT_TAC) >>
  conj_tac
  >- (irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
      conj_tac >- (fs[ptrDisciplineTheory.allocas_from_def] >> (gvs[ptrDisciplineTheory.allocas_from_def])) >>
      qexists_tac `0` >> simp[fragExecPtrTheory.ptr_inst_ok_alloca]) >>
  gvs[instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def,
      venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
      ghostPcTransportPtrTheory.step_prov_inst_idx, ghostPcTransportPtrTheory.step_taint_inst_idx_right]
QED

(* The flag store and padded copy can only write the fresh tuple row. *)
Theorem raw_call_tuple_copy_ghost_frame[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [p] /\
  not_local_ptr cenv es.scopes p /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (b,32+cnt) /\
  sf.cs_next_id <= alloc.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es0 es sf s0 s /\ allocas_from lo s /\
  sf.cs_next_var <= sa.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!v. not_fresh_at sa v ==>
    lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)) /\
  (t with vs_vars := s.vs_vars) = mcopy (b+32) a cnt (mstore b (flag:256 word) s) /\
  tnf.t_mem =
    (((tn.t_mem DIFF {i | b <= i /\ i < b+32}) DIFF {i | b+32 <= i /\ i < b+32+cnt}) UNION
       {b+32+i | i | i < cnt /\ a+i IN (tn.t_mem DIFF {i | b <= i /\ i < b+32})}) /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
  (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
       ghost_inv_at D lo dep cenv cx es Gf tnf t)
Proof
  strip_tac >> drule_all raw_call_tuple_wb_row_exclusions >> strip_tac >>
  `!v. not_fresh_at sf v ==>
    lookup_var v t = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qpat_assum `(t with vs_vars := _) = _`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [venomExecSemanticsTheory.mcopy_def,
       venomStateTheory.write_memory_with_expansion_def, venomStateTheory.mstore_def, LET_THM] o
     Q.AP_TERM `\v. (v.vs_allocas,v.vs_alloca_next,v.vs_call_ctx,
                     v.vs_accounts,v.vs_transient,v.vs_immutables)`) >>
  qabbrev_tac `R = {i | b <= i /\ i < b+(32+cnt)}` >>
  `!i. i NOTIN R ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (qpat_assum `(t with vs_vars := _) = _`
       (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >>
     simp[Abbr `R`] >> rpt strip_tac >>
     `i+1 <= b \/ b+32 <= i` by decide_tac >>
     `i+1 <= b+32 \/ (b+32)+cnt <= i` by decide_tac >>
     simp[valueEncodingPropsTheory.mcopy_mem_bytes_at_disjoint,
          valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint]) >>
  `!i. i NOTIN R /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `tnf.t_mem = _` SUBST1_TAC >>
     simp[Abbr `R`, NoAsms, pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF,
          pred_setTheory.GSPECIFICATION] >>
     rpt strip_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
  `!i. i < lo ==> i NOTIN R` by (simp[Abbr `R`] >> decide_tac) >>
  `!i. i NOTIN R <=> ~(b <= i /\ i < b+(32+cnt))` by simp[Abbr `R`] >>
  pop_assum $ mk_asm "in_R" >>
  `!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> i NOTIN R` by
    (asm "in_R" (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> i NOTIN R` by
    (asm "in_R" (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> i NOTIN R` by
    (asm "in_R" (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  drule bodyFullRawCallTupleWriteFrameTheory.raw_call_tuple_write_frame >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`tnf`,`t`,`dep`,`R`,`Gf`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

(* The ghosts follow the three cuts of the fixed physical suffix. *)
Theorem raw_call_positive_tuple_ghosts[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [Var x;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa (Var x) /\ safe_operand sa ok /\
  lookup_var x s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  0 < n /\ n < dimword (:256) /\ 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
  ?Gf tnf.
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf t) /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf) /\
    ?p b. result = Var p /\ lookup_var p t = SOME (n2w b) /\
      b < dimword (:256) /\
      ptr_covers Gf tnf p t (64 + ((n+31) DIV 32)*32) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
          (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])) b mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  drule_all raw_call_tuple_length_cut >>
  disch_then (qspec_then `PG`
    (qx_choose_then `u` (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac)))) >>
  `32 <= 32 + ((n+31) DIV 32)*32` by decide_tac >>
  `ghost_kept_at lo cenv es0 sf G0 tn0 s0 G1 tn1 /\
   (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
        ghost_inv_at D lo dep cenv cx es G1 tn1 u)` by
    (drule_at (Pat `(u with vs_vars := _) = _`) raw_call_tuple_length_ghost_frame >>
     disch_then drule_all >> simp[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `(u with vs_vars := _) = _` (mp_tac o Q.AP_TERM `\v. (v.vs_allocas,v.vs_alloca_next)`) >>
     simp[venomStateTheory.mstore_def]) >>
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = _`
       (fn th => pure_rewrite_tac[ptrDisciplineTheory.allocas_from_def,th]) >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
  `lo <= w2n w` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) <= u.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `lo <= u.vs_alloca_next` by decide_tac >>
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_id <= s4.cs_next_id` by fs[ci_mono_def] >>
  `sf.cs_next_var <= s4.cs_next_var /\ sf.cs_next_id <= s4.cs_next_id` by decide_tac >>
  `local_ptrs_reserved cenv s4 /\ safe_operand s4 (Var x) /\ safe_operand s4 ok` by
    metis_tac[exprSafeOperandTheory.safe_operand_mono,local_ptrs_reserved_next_var] >>
  drule abiBufferAllocationCodeTheory.compile_alloc_buffer_code >> strip_tac >>
  `cs_extends s4 s5` by metis_tac[compile_alloc_buffer_extends] >>
  `inst_extends s5 s6 /\ inst_extends s6 s7 /\ inst_extends s7 sb` by
    metis_tac[emitHelperPropsTheory.inst_extends_emit_op, emitHelperPropsTheory.inst_extends_emit_void] >>
  `inst_extends s5 sb` by metis_tac[emitHelperPropsTheory.inst_extends_trans] >>
  `cs_extends s5 sb` by
    ((qpat_assum `inst_extends s5 sb` mp_tac >>
     rewrite_tac[emitHelperPropsTheory.inst_extends_def, same_blocks_def, compileEnvTheory.cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[rich_listTheory.IS_PREFIX_APPEND] >> (gvs[emitHelperPropsTheory.inst_extends_def, same_blocks_def, compileEnvTheory.cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]))) >>
  `fn_has_code s4 s5 func` by metis_tac[fn_has_code_mid] >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es u`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_tuple_alloc_cut) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`dep`,`PG`]
    (qx_choose_then `p` (qx_choose_then `u2` (qx_choose_then `b` mp_tac)))) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `p = STRING #"%" (toString s4.cs_next_var)` by gvs[] >>
  `FLOOKUP u.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32)` by simp[] >>
  qabbrev_tac `bs = TAKE n s.vs_returndata` >>
  `LENGTH bs <= n` by simp[Abbr `bs`, LENGTH_TAKE_EQ] >>
  `n <= ((n+31) DIV 32)*32` by
    (qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def] >> decide_tac) >>
  `val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
   val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) <= 32 + ((n+31) DIV 32)*32` by
    (simp[valueEncodingDefsTheory.val_wf_def, val_footprint_def, type_memory_size_def, word_size_def] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (strip_tac >> conj_tac
     >- (qpat_assum `stmt_state_rel H ctx func cenv cx es u`
           (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >> simp[]) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es u` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, fmp_room_def] >> strip_tac >> res_tac >> decide_tac) >>
  qpat_assum `step_inst_base (mk_inst s4.cs_next_id ALLOCA _ _) u = _`
    (mp_then (Pat `step_inst_base _ _ = _`) mp_tac raw_call_tuple_alloc_transport) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_wf _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `i = mk_inst s4.cs_next_id ALLOCA [Lit (n2w (64 + ((n+31) DIV 32)*32))] [p]` >>
  qabbrev_tac `G2 = step_prov PG G1 i u2` >>
  qabbrev_tac `tn2 = step_taint i u u2 tn1` >>
  `safe_operand s5 (Var p)` by
    simp[exprSafeOperandTheory.safe_operand_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
  `safe_operand s5 (Var x) /\ safe_operand s5 ok` by
    (rpt conj_tac >> irule exprSafeOperandTheory.safe_operand_mono >> qexists_tac `s4` >> simp[]) >>
  `!op. safe_operand sa op ==> eval_operand op u = eval_operand op s /\
                              op_taint tn1 op = op_taint tn op` by
    (gen_tac >> Cases_on `op` >>
     simp[exprSafeOperandTheory.safe_operand_def, venomStateTheory.eval_operand_def,
          ptrDisciplineTheory.op_taint_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `lookup_var x u2 = SOME (n2w (w2n w)) /\
   eval_operand ok u2 = SOME (if success then 1w else 0w) /\ op_taint tn2 ok = {}` by
    metis_tac[venomStateTheory.eval_operand_def, w2n_n2w, n2w_w2n] >>
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es u`
       (mp_then Any mp_tac stmt_state_rel_alloca_room) >>
     simp[alloca_room_def] >> decide_tac) >>
  `FLOOKUP u2.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32)` by metis_tac[] >>
  `alloc.inst_id <> s4.cs_next_id` by decide_tac >>
  SUBGOAL_THEN
    ``w2n (w:256 word) + 32 + LENGTH (bs:word8 list) <= b \/ b+32 <= w2n w`` assume_tac
  >- (qpat_assum `stmt_state_rel H ctx func cenv cx es u2`
        (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
      pure_rewrite_tac[alloca_inv_def, allocas_non_overlapping_def] >> strip_tac >>
      qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ ==> _ \/ _` drule_all >>
      simp[] >> decide_tac) >>
  `inst_extends s4 s5` by
    (pure_rewrite_tac[emitHelperPropsTheory.inst_extends_def] >> first_assum ACCEPT_TAC) >>
  `inst_extends sa s5` by
    (irule emitHelperPropsTheory.inst_extends_trans >> qexists_tac `s4` >> simp[]) >>
  `emitted_insts sa s5 = emitted_insts sa s4 ++ emitted_insts s4 s5 /\
   emitted_insts sa sb = emitted_insts sa s5 ++ emitted_insts s5 sb` by
    (conj_tac >> irule emitted_insts_append >>
     rpt conj_tac >> first_assum (ACCEPT_TAC o PURE_REWRITE_RULE
       [emitHelperPropsTheory.inst_extends_def])) >>
  `run_inst_seq (emitted_insts sa s5) s = OK u2` by
    (qpat_assum `emitted_insts sa s5 = _` SUBST1_TAC >>
     qpat_assum `run_inst_seq (emitted_insts sa s4) s = OK u`
       (mp_then Any (fn th => pure_rewrite_tac[th]) run_inst_seq_append) >>
     first_assum ACCEPT_TAC) >>
  `run_inst_seq (emitted_insts s5 sb) u2 = OK t` by
    (qpat_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     qpat_assum `run_inst_seq (emitted_insts sa s5) s = OK u2`
       (mp_then Any (fn th => pure_rewrite_tac[th]) run_inst_seq_append) >>
     simp[]) >>
  `EVERY (\j. ~is_terminator j.inst_opcode) (emitted_insts sa s4) /\
   EVERY (\j. ~is_terminator j.inst_opcode) (emitted_insts sa s5) /\
   EVERY (\j. ~is_terminator j.inst_opcode) (emitted_insts s5 sb)` by
    (qpat_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
     qpat_assum `emitted_insts sa s5 = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> rewrite_tac[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  qabbrev_tac `k = s.vs_inst_idx + LENGTH (emitted_insts sa s5)` >>
  `run_inst_seq (emitted_insts s5 sb) (u2 with vs_inst_idx := k) =
     OK (t with vs_inst_idx := k)` by
    (qpat_assum `EVERY _ (emitted_insts s5 sb)`
       (mp_then Any (fn th => pure_rewrite_tac[th]) run_inst_seq_inst_idx) >>
     simp[instIdxIndepTheory.exec_result_map_def]) >>
  `emit_void MSTORE [Var p;ok] s5 = ((),s6) /\
   emit_op ADD [Var p;Lit 32w] s6 = (dst,s7)` by
    (qpat_assum `buf.buf_operand = Var p` (fn th => pure_rewrite_tac[GSYM th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var x (u2 with vs_inst_idx := k) = SOME (n2w (w2n w)) /\
   lookup_var p (u2 with vs_inst_idx := k) = SOME (n2w b)` by
    (qpat_assum `lookup_var x u2 = _` mp_tac >>
     qpat_assum `lookup_var p u2 = _` mp_tac >>
     simp_tac (srw_ss()) [venomStateTheory.lookup_var_def]) >>
  `ptr_covers G2 tn2 x (u2 with vs_inst_idx := k) (32 + ((n+31) DIV 32)*32) /\
   ptr_covers G2 tn2 p (u2 with vs_inst_idx := k) (64 + ((n+31) DIV 32)*32) /\
   eval_operand ok (u2 with vs_inst_idx := k) = SOME (if success then 1w else 0w) /\
   allocas_from lo (u2 with vs_inst_idx := k)` by
    (simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx,
          ghostPcTransportPtrTheory.eval_operand_inst_idx, ptrDisciplineTheory.allocas_from_def] >>
     first_assum (ACCEPT_TAC o PURE_REWRITE_RULE[ptrDisciplineTheory.allocas_from_def])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (u2 with vs_inst_idx := k)` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es u2`
       (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
     simp[NoAsms, ptrDisciplineTheory.allocas_below_fmp_def] >> tautLib.TAUT_TAC) >>
  qpat_assum `run_inst_seq (emitted_insts s5 sb) (u2 with vs_inst_idx := k) = _`
    (mp_then (Pat `run_inst_seq _ _ = _`) mp_tac
       bodyFullRawCallTupleCopyTheory.raw_call_tuple_copy_checked) >>
  qpat_assum `emit_void MSTORE [Var p;ok] s5 = _`
    (fn asm => disch_then (fn th => mp_then (Pat `emit_void MSTORE _ _ = _`) mp_tac th asm)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MCOPY _ _ = _`)) >>
  qpat_assum `lookup_var x (u2 with vs_inst_idx := k) = _`
    (fn asm => disch_then (fn th => mp_then (Pat `lookup_var x _ = _`) mp_tac th asm)) >>
  disch_then (drule_at (Pat `lookup_var p _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ x _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (qspecl_then [`func`,`bs`,`PG`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
      (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) ORELSE
      (disj1_tac >> first_assum ACCEPT_TAC) ORELSE
      (disj2_tac >> first_assum ACCEPT_TAC)))) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)) >>
  `run_inst_seq (emitted_insts s5 sb) (u2 with vs_inst_idx := u2.vs_inst_idx) =
     OK (t with vs_inst_idx := u2.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `t.vs_inst_idx = u2.vs_inst_idx` by
    fs[venomStateTheory.venom_state_component_equality] >>
  `(t with vs_vars := u2.vs_vars) =
     mcopy (b+32) (w2n w) (32 + ((n+31) DIV 32)*32)
       (mstore b (val_to_w256 (BoolV success)) u2)` by
    (qpat_assum `(t with <|vs_vars := _; vs_inst_idx := k|>) = _`
       (mp_tac o Q.AP_TERM `\v. v with vs_inst_idx := u2.vs_inst_idx`) >>
     qpat_assum `t.vs_inst_idx = u2.vs_inst_idx`
       (fn th => simp_tac (srw_ss()) [GSYM th, venomStateTheory.venom_state_fupdselfid,
          venomExecSemanticsTheory.mcopy_def, venomStateTheory.write_memory_with_expansion_def,
          venomStateTheory.mstore_def, LET_THM]) >>
     qpat_assum `t.vs_inst_idx = u2.vs_inst_idx`
       (fn th => simp_tac (srw_ss()) [th, venomStateTheory.venom_state_fupdselfid])) >>
  `!v. not_fresh_at s5 v ==>
       lookup_var v t = lookup_var v u2 /\ FLOOKUP Gf v = FLOOKUP G2 v /\
       op_taint tnf (Var v) = op_taint tn2 (Var v)` by
    (qpat_assum `!v. not_fresh_at s5 v ==> lookup_var v (t with vs_inst_idx := k) = _ /\ _`
       mp_tac >> simp_tac (srw_ss()) [venomStateTheory.lookup_var_def]) >>
  `i.inst_opcode = ALLOCA /\ i.inst_outputs = [p] /\
   FLOOKUP u2.vs_allocas i.inst_id = SOME (b,32+(32+((n+31) DIV 32)*32)) /\
   sf.cs_next_id <= i.inst_id /\ sf.cs_next_var <= s5.cs_next_var` by
    (simp[Abbr `i`, venomInstTheory.mk_inst_def, arithmeticTheory.ADD_ASSOC] >> (gvs[])) >>
  `ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
   (!D. ghost_inv_at D lo dep cenv cx es G2 tn2 u2 ==>
        ghost_inv_at D lo dep cenv cx es Gf tnf t)` by
    (qpat_assum `(t with vs_vars := u2.vs_vars) = _`
       (mp_then (Pat `(t with vs_vars := _) = _`) mp_tac raw_call_tuple_copy_ghost_frame) >>
     qpat_assum `MEM i (fn_insts func)`
       (fn asm => disch_then (fn th => mp_then (Pat `MEM _ _`) mp_tac th asm)) >>
     qpat_assum `ghost_kept_at lo cenv es0 sf G0 tn0 s0 G2 tn2`
       (fn asm => disch_then (fn th => mp_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`) mp_tac th asm)) >>
     disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
     qpat_assum `tnf.t_stor = tn2.t_stor`
       (fn asm => disch_then (fn th => mp_then (Pat `_.t_stor = _.t_stor`) mp_tac th asm)) >>
     disch_then (qspecl_then [`s5`,`p`,`dep`] mp_tac) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es u2`
       (fn asm => disch_then (fn th => mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac th asm)) >>
     disch_then (qspec_then `Gf` mp_tac) >>
          (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (simp_tac bool_ss [LET_THM] >> first_assum ACCEPT_TAC)))) >>
     simp[]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa s5) s G2 tn2` by
    (gen_tac >> qpat_assum `emitted_insts sa s5 = _` SUBST1_TAC >>
     irule instSeqComposePtrTheory.inst_seq_ptr_append_ok >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`G1`,`u`,`tn1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ (emitted_insts sa s4) _ _ _` irule) >>
     qpat_assum `emitted_insts s4 s5 = [i]` SUBST1_TAC >>
     qpat_assum `!D j. inst_seq_ptr D _ _ _ _ _ _ [i] _ _ _` irule) >>
  qexistsl_tac [`Gf`,`tnf`] >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!D. ghost_inv_at D _ _ _ _ _ G2 tn2 u2 ==> _` irule >>
      qpat_assum `!D. ghost_inv_at D _ _ _ _ _ G1 tn1 u ==> _` irule >>
      qpat_assum `!D. ghost_inv_at D _ _ _ _ _ G tn s ==> _` irule >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> qpat_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      irule instSeqComposePtrTheory.inst_seq_ptr_append_ok >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`G2`,`u2`,`tn2`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ (emitted_insts sa s5) _ _ _` irule) >>
      qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ (emitted_insts s5 sb) _ _ _` mp_tac >>
      simp_tac bool_ss [Abbr `k`]) >>
  qexistsl_tac [`p`,`b`] >> rpt conj_tac
  >- metis_tac[]
  >- (qpat_assum `!v. not_fresh_at s5 v ==> lookup_var v t = _ /\ _`
        (qspec_then `p` mp_tac) >>
      impl_tac >- gvs[exprSafeOperandTheory.safe_operand_def] >>
      simp[])
  >- decide_tac
  >- (qpat_assum `ptr_covers Gf tnf p (t with vs_inst_idx := k) _` mp_tac >>
      pure_rewrite_tac[ghostPcTransportPtrTheory.ptr_covers_inst_idx] >> simp_tac bool_ss []) >>
  qpat_assum `!mem. _ ==> val_in_memory (TupleTV _) _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Abbr `bs`]
QED

(* None of the instructions in the tuple suffix observes GAS. *)
Theorem raw_call_positive_tuple_no_gas[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  strip_tac >> drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  gvs[builtinSimpleTheory.compile_select_def, contextTheory.compile_alloc_buffer_def,
      emit_op_def, emit_void_def, compileEnvTheory.fresh_var_def,
      compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_return_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def]
QED

(* Join the physical ownership and ghost representations at the very same
   tuple endpoint. Neither H nor D is used to select the endpoint. *)
Theorem raw_call_positive_tuple_finish_joint[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [Var x;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;Var x;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa (Var x) /\ safe_operand sa ok /\
  lookup_var x s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n data) pre).vs_memory /\
  s.vs_returndata = data /\
  tn.t_mem = old_tn.t_mem DIFF {j | w2n ro <= j /\ j < w2n ro + LENGTH (TAKE n data)} /\
  w2n ro = w2n w + 32 /\ LENGTH data < dimword (:256) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  v = ArrayV (TupleV [BoolV success;BytesV (TAKE n data)]) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  ?u Gf tnf.
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v) vv es Gf tnf u /\
    ptr_buf_ok cenv e result Gf u /\
    (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
         storage_well_formed_on cx es (FST H) ==>
      vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv u /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
        es (Value v) vv u /\
      vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var x) s = SOME w` by simp[venomStateTheory.eval_operand_def] >>
  drule_all raw_call_positive_tuple_endpoint >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `t` strip_assume_tac))) >>
  drule_all raw_call_positive_payload_cut >> strip_tac >>
  `LENGTH s.vs_returndata < dimword (:256)` by simp[] >>
  drule_all raw_call_positive_tuple_ghosts >>
  disch_then (qspecl_then [`dep`,`PG`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac))) >>
  drule_all raw_call_positive_tuple_no_gas >> strip_tac >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  qabbrev_tac `code = emitted_insts sa sb` >>
  `sb.cs_current_insts = sa.cs_current_insts ++ code` by
    (drule rich_listTheory.IS_PREFIX_IMP_TAKE >>
     disch_then (fn th => simp[Abbr `code`, emitted_insts_def, Once th, listTheory.TAKE_DROP])) >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH code = LENGTH sb.cs_current_insts` by
    (qpat_assum `sb.cs_current_insts = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tnf`] >>
  simp_tac bool_ss [venomStateTheory.venom_state_accessors, LET_THM,
                    ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
  drule_all entrySinkExtractionTheory.run_inst_seq_preserves_entry_control >>
  strip_tac >>
  `code ≼ DROP s.vs_inst_idx bb.bb_instructions` by simp[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- simp[]
  >- (qpat_assum `s.vs_inst_idx + LENGTH code = _` (SUBST1_TAC o SYM) >>
      `alloca_inv s` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by
        (qpat_assum `EVERY (\i. _ /\ _) code` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >> metis_tac[]) >>
      qpat_assum `code ≼ DROP s.vs_inst_idx _` mp_tac >>
      simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPEND] >>
      disch_then (qx_choose_then `rest` assume_tac) >>
      irule allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
      goal_assum (drule_at Any) >> gvs[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt gen_tac >>
      qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
        (qspec_then `D` assume_tac) >>
      drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
      simp[])
  >- (simp_tac bool_ss [bodyPtrIfExpAllocSourceTheory.ptr_vv_ok_inst_idx] >>
      qpat_assum `vv = _` SUBST1_TAC >>
      irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
      qpat_assum `result = Var p` SUBST1_TAC >>
      qpat_assum `ptr_covers Gf tnf p t _`
        (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
      simp[mk_ptr_def, read_result_def, return_def,
           bodyPtrDefsTheory.ptr_mem_ok_def, venomStateTheory.eval_operand_def] >>
      rpt strip_tac
      >- (gvs[w2n_n2w] >> first_x_assum irule >> simp[]) >>
      gvs[w2n_n2w, val_store_size_def, type_memory_size_def, word_size_def] >>
      goal_assum (drule_at Any) >> decide_tac)
  >- (simp_tac bool_ss [] >> qpat_assum `result = Var p` SUBST1_TAC >>
      irule rawCallBufferPtrTheory.ptr_buf_ok_from_covers >>
      qexistsl_tac [`64 + ((n+31) DIV 32)*32`,`tnf`] >>
      simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx,
           compileEnvTheory.type_memory_bytes_def] >> decide_tac) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. _ ==> vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  simp[]
QED

(* The zero-capacity suffix either leaves the CALL cursor alone or jumps
   to the successful continuation without changing any framed resource. *)
Theorem raw_call_zero_finish_post[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) 0 rev ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit 0w]
     else [gas_op;to_op;val_op;dp;dl;op;Lit 0w]) sa = (ok,sc) /\
  (rev ==> success) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ op_prov G ok = NONE /\
  fn_has_code sc sb func /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func s /\
  wb_frame cenv es0 es sf s0 s /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\ lowered_value_type cenv e = expr_type e /\
  expr_type e = (if rev then NoneT else BaseT BoolT) ==>
  ?u Gf tnf.
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    u.vs_alloca_next = s.vs_alloca_next /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_vv_ok cx (post_value_type cenv e) (Value (if rev then NoneV else BoolV success)) (StackValue ann
      result) es Gf tnf u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e result Gf u) /\
    (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
         storage_well_formed_on cx es (FST H) ==>
      vv_post H ctx func cenv cx e es0 sf sb s0 es (Value (if rev then NoneV else BoolV success))
        (StackValue ann result) u /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
        es (Value (if rev then NoneV else BoolV success)) (StackValue ann result) u /\
      vv_own cenv cx (post_value_type cenv e) sf sb es (Value (if rev then NoneV else BoolV success))
        (StackValue ann result) u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `u = if rev then jump_to sb.cs_current_bb s else s` >>
  `u = if rev then jump_to sb.cs_current_bb s else s` by simp[Abbr `u`] >>
  drule_all raw_call_zero_normal_suffix_joint >>
  disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >> qpat_x_assum `u = if rev then _ else _` kall_tac >>
  qpat_x_assum `sb.cs_current_insts = if rev then _ else _` kall_tac >>
  simp_tac bool_ss [LET_THM] >> qexistsl_tac [`u`,`G`,`tn`] >>
  asm_rewrite_tac[] >>
  `u.vs_alloca_next = s.vs_alloca_next /\ alloca_history func u` by
    (Cases_on `rev` >> simp[Abbr `u`] >>
     conj_tac >- simp[venomStateTheory.jump_to_def] >>
     irule allocaHistoryTheory.alloca_history_jump >>
     simp[venomStateTheory.jump_to_def] >> qexists_tac `s` >> simp[]) >>
  asm_rewrite_tac[] >>
  `wb_frame cenv es0 es sf s0 u` by
    (`u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
       u.vs_vars = s.vs_vars` by
       (Cases_on `rev` >> simp[Abbr `u`, venomStateTheory.jump_to_def]) >>
     qpat_x_assum `wb_frame cenv es0 es sf s0 s` mp_tac >>
     asm_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def,
       venomStateTheory.lookup_var_def]) >>
  conj_tac
  >- (Cases_on `rev` >> simp[Abbr `u`, bodyFullSharedTheory.ghost_inv_at_jump]) >>
  `!H:(bool # 256 word # type_value) list # num list.
     stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u` by
    (Cases_on `rev` >> simp[Abbr `u`, stmt_state_rel_jump_to]) >>
  Cases_on `rev` >> gvs[compileEnvTheory.is_word_type_def, bodyPtrDefsTheory.ptr_buf_ok_def,
    compileEnvTheory.type_memory_bytes_def] >>
  qx_gen_tac `H` >> strip_tac >>
  rpt conj_tac >> TRY (irule raw_call_none_post >> simp[] >> NO_TAC) >>
  TRY (irule raw_call_bool_post >>
       simp[expr_val_rel_def, compileEnvTheory.is_word_type_def,
            vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
            val_to_w256_def] >> NO_TAC) >>
  simp[vv_store_bound_def, vv_own_def, expr_val_own_def, compileEnvTheory.is_word_type_def,
       vyperValueTheory.evaluate_type_def, read_result_def, return_def,
       val_store_size_def, val_footprint_def, type_memory_size_def]
QED

(* The JNZ moves to the empty good block without touching the CALL packet. *)
Theorem raw_call_positive_bytes_good_entry[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n T (Var x) op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  0 < n /\ eval_operand ok s = SOME 1w /\ op_taint tn ok = {} /\
  fn_has_code sc sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  ?sd. (do len <- emit_op RETURNDATASIZE [];
           cmp <- emit_op LT [len;Lit (n2w n)];
           capped <- compile_select cmp len (Lit (n2w n));
           emit_void MSTORE [Var x;capped]; return (Var x) od) sd = (result,sb) /\
       fn_has_code sd sb func /\ sc.cs_next_var <= sd.cs_next_var /\
       sc.cs_next_id <= sd.cs_next_id /\ sd.cs_current_insts = [] /\
       !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK (jump_to sd.cs_current_bb s),G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_call_finish_revert_compile >> simp[] >> strip_tac >>
  rename1 `fresh_label "call_failed" call_end = (fl,sl)` >>
  rename1 `emit_inst JNZ [status;Label good;Label bad] [] sj = ((),sn)` >>
  `call_end = sc /\ status = ok` by (Cases_on `stat` >> gvs[]) >>
  gvs[] >>
  `ci_mono call_end sl /\ ci_mono sl sj /\ ci_mono sj sn /\
   ci_mono sn s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
      ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, pairTheory.SND]) >>
  drule raw_call_success_code >> strip_tac >>
  `cs_extends s10 sb` by
    (irule compileEnvTheory.cs_extends_same_block >>
     fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends call_end sj /\ cs_extends sj sn /\ cs_extends sn s10 /\
   call_end.cs_next_var <= s10.cs_next_var /\ call_end.cs_next_id <= s10.cs_next_id` by
    (fs[ci_mono_def] >> rpt conj_tac >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sj sn func /\ fn_has_code s10 sb func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_trans, compileEnvTheory.cs_extends_refl] >>
  `s10.cs_current_bb = good /\ s10.cs_current_insts = []` by
    metis_tac[emitHelperPropsTheory.new_block_props] >>
  `sj.cs_current_bb = call_end.cs_current_bb /\ sj.cs_current_insts = call_end.cs_current_insts` by
    (imp_res_tac emitHelperPropsTheory.fresh_label_props >> simp[]) >>
  qexists_tac `s10` >> asm_rewrite_tac[] >> rpt gen_tac >>
  metis_tac[fragGasEmitCtrlTheory.emit_jnz_origin_ptr]
QED

(* Positive successful reverting call: the good block writes the length
   into the live CALL output row; the physical run is fixed before D. *)
Theorem raw_call_positive_bytes_finish_path[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n T (Var x) op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  0 < n /\ n < dimword (:256) /\ 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  eval_operand ok s = SOME 1w /\ op_taint tn ok = {} /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
  sf.cs_next_id <= alloc.inst_id /\ alloc.inst_id < sc.cs_next_id /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  not_fresh_at sc x /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
  ?u Gf tnf.
    result = Var x /\ lookup_var x u = SOME w /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    alloc.inst_id < sb.cs_next_id /\
    wb_frame cenv es0 es sf s0 u /\
    (!H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es u) /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_covers Gf tnf x u (32 + ((n+31) DIV 32)*32) /\
    u.vs_memory = (mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory /\
    (!i. i < w2n w \/ w2n w+32 <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_positive_bytes_good_entry >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choose_then `sd` strip_assume_tac)) >>
  qabbrev_tac `j = jump_to sd.cs_current_bb s` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK j,G,tn)` by simp[Abbr `j`] >>
  `j.vs_allocas = s.vs_allocas /\ j.vs_alloca_next = s.vs_alloca_next /\
    ~j.vs_halted /\ j.vs_current_bb = sd.cs_current_bb /\ j.vs_inst_idx = LENGTH sd.cs_current_insts /\
    j.vs_returndata = s.vs_returndata /\ j.vs_memory = s.vs_memory /\
    lookup_var x j = SOME w /\ ptr_covers G tn x j (32 + ((n+31) DIV 32)*32) /\
    allocas_from lo j /\ alloca_history func j /\ wb_frame cenv es0 es sf s0 j` by
    suspend "jump" >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es j <=> stmt_state_rel H ctx func cenv cx es s` by
    simp[Abbr `j`, stmt_state_rel_jump_to] >>
  `?len se cmp sg capped sh.
     emit_op RETURNDATASIZE [] sd = (len,se) /\
     emit_op LT [len;Lit (n2w n)] se = (cmp,sg) /\
     compile_select cmp len (Lit (n2w n)) sg = (capped,sh) /\
     emit_void MSTORE [Var x;capped] sh = ((),sb)` by suspend "split_code" >>
  `not_fresh_at sd x /\ safe_operand sd (Var x) /\ local_ptrs_reserved cenv sd /\
   sf.cs_next_var <= sd.cs_next_var` by
    (simp[exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var,
               arithmeticTheory.LESS_EQ_TRANS]) >>
  `?t. run_inst_seq (emitted_insts sd sb) j = OK t /\
    wb_frame cenv es0 es sf s0 t /\
    (!H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es j ==> stmt_state_rel H ctx func cenv cx es t) /\
    (t with vs_vars := j.vs_vars) = mstore (w2n w) (n2w (LENGTH (TAKE n j.vs_returndata))) j` by
    suspend "runtime" >>
  suspend "counted"
QED

Resume raw_call_positive_bytes_finish_path[jump]:
  simp_tac bool_ss [LET_THM] >>
  `j.vs_allocas = s.vs_allocas /\ j.vs_alloca_next = s.vs_alloca_next /\
   j.vs_memory = s.vs_memory /\ j.vs_vars = s.vs_vars` by
    simp[Abbr `j`, venomStateTheory.jump_to_def] >>
  `wb_frame cenv es0 es sf s0 j` by
    (qpat_x_assum `wb_frame cenv es0 es sf s0 s` mp_tac >>
     asm_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def,
       venomStateTheory.lookup_var_def]) >>
  `alloca_history func j` by
    (simp_tac bool_ss [Abbr `j`, venomStateTheory.jump_to_def] >>
     irule allocaHistoryTheory.alloca_history_jump >> simp[] >> qexists_tac `s` >> simp[]) >>
  `ptr_covers G tn x j (32 + ((n+31) DIV 32)*32)` by
    (qpat_x_assum `ptr_covers G tn x s _` mp_tac >>
     simp[Abbr `j`, bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.jump_to_def,
          venomStateTheory.lookup_var_def]) >>
  `allocas_from lo j` by
    (qpat_x_assum `allocas_from lo s` mp_tac >>
     simp[Abbr `j`, ptrDisciplineTheory.allocas_from_def, venomStateTheory.jump_to_def]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `j`, venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def]
QED

Resume raw_call_positive_bytes_finish_path[split_code]:
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_select _ _ _ _ = _`)) >>
  gvs[]
QED

Resume raw_call_positive_bytes_finish_path[runtime]:
  `FLOOKUP j.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32)` by simp[] >>
  `LENGTH j.vs_returndata < dimword (:256) /\
   mem_bytes_at (w2n w+32) (LENGTH (TAKE n j.vs_returndata)) j.vs_memory = TAKE n j.vs_returndata /\
   (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n j.vs_returndata) ==>
        i NOTIN tn.t_mem)` by simp[] >>
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es j ==>
    ?t. run_inst_seq (emitted_insts sd sb) j = OK t /\
        wb_frame cenv es0 es sf s0 t /\ stmt_state_rel H ctx func cenv cx es t /\
        (t with vs_vars := j.vs_vars) = mstore (w2n w) (n2w (LENGTH (TAKE n j.vs_returndata))) j` by
    (gen_tac >> disch_tac >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es j`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_call_tuple_length_cut) >>
     disch_then drule_all >>
     disch_then (qspec_then `PG` strip_assume_tac) >>
     goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
     asm_rewrite_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx es j` by simp[] >>
  qpat_assum `!H. stmt_state_rel H ctx func cenv cx es j ==> ?t. _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es j` by simp[] >>
  qpat_x_assum `!H. stmt_state_rel H ctx func cenv cx es j ==> ?t. _` drule >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u = t` by (qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >> simp[]) >>
  gvs[]
QED

Resume raw_call_positive_bytes_finish_path[counted]:
  `stmt_state_rel H0 ctx func cenv cx es j` by simp[] >>
  `FLOOKUP j.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32)` by simp[] >>
  `alloca_inv j` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es j`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  `w2n w + 32 + ((n+31) DIV 32)*32 <= j.vs_alloca_next` by
    (qpat_assum `alloca_inv j`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     qpat_assum `!aid b k. FLOOKUP j.vs_allocas aid = SOME (b,k) ==> _` drule >>
     rewrite_tac[arithmeticTheory.ADD_ASSOC]) >>
  `j.vs_alloca_next < dimword (:256)` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es j`
       (mp_then Any mp_tac stmt_state_rel_alloca_room) >> simp[alloca_room_def] >> decide_tac) >>
  `w2n w + 32 + ((n+31) DIV 32)*32 < dimword (:256)` by decide_tac >>
  `lo <= w2n w` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `n <= ((n+31) DIV 32)*32` by
    (qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def] >> decide_tac) >>
  `lookup_var x j = SOME (n2w (w2n w))` by simp[] >>
  `LENGTH j.vs_returndata < dimword (:256) /\
   mem_bytes_at (w2n w+32) (LENGTH (TAKE n j.vs_returndata)) j.vs_memory = TAKE n j.vs_returndata /\
   (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n j.vs_returndata) ==>
        i NOTIN tn.t_mem)` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp j` by
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es j`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  drule_at (Pat `run_inst_seq _ _ = _`) raw_call_bytes_success_full_path >>
  disch_then (drule_at (Pat `comp_bind _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`lo`,`func`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [] >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)) >>
  `32 <= 32 + ((n+31) DIV 32)*32` by decide_tac >>
  `ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tf /\
   (!D. ghost_inv_at D lo dep cenv cx es G tn j ==>
        ghost_inv_at D lo dep cenv cx es Gf tf t)` by
    (drule_at (Pat `(t with vs_vars := _) = _`) raw_call_tuple_length_ghost_frame >>
     disch_then drule_all >> simp[]) >>
  `ci_mono sd se /\ ci_mono se sg /\ ci_mono sg sh /\ ci_mono sh sb` by
    (rpt conj_tac >> metis_tac[ci_mono_emit_op, ci_mono_compile_select, ci_mono_emit_void, pairTheory.SND]) >>
  `alloc.inst_id < sb.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `t.vs_memory = (mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory` by
    (qpat_assum `(t with vs_vars := _) = _` (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >>
     simp[venomStateTheory.mstore_def]) >>
  `!i. i < w2n w \/ w2n w+32 <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt (gen_tac ORELSE disch_tac) >> simp_tac bool_ss [] >>
     qpat_assum `t.vs_memory = (mstore _ _ s).vs_memory` SUBST1_TAC >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
       ghost_inv_at D lo dep cenv cx es Gf tf t` by
    (gen_tac >> strip_tac >> first_assum irule >>
     simp[Abbr `j`, bodyFullSharedTheory.ghost_inv_at_jump]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _` (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (j,G,tn) [] _` (qspecl_then [`D`,`explicit`] mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND_NIL]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tf`] >>
  simp_tac bool_ss [venomStateTheory.venom_state_accfupds, LET_THM, combinTheory.K_THM,
    venomStateTheory.lookup_var_def, ghostPcTransportPtrTheory.ptr_covers_inst_idx,
    raw_call_wb_frame_inst_idx, stmt_state_rel_inst_idx,
    ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
  qpat_assum `lookup_var x t = _` (assume_tac o REWRITE_RULE [venomStateTheory.lookup_var_def, n2w_w2n]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> strip_tac >> first_assum irule >> simp[]) >>
  qpat_assum `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> _` mp_tac >>
  qpat_assum `j.vs_returndata = _` (rewrite_tac o single) >>
  qpat_assum `tf.t_mem = _` (rewrite_tac o single) >>
  qpat_assum `t.vs_memory = _` (rewrite_tac o single)
QED

Finalise raw_call_positive_bytes_finish_path

Theorem raw_call_positive_bytes_finish_post[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n T (Var x) op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  0 < n /\ n < dimword (:256) /\ 64 + ((n+31) DIV 32)*32 < dimword (:256) /\
  eval_operand ok s = SOME 1w /\ op_taint tn ok = {} /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
  sf.cs_next_id <= alloc.inst_id /\ alloc.inst_id < sc.cs_next_id /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  not_fresh_at sc x /\ lookup_var x s = SOME w /\
  ptr_covers G tn x s (32 + ((n+31) DIV 32)*32) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  v = BytesV (TAKE n s.vs_returndata) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  ?u Gf tnf.
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    u.vs_alloca_next = s.vs_alloca_next /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
      ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v) vv es Gf tnf u /\
    ptr_buf_ok cenv e result Gf u /\
    (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
         storage_well_formed_on cx es (FST H) ==>
      vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv u /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
        es (Value v) vv u /\
      vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_positive_bytes_finish_path >>
  disch_then (qspecl_then [`dep`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)))) >>
  qabbrev_tac `cap = 32 + ((n+31) DIV 32)*32` >>
  `stmt_state_rel H0 ctx func cenv cx es u /\
   FLOOKUP u.vs_allocas alloc.inst_id = SOME (w2n w,cap) /\
   eval_operand result u = SOME w` by
    simp[Abbr `cap`, venomStateTheory.eval_operand_def] >>
  qpat_assum `stmt_state_rel H0 ctx func cenv cx es u`
    (mp_then Any strip_assume_tac stmt_state_rel_local_ptrs_alloca) >>
  `!name lb lsz. local_region cenv es.scopes u name lb lsz ==>
      w2n w + cap <= lb \/ lb + lsz <= w2n w` by suspend "regions" >>
  `w2n w + cap <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     qpat_assum `!aid b k. FLOOKUP u.vs_allocas aid = SOME (b,k) ==> _` drule >> simp[]) >>
  `type_memory_size (BaseTV (BytesT (Dynamic n))) = cap /\
   ~is_word_type (expr_type e) /\
   evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n)))` by
    (simp[Abbr `cap`, type_memory_size_def, word_size_def, vyperValueTheory.type_slot_size_def,
      compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def] >>
     decide_tac) >>
  `val_wf (BaseTV (BytesT (Dynamic n))) v` by
    (simp[valueEncodingDefsTheory.val_wf_def, listTheory.LENGTH_TAKE_EQ,
       type_memory_size_def] >>
     qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def, Abbr `cap`] >>
     IF_CASES_TAC >> decide_tac) >>
  `val_footprint (BaseTV (BytesT (Dynamic n))) v <= cap` by
    metis_tac[val_footprint_le] >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "ptr_value" >>
  conj_tac
  >- (qpat_assum `result = _` SUBST1_TAC >>
      irule rawCallBufferPtrTheory.ptr_buf_ok_from_covers >>
      qexistsl_tac [`cap`,`tnf`] >>
      simp[Abbr `cap`, compileEnvTheory.type_memory_bytes_def]) >>
  suspend "vv_post"
QED

Resume raw_call_positive_bytes_finish_post[regions]:
  rpt gen_tac >> disch_tac >>
  `regions_disjoint (w2n w) cap lb lsz` by
    (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`,`func`,`alloc`,`name`,`q`,`es.scopes`,`u`] >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume raw_call_positive_bytes_finish_post[ptr_value]:
  qpat_assum `vv = _` SUBST1_TAC >>
  qpat_assum `result = _` SUBST1_TAC >>
  irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
  simp[mk_ptr_def, read_result_def, return_def] >>
  conj_tac >- fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `ptr_val_ok cx (post_value_type cenv e) v (Var x) Gf tnf u` by
    (irule rawCallBufferPtrTheory.ptr_val_ok_from_type_covers >>
     gvs[]) >>
  gvs[bodyPtrDefsTheory.ptr_val_ok_def]
QED

Resume raw_call_positive_bytes_finish_post[vv_post]:
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es u` by simp[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) v (w2n w) u.vs_memory` by
    (qpat_assum `!mem. mem_agree_outside _ _ mem ==> _`
       (qspec_then `u.vs_memory` mp_tac) >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  conj_asm1_tac
  >- (qpat_assum `vv = _` SUBST1_TAC >>
      qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
      irule vv_post_allocated_memory_intro >> simp[mk_ptr_def] >>
      qexistsl_tac [`alloc.inst_id`,`w2n w`,`cap`,`w`] >>
      gvs[venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `vv = _` SUBST1_TAC >>
      qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
      irule (INST_TYPE [alpha |-> ``:256``] vv_store_bound_capacity) >> simp[mk_ptr_def] >>
      conj_tac
      >- (qexists_tac `w` >> gvs[venomStateTheory.eval_operand_def]) >>
      qexistsl_tac [`H`,`cenv`,`ctx`,`es0`,`func`,`s0`,`sf`,`sb`] >> gvs[mk_ptr_def]) >>
  gvs[vv_own_def, mk_ptr_def, read_result_def, return_def] >>
  disj1_tac >>
  qexistsl_tac [`alloc.inst_id`,`w2n w`,`type_memory_size (BaseTV (BytesT (Dynamic n)))`] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise raw_call_positive_bytes_finish_post

Theorem raw_call_finish_continuation_full:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n rev ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ op_prov G ok = NONE /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\ LENGTH (s.vs_returndata) < dimword (:256) /\
  stmt_state_rel (H0:(bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\ wb_frame cenv
    es0 es sf s0 s /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  (!a sz. cenv.ce_return_buf = SOME (PtrVar (Var a) sz) ==> not_fresh_at sf a) /\
  (!a sz. cenv.ce_return_pc = SOME (PtrVar (Var a) sz) ==> not_fresh_at sf a) /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = (if n = 0 then (if rev then NoneT else BaseT
    BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) /\
  (0 < n /\ (~rev \/ success) ==>
    ?x w alloc q pre (ro:'a word) old_tn.
      ov = Var x /\ n < dimword (:256) /\ 32 + (32 + ((n + 31) DIV 32) * 32) < dimword (:256) /\
      MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
      alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
      FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,(32 + ((n + 31) DIV 32) * 32)) /\
      local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
      sf.cs_next_var <= sc.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
      alloc.inst_id < sc.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
      not_fresh_at sc x /\ lookup_var x s = SOME w /\ ptr_covers G tn x s (32 + ((n + 31) DIV 32) * 32) /\
      w2n ro = w2n w + 32 /\
      s.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE n (s.vs_returndata)) pre).vs_memory /\
      tn.t_mem = old_tn.t_mem DIFF
        {i | i | w2n ro <= i /\ i < w2n ro + LENGTH (TAKE n (s.vs_returndata))} /\
      (~rev ==> safe_operand sc ok /\ evaluate_type (get_tenv cx) (if n = 0 then (if rev then NoneT else
        BaseT BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT
        (Dynamic n))]) =
        SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]))) ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (r,Gf,tnf)) /\
    (if rev /\ ~success then
       ?u. r = Abort Revert_abort u /\ u.vs_returndata = (s.vs_returndata) /\
           expr_exit (INR (Error (RevertData (s.vs_returndata)))) r /\
           !H. halt_exit H cx es (INR (Error (RevertData (s.vs_returndata)))) r
     else
       ?u. r = OK u /\ ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
       ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
       (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
         ghost_inv_at D lo dep cenv cx es Gf tnf u) /\
       ptr_vv_ok cx (post_value_type cenv e) (Value (if n = 0 then (if rev then NoneV else BoolV success)
         else if rev then BytesV (TAKE n (s.vs_returndata)) else ArrayV (TupleV [BoolV success;BytesV (TAKE
         n (s.vs_returndata))]))) (if n = 0 then StackValue ann result else LocatedValue (if n = 0 then (if
         rev then NoneT else BaseT BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT
         BoolT;BaseT (BytesT (Dynamic n))]) (mk_ptr result LocMemory)) es Gf tnf u /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e result Gf u) /\
       (!H:(bool # 256 word # type_value) list # num list.
         stmt_state_rel H ctx func cenv cx es s /\
            storage_well_formed_on cx es (FST H) ==>
         vv_post H ctx func cenv cx e es0 sf sb s0 es (Value (if n = 0 then (if rev then NoneV else BoolV
           success) else if rev then BytesV (TAKE n (s.vs_returndata)) else ArrayV (TupleV [BoolV
           success;BytesV (TAKE n (s.vs_returndata))]))) (if n = 0 then StackValue ann result else
           LocatedValue (if n = 0 then (if rev then NoneT else BaseT BoolT) else if rev then BaseT (BytesT
           (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) (mk_ptr result LocMemory)) u /\
         vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
           es (Value (if n = 0 then (if rev then NoneV else BoolV success) else if rev then BytesV (TAKE n
             (s.vs_returndata)) else ArrayV (TupleV [BoolV success;BytesV (TAKE n (s.vs_returndata))]))) (if
             n = 0 then StackValue ann result else LocatedValue (if n = 0 then (if rev then NoneT else BaseT
             BoolT) else if rev then BaseT (BytesT (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT
             (Dynamic n))]) (mk_ptr result LocMemory)) u /\
         vv_own cenv cx (post_value_type cenv e) sf sb es (Value (if n = 0 then (if rev then NoneV else
           BoolV success) else if rev then BytesV (TAKE n (s.vs_returndata)) else ArrayV (TupleV [BoolV
           success;BytesV (TAKE n (s.vs_returndata))]))) (if n = 0 then StackValue ann result else
           LocatedValue (if n = 0 then (if rev then NoneT else BaseT BoolT) else if rev then BaseT (BytesT
           (Dynamic n)) else TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) (mk_ptr result LocMemory)) u))
Proof
  simp_tac bool_ss [LET_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `rev /\ ~success` >- suspend "revert" >>
  Cases_on `n = 0` >- suspend "zero" >>
  qpat_x_assum `_ ==> ?x w alloc q pre ro old_tn. _` mp_tac >>
  (impl_tac >- gvs[]) >>
  disch_then (qx_choose_then `x` (qx_choose_then `w`
    (qx_choose_then `alloc` (qx_choose_then `q`
      (qx_choose_then `pre` (qx_choose_then `ro`
        (qx_choose_then `old_tn` (map_every assume_tac o CONJUNCTS)))))))) >>
  Cases_on `rev` >- suspend "bytes" >>
  suspend "tuple"
QED

Resume raw_call_finish_continuation_full[revert]:
  gvs[] >>
  drule_all bodyFullRawCallRevertExitTheory.raw_call_revert_suffix_full_exit >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Abort Revert_abort u`,`Gf`,`tnf`] >> simp[exprSimDefsTheory.halt_exit_def]
QED

Resume raw_call_finish_continuation_full[zero]:
  qpat_x_assum `n = 0` SUBST_ALL_TAC >>
  qpat_x_assum `emit_op _ _ _ = _` (assume_tac o SRULE []) >>
  qpat_x_assum `expr_type e = _` (assume_tac o SRULE []) >>
  `(rev ==> success)` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by metis_tac[] >>
  drule_all raw_call_zero_finish_post >>
  disch_then (qspecl_then [`dep`,`cx`,`ann`,`PG`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`OK u`,`Gf`,`tnf`] >> gvs[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Resume raw_call_finish_continuation_full[bytes]:
  qpat_x_assum `ov = Var x` SUBST_ALL_TAC >>
  `success` by fs[] >>
  `0 < n /\ 64 + ((n+31) DIV 32)*32 < dimword (:256)` by decide_tac >>
  `eval_operand ok s = SOME 1w` by simp[] >>
  `expr_type e = BaseT (BytesT (Dynamic n))` by fs[] >>
  drule_all (REWRITE_RULE [] (Q.INST [`data` |-> `u.vs_returndata`] raw_call_positive_payload_cut)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[] >>
  qabbrev_tac `v = BytesV (TAKE n s.vs_returndata)` >>
  qabbrev_tac `vv = LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr result LocMemory)` >>
  `v = BytesV (TAKE n s.vs_returndata) /\ vv = LocatedValue (expr_type e) (mk_ptr result LocMemory)` by
    simp[Abbr `v`, Abbr `vv`] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by metis_tac[] >>
  drule_all raw_call_positive_bytes_finish_post >>
  disch_then (qspecl_then [`dep`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gf`
      (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS))))) >>
  qexistsl_tac [`OK u`,`Gf`,`tnf`] >> gvs[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Resume raw_call_finish_continuation_full[tuple]:
  qpat_x_assum `ov = Var x` SUBST_ALL_TAC >>
  drule raw_call_nonrevert_finish_code >>
  disch_then (qx_choose_then `ok1` (qx_choose_then `sc1`
    (map_every assume_tac o CONJUNCTS))) >>
  `(ok1,sc1) = (ok,sc)` by (Cases_on `stat` >> fs[]) >>
  pop_assum (map_every SUBST_ALL_TAC o CONJUNCTS o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  `safe_operand sc (Var x)` by simp[exprSafeOperandTheory.safe_operand_def] >>
  `0 < n /\ 64 + ((n+31) DIV 32)*32 < dimword (:256)` by decide_tac >>
  `expr_type e = TupleT [BaseT BoolT; BaseT (BytesT (Dynamic n))]` by fs[] >>
  `safe_operand sc ok /\ evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])` by fs[] >>
  simp[] >>
  qabbrev_tac `v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])` >>
  qabbrev_tac `vv = LocatedValue (TupleT [BaseT BoolT; BaseT (BytesT (Dynamic n))])
     (mk_ptr result LocMemory)` >>
  `v = ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]) /\
   vv = LocatedValue (expr_type e) (mk_ptr result LocMemory)` by simp[Abbr `v`, Abbr `vv`] >>
  drule_all (REWRITE_RULE [] (Q.INST [`data` |-> `s.vs_returndata`] raw_call_positive_tuple_finish_joint)) >>
  disch_then (qspecl_then [`dep`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gf`
      (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS))))) >>
  qexistsl_tac [`OK u`,`Gf`,`tnf`] >> gvs[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Finalise raw_call_finish_continuation_full
