(* Positive successful raw CALL: the old output row gets one header write. *)
Theory bodyRawBufferedBytesFrameMods
Ancestors
  emitHelperProps[qualified,ignore_grammar] compileEnv[qualified,ignore_grammar]
  rich_list[qualified,ignore_grammar] ptrDiscipline[qualified,ignore_grammar]
  bodyFullRawCallBytes bodyFullRawCallTupleLength bodyFullRawCallTupleWriteFrame
  bodyFullRawCallFinishJoint bodyFullHashKeccakFixed[qualified,ignore_grammar]
  exprSimRawCall exprSimRawCallCalldata exprSimMemDefs stateRelProj
  exprSimProps valueEncoding valueTypingMemoryProps loweringPosts
  vfmConstants context vyperState venomMemDefs exprSimHash exprLowering
  exprLoweringProps loweringHalt fragExec fragExecMem instIdxIndep
  words list emitHelper venomInst
  fragGasEmitCtrl[qualified,ignore_grammar] venomMemProps[qualified,ignore_grammar]
Libs
  monadsyntax

Theorem raw_buffered_bytes_jump[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    call_ty n T (Var x) op sa = (result,sb) /\
  (case call_ty of
    RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]
  | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]
  | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
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
  `call_end = sc /\ status = ok` by (Cases_on `call_ty` >> gvs[]) >>
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

(* Properties of the exact MSTORE state equation, not of an opaque view. *)
Theorem raw_buffered_bytes_store_fields[local]:
  (t with vs_vars := j.vs_vars) = mstore a len j /\
  j = jump_to bb s ==>
  t.vs_memory = (mstore a len s).vs_memory /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  t.vs_data_section = s.vs_data_section /\ t.vs_returndata = s.vs_returndata /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `t.vs_memory = (mstore a len s).vs_memory` by
    (qpat_assum `(t with vs_vars := _) = _` (mp_tac o Q.AP_TERM `\v. v.vs_memory`) >>
     simp[venomStateTheory.mstore_def, venomStateTheory.jump_to_def]) >>
  simp[venomMemPropsTheory.mstore_memory_nondecreasing] >>
  qpat_assum `(t with vs_vars := _) = _` mp_tac >>
  simp[venomStateTheory.venom_state_component_equality, venomStateTheory.mstore_def,
    venomStateTheory.jump_to_def]
QED

Theorem raw_buffered_bytes_run[local]:
  emit_op RETURNDATASIZE [] sd = (len,se) /\
  emit_op LT [len;Lit (n2w n)] se = (cmp,sg) /\
  compile_select cmp len (Lit (n2w n)) sg = (capped,sh) /\
  emit_void MSTORE [Var x;capped] sh = ((),sb) /\
  safe_operand sd (Var x) /\ n < dimword (:256) /\
  LENGTH j.vs_returndata < dimword (:256) /\ lookup_var x j = SOME w /\
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n j.vs_returndata)) j.vs_memory =
    TAKE n j.vs_returndata /\
  stmt_state_rel H ctx func cenv cx es j /\
  wb_frame cenv es0 es sf s0 j /\ local_ptrs_reserved cenv sd /\
  sf.cs_next_var <= sd.cs_next_var /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\ sf.cs_next_id <= alloc.inst_id /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP j.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) ==>
  ?t. run_inst_seq (emitted_insts sd sb) j = OK t /\
      stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t
Proof
  strip_tac >>
  `eval_operand (Var x) j = SOME w` by simp[venomStateTheory.eval_operand_def] >>
  `stmt_state_rel H ctx func cenv cx es (j with vs_fmp := j.vs_fmp)` by simp[] >>
  `w2n w <= w2n w /\ w2n w + 32 <= w2n w + (32 + ((n+31) DIV 32)*32)` by decide_tac >>
  drule_all raw_call_output_prefix_ready >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `t with vs_fmp := j.vs_fmp = t` by
    (qpat_assum `t.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >>
  qexists_tac `t` >> fs[]
QED

(* Obtain row separation at the entry state; transport old local regions
   through the writeback frame, not through the result representation. *)
Theorem raw_buffered_bytes_row_exclusions[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (b,k) /\ 32 <= k /\
  sf.cs_next_id <= alloc.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es0 es sf s0 s /\ allocas_from lo s ==>
  let R = {i | b <= i /\ i < b+32} in
    (!i. i < lo ==> i NOTIN R) /\
    (!name a m i. local_region cenv es.scopes s name a m /\ a <= i /\ i < a+m ==>
       i NOTIN R) /\
    (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
       aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> i NOTIN R) /\
    (!name a m i. local_region cenv es0.scopes s0 name a m /\ a <= i /\ i < a+m ==>
       i NOTIN R)
Proof
  strip_tac >> drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `!aid a m. FLOOKUP s.vs_allocas aid = SOME (a,m) /\ aid < alloc.inst_id ==>
     a+m <= b \/ b+k <= a` by
    (rpt strip_tac >> `aid <> alloc.inst_id` by decide_tac >>
     fs[alloca_inv_def,venomMemDefsTheory.allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`aid`,`alloc.inst_id`] mp_tac) >> simp[]) >>
  `lo <= b` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  simp_tac bool_ss [LET_THM] >>
  conj_tac >- (simp[] >> decide_tac) >>
  `!name a m i. local_region cenv es.scopes s name a m /\ a <= i /\ i < a+m ==>
      i NOTIN {i | b <= i /\ i < b+32}` by
    (rpt strip_tac >> drule_all localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  conj_tac
  >- (simp[] >> rpt strip_tac >>
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

Theorem raw_buffered_bytes_kept[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (b,k) /\ 32 <= k /\
  sf.cs_next_id <= alloc.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es0 es sf s0 s /\ allocas_from lo s /\
  sf.cs_next_var <= sc.cs_next_var /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v. not_fresh_at sc v ==> lookup_var v t = lookup_var v s /\
       FLOOKUP Gf v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v)) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  tf.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32} /\
  (!i. i < b \/ b+32 <= i ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tf
Proof
  strip_tac >>
  drule_all raw_buffered_bytes_row_exclusions >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  `!v. not_fresh_at sf v ==> lookup_var v t = lookup_var v s /\
       FLOOKUP Gf v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v)` by
    (gen_tac >> disch_tac >> `not_fresh_at sc v` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]) >>
  qabbrev_tac `R = {i | b <= i /\ i < b+32}` >>
  `!i. i NOTIN R ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (simp[Abbr `R`] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!i. i NOTIN R /\ i IN tf.t_mem ==> i IN tn.t_mem` by simp[Abbr `R`] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[bodyPtrDefsTheory.ghost_kept_at_def] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem raw_buffered_bytes_path[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    call_ty n T (Var x) op sa = (result,sb) /\
  (case call_ty of
    RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]
  | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]
  | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
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
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory = TAKE n s.vs_returndata /\
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
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_covers Gf tnf x u (32 + ((n+31) DIV 32)*32) /\
    u.vs_memory = (mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory /\
    (!i. i < w2n w \/ w2n w+32 <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    u.vs_data_section = s.vs_data_section /\ u.vs_returndata = s.vs_returndata /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!v. not_fresh_at sc v ==> lookup_var v u = lookup_var v s /\
       FLOOKUP Gf v = FLOOKUP G v /\ op_taint tnf (Var v) = op_taint tn (Var v)) /\
    (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_buffered_bytes_jump >>
  disch_then (qspecl_then [`PG`,`G`] (qx_choose_then `sd` strip_assume_tac)) >>
  qabbrev_tac `j = jump_to sd.cs_current_bb s` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK j,G,tn)` by simp[Abbr `j`] >>
  `j.vs_allocas = s.vs_allocas /\ j.vs_alloca_next = s.vs_alloca_next /\
    ~j.vs_halted /\ j.vs_current_bb = sd.cs_current_bb /\ j.vs_inst_idx = LENGTH sd.cs_current_insts /\
    j.vs_returndata = s.vs_returndata /\ j.vs_memory = s.vs_memory /\
    (!v. lookup_var v j = lookup_var v s) /\
    ptr_covers G tn x j (32 + ((n+31) DIV 32)*32) /\
    allocas_from lo j /\ alloca_history func j /\ wb_frame cenv es0 es sf s0 j` by
    suspend "jump_fields" >>
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
  `FLOOKUP j.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
   lookup_var x j = SOME w /\ LENGTH j.vs_returndata < dimword (:256) /\
   mem_bytes_at (w2n w+32) (LENGTH (TAKE n j.vs_returndata)) j.vs_memory = TAKE n j.vs_returndata /\
   (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n j.vs_returndata) ==>
        i NOTIN tn.t_mem)` by simp[] >>
  `?t. run_inst_seq (emitted_insts sd sb) j = OK t /\
    wb_frame cenv es0 es sf s0 t /\
    (!H:(bool # 256 word # type_value) list # num list.
      stmt_state_rel H ctx func cenv cx es s ==> stmt_state_rel H ctx func cenv cx es t)` by
    suspend "run" >>
  suspend "footprint"
QED

Resume raw_buffered_bytes_path[jump_fields]:
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

Resume raw_buffered_bytes_path[split_code]:
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op LT _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_select _ _ _ _ = _`)) >>
  gvs[]
QED

Resume raw_buffered_bytes_path[run]:
  `!H:(bool # 256 word # type_value) list # num list.
    stmt_state_rel H ctx func cenv cx es s ==>
    ?t. run_inst_seq (emitted_insts sd sb) j = OK t /\
        wb_frame cenv es0 es sf s0 t /\ stmt_state_rel H ctx func cenv cx es t` by
    (gen_tac >> disch_tac >>
     `stmt_state_rel H ctx func cenv cx es j` by simp[] >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es j`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac raw_buffered_bytes_run) >>
     disch_then drule_all >>
     disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> asm_rewrite_tac[]) >>
  qpat_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> ?t. _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_x_assum `!H. stmt_state_rel H ctx func cenv cx es s ==> ?t. _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `u = t` by (qpat_x_assum `run_inst_seq _ _ = OK u` mp_tac >> simp[]) >>
  gvs[]
QED

Resume raw_buffered_bytes_path[footprint]:
  `stmt_state_rel H0 ctx func cenv cx es j` by simp[] >>
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
  `w2n w + (32 + ((n+31) DIV 32)*32) < dimword (:256) /\
   w2n w + 32 + ((n+31) DIV 32)*32 < dimword (:256)` by decide_tac >>
  `lo <= w2n w` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `n <= ((n+31) DIV 32)*32` by
    (qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def] >> decide_tac) >>
  `lookup_var x j = SOME (n2w (w2n w))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp j` by
    qpat_assum `stmt_state_rel H0 ctx func cenv cx es j`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  drule_all raw_call_tuple_length_checked >>
  disch_then (qspecl_then [`func`,`PG`]
    (qx_choose_then `Gcheck` (qx_choose_then `tcheck` strip_assume_tac))) >>
  `j = jump_to sd.cs_current_bb s` by simp[Abbr `j`] >>
  drule_all raw_buffered_bytes_store_fields >> strip_tac >>
  `t.vs_memory = (mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory` by
    (qpat_assum `t.vs_memory = (mstore _ _ s).vs_memory` mp_tac >> simp[]) >>
  drule_at (Pat `run_inst_seq _ _ = _`) raw_call_bytes_success_full_path >>
  disch_then (drule_at (Pat `comp_bind _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers G tn x j _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`lo`,`func`,`ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp_tac bool_ss [] >> asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL])) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)) >>
  `ci_mono sd se /\ ci_mono se sg /\ ci_mono sg sh /\ ci_mono sh sb` by
    (rpt conj_tac >> metis_tac[ci_mono_emit_op, ci_mono_compile_select,
      ci_mono_emit_void, pairTheory.SND]) >>
  `alloc.inst_id < sb.cs_next_id` by
    (ntac 4 (qpat_x_assum `ci_mono _ _` (strip_assume_tac o REWRITE_RULE [ci_mono_def])) >>
     decide_tac) >>
  `!v. not_fresh_at sc v ==> lookup_var v t = lookup_var v s /\
       FLOOKUP Gf v = FLOOKUP G v /\ op_taint tf (Var v) = op_taint tn (Var v)` by
    (gen_tac >> disch_tac >> `not_fresh_at sd v` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]) >>
  `!i. i < w2n w \/ w2n w+32 <= i ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt (gen_tac ORELSE disch_tac) >>
     qpat_assum `t.vs_memory = (mstore _ _ s).vs_memory` SUBST1_TAC >>
     irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  `ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tf` by
    (`32 <= 32 + ((n+31) DIV 32)*32` by decide_tac >>
     irule raw_buffered_bytes_kept >> asm_rewrite_tac[] >>
     qpat_assum `FLOOKUP s.vs_allocas alloc.inst_id = SOME _`
       (irule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx es s` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn`
       (irule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`t`,`sc`,`q`] >> asm_rewrite_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tf)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _` (qspecl_then [`D`,`explicit`] mp_tac) >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (j,G,tn) [] _` (qspecl_then [`D`,`explicit`] mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND_NIL]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`Gf`,`tf`] >>
  simp_tac bool_ss [venomStateTheory.venom_state_accfupds, LET_THM, combinTheory.K_THM,
    venomStateTheory.lookup_var_def, ghostPcTransportPtrTheory.ptr_covers_inst_idx,
    raw_call_wb_frame_inst_idx, stmt_state_rel_inst_idx] >>
  qpat_assum `lookup_var x t = _` (assume_tac o REWRITE_RULE [venomStateTheory.lookup_var_def, n2w_w2n]) >>
  qpat_assum `!v. not_fresh_at sc v ==> lookup_var _ _ = _ /\ _`
    (assume_tac o REWRITE_RULE [venomStateTheory.lookup_var_def]) >>
  asm_rewrite_tac[] >>
  qpat_assum `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> _` mp_tac >>
  qpat_assum `j.vs_returndata = _` (rewrite_tac o single) >>
  qpat_assum `tf.t_mem = _` (rewrite_tac o single) >>
  qpat_assum `t.vs_memory = (mstore _ (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory`
    (rewrite_tac o single)
QED

Finalise raw_buffered_bytes_path

(* The physical endpoint is also the ordinary value-post endpoint.  Keep its
   exact header footprint for the separate linked-frame transport. *)
Theorem raw_buffered_bytes_finish_frame:
  compile_raw_call_finish to_op dp dl gas_op val_op
    call_ty n T (Var x) op sa = (result,sb) /\
  (case call_ty of
    RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]
  | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]
  | DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
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
  mem_bytes_at (w2n w+32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory = TAKE n s.vs_returndata /\
  (!i. w2n w+32 <= i /\ i < w2n w+32+LENGTH (TAKE n s.vs_returndata) ==>
       i NOTIN tn.t_mem) /\
  (!v sz. cenv.ce_return_buf = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  (!v sz. cenv.ce_return_pc = SOME (PtrVar (Var v) sz) ==> not_fresh_at sf v) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  expr_has_effect e /\ post_value_type cenv e = expr_type e /\
  lowered_value_type cenv e = expr_type e /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
  v = BytesV (TAKE n s.vs_returndata) /\
  vv = LocatedValue (expr_type e) (mk_ptr result LocMemory) ==>
  ?u Gf tnf.
    result = Var x /\ lookup_var x u = SOME w /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func u /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    FLOOKUP u.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n+31) DIV 32)*32) /\
    alloc.inst_id < sb.cs_next_id /\
    wb_frame cenv es0 es sf s0 u /\
    ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    ptr_covers Gf tnf x u (32 + ((n+31) DIV 32)*32) /\
    u.vs_memory = (mstore (w2n w) (n2w (LENGTH (TAKE n s.vs_returndata))) s).vs_memory /\
    (!i. i < w2n w \/ w2n w+32 <= i ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
    u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
    u.vs_data_section = s.vs_data_section /\ u.vs_returndata = s.vs_returndata /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n w <= i /\ i < w2n w+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sc p ==> lookup_var p u = lookup_var p s /\
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n))) v (w2n w) mem) /\
    ptr_vv_ok cx (post_value_type cenv e) (Value v) vv es Gf tnf u /\
    ptr_buf_ok cenv e result Gf u /\
    (!H:(bool # 256 word # type_value) list # num list.
       stmt_state_rel H ctx func cenv cx es s /\ storage_well_formed_on cx es (FST H) ==>
       vv_post H ctx func cenv cx e es0 sf sb s0 es (Value v) vv u /\
       vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) es (Value v) vv u /\
       vv_own cenv cx (post_value_type cenv e) sf sb es (Value v) vv u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_buffered_bytes_path >>
  disch_then (qspec_then `PG`
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
      compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def] >> decide_tac) >>
  `val_wf (BaseTV (BytesT (Dynamic n))) v` by
    (simp[valueEncodingDefsTheory.val_wf_def, listTheory.LENGTH_TAKE_EQ,
       type_memory_size_def] >>
     qspec_then `n` mp_tac word_size_capacity >> simp[word_size_def, Abbr `cap`] >>
     IF_CASES_TAC >> decide_tac) >>
  `val_footprint (BaseTV (BytesT (Dynamic n))) v <= cap` by
    (drule val_footprint_le >> asm_rewrite_tac[]) >>
  `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n))) v (w2n w) mem` by
    (qpat_assum `!mem. mem_agree_outside tnf.t_mem u.vs_memory mem ==> _` mp_tac >>
     qpat_assum `v = _` (rewrite_tac o single)) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  conj_tac >- suspend "ptr_value" >>
  conj_tac
  >- (qpat_assum `result = _` SUBST1_TAC >>
      irule rawCallBufferPtrTheory.ptr_buf_ok_from_covers >>
      qexistsl_tac [`cap`,`tnf`] >> simp[Abbr `cap`, compileEnvTheory.type_memory_bytes_def]) >>
  suspend "vv_post"
QED

Resume raw_buffered_bytes_finish_frame[regions]:
  rpt gen_tac >> disch_tac >>
  `regions_disjoint (w2n w) cap lb lsz` by
    (irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`cenv`,`func`,`alloc`,`name`,`q`,`es.scopes`,`u`] >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Resume raw_buffered_bytes_finish_frame[ptr_value]:
  qpat_assum `vv = _` SUBST1_TAC >>
  qpat_assum `result = _` SUBST1_TAC >>
  irule bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
  simp[mk_ptr_def, read_result_def, return_def] >>
  conj_tac >- fs[bodyPtrDefsTheory.ptr_covers_def] >>
  `ptr_val_ok cx (post_value_type cenv e) v (Var x) Gf tnf u` by
    (irule rawCallBufferPtrTheory.ptr_val_ok_from_type_covers >> gvs[]) >>
  gvs[bodyPtrDefsTheory.ptr_val_ok_def]
QED

Resume raw_buffered_bytes_finish_frame[vv_post]:
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

Finalise raw_buffered_bytes_finish_frame
