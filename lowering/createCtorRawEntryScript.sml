Theory createCtorRawEntry
Ancestors
  bodyFullExtCallDirectState bodyFullMemoryFrames bodyFullAbiEncodeCopy
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission
  abiEncoderWindowLeaves abiEncoderWindowPhase typedCopyOriginPtrBase
  abiBuiltinAllocation emitHelperProps fragGasOrigin fragExec context
  gasEventsFuel exprLoweringProps venomMemDefs abiEncoderWindowContract
  venomExecSemantics venomState venomInst words
  list arithmetic finite_map pred_set createCtorBlueprintEntry
  bodyFullStoreSlotsAddresses abiDecodePtrBytesTail abiEncoderWindowSequence ptrDiscipline bodyPtrDefs
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFramedArrayBody ghostPcTransportPtr
  loweringPosts freshWrites assignTuplePtrCopyLen memoryReadProps
  fragGasOriginPtr exprSimProps

(* Each instruction in the raw prologue is nonterminating and is not an
   INVOKE.  The supplied origin edge therefore fixes its result. *)
Theorem raw_prologue_edge_result[local]:
  gas_origin_edge F explicit ctx func s marks (OK t) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK r ==>
  t = r with vs_inst_idx := SUC s.vs_inst_idx
Proof
  rw[gas_origin_edge_def] >> gvs[step_inst_non_invoke,exit_result_def]
QED

Theorem raw_prologue_copy_observed[local]:
  compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var root s = SOME w /\ lookup_var src s = SOME p /\
  eval_operand len s = SOME n /\ gas_origin_edge F explicit ctx func s marks (OK t) ==>
  t = (mcopy (w2n w) (w2n p) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  `step_inst_base (mk_inst a.cs_next_id MCOPY [Var root;Var src;len] []) s =
   OK (mcopy (w2n w) (w2n p) (w2n n) s)` by
    simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
  `t = (mcopy (w2n w) (w2n p) (w2n n) s) with vs_inst_idx := SUC s.vs_inst_idx` by
    (irule raw_prologue_edge_result >>
     goal_assum (drule_at (Pat `gas_origin_edge F _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `step_inst_base _ _ = _`)) >>
     simp[mk_inst_def,is_terminator_def] >> metis_tac[]) >>
  simp[mcopy_def,write_memory_with_expansion_def]
QED

Theorem raw_prologue_copy_phase[local]:
  compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  alloca_inv s /\ alloca_room ctx func s /\
  lookup_var root s = SOME w /\ lookup_var src s = SOME p /\
  eval_operand len s = SOME n /\ gas_origin_edge F explicit ctx func s marks (OK t) ==>
  window_phase ctx func a b {} [(w2n w,w2n n)] s t /\
  abi_encode_exec_frame func s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  !x. lookup_var x t = lookup_var x s
Proof
  strip_tac >> drule_all raw_prologue_copy_observed >> strip_tac >>
  qpat_assum `t = _` (fn th => PURE_REWRITE_TAC [th]) >>
  reverse conj_tac >-
    simp[exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_mcopy,
         exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_inst_idx,
         mcopy_def,write_memory_with_expansion_def,lookup_var_def] >>
  `emit_void MCOPY [Var root; Var src;len] a = ((),b)` by
    fs[compile_copy_memory_dynamic_def] >>
  `eval_operand (Var root) s = SOME (n2w (w2n w)) /\
   eval_operand (Var src) s = SOME (n2w (w2n p)) /\
   eval_operand len s = SOME (n2w (w2n n))` by simp[eval_operand_def] >>
  `w2n w < dimword(:256) /\ w2n p < dimword(:256) /\ w2n n < dimword(:256)` by simp[w2n_lt] >>
  drule_all window_emit_copy_run >> simp[] >> strip_tac >>
  `ci_mono a b` by metis_tac[ci_mono_emit_void,pairTheory.SND] >>
  `window_seq a b s (mcopy (w2n w) (w2n p) (w2n n) s)` by
    fs[abiEncoderWindowSequenceTheory.window_seq_def,ci_mono_def,
      mcopy_def,write_memory_with_expansion_def,lookup_var_def] >>
  `alloca_inv (mcopy (w2n w) (w2n p) (w2n n) s) /\
   alloca_room ctx func (mcopy (w2n w) (w2n p) (w2n n) s) /\
   window_alloca_growth s (mcopy (w2n w) (w2n p) (w2n n) s)` by
    (fs[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def,
        alloca_room_def,pending_alloca_size_def,window_alloca_growth_def,
        mcopy_def,write_memory_with_expansion_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> rw[] >> fs[]) >>
  `abi_encoder_registered_effect {} [(w2n w,w2n n)] s
      (mcopy (w2n w) (w2n p) (w2n n) s)` by
    simp[abiEncoderPrimitiveEffectTheory.abi_encoder_registered_output_copy] >>
  `SUC (LENGTH a.cs_current_insts) = LENGTH b.cs_current_insts` by
    (drule_all emit_void_fetch_boundary >> strip_tac >> simp[]) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >> irule window_seq_phase >>
  simp[mcopy_def,write_memory_with_expansion_def]
QED

Theorem raw_prologue_copy_ghost[local]:
  compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_var root s = SOME w /\ lookup_var src s = SOME p /\
  eval_operand len s = SOME n /\ op_taint tn len = {} /\
  ptr_covers G tn root s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  w2n w + w2n n <= s.vs_alloca_next /\ w2n p + w2n n <= s.vs_alloca_next /\
  gas_origin_edge F explicit ctx func s marks (OK t) ==>
  ?tf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
              (s,G,tn) [] (OK t,G,tf)) /\
       tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
       tf.t_imm = tn.t_imm /\
       (!i. (i < w2n w \/ w2n w + w2n n <= i) /\ i IN tf.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >> drule_all raw_prologue_copy_observed >> strip_tac >>
  `emit_void MCOPY [Var root; Var src; len] a = ((),b)` by
    fs[compile_copy_memory_dynamic_def] >>
  drule_all emit_void_fetch_boundary >> strip_tac >>
  qabbrev_tac `i = mk_inst a.cs_next_id MCOPY [Var root;Var src;len] []` >>
  qabbrev_tac `r = mcopy (w2n w) (w2n p) (w2n n) s` >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by
    simp[Abbr `i`,mk_inst_def,unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.sized_source_write_range_def,
         codegenRelTheory.source_memory_write_ranges_def,eval_operand_def] >>
  qexists_tac `step_taint i s r tn` >> conj_tac >-
    (gen_tac >> qpat_assum `t = _` SUBST1_TAC >>
     qunabbrev_tac `i` >> qunabbrev_tac `r` >>
     irule abi_encode_mcopy_origin_path >> simp[] >> metis_tac[]) >>
  `eval_operand (Var root) s = SOME w /\ eval_operand (Var src) s = SOME p` by
    simp[eval_operand_def] >>
  qspecl_then [`ARB`,`G`,`tn`,`s`,`a.cs_next_id`,`Var root`,`Var src`,`len`]
    mp_tac fragExecPtrTheory.mcopy_operand_ghost_frame >>
  simp[Abbr `i`,Abbr `r`,
       decoderGhostFramePtrTheory.step_taint_nonmemory_frame,mk_inst_def] >>
  rpt strip_tac >> fs[] >> decide_tac
QED

(* Raw prologue entry transfer.  The compiler facts identify the actual
   allocation/copy/add fragment; the phase hypotheses are the public window
   interface used by the saved-state contract. *)
Theorem ctor_encoder_raw_entry:
  compile_alloc_buffer cap se = (buf,a) /\
  compile_copy_memory_dynamic buf.buf_operand src len a = ((),b) /\
  emit_op ADD [buf.buf_operand;len] b = (dst,c) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst0 dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = shared /\ inst.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  ci_mono a c /\ window_phase ctx func a c {} [] u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\
    op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\
  tv.t_imm = tu.t_imm /\ tv.t_mem = tu.t_mem ==>
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst0 dst_offset prefix c v Gv tv
Proof
  rpt strip_tac >>
  metis_tac[abi_encode_saved_state_arith]
QED

(* The observed ADD, not just a successful arithmetic run, gives the
   destination and its residual coverage. *)
Theorem raw_prologue_add_phase[local]:
  emit_op ADD [Var root;len] b = (dst,c) /\ fn_has_code b c func /\
  not_fresh_at b root /\ lookup_var root t = SOME (n2w pbase) /\
  eval_operand len t = SOME n /\ op_taint tf len = {} /\
  ptr_covers G tf root t capacity /\ w2n n <= capacity /\
  pbase + capacity < dimword (:256) /\
  alloca_inv t /\ alloca_room ctx func t /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  gas_origin_edge F explicit ctx func t marks (OK v) ==>
  ?out Gv tv. dst = Var out /\ not_fresh_at c out /\
    eval_operand dst v = SOME (n2w (pbase + w2n n)) /\
    ptr_covers Gv tv out v (capacity - w2n n) /\
    window_phase ctx func b c {} [] t v /\ abi_encode_exec_frame func t v /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tf) [] (OK v,Gv,tv)) /\
    tv.t_mem = tf.t_mem /\ tv.t_stor = tf.t_stor /\ tv.t_trans = tf.t_trans /\
    tv.t_imm = tf.t_imm /\
    (!x. not_fresh_at b x ==> lookup_var x v = lookup_var x t /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tf (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand (Var root) t = SOME (n2w pbase) /\ op_taint tf (Var root) = {}` by
    (simp[eval_operand_def] >> fs[ptr_covers_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`] store_address_binop_uniform)) >>
  disch_then (qspecl_then [`explicit`,`PG`,`G`]
    (qx_choose_then `out` strip_assume_tac)) >>
  drule_all emit_op_fetch_boundary >>
  disch_then (qx_choosel_then [`q`,`bb`] strip_assume_tac) >>
  `q = out` by metis_tac[operand_11] >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `i = mk_inst b.cs_next_id ADD [Var root;len] [out]` >>
  qabbrev_tac `raw = update_var out (n2w pbase+n) t` >>
  qabbrev_tac `Gv = step_prov PG G i raw` >>
  qabbrev_tac `tv = step_taint i t raw tf` >>
  `step_inst_base i t = OK raw` by
    simp[Abbr `i`,Abbr `raw`,step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
         eval_operand_def,eval_operands_def,ADD_COMM] >>
  `v = raw with vs_inst_idx := SUC t.vs_inst_idx` by
    (irule raw_prologue_edge_result >>
     goal_assum (drule_at (Pat `gas_origin_edge F _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `step_inst_base _ _ = _`)) >>
     qexists_tac `bb` >> gvs[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  qexistsl_tac [`out`,`Gv`,`tv`] >>
  `n2w pbase + n = n2w (pbase + w2n n)` by metis_tac[n2w_w2n,word_add_n2w] >>
  `ptr_covers Gv tv out v (capacity - w2n n)` by suspend "coverage" >>
  `window_pure_seq b c t raw` by suspend "pure" >>
  `abi_encode_exec_frame func t v` by suspend "frame" >>
  `window_phase ctx func b c {} [] t v` by
    (qpat_assum `v = _` SUBST1_TAC >> simp[] >> metis_tac[window_pure_seq_phase]) >>
  gvs[eval_operand_inst_idx]
QED

Resume raw_prologue_add_phase[coverage]:
  qpat_assum `v = _` SUBST1_TAC >>
  simp_tac bool_ss [Abbr `Gv`,Abbr `tv`,Abbr `i`,Abbr `raw`] >>
  irule (REWRITE_RULE [n2w_w2n]
    (Q.INST [`q` |-> `w2n (n:bytes32)`] abi_decode_ptr_output_address_covers)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `capacity` >>
  `pbase < dimword (:256)` by decide_tac >>
  simp[w2n_n2w] >> decide_tac
QED

Resume raw_prologue_add_phase[pure]:
  `run_inst_seq (emitted_insts b c) t = OK raw` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[Abbr `i`,run_inst_seq_def]) >>
  qunabbrev_tac `raw` >>
  gs[] >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `ADD`] window_emit_register_pure)) >> simp[]
QED

Resume raw_prologue_add_phase[frame]:
  qpat_assum `v = _` SUBST1_TAC >> PURE_REWRITE_TAC [abi_encode_exec_frame_inst_idx] >>
  irule abi_encode_framed_ordinary_pure_sequence >>
  qexistsl_tac [`c`,`b`] >> simp[] >>
  drule emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def,is_alloca_op_def,is_ext_call_op_def]
QED

Finalise raw_prologue_add_phase

(* Initialize the ABI suffix at the actual end of the raw prologue. *)
Theorem ctor_raw_destination_actual:
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
  fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst,c) /\
  fn_has_code b c func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  capacity < dimword (:256) /\ w2n n <= capacity /\
  not_fresh_at se src /\ not_fresh_at se len /\
  lookup_var src s = SOME p /\ lookup_var len s = SOME n /\
  ptr_covers G tn src s (w2n n) /\ op_taint tn (Var len) = {} /\
  w2n p + w2n n <= s.vs_alloca_next /\
  (!x z. ce.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (!x z. ce.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  gas_origin_edge F explicit ctx func s am (OK u) /\
  gas_origin_edge F explicit ctx func u bm (OK t) /\
  gas_origin_edge F explicit ctx func t cm (OK v) ==>
  ?root pbase out Gv tv inst.
    buf.buf_operand = Var root /\ dst = Var out /\
    inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root] /\
    MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root out (w2n n) [] c v Gv tv /\
    pure_frame ce func ee se s v /\
    (!x. not_fresh_at se x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,Gv,tv))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all ctor_encoder_blueprint_entry >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`root`,`pbase`,`u0`,`Gu`,`tu`,`inst`] strip_assume_tac)) >>
  `u = u0` by metis_tac[] >> pop_assum (SUBST_ALL_TAC o SYM) >>
  `compile_copy_memory_dynamic (Var root) (Var src) (Var len) a = ((),b) /\
   emit_op ADD [Var root;Var len] b = (dst,c)` by metis_tac[] >>
  `ci_mono se a /\ ci_mono a b /\ ci_mono b c` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_compile_copy_memory_dynamic,
      ci_mono_emit_op,pairTheory.SND] >>
  `!x. not_fresh_at se x ==> not_fresh_at a x /\ not_fresh_at b x` by
    metis_tac[ci_mono_trans,ci_mono_def,not_fresh_at_mono] >>
  `lookup_var src u = SOME p /\ eval_operand (Var len) u = SOME n /\
   op_taint tu (Var len) = {} /\ ptr_covers Gu tu src u (w2n n)` by suspend "src" >>
  `?tf. abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id pbase capacity root root 0 [] b t Gu tf /\
   pure_frame ce func ee se u t /\ t.vs_allocas = u.vs_allocas /\
   (!x. lookup_var x t = lookup_var x u /\ op_taint tf (Var x) = op_taint tu (Var x)) /\
   (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,Gu,tf))`
    suffices_by (disch_then (qx_choose_then `tf` strip_assume_tac) >> suspend "add") >>
  suspend "copy"
QED

Resume ctor_raw_destination_actual[src]:
  qpat_assum `!x. not_fresh_at se x ==> lookup_var x u = _ /\ _`
    (fn th => map_every (fn x => qspec_then x (drule_then strip_assume_tac) th) [`src`,`len`]) >>
  simp[eval_operand_def] >> irule ptr_covers_lookup_frame >> metis_tac[]
QED

Resume ctor_raw_destination_actual[copy]:
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_saved_state_def]) >>
  `pbase + capacity <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u` (strip_assume_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     metis_tac[ADD_COMM]) >>
  `pbase < dimword (:256) /\ w2n p + w2n n <= u.vs_alloca_next` by
    (drule alloca_room_next_lt >> decide_tac) >>
  `lookup_var root u = SOME (n2w pbase) /\ w2n (n2w pbase : bytes32) = pbase` by
    fs[eval_operand_def,w2n_n2w] >>
  `ptr_covers Gu tu root u (w2n n)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> metis_tac[]) >>
  drule_all raw_prologue_copy_phase >> strip_tac >>
  `w2n (n2w pbase : bytes32) + w2n n <= u.vs_alloca_next` by (simp[] >> decide_tac) >>
  drule_all raw_prologue_copy_ghost >>
  disch_then (qspec_then `PG` (qx_choose_then `tf` strip_assume_tac)) >>
  qexists_tac `tf` >>
  `!x. op_taint tf (Var x) = op_taint tu (Var x)` by simp[op_taint_def] >>
  `(pure_frame ce func ee se u t /\ wb_frame ce ee ee se u t) /\
   abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
     se.cs_next_id pbase capacity root root 0 [] b t Gu tf` by suspend "copy_saved" >>
  simp[]
QED

Resume ctor_raw_destination_actual[copy_saved]:
  irule abi_encode_saved_state_phase_pure >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gu`,`PG`,`a`,`explicit`,`{}:num set`,
    `[(w2n (n2w pbase : bytes32),w2n n)]`,`tu`] >>
  asm_simp_tac (srw_ss()) [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (decide_tac >> NO_TAC) >>
  TRY (qexistsl_tac [`inst`,`root`] >> fs[mk_inst_def] >> NO_TAC) >>
  rpt strip_tac >> fs[]
QED

Resume ctor_raw_destination_actual[add]:
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_saved_state_def]) >>
  `pbase + capacity < dimword (:256)` by
    (qpat_assum `alloca_inv t` (strip_assume_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
     `pbase + capacity <= t.vs_alloca_next` by metis_tac[ADD_COMM] >>
     qpat_assum `alloca_room ctx func t` (mp_tac o MATCH_MP alloca_room_next_lt) >> decide_tac) >>
  `lookup_var root t = SOME (n2w pbase) /\ eval_operand (Var len) t = SOME n /\
   op_taint tf (Var len) = {}` by fs[eval_operand_def] >>
  drule_all raw_prologue_add_phase >>
  disch_then (qspecl_then [`PG`] (qx_choosel_then [`out`,`Gv`,`tv`] strip_assume_tac)) >>
  `(pure_frame ce func ee se t v /\ wb_frame ce ee ee se t v) /\
   abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
     se.cs_next_id pbase capacity root root 0 [] c v Gv tv` by suspend "add_saved" >>
  qexistsl_tac [`root`,`pbase`,`out`,`Gv`,`tv`,`inst`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "shift"
  >- suspend "pure_frame"
  >- (rpt strip_tac >> fs[] >> metis_tac[]) >>
  suspend "ghost_path"
QED

Resume ctor_raw_destination_actual[add_saved]:
  irule abi_encode_saved_state_arith_pure >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexists_tac `inst` >> fs[mk_inst_def]) >>
  qexistsl_tac [`Gu`,`PG`,`b`,`explicit`,`tf`] >>
  asm_simp_tac (srw_ss()) [] >> metis_tac[]
QED

Resume ctor_raw_destination_actual[shift]:
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c _ _ _`
     (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_saved_state_def]) >>
  simp[abi_encode_saved_state_def,read_memory_def] >> metis_tac[]
QED

Resume ctor_raw_destination_actual[pure_frame]:
  `pure_frame ce func ee se s t` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ee`,`se`,`u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     fs[wb_frame_def] >> metis_tac[]) >>
  irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`ee`,`se`,`t`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  fs[wb_frame_def] >> metis_tac[]
QED

Resume ctor_raw_destination_actual[ghost_path]:
  gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`t`,`tf`] >> simp[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gu`,`u`,`tu`] >> simp[]
QED

Finalise ctor_raw_destination_actual
