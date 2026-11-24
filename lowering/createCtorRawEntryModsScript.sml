Theory createCtorRawEntryMods
Ancestors
  createCtorRawEntry createExprSizeExitDefsMods
  bodyFullExtCallDirectState bodyFullMemoryFrames bodyFullAbiEncodeCopy
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission
  abiEncoderWindowLeaves abiEncoderWindowPhase typedCopyOriginPtrBase
  abiBuiltinAllocation emitHelperProps fragGasOrigin fragExec context
  gasEventsFuel exprLoweringProps venomMemDefs abiEncoderWindowContract
  venomExecSemantics venomState venomInst words
  list arithmetic finite_map pred_set createCtorBlueprintEntryMods
  bodyFullStoreSlotsAddresses abiDecodePtrBytesTail abiEncoderWindowSequence ptrDiscipline bodyPtrDefs
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFramedArrayBody ghostPcTransportPtr
  loweringPosts freshWrites assignTuplePtrCopyLen memoryReadProps
  fragGasOriginPtr exprSimProps bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit typedMemoryCopy loweringSlice loweringStateRelDefs

(* Each instruction in the raw prologue is nonterminating and is not an
   INVOKE.  The supplied origin edge therefore fixes its result. *)

Theorem ctor_raw_destination_actual_mods:
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
    stmt_state_rel H ctx func ce cx ee s /\
    immutable_frame_mods func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  gas_origin_edge F explicit ctx func s am (OK u) /\
  gas_origin_edge F explicit ctx func u bm (OK t) /\
  gas_origin_edge F explicit ctx func t cm (OK v) ==>
  ?root pbase out Gv tv inst.
    buf.buf_operand = Var root /\ dst = Var out /\
    inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w capacity)] [root] /\
    MEM inst (fn_insts func) /\ not_local_ptr ce ee.scopes root /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root out (w2n n) [] c v Gv tv /\
    pure_frame ce func ee se s v /\
    (!x. not_fresh_at se x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tn (Var x)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK v,Gv,tv))
Proof
  cheat
QED

(* At floor zero only the common part of the ghost invariant remains. *)
Theorem raw_entry_saved_view[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst off prefix a u Gu tu <=>
  abi_encode_saved_state ctx func ce cx st0 ee DF 0 d se s G tn
    shared pbase capacity root dst off prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    immutable_frame_mods func ce cx ee u /\
    (!i. i < lo /\ i IN tu.t_mem ==>
      imm_section_dead_mods ce (mem_bytes_at 0 lo u.vs_memory) i) /\
    (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
      FLOOKUP Gu x = NONE /\ op_taint tu (Var x) = {}) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next)
Proof
  simp_tac bool_ss [abi_encode_saved_state_mods_def, abi_encode_saved_state_def,
    ghost_inv_at_mods_def, ghost_inv_at_def, ghost_kept_at_def,
    allocas_from_def, DECIDE ``!n:num. ~(n < 0) /\ 0 <= n``,
    IMP_CONJ_THM, FORALL_AND_THM] >>
  CONV_TAC (AC_CONV (CONJ_ASSOC, CONJ_COMM))
QED

(* Preserve the immutable relation of every module, not just the active one. *)

Theorem raw_entry_registered_immutable_frame[local]:
  immutable_frame_mods func ce cx ee u /\ local_ptrs_reserved ce se /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (pbase,capacity) /\
  typed_copy_state_frame se pbase capacity u v ==>
  immutable_frame_mods func ce cx ee v
Proof
  strip_tac >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `v.vs_data_section = u.vs_data_section /\ v.vs_allocas = u.vs_allocas /\
   v.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `_ = u`
      (mp_tac o AP_TERM ``\z. (z.vs_data_section,z.vs_allocas,z.vs_alloca_next)``) >> simp[]) >>
  `!src id b sz. local_region (ce with ce_module := src) ee.scopes v id b sz ==>
    local_region (ce with ce_module := src) ee.scopes u id b sz` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at se p` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule immutables_rel_mem_agree >>
      qexists_tac `u` >> simp[] >> conj_tac
      >- fs[typed_copy_frame_def] >>
      disch_tac >> rpt gen_tac >> strip_tac >>
      qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
      `regions_disjoint off (type_memory_size tv) pbase capacity` by metis_tac[] >>
      fs[typed_copy_frame_def, loweringStateRelDefsTheory.regions_disjoint_def]) >>
  rpt gen_tac >> strip_tac >> irule immutable_alloca_sep_fields >>
  qexistsl_tac [`u`,`ee`] >> simp[] >> metis_tac[]
QED

Theorem raw_entry_saved_phase_mods[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root root 0 [] a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c {} outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,0,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) outs /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = shared /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\ i IN tv.t_mem ==> i IN tu.t_mem) /\
  typed_copy_state_frame se pbase capacity u v ==>
  (pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root root 0 [] c v Gv tv
Proof
  simp_tac bool_ss [raw_entry_saved_view] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `(pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
   abi_encode_saved_state ctx func ce cx st0 ee DF 0 d se s G tn
     shared pbase capacity root root 0 [] c v Gv tv` by
    (irule abi_encode_saved_state_phase_pure >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl_tac [`Gu`,`PG`,`a`,`explicit`,`{}:num set`,`outs`,`tu`] >>
     asm_simp_tac (srw_ss()) [] >>
     qexistsl_tac [`inst`,`root`] >> simp[]) >>
  asm_rewrite_tac[] >> qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> immutable_frame_mods _ _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  `lo <= pbase` by
    (qpat_assum `allocas_from lo u` (drule_then irule o REWRITE_RULE [allocas_from_def]) >> simp[]) >>
  conj_tac
  >- (irule raw_entry_registered_immutable_frame >>
      qpat_assum `typed_copy_state_frame _ _ _ u v` (irule_at Any) >>
      qexists_tac `inst` >> simp[]) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `_ = u` (mp_tac o AP_TERM ``\z. (z.vs_allocas,z.vs_alloca_next)``) >> simp[]) >>
  `mem_bytes_at 0 lo v.vs_memory = mem_bytes_at 0 lo u.vs_memory` by fs[typed_copy_frame_def] >>
  `!i. i < lo /\ i IN tv.t_mem ==> i IN tu.t_mem` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     simp_tac bool_ss [EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     qpat_assum `EVERY _ outs`
       (drule_then strip_assume_tac o SRULE [EVERY_MEM, pairTheory.FORALL_PROD]) >>
     simp[] >> decide_tac) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> qpat_assum `!i. i < lo /\ i IN tu.t_mem ==> _` irule >> simp[]) >>
  reverse conj_tac >-
    (qpat_assum `v.vs_allocas = u.vs_allocas` (fn th =>
       PURE_REWRITE_TAC [allocas_from_def, th]) >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qx_gen_tac `x` >> strip_tac >>
  `not_fresh_at se x` by metis_tac[local_ptrs_reserved_imm_base] >>
  `not_fresh_at a x` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> _`
    (qspec_then `x` mp_tac) >>
  qpat_assum `!x. not_fresh_at a x ==> FLOOKUP Gv x = _ /\ _`
    (qspec_then `x` mp_tac) >> simp[]
QED

Theorem raw_entry_add_step:
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
    typed_copy_state_frame b pbase capacity t v /\
    (!k D. allocas_from k t ==>
      gas_origin_ptr_path (D,k,explicit,ctx,func,PG) (t,G,tf) [] (OK v,Gv,tv)) /\
    tv.t_mem = tf.t_mem /\ tv.t_stor = tf.t_stor /\ tv.t_trans = tf.t_trans /\
    tv.t_imm = tf.t_imm /\
    (!x. not_fresh_at b x ==> lookup_var x v = lookup_var x t /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tf (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand (Var root) t = SOME (n2w pbase) /\ op_taint tf (Var root) = {}` by
    (simp[eval_operand_def] >> fs[ptr_covers_def]) >>
  drule_all emit_op_fetch_boundary >>
  disch_then (qx_choosel_then [`out`,`bb`] strip_assume_tac) >>
  qabbrev_tac `i = mk_inst b.cs_next_id ADD [Var root;len] [out]` >>
  qabbrev_tac `raw = update_var out (n2w pbase+n) t` >>
  qabbrev_tac `Gv = step_prov PG G i raw` >>
  qabbrev_tac `tv = step_taint i t raw tf` >>
  `step_inst_base i t = OK raw` by
    simp[Abbr `i`,Abbr `raw`,step_inst_base_opcode_eqs,mk_inst_def,exec_pure2_def,
         eval_operand_def,eval_operands_def,ADD_COMM] >>
  `v = raw with vs_inst_idx := SUC t.vs_inst_idx` by suspend "observed" >>
  `n2w pbase + n = n2w (pbase + w2n n)` by metis_tac[n2w_w2n,word_add_n2w] >>
  `ptr_covers Gv tv out v (capacity - w2n n)` by suspend "coverage" >>
  `window_pure_seq b c t raw /\ eval_operand dst raw = SOME (n2w pbase + n) /\
    not_fresh_at c out` by suspend "pure" >>
  `abi_encode_exec_frame func t v` by suspend "frame" >>
  `window_phase ctx func b c {} [] t v` by
    (qpat_assum `v = _` SUBST1_TAC >> simp[] >> metis_tac[window_pure_seq_phase]) >>
  `!k D. allocas_from k t ==>
    gas_origin_ptr_path (D,k,explicit,ctx,func,PG) (t,G,tf) [] (OK v,Gv,tv) /\
    typed_copy_state_frame b pbase capacity t v` by suspend "path" >>
  qexistsl_tac [`out`,`Gv`,`tv`] >>
  `typed_copy_state_frame b pbase capacity t v` by metis_tac[] >>
  `!k D. allocas_from k t ==>
    gas_origin_ptr_path (D,k,explicit,ctx,func,PG) (t,G,tf) [] (OK v,Gv,tv)` by metis_tac[] >>
  simp[] >> suspend "registers"
QED

Resume raw_entry_add_step[observed]:
  qpat_assum `gas_origin_edge F _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_origin_edge_def] >>
  strip_tac >> gvs[step_inst_non_invoke,exit_result_def,Abbr `i`,mk_inst_def,is_terminator_def]
QED

Resume raw_entry_add_step[coverage]:
  qpat_assum `v = _` SUBST1_TAC >>
  simp_tac bool_ss [Abbr `Gv`,Abbr `tv`,Abbr `i`,Abbr `raw`] >>
  irule (REWRITE_RULE [n2w_w2n]
    (Q.INST [`q` |-> `w2n (n:bytes32)`] abi_decode_ptr_output_address_covers)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `capacity` >>
  `pbase < dimword (:256)` by decide_tac >>
  simp[w2n_n2w] >> decide_tac
QED

Resume raw_entry_add_step[pure]:
  `run_inst_seq (emitted_insts b c) t = OK raw` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[Abbr `i`,run_inst_seq_def]) >>
  qunabbrev_tac `raw` >>
  gs[] >>
  drule_all (SRULE [is_terminator_def]
    (Q.INST [`opc` |-> `ADD`] window_emit_register_pure)) >> simp[]
QED

Resume raw_entry_add_step[frame]:
  qpat_assum `v = _` SUBST1_TAC >> PURE_REWRITE_TAC [abi_encode_exec_frame_inst_idx] >>
  irule abi_encode_framed_ordinary_pure_sequence >>
  qexistsl_tac [`c`,`b`] >> simp[] >>
  drule emitted_insts_emit_op >> simp[mk_inst_def,is_terminator_def,is_alloca_op_def,is_ext_call_op_def]
QED

Resume raw_entry_add_step[path]:
  qx_genl_tac [`k`,`D`] >> strip_tac >>
  qpat_x_assum `allocas_from lo t` kall_tac >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `x+y`]
    typed_copy_origin_ptr_binop_path)) >>
  disch_then (qspecl_then [`pbase`,`capacity`,`explicit`,`PG`,`G`,`D`] strip_assume_tac) >>
  gvs[Abbr `raw`,Abbr `Gv`,Abbr `tv`,Abbr `i`]
QED

Resume raw_entry_add_step[registers]:
  qpat_assum `v = _` SUBST1_TAC >>
  simp[eval_operand_inst_idx] >>
  simp[Abbr `Gv`,Abbr `tv`,Abbr `i`,Abbr `raw`,typed_copy_origin_ptr_binop_ghost_frame] >>
  conj_tac >- simp[eval_operand_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  qx_gen_tac `x` >> disch_tac >>
  `x <> STRING #"%" (toString b.cs_next_var)` by metis_tac[] >>
  simp[update_var_def,lookup_var_def,FLOOKUP_UPDATE] >> metis_tac[]
QED

Finalise raw_entry_add_step[local]
