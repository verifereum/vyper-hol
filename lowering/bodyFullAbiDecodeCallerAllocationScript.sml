Theory bodyFullAbiDecodeCallerAllocation
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeDecoderFrame bodyFullAllocGeneric
  bodyPtrBytestringBuiltinsBuffer bodyPtrIfExpAllocSeparation
  abiBuiltinDecodeSetup abiEncoderChildContext fragGasSeq fragGasOriginPtr
  bufferAllocationExecution allocaHistory ptrSafetyTransport
  abiBuiltinDecodeHeader abiBuiltinAllocation fragExec loweringStateRelDefs
  loweringHalt exprLoweringProps compileEnv emitHelperProps venomInst venomState venomExecSemantics
  words list rich_list finite_map allocaBudgetProps

(* Concrete 256-word horizon-type instances of the installed caller propositions. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H:((bool # (256 word) # type_value) list # num list). V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val caller_setup_pre = ``\data min_size max_size outsz st ready ops s G tn b data_var d.
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ (?H:((bool # (256 word) # type_value) list # num list). V H) /\
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= s.vs_alloca_next) /\
  (!H:((bool # (256 word) # type_value) list # num list). V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  data = Var data_var /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s data_var (n2w b) (32+LENGTH input_bytes) /\
  mload b s = n2w (LENGTH input_bytes) /\
  mem_bytes_at (b+32) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  b+32+LENGTH input_bytes <= s.vs_alloca_next /\
  b+32+LENGTH input_bytes < dimword (:256) /\
  min_size <= max_size /\ max_size < dimword (:256) /\
  outsz < dimword (:256) /\ d+outsz < dimword (:256) /\
  (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
     SOME (d,outsz))``;

val caller_setup_success = ``\st ready ops s G tn b min_size max_size outsz t G' tn' d.
  ?output input.
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    FST ops = Var output /\ FST (SND ops) = Var input /\
    eval_operand (SND (SND ops)) t = SOME (n2w (LENGTH input_bytes)) /\
    min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size /\
    (\live protected input_word output_base output_cap output_id.
       (^owned_decoder_state) ready t G' tn')
      [] [] (n2w (b+32)) d outsz
      (abi_builtin_decode_output_site st min_size max_size) /\
    FLOOKUP G' output = SOME (d,outsz) /\
    (b+32+LENGTH input_bytes <= d \/ d+outsz <= b+32) /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
       SOME (d,outsz)) /\
    op_prov G' (SND (SND ops)) = NONE /\
    op_taint tn' (FST ops) = {} /\ op_taint tn' (FST (SND ops)) = {} /\
    op_taint tn' (SND (SND ops)) = {} /\
    abi_decoder_operand_live ready.cs_next_var (FST ops) /\
    abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))``;

Theorem abi_decode_caller_allocation_joint:
  (^caller_setup_pre) data min_size max_size outsz st ready ops s G tn b data_var d /\
  abi_builtin_decode_header data min_size max_size st = (inputs,header_st) /\
  compile_alloc_buffer outsz header_st = (buf,ready) /\
  ops = (buf.buf_operand,SND inputs,FST inputs) /\
  ~u.vs_halted /\ u.vs_current_bb = header_st.cs_current_bb /\
  u.vs_inst_idx = LENGTH header_st.cs_current_insts /\
  SND inputs = Var input /\
  eval_operand (FST inputs) u = SOME (n2w (LENGTH input_bytes)) /\
  min_size <= LENGTH input_bytes /\ LENGTH input_bytes <= max_size /\
  abi_decode_ptr_window Gh tnh u input (n2w (b+32)) (LENGTH input_bytes) /\
  op_prov Gh (FST inputs) = NONE /\
  op_taint tnh (FST inputs) = {} /\ op_taint tnh (SND inputs) = {} /\
  abi_decoder_operand_live header_st.cs_next_var (FST inputs) /\
  abi_decoder_operand_live header_st.cs_next_var (SND inputs) /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  tnh.t_mem = tn.t_mem /\ tnh.t_stor = tn.t_stor /\
  tnh.t_trans = tn.t_trans /\ tnh.t_imm = tn.t_imm /\
  alloca_history fn u /\
  (!x. not_fresh_at st x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gh x = FLOOKUP G x /\
    op_taint tnh (Var x) = op_taint tn (Var x)) /\
  (!H:((bool # (256 word) # type_value) list # num list).
    V H ==> stmt_state_rel H ctx fn ce cx es u /\
    ghost_inv_at (DF H) lo delta ce cx es Gh tnh u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gh tnh) ==>
  ?t G' tn'.
    (!H:((bool # (256 word) # type_value) list # num list). V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (u,Gh,tnh) [] (OK t,G',tn')) /\
    (!obs. fn_has_code header_st ready obs ==> gas_path ctx obs u 0 (OK t)) /\
    (^caller_setup_success) st ready ops s G tn b min_size max_size outsz t G' tn' d
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `cs_extends st header_st /\ cs_extends header_st ready` by
    (conj_tac >- metis_tac[abi_encoder_straight_extends] >>
     metis_tac[compile_alloc_buffer_extends]) >>
  `fn_has_code header_st ready fn` by metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce header_st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `stmt_state_rel H ctx fn ce cx es u` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  drule_all bodyPtrBytestringBuiltinsBufferTheory.compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`tnh`, `PG`, `Gh`, `ARB`] strip_assume_tac) >>
  rename1 `step_inst_base _ u = OK v` >>
  drule_all bodyPtrIfExpAllocSourceTheory.compile_alloc_buffer_raw_resources >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME
      (mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`v with vs_inst_idx := SUC u.vs_inst_idx`, `G1`, `tn1`] >>
  (conj_tac >- suspend "origin" >>
   conj_tac >- suspend "observer" >>
   suspend "owned")
QED

Resume abi_decode_caller_allocation_joint[origin]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_x_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _`
       (qspec_then `H'` mp_tac) >> simp[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  `gas_origin_ptr_edge (DF H',lo,explicit,ctx,fn,PG) (u,Gh,tnh) []
    (OK (v with vs_inst_idx := SUC u.vs_inst_idx),G1,tn1)` by
    (qpat_x_assum `G1 = _` SUBST1_TAC >>
     qpat_x_assum `tn1 = _` SUBST1_TAC >>
     irule ifexp_alloca_origin_ptr_edge >> gvs[]) >>
  drule_all bodyPtrIfExpAllocSourceTheory.alloca_step_contracts >> strip_tac >>
  `~(v with vs_inst_idx := SUC u.vs_inst_idx).vs_halted` by simp[] >>
  pop_assum mp_tac >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]
QED

Resume abi_decode_caller_allocation_joint[observer]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `?bb. lookup_block u.vs_current_bb obs.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME
      (mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb'` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  `gas_path_edge ctx obs u 0 (OK (v with vs_inst_idx := SUC u.vs_inst_idx))` by
    (qpat_x_assum `step_inst_base _ u = OK v` mp_tac >>
     qpat_x_assum `get_instruction bb' _ = _` mp_tac >>
     qpat_x_assum `lookup_block _ obs.fn_blocks = _` mp_tac >>
     qpat_x_assum `~u.vs_halted` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule_at (Pos last) tuple_straight_line_edge >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >> strip_tac >>
  drule fragGasPathTheory.gas_path_edge_normal >> strip_tac >>
  metis_tac[fragGasPathTheory.gas_path_rules, arithmeticTheory.ADD_CLAUSES]
QED

Resume abi_decode_caller_allocation_joint[owned]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `abi_builtin_decode_output_site st min_size max_size = header_st.cs_next_id` by
    simp[abi_builtin_decode_output_site_def] >>
  `buffer_allocation_base u header_st.cs_next_id = d` by
    (pure_rewrite_tac[buffer_allocation_base_def] >>
     qpat_x_assum `abi_builtin_decode_output_site _ _ _ = _`
       (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
  drule_all ifexp_alloca_step_site >> strip_tac >>
  `a = d` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  drule_all bodyPtrIfExpAllocSourceTheory.alloca_step_contracts >> strip_tac >>
  `~not_fresh_at origin out /\ input <> out` by
    (gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_EQ_ADD]) >>
  `w2n (n2w (b+32):256 word) = b+32` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es u` by metis_tac[] >>
  `!H. V H ==> ghost_inv_at (DF H) lo delta ce cx es G1 tn1 v /\
     ghost_kept_at lo ce es0 origin G0 tn0 s0 G1 tn1 /\
     abi_decode_ptr_window G1 tn1 v input (n2w (b+32)) (LENGTH input_bytes) /\
     (!x. x <> out ==> lookup_var x v = lookup_var x u /\
       FLOOKUP G1 x = FLOOKUP Gh x /\ op_taint tn1 (Var x) = op_taint tnh (Var x)) /\
     stmt_state_rel H ctx fn ce cx es v` by
    (qx_gen_tac `h` >> disch_tac >>
     `ghost_inv_at (DF h) lo delta ce cx es Gh tnh u /\
       ghost_kept_at lo ce es0 origin G0 tn0 s0 Gh tnh` by metis_tac[] >>
     `st.cs_next_var <= header_st.cs_next_var` by simp[] >>
     `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x)` by
       metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
     `w2n (n2w (b+32):256 word)+LENGTH input_bytes <= u.vs_alloca_next /\
      lo <= u.vs_alloca_next` by simp[] >>
     `(!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
       aid < origin.cs_next_id ==> off+sz <= u.vs_alloca_next) /\
      (!name a sz. local_region ce es0.scopes s0 name a sz ==>
       a+sz <= u.vs_alloca_next)` by metis_tac[] >>
     drule_all abi_decode_scratch_alloc_frame_joint >>
     disch_then (qspec_then `PG` strip_assume_tac) >>
     gvs[]) >>
  `~not_fresh_at header_st out /\ not_fresh_at ready out` by
    (fs[] >> (metis_tac[])) >>
  `!x. not_fresh_at st x ==> x <> out` by
    (`st.cs_next_var <= header_st.cs_next_var` by simp[] >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `FST inputs <> Var out` by
    (strip_tac >>
     gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
         abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `alloca_inv u` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `alloca_history fn (v with vs_inst_idx := SUC u.vs_inst_idx)` by
    (drule_all allocaHistoryTheory.alloca_history_base_step >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `u.vs_alloca_next <= v.vs_alloca_next` by
    (`(mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out]).inst_opcode = ALLOCA` by
       simp[venomInstTheory.mk_inst_def] >>
     drule_all allocaBudgetPropsTheory.step_inst_base_alloca_effect >>
     IF_CASES_TAC >> simp[]) >>
  `allocas_from lo v` by
    (qpat_assum `!h. V h ==> ghost_inv_at _ _ _ _ _ _ G1 tn1 v /\ _`
       (drule o cj 1) >>
     pure_rewrite_tac[bodyPtrDefsTheory.ghost_inv_at_def] >> strip_tac >>
     asm_rewrite_tac[]) >>
  `lo <= d` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `not_local_ptr ce es.scopes out` by metis_tac[exprSimOperandsTheory.fresh_not_local_ptr] >>
  `!k name lb n. local_region ce es.scopes (v with vs_inst_idx := k) name lb n <=>
                 local_region ce es.scopes v name lb n` by
    (rpt gen_tac >> irule loweringStateRelDefsTheory.local_region_lookup_cong >>
     simp[venomStateTheory.lookup_var_def]) >>
  `!k. abi_decode_ptr_window G1 tn1 (v with vs_inst_idx := k) input
              (n2w (b+32)) (LENGTH input_bytes)` by
    (`abi_decode_ptr_window G1 tn1 v input (n2w (b+32)) (LENGTH input_bytes)` by metis_tac[] >>
     gs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def, venomStateTheory.lookup_var_def]) >>
  qpat_assum `!h. V h ==> ghost_inv_at _ _ _ _ _ _ G1 tn1 v /\ _`
    (drule o cj 4) >> strip_tac >>
  `eval_operand (FST inputs) v = SOME (n2w (LENGTH input_bytes))` by
    (drule allocationPtrTheory.alloca_step_operand_preserved >>
     disch_then (qspec_then `FST inputs` mp_tac) >> simp[]) >>
  `op_prov G1 (FST inputs) = NONE /\ op_taint tn1 (FST inputs) = {}` by
    (qpat_assum `op_prov Gh (FST inputs) = NONE` mp_tac >>
     qpat_assum `op_taint tnh (FST inputs) = {}` mp_tac >>
     qpat_assum `FST inputs <> Var out` mp_tac >>
     qpat_assum `!x. x <> out ==> lookup_var x v = lookup_var x u /\ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `FST inputs` >>
     simp[ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def]) >>
  `op_taint tn1 (Var out) = {} /\ op_taint tn1 (Var input) = {}` by
    metis_tac[bodyPtrDefsTheory.ptr_covers_def] >>
  `FLOOKUP G1 out = SOME (d,outsz)` by
    (qpat_x_assum `G1 = _` SUBST1_TAC >>
     `FLOOKUP v.vs_allocas header_st.cs_next_id = SOME (d,outsz)` by metis_tac[] >>
     drule fragExecPtrTheory.step_prov_alloca >> simp[FLOOKUP_UPDATE]) >>
  `!h. V h ==> ghost_kept_at lo ce es0 origin G0 tn0 s0 G1 tn1` by
    qpat_assum `!h. V h ==> ghost_inv_at _ _ _ _ _ _ G1 tn1 v /\ _`
      (CHECK_ASSUME_TAC o cj 2) >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off+sz <= v.vs_alloca_next` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `!name a sz. local_region ce es0.scopes s0 name a sz ==>
    a+sz <= v.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [out] /\ inst.inst_id = header_st.cs_next_id` by
    (qexists_tac `mk_inst header_st.cs_next_id ALLOCA [Lit (n2w outsz)] [out]` >>
     simp[venomInstTheory.mk_inst_def]) >>
  `!name a k. local_region ce es.scopes v name a k ==>
    d+outsz <= a \/ a+k <= d` by
    metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  `header_st.cs_next_var <= ready.cs_next_var` by simp[] >>
  `abi_decoder_operand_live ready.cs_next_var (Var out) /\
   abi_decoder_operand_live ready.cs_next_var (Var input) /\
   abi_decoder_operand_live ready.cs_next_var (FST inputs)` by
    (conj_tac
     >- (qpat_assum `not_fresh_at ready out` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
           abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
     metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono]) >>
  `!x. not_fresh_at st x ==>
    lookup_var x v = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `lo <= v.vs_alloca_next /\ s0.vs_alloca_next <= v.vs_alloca_next /\
    b+32+LENGTH input_bytes <= v.vs_alloca_next /\
    origin.cs_next_var <= ready.cs_next_var` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD] >>
  `SUC u.vs_inst_idx = LENGTH ready.cs_current_insts /\
    header_st.cs_next_id < ready.cs_next_id` by simp[] >>
  `ptr_covers G1 tn1 out v outsz` by
    qpat_assum `ptr_covers G1 tn1 out (v with vs_inst_idx := _) outsz`
      (CHECK_ASSUME_TAC o REWRITE_RULE[ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
  `!h. V h ==> stmt_state_rel h ctx fn ce cx es v /\
    ghost_inv_at (DF h) lo delta ce cx es G1 tn1 v /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G1 tn1` by metis_tac[] >>
  (* Keep the certified allocation site, compiler counters and ghosts abstract. *)
  map_every (fn p => qpat_x_assum p kall_tac)
    [`header_st.cs_next_id = _`, `ready.cs_next_id = _`,
     `header_st.cs_next_var = _`, `ready.cs_next_var = _`,
     `G1 = _`, `tn1 = _`, `ready.cs_current_insts = _`,
     `u.vs_inst_idx = _`] >>
  qexistsl_tac [`out`, `input`] >>
  qpat_assum `w2n (n2w (b+32):256 word) = _`
    (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms, blockPrefixEquivTheory.lookup_var_set_inst_idx,
       ghostPcTransportPtrTheory.eval_operand_inst_idx,
       exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       ghostPcTransportPtrTheory.ghost_inv_at_inst_idx] >>
  asm_rewrite_tac[] >>
  qpat_assum `!name a k. local_region ce es.scopes v name a k ==>
    d + outsz <= a \/ a + k <= d` mp_tac >>
  simp[SF SFY_ss, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  >> (gvs[])
QED

Finalise abi_decode_caller_allocation_joint
