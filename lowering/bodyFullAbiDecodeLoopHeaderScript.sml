Theory bodyFullAbiDecodeLoopHeader
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteGuard assignBasePtrBytesPrefix
  typedCopyOriginPtrBase typedMemoryCopy bodyPtrMakeArrayEmission bodyFullShared bodyPtrDefs
  allocaFootprint gasOriginPtrLabels instSeqPtrLo fragGasOriginPtrDead
  fragGasOriginPtrLoop fragGasCopyLoop stmtReasonLitFragMemory fragExec
  stateFrame emitHelperProps loweringShapeRules
  compileEnv emitHelper venomInst venomExecSemantics venomState
  words list finite_map exprLoweringProps freshWrites rich_list loweringStateRelDefs

(* Alpha-identical owned state quotation, not a HOL definition. *)
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
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
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

(* The loop counter is a protected, clean one-word pointer read. *)
Theorem abi_decode_loop_counter_load:
  emit_op MLOAD [Var counter] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ allocas_from lo s /\
  ptr_covers G tn counter s 32 /\ lookup_var counter s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  w2n a+32 <= s.vs_alloca_next /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    eval_operand (Var out) t = SOME (mload (w2n a) s) /\
    op_prov Gf (Var out) = NONE /\ op_taint tnf (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all (assign_base_bytes_mload_seq |> Q.SPECL
    [`<|d_stor := K (K {}); d_trans := K (K {});
                d_imm := K {}; d_ret := K {}|>`, `ctx`, `fn`, `PG`]) >>
  disch_then (qspecl_then [`fn`, `PG`, `sa.cs_next_id`, `out`] strip_assume_tac) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] /\
   inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   (!x. not_fresh_at sa x ==> x <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def, emitted_insts_def,
      inst_extends_def, not_fresh_at_def, DROP_APPEND1] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s with
    vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
   t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[Abbr `t`, update_var_def, state_frame_def] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `t`, lookup_var_update_var, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `lo <= s.vs_alloca_next /\ alloca_history fn s` by fs[] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[mk_inst_def] >>
     gvs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `(^owned_decoder_state) sb t G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
    gvs[inst_extends_def, emitted_insts_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `run_inst_seq_mem_ok [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] s` by
    (drule emit_mload_mem_ok >>
     disch_then (qspec_then `s` mp_tac) >> simp[eval_operand_def]) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> 0 ctx fn PG G tn
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] s G' tn'` by
    (qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  reverse conj_tac >- simp[Abbr `t`, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
     [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_origin_ptr_lift >>
  simp[Abbr `t`]
QED

(* Control transfer changes only the cursor, not owned resources. *)
Theorem abi_decode_loop_owned_jump[local]:
  (^owned_decoder_state) st s G tn ==>
  (^owned_decoder_state) st (jump_to lbl s) G tn
Proof
  strip_tac >>
  `alloca_history fn (jump_to lbl s)` by
    (irule allocaHistoryTheory.alloca_history_jump >>
     simp[jump_to_def] >> qexists_tac `s` >> fs[]) >>
  simp[stmt_state_rel_jump_to, bodyFullSharedTheory.ghost_inv_at_jump] >>
  gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
      bodyPtrDefsTheory.ptr_covers_def, local_region_def,
      jump_to_def, lookup_var_def] >> rpt conj_tac >> metis_tac[]
QED

Theorem abi_decode_loop_owned_branch[local]:
  emit_op LT [Var counter; length] sa = (lt,sb) /\
  emit_op ISZERO [lt] sb = (done,sc) /\
  emit_inst JNZ [done; Label exit; Label body_lbl] [] sc = ((),sd) /\
  lookup_var counter s = SOME (n2w j) /\
  eval_operand length s = SOME (n2w n) /\ j <= n /\ n < dimword (:256) /\
  FLOOKUP G counter = NONE /\ op_prov G length = NONE /\
  op_taint tn (Var counter) = {} /\ op_taint tn length = {} /\
  fn_has_code sa sd fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^owned_decoder_state) sd t Gf tnf /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j = n then exit else body_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all (typed_copy_origin_ptr_header_branch_path |> Q.GEN `D`) >>
  disch_then assume_tac >>
  first_assum (qspecl_then [`explicit`, `PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)` by
    (gen_tac >> first_x_assum (qspecl_then [`explicit`,`PG`,`D`] mp_tac) >>
     rpt strip_tac >> gvs[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\
   sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by
    gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  `!p. not_fresh_at sa p ==> p <> x /\ p <> y` by
    metis_tac[emit_op_old_var_separate, arithmeticTheory.LESS_EQ_REFL] >>
  qabbrev_tac `u = update_var y (if j = n then 1w else 0w)
      (update_var x (if j < n then 1w else 0w) s)` >>
  `t = jump_to (if j = n then exit else body_lbl) u` by simp[Abbr `u`] >>
  `alloca_history fn u` by
    (irule allocaHistoryTheory.alloca_history_frame >>
     qexists_tac `s` >> fs[Abbr `u`, update_var_def]) >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx)` by
    simp[Abbr `u`, update_var_def, state_frame_def] >>
  `!p. not_fresh_at sa p ==>
    lookup_var p u = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)` by
    (simp[Abbr `u`, lookup_var_update_var] >> metis_tac[]) >>
  `(^owned_decoder_state) sd u Gf tnf` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >> asm_rewrite_tac[]) >>
  `(^owned_decoder_state) sd t Gf tnf` by
    (qpat_assum `t = jump_to _ u` SUBST1_TAC >>
     irule abi_decode_loop_owned_jump >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  asm_rewrite_tac[] >> simp[Abbr `u`, jump_to_def, update_var_def] >>
  rpt strip_tac >>
  `p <> x /\ p <> y` by metis_tac[] >>
  simp[FLOOKUP_DRESTRICT, ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE]
QED

(* The concrete header segments select one endpoint before any horizon. *)
Theorem abi_decode_loop_header_joint:
  emit_op MLOAD [Var counter] sa = (Var idx,sb) /\
  compile_abi_dec_addr (Var input) src sb = (addr,sc) /\
  emit_op MLOAD [addr] sc = (count_op,sd) /\
  emit_op LT [Var idx;count_op] sd = (lt,se) /\
  emit_op ISZERO [lt] se = (done,sf) /\
  emit_inst JNZ [done;Label exit_lbl;Label body_lbl] [] sf = ((),sg) /\
  fn_has_code sa sb fn /\ fn_has_code sb sd fn /\ fn_has_code sd sg fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ sa.cs_current_insts = [] /\
  s.vs_inst_idx = 0 /\ allocas_from lo s /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. hi = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var counter s = SOME (n2w cell) /\ ptr_covers G tn counter s 32 /\
  mem_word_at cell s.vs_memory = n2w j /\
  (!i. cell <= i /\ i < cell+32 ==> i NOTIN tn.t_mem) /\
  cell+32 <= s.vs_alloca_next /\ cell < dimword (:256) /\
  eval_operand src s = SOME (n2w srcoff) /\ op_taint tn src = {} /\
  eval_operand hi s = SOME (n2w h) /\
  srcoff+32+n*asz <= h /\ h <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  mem_word_at (w2n input_word+srcoff) s.vs_memory = n2w n /\
  j <= n /\ n < dimword (:256) ==>
  ?t Gf tnf.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (^owned_decoder_state) sg t Gf tnf /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j = n then exit_lbl else body_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels /\
    tnf.t_mem = tn.t_mem /\
    eval_operand src t = SOME (n2w srcoff) /\
    eval_operand hi t = SOME (n2w h) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   (!i. w2n (n2w cell :256 word) <= i /\
     i < w2n (n2w cell :256 word)+32 ==> i NOTIN tn.t_mem) /\
   w2n (n2w cell :256 word)+32 <= s.vs_alloca_next` by simp[] >>
  drule_all abi_decode_loop_counter_load >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  rename1 `eval_operand (Var idx) u = _` >>
  `sa.cs_next_var <= sb.cs_next_var` by
    gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
        fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (qpat_x_assum `sa.cs_next_var <= sb.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `not_fresh_at sb input /\ local_ptrs_reserved ce sb /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x)` by
    (conj_tac >- simp[] >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     conj_tac >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sb x` irule >>
     metis_tac[]) >>
  `eval_operand src u = SOME (n2w srcoff) /\ op_taint tnf src = {}` by
    (Cases_on `src` >> gvs[eval_operand_def, ptrDisciplineTheory.op_taint_def]) >>
  `srcoff+32 <= LENGTH input_bytes` by decide_tac >>
  `allocas_from lo u` by
    (simp[ptrDisciplineTheory.allocas_from_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     simp[ptrDisciplineTheory.allocas_from_def]) >>
  drule_all abi_decode_owned_relative_load >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `sb.cs_next_var <= sd.cs_next_var /\ not_fresh_at sb idx` by
    gvs[abiEncoderTheory.compile_abi_dec_addr_def, emit_op_def, emit_inst_def,
        comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
        emit_def, comp_return_def, not_fresh_at_def] >>
  `!x. not_fresh_at sb x ==> not_fresh_at sd x` by
    (qpat_x_assum `sb.cs_next_var <= sd.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `not_fresh_at sd input /\ local_ptrs_reserved ce sd /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by
    (conj_tac >- simp[] >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sb` >> simp[]) >>
     conj_tac >> rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sb x ==> not_fresh_at sd x` irule >>
     metis_tac[]) >>
  `lookup_var idx t = SOME (n2w j) /\ FLOOKUP Gf' idx = NONE /\
   op_taint tnf' (Var idx) = {} /\
   eval_operand count_op t = SOME (n2w n)` by
    (fs[eval_operand_def, ptrDisciplineTheory.op_prov_def,
        valueEncodingPropsTheory.mem_word_at_eq_mload] >>
     gvs[mload_def]) >>
  `allocas_from lo t` by
    (simp[ptrDisciplineTheory.allocas_from_def] >>
     qpat_x_assum `allocas_from lo u` mp_tac >>
     simp[ptrDisciplineTheory.allocas_from_def]) >>
  drule_all abi_decode_loop_owned_branch >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p /\ not_fresh_at sd p` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `!p. not_fresh_at sa p ==>
    lookup_var p t' = lookup_var p s /\ FLOOKUP Gf'' p = FLOOKUP G p /\
    op_taint tnf'' (Var p) = op_taint tn (Var p)` by metis_tac[] >>
  `eval_operand src t' = SOME (n2w srcoff) /\
   eval_operand hi t' = SOME (n2w h)` by
    (conj_tac
     >- (qpat_x_assum `eval_operand src s = _` mp_tac >>
         Cases_on `src` >> simp[eval_operand_def] >> metis_tac[]) >>
     qpat_x_assum `eval_operand hi s = _` mp_tac >>
     Cases_on `hi` >> simp[eval_operand_def] >> metis_tac[]) >>
  qexistsl_tac [`t'`,`Gf''`,`tnf''`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gf`,`u`,`tnf`] >> simp[] >>
  irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`Gf'`,`t`,`tnf'`] >> simp[]
QED
