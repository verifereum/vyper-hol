Theory bodyFullAbiDecodeLoopSource
Ancestors
  bodyFullAbiDecodeLeafCases decoderArraySetupPtr calldataDynOwned
  bodyPtrBopScalarOutcome bodyPtrBopScalarSeq stateFrame
  allocaFootprint emitHelperProps exprLoweringProps freshWrites
  compileEnv emitHelper venomInst venomExecSemantics venomState
  abiDecoderIndexedAddress abiDecoderReentry loweringStateRelDefs
  words list rich_list finite_map

(* The shared owned-state quotation; this introduces no HOL constant. *)
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

Theorem abi_decode_loop_source_joint:
  emit_op ADD [src;Lit 32w] sa = (data,s1) /\
  emit_op MUL [idx;Lit (n2w asz)] s1 = (offset,s2) /\
  emit_op ADD [data;offset] s2 = (head,sb) /\
  eval_operand src s = SOME (n2w srcoff) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var idx /\
  op_prov G src = NONE /\ op_prov G idx = NONE /\
  op_taint tn src = {} /\ op_taint tn idx = {} /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gu tnu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gu tnu /\
    eval_operand data u = SOME (n2w (srcoff+32)) /\
    eval_operand head u = SOME (n2w (srcoff+32+j*asz)) /\
    op_prov Gu data = NONE /\ op_taint tnu data = {} /\
    op_prov Gu head = NONE /\ op_taint tnu head = {} /\
    abi_decoder_operand_live sb.cs_next_var data /\
    abi_decoder_operand_live sb.cs_next_var head /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ u.vs_labels = s.vs_labels /\
    tnu.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==>
      lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
      op_taint tnu (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `abi_decode_indexed_address src idx asz sa = (head,sb)` by
    simp[abi_decode_indexed_address_def, comp_bind_def] >>
  drule_all calldataDynOwnedTheory.calldata_indexed_address_repeat >> strip_tac >>
  `(!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. idx = Var x ==> not_fresh_at sa x)` by
    (conj_tac >> rpt strip_tac >> gvs[abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def]) >>
  drule_all clean_scaled_source_prefix_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`, `cx`, `ctx`, `PG`, `ARB`] strip_assume_tac) >>
  `!i. MEM i (emitted_insts sa sb) ==> MEM i.inst_opcode [ADD;MUL]` by
    (qpat_x_assum `emit_op ADD [src;Lit 32w] sa = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ s1 = _` mp_tac >>
     qpat_x_assum `emit_op ADD [data;offset] s2 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, comp_ignore_bind_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `MEM i _` mp_tac >>
     pure_rewrite_tac [emitted_insts_def, compile_state_accfupds,
       compile_state_accessors, GSYM APPEND_ASSOC, DROP_LENGTH_APPEND,
       combinTheory.K_THM, MEM, mk_inst_def, instruction_accessors] >>
     rpt strip_tac >> gvs[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (mp_tac (Q.SPECL [`emitted_insts sa sb`, `\x:string. F`, `s`, `t`]
      run_inst_seq_protected_frame) >>
     impl_tac >- (conj_tac >- (rpt gen_tac >> strip_tac >>
       `MEM i.inst_opcode [ADD;MUL]` by metis_tac[] >>
       `MEM i.inst_opcode
         [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
          EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
          SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN; ASSERT; ASSERT_UNREACHABLE]`
         by (fs[MEM] >> metis_tac[]) >>
       drule_all bop_scalar_inst_protected_frame >> simp[]) >> simp[]) >> simp[]) >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_assum `emit_op ADD [src;Lit 32w] sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MUL _ s1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD [data;offset] s2 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >> simp[] >>
     qpat_x_assum `emit_op ADD [src;Lit 32w] sa = _` mp_tac >>
     qpat_x_assum `emit_op MUL _ s1 = _` mp_tac >>
     qpat_x_assum `emit_op ADD [data;offset] s2 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def, comp_ignore_bind_def] >>
     rpt strip_tac >> gvs[]) >>
  qabbrev_tac `r = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame r = state_frame (s with vs_inst_idx := r.vs_inst_idx)` by
    (simp[Abbr `r`] >>
     qpat_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  `alloca_history fn r` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >>
     fs[Abbr `r`, inst_extends_def, IS_PREFIX_APPEND, EVERY_MEM, MEM] >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` drule >> strip_tac >> simp[]) >>
  `(^owned_decoder_state) sb r HG u` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
     asm_rewrite_tac[] >> simp[Abbr `r`, lookup_var_def] >>
     metis_tac[lookup_var_def]) >>
  qexistsl_tac [`r`, `HG`, `u`] >>
  conj_tac >- (gen_tac >> first_assum irule >> simp[]) >>
  asm_rewrite_tac[] >>
  simp[Abbr `r`, eval_operand_def, lookup_var_def, word_add_n2w] >>
  conj_tac >- metis_tac[GSYM word_add_n2w, GSYM word_mul_n2w,
    arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM,
    arithmeticTheory.MULT_COMM] >>
  conj_tac >- (Cases_on `data` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
  metis_tac[lookup_var_def]
QED
