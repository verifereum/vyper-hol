Theory bodyFullAbiDecodeLoopHeaderExact
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeRelativeLoadExact
  bodyFullAbiDecodeFiniteGuard assignBasePtrBytesPrefix
  typedCopyOriginPtrBase typedMemoryCopy bodyPtrMakeArrayEmission bodyFullShared bodyPtrDefs
  allocaFootprint gasOriginPtrLabels instSeqPtrLo fragGasOriginPtrDead
  fragGasOriginPtrLoop fragGasCopyLoop stmtReasonLitFragMemory fragExec fragGasPath
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
Theorem abi_decode_loop_counter_load_exact:
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
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)) /\
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
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)` by
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] /\
      LENGTH (FILTER (\i. i.inst_opcode = GAS)
        [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]) = 0` by
       simp[mk_inst_def, is_terminator_def] >>
     qpat_x_assum `fn_has_code sa sb fn` kall_tac >>
     rpt strip_tac >> drule_all abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `t`]) >>
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
  conj_tac >- asm_rewrite_tac[] >>
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
