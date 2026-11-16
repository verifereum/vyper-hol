Theory bodyFullAbiDecodeBytesPrefix
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeFiniteGuard
  bodyFullAbiDecodeAge bodyFullAbiDecodeBytesArithmetic
  abiDecoderBytesBound abiDecoderBytesPhases abiDecoderRange abiDecoderGuards
  abiDecodePtrPrims abiDecodePtrBytesMember bodyPtrBopScalarCompile bodyPtrBopScalarOutcome
  gasOriginPtrLabels ptrDiscipline freshWrites exprLoweringProps emitHelperProps
  abiEncoder compileEnv emitHelper venomState venomExecSemantics venomInst
  words arithmetic list rich_list finite_map pred_set

Theorem abi_decode_bytes_head_run[local]:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  eval_operand src s = SOME (n2w off) /\
  eval_operand hi s = SOME (n2w h) /\
  off < dimword(:256) /\ h < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand head t = SOME (n2w (off+32)) /\
       off <= w2n (n2w (off+32):bytes32) /\
       w2n (n2w (off+32):bytes32) <= w2n (n2w h:bytes32)) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj, word_add_n2w] >>
  Cases_on `src` >> Cases_on `hi` >>
  gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
      abiDecoderReentryTheory.abi_decoder_older_vars_def, eval_operand_def,
      lookup_var_update_var, ASCIInumbersTheory.toString_inj,
      bool_to_word_def] >>
  IF_CASES_TAC >>
  gvs[lookup_var_update_var, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_bytes_payload_run[local]:
  abi_decode_bytes_payload_guard head len hi sa = ((),sb) /\ hi <> Lit 0w /\
  eval_operand head s = SOME (n2w off) /\
  eval_operand len s = SOME (n2w c) /\
  eval_operand hi s = SOME (n2w h) /\
  off < dimword(:256) /\ h < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var head /\
  abi_decoder_operand_live sa.cs_next_var len /\
  abi_decoder_operand_live sa.cs_next_var hi ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       off <= w2n (n2w (off+c):bytes32) /\
       w2n (n2w (off+c):bytes32) <= w2n (n2w h:bytes32)) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  simp[abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj, word_add_n2w] >>
  qpat_x_assum `abi_decoder_operand_live _ len` kall_tac >>
  qpat_x_assum `eval_operand len s = _` kall_tac >>
  Cases_on `head` >> Cases_on `hi` >>
  gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
      abiDecoderReentryTheory.abi_decoder_older_vars_def, eval_operand_def,
      lookup_var_update_var, ASCIInumbersTheory.toString_inj,
      bool_to_word_def] >>
  IF_CASES_TAC >>
  gvs[lookup_var_update_var, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_bytes_count_run[local]:
  emit_op GT [cnt;Lit (n2w n)] sa = (many,c1) /\
  emit_op ISZERO [many] c1 = (ok,c2) /\
  emit_void ASSERT [ok] c2 = ((),sb) /\
  eval_operand cnt s = SOME (n2w c) /\
  c < dimword(:256) /\ n < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var cnt ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ c <= n) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  simp[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure1_def, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, eval_operand_update_other,
       ASCIInumbersTheory.toString_inj, bool_to_word_def] >>
  Cases_on `c <= n` >> simp[]
QED

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
  EVERY (\(aid,p,b,k,bytes). not_fresh_at st p) live``;

(* Keep canonical scalar witnesses while assembling owned and emitted frames. *)
Theorem abi_decode_bytes_scalar_frame_joint[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    u = t with vs_inst_idx := LENGTH sb.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\
    u.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo u /\
    (!op. op IN B ==> op_prov Gf op = NONE /\ op_taint tnf op = {}) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all (bodyPtrBopScalarSeqTheory.bop_scalar_seq_run |>
    Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s G' tn'` by
    (irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bodyPtrBopScalarSeqTheory.bop_scalar_seq_mem_ok] >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
   u.vs_memory = s.vs_memory` by
    (simp[Abbr `u`] >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[stateFrameTheory.state_frame_def]) >>
  suspend "scalar_owned"
QED

Resume abi_decode_bytes_scalar_frame_joint[scalar_owned]:
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`, lookup_var_def, op_taint_def] >> gvs[]) >>
  `alloca_history fn s` by fs[] >>
  `alloca_history fn u` by
    (irule abi_decode_no_alloca_endpoint_history >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[] >>
     gvs[inst_extends_def]) >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  qexistsl_tac [`u`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
  simp[Abbr `u`] >> gen_tac >>
  irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
  asm_rewrite_tac[]
QED

Finalise abi_decode_bytes_scalar_frame_joint

Theorem abi_decode_bytes_head_joint[local]:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ allocas_from lo s /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w off) /\
  eval_operand hi s = SOME (n2w h) /\
  off < dimword(:256) /\ h < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  op_prov G src = NONE /\ op_taint tn src = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ off+32 <= h /\
    eval_operand head t = SOME (n2w (off+32)) /\
    op_prov Gf head = NONE /\ op_taint tnf head = {} /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))) \/
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {src;hi;Lit 32w}
     (emitted_insts sa sb) B /\ {src;hi;Lit 32w} SUBSET B /\ head IN B` by
    (irule abi_decode_bytes_head_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {src;hi;Lit 32w} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  drule_all abi_decode_bytes_head_run >> strip_tac
  >- (disj1_tac >>
      `off+32 <= h` by
        (irule abi_decode_checked_add_bound >>
         asm_simp_tac (srw_ss()) [LESS_MOD] >>
         conj_tac >- simp[dimword_def] >>
         (bossLib.gvs [wordsTheory.w2n_n2w , arithmeticTheory.MOD_LESS_EQ , arithmeticTheory.LESS_EQ_TRANS])) >>
      `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
        (drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_memory_checks >>
         simp[EVERY_MEM] >> metis_tac[]) >>
      `inst_extends sa sb` by simp[inst_extends_def] >>
      drule_all abi_decode_bytes_scalar_frame_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`u`, `Gf`, `tnf`] >>
      simp[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  disj2_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >> simp[]
QED

Theorem abi_decode_bytes_payload_joint[local]:
  abi_decode_bytes_payload_guard head cnt hi sa = ((),sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ allocas_from lo s /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand head s = SOME (n2w p) /\
  eval_operand cnt s = SOME (n2w c) /\
  eval_operand hi s = SOME (n2w h) /\
  p < dimword(:256) /\ h < dimword(:256) /\ c < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var head /\
  abi_decoder_operand_live sa.cs_next_var cnt /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  op_prov G head = NONE /\ op_taint tn head = {} /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ p+c <= h /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))) \/
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    (qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[]) >>
  drule abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {head;cnt;hi}
     (emitted_insts sa sb) B /\ {head;cnt;hi} SUBSET B` by
    (irule abi_decode_bytes_payload_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {head;cnt;hi} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[]) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  drule_all abi_decode_bytes_payload_run >> strip_tac
  >- (disj1_tac >>
      `p+c <= h` by
        (irule abi_decode_checked_add_bound >>
         asm_simp_tac (srw_ss()) [LESS_MOD] >>
         gvs[w2n_n2w, MOD_LESS_EQ, LESS_EQ_TRANS]) >>
      `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
        (drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_memory_checks >>
         simp[EVERY_MEM] >> metis_tac[]) >>
      `inst_extends sa sb` by simp[inst_extends_def] >>
      drule_all abi_decode_bytes_scalar_frame_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[]) >>
  disj2_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >> simp[]
QED

Theorem abi_decode_bytes_count_joint[local]:
  abi_decode_le_guard cnt (Lit (n2w n)) sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ allocas_from lo s /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand cnt s = SOME (n2w c) /\
  c < dimword(:256) /\ n < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var cnt /\
  op_prov G cnt = NONE /\ op_taint tn cnt = {} ==>
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ c <= n /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))) \/
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   sb.cs_current_bb = sa.cs_current_bb /\ inst_extends sa sb` by
    (qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     simp[abiDecoderGuardTheory.abi_decode_le_guard_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pop_assum kall_tac) >> strip_tac >> gvs[] >>
     simp_tac (srw_ss()) [inst_extends_def, emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND]) >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} {cnt;Lit (n2w n)}
     (emitted_insts sa sb) B /\ {cnt;Lit (n2w n)} SUBSET B` by
    (irule abi_decode_le_guard_scalar >> simp[] >> metis_tac[]) >>
  `!op. op IN {cnt;Lit (n2w n)} ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  `(?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ c <= n) \/
   (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)` by
    (Cases_on `emit_op GT [cnt;Lit (n2w n)] sa` >>
     rename1 `emit_op GT [cnt;Lit (n2w n)] sa = (many,c1)` >>
     Cases_on `emit_op ISZERO [many] c1` >>
     rename1 `emit_op ISZERO [many] c1 = (ok,c2)` >>
     `emit_void ASSERT [ok] c2 = ((),sb)` by
       (qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
        simp[abiDecoderGuardTheory.abi_decode_le_guard_def,
             comp_bind_def, comp_ignore_bind_def]) >>
     drule_all abi_decode_bytes_count_run >> simp[]) >>
  pop_assum strip_assume_tac
  >- (disj1_tac >>
      `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
        (drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_memory_checks >>
         simp[EVERY_MEM] >> metis_tac[]) >>
      drule_all abi_decode_bytes_scalar_frame_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[]) >>
  disj2_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >> simp[]
QED

(* Retain the canonical load's fresh address certificate at its actual endpoint. *)
Theorem abi_decode_bytes_owned_load_frame_joint[local]:
  compile_abi_dec_addr (Var input) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  p+32 <= LENGTH input_bytes /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  allocas_from lo s ==>
  ?out ar t Gf tnf.
    v = Var out /\ not_fresh_at sc out /\
    addr = Var ar /\ not_fresh_at sc ar /\
    abi_decode_ptr_window Gf tnf t ar
      (input_word+n2w p) (LENGTH input_bytes-p) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    eval_operand v t = SOME (mload (w2n input_word+p) s) /\
    op_prov Gf v = NONE /\ op_taint tnf v = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\ allocas_from lo t /\
    (^owned_decoder_state) sc t Gf tnf /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
   lo <= s.vs_alloca_next /\
   w2n input_word+LENGTH input_bytes <= s.vs_alloca_next /\
   alloca_history fn s` by fs[] >>
  drule_all (abiDecodePtrReadTheory.abi_decode_ptr_relative_load |>
    Q.INST [`D` |-> `ARB`, `PG` |-> `PG`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G' tn'` by
    (gen_tac >>
     drule_all (abiDecodePtrReadTheory.abi_decode_ptr_relative_load |>
       Q.INST [`D` |-> `D`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
     qpat_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique) >>
     disch_then drule >> simp[] >> strip_tac >> gvs[]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sc) s G' tn'` by
    (gen_tac >> irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists_tac `D` >> simp[]) >>
  `emit_op ADD [Var input;pos] sa = (addr,sb)` by
    gvs[compile_abi_dec_addr_def] >>
  `inst_extends sa sb /\ inst_extends sb sc /\ inst_extends sa sc` by
    metis_tac[inst_extends_emit_op, inst_extends_trans] >>
  `sc.cs_current_bb = sa.cs_current_bb` by gvs[inst_extends_def] >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS) (emitted_insts sa sc)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    suspend "load_memory" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >>
     qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     `((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sc.cs_current_insts) = t` by
       simp[venom_state_component_equality] >> asm_rewrite_tac[]) >>
  suspend "load_owned"
QED

Resume abi_decode_bytes_owned_load_frame_joint[load_memory]:
  `lookup_var input s = SOME input_word` by
    gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
  asm_rewrite_tac[] >>
  simp[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
  conj_tac
  >- (irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var input;pos]
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (input_word+n2w p) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[] >>
  simp[instMemFrontierTheory.below_frontier_MLOAD, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (`w2n (input_word+n2w p) = w2n input_word+p` by
        (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
      decide_tac) >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume abi_decode_bytes_owned_load_frame_joint[load_owned]:
  `isPREFIX sa.cs_current_insts sc.cs_current_insts` by
    metis_tac[inst_extends_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sc)` by
    simp[mk_inst_def] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history >> metis_tac[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    simp[] >>
  `(^owned_decoder_state) sc t G' tn'` by
    (irule abi_decode_owned_scalar_frame_with_history >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `allocas_from lo t` by
    (fs[allocas_from_def, stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  qexistsl_tac [`out`, `ap`, `t`, `G'`, `tn'`] >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >>
  metis_tac[operand_11, ADD_COMM]
QED

Finalise abi_decode_bytes_owned_load_frame_joint

Theorem abi_decode_bytes_prefix_joint:
  abi_decode_bytes_head pos hi sa = (head,sh) /\
  compile_abi_dec_addr (Var input) pos sh = (addr,sl) /\
  emit_op MLOAD [addr] sl = (cnt,sc) /\
  abi_decode_le_guard cnt (Lit (n2w n)) sc = ((),sg) /\
  abi_decode_bytes_payload_guard head cnt hi sg = ((),sb) /\
  hi <> Lit 0w /\ fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ allocas_from lo s /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand pos s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
  off < dimword(:256) /\ h < dimword(:256) /\
  h <= LENGTH input_bytes /\ n+31 < dimword(:256) /\
  w2n input_word+LENGTH input_bytes < dimword(:256) /\
  abi_decoder_operand_live sa.cs_next_var pos /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} ==>
  (?t Gf tnf c ar out.
    cnt = Var out /\ addr = Var ar /\
    not_fresh_at sb out /\ not_fresh_at sb ar /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ c <= n /\ off+32+c <= h /\
    eval_operand cnt t = SOME (n2w c) /\
    op_prov Gf cnt = NONE /\ op_taint tnf cnt = {} /\
    abi_decode_ptr_window Gf tnf t ar (input_word+n2w off) (32+c) /\
    op_taint tnf (Var ar) = {} /\
    t.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x))) \/
  (?t Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf))
Proof
  strip_tac >>
  `inst_extends sa sh /\ inst_extends sh sl /\ inst_extends sl sc /\
   inst_extends sc sg /\ inst_extends sg sb` by
    (conj_tac >- metis_tac[abi_decode_bytes_head_shape] >>
     conj_tac >- (gvs[compile_abi_dec_addr_def] >> metis_tac[inst_extends_emit_op]) >>
     conj_tac >- metis_tac[inst_extends_emit_op] >>
     conj_tac
     >- (qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
         simp[abiDecoderGuardTheory.abi_decode_le_guard_def, comp_bind_def,
           comp_ignore_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
         metis_tac[inst_extends_emit_op, inst_extends_emit_void, inst_extends_trans]) >>
     metis_tac[abi_decode_bytes_payload_guard_fragment_shape]) >>
  suspend "prefix_layout"
QED

Resume abi_decode_bytes_prefix_joint[prefix_layout]:
  `inst_extends sh sc /\ inst_extends sa sg /\ inst_extends sh sb /\
   inst_extends sc sb /\ inst_extends sa sc` by metis_tac[inst_extends_trans] >>
  `sh.cs_blocks = sa.cs_blocks /\ sh.cs_current_bb = sa.cs_current_bb /\
   sc.cs_blocks = sh.cs_blocks /\ sc.cs_current_bb = sh.cs_current_bb /\
   sg.cs_blocks = sc.cs_blocks /\ sg.cs_current_bb = sc.cs_current_bb /\
   sb.cs_blocks = sg.cs_blocks /\ sb.cs_current_bb = sg.cs_current_bb` by
    (drule abi_decode_bytes_head_fragment_shape >> strip_tac >>
     drule abi_decode_bytes_payload_guard_fragment_shape >> strip_tac >>
     qpat_x_assum `sh.cs_blocks = _` mp_tac >>
     qpat_x_assum `sh.cs_current_bb = _` mp_tac >>
     qpat_x_assum `sb.cs_blocks = _` mp_tac >>
     qpat_x_assum `sb.cs_current_bb = _` mp_tac >>
     qpat_x_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_abi_dec_addr_def, abiDecoderGuardTheory.abi_decode_le_guard_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  `fn_has_code sa sh fn /\ fn_has_code sh sc fn /\
   fn_has_code sc sg fn /\ fn_has_code sg sb fn` by
    (`!a b. inst_extends a b /\ b.cs_blocks = a.cs_blocks /\
       b.cs_current_bb = a.cs_current_bb ==> cs_extends a b` by
       (simp[inst_extends_def, cs_extends_def] >> rpt strip_tac >>
        qexists_tac `[]` >> simp[IS_PREFIX_APPEND]) >>
     metis_tac[fragExecTheory.fn_has_code_split, inst_extends_trans]) >>
  drule_all abi_decode_bytes_head_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- suspend "prefix_load"
  >> metis_tac[]
QED

Resume abi_decode_bytes_prefix_joint[prefix_load]:
  rename1 `gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gh,tnh)` >>
  `sa.cs_next_var <= sh.cs_next_var` by
    (qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_x_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_x_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` mp_tac) >>
     metis_tac[gas_origin_ptr_path_preserves_labels]) >>
  `eval_operand pos u = SOME (n2w off) /\ op_taint tnh pos = {}` by
    (Cases_on `pos` >>
     gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `not_fresh_at sh input /\ local_ptrs_reserved ce sh /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x)` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `off+32 <= LENGTH input_bytes` by decide_tac >>
  drule_all abi_decode_bytes_owned_load_frame_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  suspend "prefix_count"
QED

Resume abi_decode_bytes_prefix_joint[prefix_count]:
  rename1 `abi_decode_ptr_window Gc tnc v ar _ _` >>
  `sh.cs_next_var <= sc.cs_next_var` by
    (qpat_x_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_abi_dec_addr_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `not_fresh_at sc input /\ local_ptrs_reserved ce sc /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  qmatch_asmsub_abbrev_tac `eval_operand cnt v = SOME wc` >>
  qabbrev_tac `c = w2n wc` >>
  `wc = (n2w c:bytes32) /\ c < dimword(:256) /\ n < dimword(:256)` by
    (simp[Abbr `c`, w2n_lt] >> decide_tac) >>
  `abi_decoder_operand_live sc.cs_next_var cnt` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_emit] >>
  `eval_operand cnt v = SOME (n2w c)` by metis_tac[] >>
  drule_all abi_decode_bytes_count_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- suspend "prefix_payload"
  >> (disj2_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> gen_tac >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND])
QED

Resume abi_decode_bytes_prefix_joint[prefix_payload]:
  rename1 `gas_origin_ptr_path _ (v,Gc,tnc) [] (OK w,Gg,tng)` >>
  `sc.cs_next_var <= sg.cs_next_var` by
    (qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abiDecoderGuardTheory.abi_decode_le_guard_def, emit_op_def,
       emit_void_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `abi_decoder_operand_live sh.cs_next_var head` by
    (qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_x_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def]) >>
  suspend "prefix_transport"
QED

Resume abi_decode_bytes_prefix_joint[prefix_transport]:
  `v.vs_labels = u.vs_labels /\ w.vs_labels = v.vs_labels` by
    metis_tac[gas_origin_ptr_path_preserves_labels] >>
  `not_fresh_at sg input /\ local_ptrs_reserved ce sg /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sg x)` by
    metis_tac[not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `eval_operand head w = SOME (n2w (off+32)) /\
   op_prov Gg head = NONE /\ op_taint tng head = {}` by
    (qpat_x_assum `eval_operand head u = _` mp_tac >>
     qpat_x_assum `op_prov Gh head = _` mp_tac >>
     qpat_x_assum `op_taint tnh head = _` mp_tac >>
     qpat_x_assum `abi_decoder_operand_live sh.cs_next_var head` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sh x ==> _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sc x ==> _` mp_tac >>
     qpat_x_assum `sh.cs_next_var <= sc.cs_next_var` mp_tac >>
     qpat_x_assum `v.vs_labels = u.vs_labels` mp_tac >>
     qpat_x_assum `w.vs_labels = v.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `head` >>
     gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def,
       op_prov_def, op_taint_def] >> metis_tac[]) >>
  `!op. abi_decoder_operand_live sa.cs_next_var op ==>
     eval_operand op w = eval_operand op s /\
     op_prov Gg op = op_prov G op /\ op_taint tng op = op_taint tn op` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sh x ==> _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sc x ==> _` mp_tac >>
     qpat_x_assum `sa.cs_next_var <= sh.cs_next_var` mp_tac >>
     qpat_x_assum `sh.cs_next_var <= sc.cs_next_var` mp_tac >>
     qpat_x_assum `u.vs_labels = s.vs_labels` mp_tac >>
     qpat_x_assum `v.vs_labels = u.vs_labels` mp_tac >>
     qpat_x_assum `w.vs_labels = v.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `op` >>
     gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,
       loweringStateRelDefsTheory.not_fresh_at_def, eval_operand_def,
       op_prov_def, op_taint_def] >> metis_tac[]) >>
  `eval_operand hi w = SOME (n2w h) /\ op_prov Gg hi = NONE /\
   op_taint tng hi = {}` by metis_tac[] >>
  `eval_operand cnt w = SOME (n2w c) /\ op_prov Gg cnt = NONE /\
   op_taint tng cnt = {}` by
    (qpat_x_assum `!x. not_fresh_at sc x ==> _` (qspec_then `out` mp_tac) >>
     qpat_x_assum `cnt = Var out` mp_tac >>
     qpat_x_assum `not_fresh_at sc out` mp_tac >>
     qpat_x_assum `eval_operand cnt v = SOME (n2w c)` mp_tac >>
     qpat_x_assum `op_prov Gc cnt = _` mp_tac >>
     qpat_x_assum `op_taint tnc cnt = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[eval_operand_def, op_prov_def]) >>
  `abi_decoder_operand_live sg.cs_next_var head /\
   abi_decoder_operand_live sg.cs_next_var cnt /\
   abi_decoder_operand_live sg.cs_next_var hi` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono, LESS_EQ_TRANS] >>
  `off+32 < dimword(:256)` by decide_tac >>
  drule_all abi_decode_bytes_payload_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- suspend "prefix_success"
  >> (disj2_tac >> qexistsl_tac [`t`, `Gf`, `tnf`] >> gen_tac >>
      metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND])
QED

Resume abi_decode_bytes_prefix_joint[prefix_success]:
  `sg.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
     qpat_x_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abi_decode_bytes_payload_guard_def, compile_abi_decode_range_check_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x v /\
     FLOOKUP Gf x = FLOOKUP Gc x /\ op_taint tnf (Var x) = op_taint tnc (Var x)` by
    metis_tac[not_fresh_at_mono] >>
  `abi_decode_ptr_window Gf tnf t ar (input_word+n2w off) (LENGTH input_bytes-off)` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
     qexistsl_tac [`Gc`, `v`, `tnc`] >> simp[] >> metis_tac[]) >>
  `32+c <= LENGTH input_bytes-off` by decide_tac >>
  `abi_decode_ptr_window Gf tnf t ar (input_word+n2w off) (32+c)` by
    (qpat_x_assum `abi_decode_ptr_window Gf tnf t ar _ _` mp_tac >>
     qpat_x_assum `32+c <= LENGTH input_bytes-off` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
     rpt strip_tac >- metis_tac[reasonCopySourcePtrTheory.ptr_covers_mono] >>
     first_x_assum irule >> decide_tac) >>
  `op_taint tnf (Var ar) = {}` by
    (qpat_x_assum `abi_decode_ptr_window Gf tnf t ar _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def, bodyPtrDefsTheory.ptr_covers_def]) >>
  `eval_operand cnt t = SOME (n2w c) /\ op_prov Gf cnt = NONE /\ op_taint tnf cnt = {}` by
    (qpat_x_assum `!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x v /\ _`
       (qspec_then `out` mp_tac) >>
     qpat_x_assum `cnt = Var out` mp_tac >>
     qpat_x_assum `not_fresh_at sc out` mp_tac >>
     qpat_x_assum `eval_operand cnt v = SOME (n2w c)` mp_tac >>
     qpat_x_assum `op_prov Gc cnt = _` mp_tac >>
     qpat_x_assum `op_taint tnc cnt = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[eval_operand_def, op_prov_def]) >>
  disj1_tac >> qexistsl_tac [`t`, `Gf`, `tnf`, `c`, `ar`, `out`] >>
  asm_rewrite_tac[] >> suspend "prefix_finish"
QED

Resume abi_decode_bytes_prefix_joint[prefix_finish]:
  conj_tac >- metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
  conj_tac >- metis_tac[not_fresh_at_mono, LESS_EQ_TRANS] >>
  conj_tac
  >- (gen_tac >> metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]) >>
  metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]
QED

Finalise abi_decode_bytes_prefix_joint
