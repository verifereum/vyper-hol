Theory bodyFullAbiDecodeGuardReadObserved
Ancestors
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeFiniteGuard bodyFullAbiDecodeScalarNoAlloca
  bodyFullAbiDecodeAge bodyFullAbiDecodeBytesArithmetic bodyFullAbiDecodeClampMemory
  abiDecoderBytesBound abiDecoderBytesPhases abiDecoderRange abiDecoderGuards
  abiDecodePtrPrims abiDecodePtrBytesMember bodyPtrBopScalarCompile bodyPtrBopScalarOutcome
  gasOriginPtrLabels ptrDiscipline freshWrites exprLoweringProps emitHelperProps
  abiEncoder compileEnv emitHelper venomState venomExecSemantics venomInst
  words arithmetic list rich_list finite_map pred_set
  bodyFullAbiDecodeFiniteObserved bodyPtrBopScalarDynamic fragGasPath fragExec
  bodyFullAbiDecodeRelativeLoadExact[qualified]

Theorem abi_decode_bytes_head_run:
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
  fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
      abiDecoderReentryTheory.abi_decoder_older_vars_def, eval_operand_def,
      lookup_var_update_var, ASCIInumbersTheory.toString_inj,
      bool_to_word_def] >>
  IF_CASES_TAC >>
  gvs[lookup_var_update_var, ASCIInumbersTheory.toString_inj]
QED

Theorem abi_decode_bytes_count_run:
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
Theorem abi_decode_bytes_scalar_frame_joint:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
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
    metis_tac[bodyFullAbiDecodeClampMemoryTheory.abi_decode_scalar_seq_mem_ok] >>
  `ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     drule_all bop_scalar_seq_outputs >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[]) >>
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
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[] >>
     gvs[inst_extends_def]) >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `allocas_from lo u` by metis_tac[allocas_from_def] >>
  qexistsl_tac [`u`, `G'`, `tn'`] >> asm_rewrite_tac[] >>
  simp[Abbr `u`] >> gen_tac >>
  irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
  asm_rewrite_tac[]
QED

Finalise abi_decode_bytes_scalar_frame_joint

Theorem scalar_success_observed[local]:
  bop_scalar_seq R A (emitted_insts sa sb) B /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  !obs. fn_has_code sa sb obs ==>
    gas_path ctx obs s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >>
  simp[EVERY_CONJ] >> strip_tac >>
  rpt strip_tac >> irule abi_decode_finite_success_observed >>
  conj_tac >- asm_rewrite_tac[] >>
  qexistsl_tac [`emitted_insts sa sb`, `sa`] >>
  fs[inst_extends_def, LENGTH_NIL, FILTER_EQ_NIL, EVERY_CONJ]
QED

Theorem revert_paths_same[local]:
  gas_path ctx fn s n (Abort Revert_abort t) /\
  gas_path ctx fn s m (Abort Revert_abort u) ==> t = u
Proof
  strip_tac >>
  `?i. run_from i ctx fn s = Abort Revert_abort t` by
    metis_tac[gas_path_exit, exit_result_def] >>
  `?j. run_from j ctx fn s = Abort Revert_abort u` by
    metis_tac[gas_path_exit, exit_result_def] >>
  `run_from (i+j) ctx fn s = Abort Revert_abort t` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `i` >> simp[]) >>
  `run_from (i+j) ctx fn s = Abort Revert_abort u` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `j` >> simp[]) >>
  fs[]
QED

(* Compare only terminal executions, both in the original function. *)
Theorem scalar_revert_observed[local]:
  bop_scalar_seq R A (emitted_insts sa sb) B /\ inst_extends sa sb /\
  EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb) /\
  sb.cs_current_bb = sa.cs_current_bb /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (Abort Revert_abort u,Gf,tnf) ==>
  !obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort u)
Proof
  strip_tac >> drule_all bodyPtrBopScalarDynamicTheory.bop_scalar_seq_abort_prefix >>
  reverse strip_tac >- fs[EVERY_APPEND, mk_inst_def] >>
  rename1 `emitted_insts sa sb = prefix ++ [mk_inst id opc [cond] []] ++ suffix` >>
  qpat_x_assum `opc = ASSERT` SUBST_ALL_TAC >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) prefix) = 0` by
    (drule_at (Pat `bop_scalar_seq _ _ prefix _`) bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >>
     simp[EVERY_CONJ, LENGTH_NIL, FILTER_EQ_NIL]) >>
  `sb.cs_current_insts = sa.cs_current_insts ++
      (prefix ++ mk_inst id ASSERT [cond] [] :: suffix)` by
    fs[inst_extends_def] >>
  qabbrev_tac `v = t with vs_inst_idx := LENGTH sa.cs_current_insts + LENGTH prefix` >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort v)` by
    (unabbrev_all_tac >> rpt strip_tac >> irule abi_decode_finite_revert_observed >>
     fs[LENGTH_NIL, APPEND_ASSOC] >>
     qexistsl_tac [`cond`, `id`, `sb`, `suffix`] >> simp[]) >>
  `gas_path ctx fn s 0 (Abort Revert_abort u)` by
    (drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >>
     simp[] >> metis_tac[fragGasPathPtrTheory.gas_path_ptr_erase]) >>
  `v = u` by metis_tac[revert_paths_same] >>
  qpat_x_assum `v = u` SUBST_ALL_TAC >> asm_rewrite_tac[]
QED

Theorem abi_decode_bytes_head_joint_observed:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t))) \/
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort t)))
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     simp[abi_decode_bytes_head_def, compile_abi_decode_range_check_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[] >> simp_tac (srw_ss()) [emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def]) >>
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
         gvs[w2n_n2w, MOD_LESS_EQ, LESS_EQ_TRANS]) >>
      `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
        metis_tac[abi_decode_scalar_seq_no_alloca] >>
      drule_all abi_decode_bytes_scalar_frame_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)` by
        (qpat_assum `u = _` SUBST1_TAC >>
         rpt strip_tac >> irule scalar_success_observed >>
         asm_rewrite_tac[] >> metis_tac[]) >>
      qexistsl_tac [`u`, `Gf`, `tnf`] >>
      simp[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  disj2_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >>
  conj_tac >- asm_rewrite_tac[] >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
  rpt strip_tac >> irule scalar_revert_observed >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem abi_decode_bytes_count_joint_observed:
  abi_decode_le_guard cnt (Lit (n2w n)) sa = ((),sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t))) \/
  (?t Gf tnf. (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort t,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort t)))
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
   sb.cs_current_bb = sa.cs_current_bb /\ inst_extends sa sb /\
   EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     simp[abiDecoderGuardTheory.abi_decode_le_guard_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pop_assum kall_tac) >> strip_tac >> gvs[] >>
     simp_tac (srw_ss()) [inst_extends_def, emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def]) >>
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
        metis_tac[abi_decode_scalar_seq_no_alloca] >>
      drule_all abi_decode_bytes_scalar_frame_joint >>
      disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
      `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)` by
        (qpat_assum `u = _` SUBST1_TAC >>
         rpt strip_tac >> irule scalar_success_observed >>
         asm_rewrite_tac[] >> metis_tac[]) >>
      qexistsl_tac [`u`, `Gf`, `tnf`] >> simp[]) >>
  disj2_tac >> drule_all abi_decode_scalar_guard_abort_joint >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`t with vs_inst_idx := j`, `Gf`, `tnf`] >>
  conj_tac >- asm_rewrite_tac[] >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `ARB` assume_tac) >>
  rpt strip_tac >> irule scalar_revert_observed >>
  asm_rewrite_tac[] >> metis_tac[]
QED

(* Retain the canonical load's fresh address certificate at its actual endpoint. *)
Theorem abi_decode_bytes_owned_load_frame_joint_observed:
  compile_abi_dec_addr (Var input) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  fn_has_code sa sc fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
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
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t))
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
  `ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sc = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sc)` by
       (qpat_assum `emitted_insts sa sc = pre ++ i::post`
          (fn th => pure_rewrite_tac[th]) >> simp[MEM_APPEND]) >>
     pop_assum mp_tac >>
     qpat_assum `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc`
       (fn th => pure_rewrite_tac[th]) >>
     simp[mk_inst_def] >> strip_tac >> simp[]) >>
  `((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sc.cs_current_insts) = t` by
    simp[venom_state_component_equality] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >>
     qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >> asm_rewrite_tac[]) >>
  `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t)` by
    (qsuff_tac `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0
       (OK ((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sc.cs_current_insts))`
     >- asm_rewrite_tac[] >>
     rpt strip_tac >> irule abi_decode_finite_success_observed >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`emitted_insts sa sc`, `sa`] >>
     gvs[inst_extends_def, mk_inst_def, is_terminator_def,
         LENGTH_NIL, FILTER_EQ_NIL, EVERY_CONJ]) >>
  suspend "load_owned"
QED

Resume abi_decode_bytes_owned_load_frame_joint_observed[load_memory]:
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

Resume abi_decode_bytes_owned_load_frame_joint_observed[load_owned]:
  `isPREFIX sa.cs_current_insts sc.cs_current_insts` by
    metis_tac[inst_extends_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sc)` by
    simp[mk_inst_def] >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >> metis_tac[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    simp[] >>
  `(^owned_decoder_state) sc t G' tn'` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> asm_rewrite_tac[]) >>
  `allocas_from lo t` by
    (fs[allocas_from_def, stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  qexistsl_tac [`out`, `ap`, `t`, `G'`, `tn'`] >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >>
  metis_tac[operand_11, ADD_COMM]
QED

Finalise abi_decode_bytes_owned_load_frame_joint_observed
