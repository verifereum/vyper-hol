Theory bodyFullAbiDecodeArrayPrepareSuffix
Ancestors ptrDiscipline[qualified,ignore_grammar] dynCopyExec[qualified,ignore_grammar]
  bodyFullAbiDecodeOwnedStateProps[qualified,ignore_grammar]
  bodyFullAbiDecodeGuardReadJoint bodyFullAbiDecodeBytesArithmetic
  abiDecoderDynarrayBound abiDecoderRange abiDecoderReentry
  exprSimWordBuiltins abiEncoder emitHelper emitHelperProps
  venomInst venomExecSemantics venomState words list rich_list arithmetic
  ASCIInumbers loweringStateRelDefs compileEnv exprLoweringProps
  abiDecodePtrBytesMember bodyPtrBopScalarCompile bodyPtrBopScalarSeq pred_set exprSimBopRestWordTail[qualified,ignore_grammar] builtinBytesMemory[qualified,ignore_grammar] exprOperandVar[qualified,ignore_grammar] bodyPtrIfExpBytesCounted[qualified,ignore_grammar] exprSimPrecompiles[qualified,ignore_grammar] calldataDecodePtr[qualified,ignore_grammar] bodyPtrBopArithmeticCompile[qualified,ignore_grammar] bodyFullAbiDecodeScalarObserved bodyFullAbiDecodeArrayPrepareCountStride bodyFullAbiDecodeLoopHeaderExact bodyFullAbiDecodeOwnedWordStoreObserved bodyFullAbiDecodeInputOrigin fragGasOriginPtrLoop fragGasPath valueEncodingProps venomMemProps
  bodyFullAbiDecodeGuardReadObserved[qualified]

(* Guard inputs are older than the emitted temporaries; the temporaries
   themselves may still contain values from an earlier iteration. *)
Theorem payload_old_operand_update[local]:
  abi_decoder_operand_live sa.cs_next_var op /\ sa.cs_next_var <= n ==>
  eval_operand op (update_var (STRING #"%" (toString n)) w s) =
  eval_operand op s
Proof
  strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
  qexists_tac `sa` >> simp[] >>
  rpt strip_tac >> gvs[abi_decoder_operand_live_def,
    abi_decoder_older_vars_def, not_fresh_at_def]
QED

Theorem array_payload_guard_shape[local]:
  abi_decode_dynarray_payload_guard head cnt abi_sz hi sa = ((),sb) /\
  hi <> Lit 0w ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> ASSERT_UNREACHABLE) (emitted_insts sa sb)
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_dynarray_payload_guard_def,compile_abi_decode_range_check_def,
    comp_bind_def,comp_ignore_bind_def,emit_op_def,emit_void_def,
    fresh_var_def,fresh_id_def,emit_def,comp_return_def] >>
  strip_tac >> gvs[inst_extends_def,IS_PREFIX_APPEND,emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND,mk_inst_def]
QED

Theorem array_payload_guard_run[local]:
  abi_decode_dynarray_payload_guard head cnt abi_sz hi sa = ((),sb) /\
  hi <> Lit 0w /\
  abi_decoder_operand_live sa.cs_next_var head /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  eval_operand head s = SOME p /\ eval_operand hi s = SOME h /\
  eval_operand cnt s = SOME (n2w c) /\ c * abi_sz < dimword (:256) ==>
  (?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       w2n p + c * abi_sz <= w2n h)
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_dynarray_payload_guard_def,compile_abi_decode_range_check_def,
    comp_bind_def,comp_ignore_bind_def,emit_op_def,emit_void_def,
    fresh_var_def,fresh_id_def,emit_def,comp_return_def] >>
  strip_tac >> gvs[] >>
  `!n w u. sa.cs_next_var <= n ==>
     eval_operand head (update_var (STRING #"%" (toString n)) w u) =
       eval_operand head u` by metis_tac[payload_old_operand_update] >>
  `!n w u. sa.cs_next_var <= n ==>
     eval_operand hi (update_var (STRING #"%" (toString n)) w u) =
       eval_operand hi u` by metis_tac[payload_old_operand_update] >>
  `!x y w u. eval_operand (Var x) (update_var y w u) =
     if x = y then SOME w else eval_operand (Var x) u` by
    simp[eval_operand_def,lookup_var_def,update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE,EQ_SYM_EQ] >>
  qabbrev_tac `q = p + n2w (abi_sz * c)` >>
  simp_tac (srw_ss()) [emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq code s` >>
  `w2n p <= w2n q /\ w2n q <= w2n h ==> w2n p + abi_sz * c <= w2n h` by
    (strip_tac >>
     `q = n2w (w2n p + abi_sz * c)` by simp[Abbr `q`,GSYM word_add_n2w] >>
     irule abi_decode_checked_add_bound >> gvs[w2n_lt]) >>
  qsuff_tac `?t. run_inst_seq code s =
    if w2n p <= w2n q /\ w2n q <= w2n h then OK t else Abort Revert_abort t` >-
    (strip_tac >> Cases_on `w2n p <= w2n q /\ w2n q <= w2n h` >> gvs[]) >>
  simp[Abbr `code`] >>
  simp[Once run_inst_seq_def,mk_inst_def,step_inst_base_opcode_eqs,
       exec_pure2_def,eval_operand_def,word_mul_n2w] >>
  `eval_operand head
     (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w (abi_sz * c)) s) =
     SOME p` by simp[] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs,exec_pure2_def,eval_operand_update_var] >>
  simp[Once run_inst_seq_def,step_inst_base_opcode_eqs,exec_pure2_def,
       eval_operand_update_var,payload_old_operand_update,bool_to_word_def] >>
  simp[Once run_inst_seq_def,step_inst_base_opcode_eqs,exec_pure1_def,
       eval_operand_update_var] >>
  simp[Once run_inst_seq_def,step_inst_base_opcode_eqs,exec_pure2_def,
       eval_operand_update_var,payload_old_operand_update,toString_inj,
       bool_to_word_def] >>
  simp[Once run_inst_seq_def,step_inst_base_opcode_eqs,exec_pure1_def,
       eval_operand_update_var] >>
  simp[Once run_inst_seq_def,step_inst_base_opcode_eqs,exec_pure2_def,
       eval_operand_update_var,toString_inj] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq [_] v` >>
  `eval_operand (Var (STRING #"%" (toString (sa.cs_next_var+6)))) v =
   SOME (bool_to_word (w2n p <= w2n q /\ w2n q <= w2n h))` by
    simp[Abbr `v`,eval_operand_update_var,GREATER_DEF,NOT_LESS] >>
  simp[Once run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs] >>
  Cases_on `w2n p <= w2n q /\ w2n q <= w2n h` >>
  simp[bool_to_word_def,run_inst_seq_def]
QED

Theorem array_payload_guard_scalar[local]:
  abi_decode_dynarray_payload_guard head cnt abi_sz hi sa = ((),sb) /\
  hi <> Lit 0w /\ head IN A /\ cnt IN A /\ hi IN A /\
  Lit (n2w abi_sz) IN A /\ (!x. x IN R ==> not_fresh_at sa x) ==>
  ?B. bop_scalar_seq R A (emitted_insts sa sb) B
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_dynarray_payload_guard_def,comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op MUL _ sa = (payload,sm)` >>
  Cases_on `emit_op ADD [head;payload] sm` >> gvs[] >>
  rename1 `emit_op ADD [head;payload] sm = (e,sa')` >>
  `bop_scalar_seq R A (emitted_insts sa sm) (payload INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`MUL`,`[cnt;Lit (n2w abi_sz)]`] >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `emit_op MUL _ sa = _` mp_tac >>
     simp[emit_op_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,
          fresh_var_def,fresh_id_def,emit_def] >> strip_tac >> gvs[]) >>
  `!x. x IN R ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `?B. bop_scalar_seq R (payload INSERT A) (emitted_insts sm sb) B /\
       (payload INSERT A) SUBSET B /\ e IN B` by
    (irule abi_decode_add_range_scalar >>
     simp[] >> qexistsl_tac [`hi`,`payload`,`sa'`,`head`] >> simp[]) >>
  `inst_extends sa sm /\ inst_extends sm sb` by
    metis_tac[inst_extends_emit_op,compile_abi_decode_range_check_shape,inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  qexists_tac `B` >> simp[] >> irule bop_scalar_seq_append >>
  qexists_tac `payload INSERT A` >> simp[]
QED

Theorem array_payload_guard_age[local]:
  abi_decode_dynarray_payload_guard head cnt abi_sz hi sa = ((),sb) /\
  hi <> Lit 0w ==>
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  simp[abi_decode_dynarray_payload_guard_def,compile_abi_decode_range_check_def,
    comp_bind_def,comp_ignore_bind_def,emit_op_def,emit_void_def,
    fresh_var_def,fresh_id_def,emit_def,comp_return_def] >>
  strip_tac >> gvs[emit_def,fresh_id_def,fresh_var_def,comp_return_def,comp_bind_def]
QED

Theorem array_payload_guard_lifts[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ((?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
   (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ P t)) ==>
  (?u Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
         (Abort Revert_abort u,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort u))) \/
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ P t /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))))
Proof
  strip_tac
  >- (disj1_tac >> drule_all member_scalar_revert_observed >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  disj2_tac >> qexists_tac `t` >> asm_rewrite_tac[] >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >>
  strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  drule bop_scalar_seq_opcodes >> simp[EVERY_CONJ] >> strip_tac >>
  qpat_x_assum `t = s with vs_vars := _` kall_tac >>
  conj_tac >- metis_tac[bodyFullAbiDecodeScalarNoAllocaTheory.abi_decode_scalar_seq_no_alloca] >>
  rpt strip_tac >>
  irule bodyFullAbiDecodeFiniteObservedTheory.abi_decode_finite_success_observed >>
  simp[] >> qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
  fs[inst_extends_def,LENGTH_NIL,FILTER_EQ_NIL,EVERY_CONJ]
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
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val input_origin = ``\s.
  ((?aid ib isz. aid < output_id /\
     FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= w2n (input_word:256 word) /\
     w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``;

Theorem array_payload_guard_owned[local]:
  abi_decode_dynarray_payload_guard head first stride hi sa = ((),sb) /\
  hi <> Lit 0w /\ fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ allocas_from lo s /\
  (^owned_decoder_state) sa s G tn /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  abi_decoder_operand_live sa.cs_next_var head /\
  abi_decoder_operand_live sa.cs_next_var hi /\
  eval_operand head s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w h) /\
  eval_operand first s = SOME (n2w c) /\ c * stride < dimword (:256) /\
  p < dimword (:256) /\ h < dimword (:256) /\
  op_prov G head = NONE /\ op_taint tn head = {} /\
  op_prov G first = NONE /\ op_taint tn first = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} ==>
  (?v Gv tnv.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort v,Gv,tnv)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort v))) \/
  (?v Gv tnv.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,Gv,tnv)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK v)) /\
    p + c * stride <= h /\
    ~v.vs_halted /\ v.vs_current_bb = sb.cs_current_bb /\
    v.vs_inst_idx = LENGTH sb.cs_current_insts /\ allocas_from lo v /\
    (^owned_decoder_state) sb v Gv tnv /\
    v.vs_memory = s.vs_memory /\ v.vs_allocas = s.vs_allocas /\
    v.vs_alloca_next = s.vs_alloca_next /\ tnv.t_mem = tn.t_mem /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tnv (Var x) = op_taint tn (Var x)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all array_payload_guard_shape >> strip_tac >>
  drule_all array_payload_guard_age >> strip_tac >>
  qabbrev_tac `A = {head;first;hi;Lit (n2w stride)}` >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B` by
    (irule array_payload_guard_scalar >> simp[Abbr `A`] >>
     qexistsl_tac [`stride`,`first`,`head`,`hi`] >> simp[]) >>
  `!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[Abbr `A`] >> rpt strip_tac >>
     gvs[NoAsms,ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def]) >>
  SUBGOAL_THEN
    ``(?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
      (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ p + c * stride <= h)``
    ASSUME_TAC >-
      (drule_all array_payload_guard_run >> simp[w2n_n2w,LESS_MOD]) >>
  `(?v Gv tnv.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort v,Gv,tnv)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (Abort Revert_abort v))) \/
   (?raw. run_inst_seq (emitted_insts sa sb) s = OK raw /\ p + c * stride <= h /\
    EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
    raw.vs_allocas = s.vs_allocas /\ raw.vs_alloca_next = s.vs_alloca_next /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0
      (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts))))` by
    (drule_all (array_payload_guard_lifts |> Q.INST [`P` |-> `\t. p + c * stride <= h`] |> BETA_RULE) >>
     disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC))
  >- (disj1_tac >> qexistsl_tac [`v`,`Gv`,`tnv`] >> asm_rewrite_tac[]) >>
  disj2_tac >>
  mp_tac (BETA_RULE (Q.INST [`t` |-> `raw`]
    bodyFullAbiDecodeGuardReadObservedTheory.abi_decode_bytes_scalar_frame_joint)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v`
    (qx_choose_then `Gv` (qx_choose_then `tnv` strip_assume_tac))) >>
  qexistsl_tac [`v`,`Gv`,`tnv`] >> asm_rewrite_tac[] >> simp[]
QED

(* All three phases use the same physical state and ghost pair at each cut. *)
Theorem abi_decode_array_prepare_suffix_width_joint:
  abi_decode_dynarray_payload_guard head first stride hi count_st = ((),guard_st) /\
  emit_op MLOAD [Var addr] guard_st = (Var cnt,reload_st) /\
  emit_void MSTORE [Var dst;Var cnt] reload_st = ((),header_st) /\
  fn_has_code count_st header_st fn /\ fn_inst_ids_distinct fn /\
  (!obs. fn_has_code count_st header_st obs ==>
    fn_has_code count_st guard_st obs /\ fn_has_code guard_st reload_st obs /\
    fn_has_code reload_st header_st obs) /\
  ~u.vs_halted /\ u.vs_current_bb = count_st.cs_current_bb /\
  u.vs_inst_idx = LENGTH count_st.cs_current_insts /\ allocas_from lo u /\
  (^owned_decoder_state) count_st u Gu tnu /\ (?H. V H) /\ (^input_origin) u /\
  EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
  not_fresh_at count_st input /\ local_ptrs_reserved ce count_st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x) /\
  c * stride < dimword (:256) /\
  w2n dw + type_memory_size (ArrayTV tv (Dynamic maxn)) <= output_base+output_cap /\
  abi_decoder_operand_live count_st.cs_next_var head /\
  abi_decoder_operand_live count_st.cs_next_var hi /\ hi <> Lit 0w /\
  eval_operand head u = SOME (n2w p) /\ eval_operand hi u = SOME (n2w h) /\
  p < dimword (:256) /\ h < dimword (:256) /\ h <= LENGTH input_bytes /\
  eval_operand first u = SOME (n2w c) /\ c <= maxn /\
  op_prov Gu head = NONE /\ op_taint tnu head = {} /\
  op_prov Gu first = NONE /\ op_taint tnu first = {} /\
  op_prov Gu hi = NONE /\ op_taint tnu hi = {} /\
  not_fresh_at count_st addr /\ abi_decode_ptr_window Gu tnu u addr a 32 /\
  w2n a+32 <= u.vs_alloca_next /\ mem_word_at (w2n a) u.vs_memory = n2w c /\
  not_fresh_at count_st dst /\ lookup_var dst u = SOME dw /\ ptr_covers Gu tnu dst u 32 /\
  output_base <= w2n dw /\ w2n dw+32 <= output_base+output_cap /\
  w2n dw+32 <= u.vs_alloca_next /\
  (w2n input_word+LENGTH input_bytes <= w2n dw \/ w2n dw+32 <= w2n input_word) /\
  EVERY (\(aid,q,b,k,bytes). b+k <= w2n dw \/ w2n dw+32 <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= w2n dw \/ w2n dw+32 <= b) protected ==>
  ?r Gp tnp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,Gu,tnu) [] (r,Gp,tnp)) /\
    (!obs. fn_has_code count_st header_st obs ==> gas_path ctx obs u 0 r) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ p+c*stride <= h /\ p+c*stride <= LENGTH input_bytes /\
       ~t.vs_halted /\ t.vs_current_bb = header_st.cs_current_bb /\
       t.vs_inst_idx = LENGTH header_st.cs_current_insts /\ allocas_from lo t /\
       (^owned_decoder_state) header_st t Gp tnp /\ (^input_origin) t /\
       EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
       eval_operand (Var cnt) t = SOME (n2w c) /\ op_prov Gp (Var cnt) = NONE /\
       op_taint tnp (Var cnt) = {} /\ not_fresh_at header_st cnt /\
       mem_word_at (w2n dw) t.vs_memory = n2w c /\
       (!i. w2n dw <= i /\ i < w2n dw+32 ==> i NOTIN tnp.t_mem) /\
       (!x. not_fresh_at count_st x ==> lookup_var x t = lookup_var x u /\
         FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tnp (Var x) = op_taint tnu (Var x)) /\
       (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnp.t_mem ==>
         i IN tnu.t_mem)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_has_code count_st guard_st fn /\ fn_has_code guard_st reload_st fn /\
   fn_has_code reload_st header_st fn` by
    simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (BETA_RULE (Q.INST [`sa` |-> `count_st`, `sb` |-> `guard_st`,
    `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`] array_payload_guard_owned)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `v` (qx_choose_then `Gv` (qx_choose_then `tnv` strip_assume_tac))))
  >- (qexistsl_tac [`Abort Revert_abort v`,`Gv`,`tnv`] >>
      asm_rewrite_tac[] >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
      disj1_tac >> qexists_tac `v` >> REFL_TAC) >>
  suspend "reload"
QED

Resume abi_decode_array_prepare_suffix_width_joint[reload]:
  drule_all array_payload_guard_age >> strip_tac >>
  `(!x. not_fresh_at count_st x ==> not_fresh_at guard_st x) /\
   local_ptrs_reserved ce guard_st` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `not_fresh_at guard_st input /\ not_fresh_at guard_st dst /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at guard_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at guard_st x)` by simp[] >>
  `abi_decode_ptr_window Gv tnv v addr a 32` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >> simp[]) >>
  `lookup_var addr v = SOME a /\ ptr_covers Gv tnv addr v 32 /\
   (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tnv.t_mem) /\
   w2n a+32 <= v.vs_alloca_next` by
    fs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es v /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (BETA_RULE (Q.INST [`sa` |-> `guard_st`, `sb` |-> `reload_st`,
    `s` |-> `v`, `G` |-> `Gv`, `tn` |-> `tnv`, `counter` |-> `addr`,
    `out` |-> `cnt`] bodyFullAbiDecodeLoopHeaderExactTheory.abi_decode_loop_counter_load_exact)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `w`
    (qx_choose_then `Gw` (qx_choose_then `tnw` strip_assume_tac))) >>
  suspend "store"
QED

Resume abi_decode_array_prepare_suffix_width_joint[store]:
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >>
  qpat_x_assum `Var cnt = Var out` (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  `not_fresh_at reload_st cnt /\ guard_st.cs_next_var <= reload_st.cs_next_var` by simp[] >>
  `(!x. not_fresh_at guard_st x ==> not_fresh_at reload_st x) /\
   local_ptrs_reserved ce reload_st` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at reload_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at reload_st x)` by simp[] >>
  `!x. not_fresh_at count_st x ==> lookup_var x w = lookup_var x u /\
       FLOOKUP Gw x = FLOOKUP Gu x /\ op_taint tnw (Var x) = op_taint tnu (Var x)` by simp[] >>
  `lookup_var dst w = SOME dw /\ ptr_covers Gw tnw dst w 32 /\
   w2n dw+32 <= w.vs_alloca_next` by
    (conj_tac >- simp[] >> reverse conj_tac >- simp[] >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >> simp[]) >>
  `eval_operand (Var cnt) w = SOME (n2w c)` by
    fs[mload_def,mem_word_at_eq_mload] >>
  Q_TAC (fn tm => SUBGOAL_THEN (rhs (concl (BETA_CONV tm))) ASSUME_TAC)
    `(^input_origin) w` >-
    (irule abi_decode_input_origin_transport >> qexistsl_tac [`u`,`count_st`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp w` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es w /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (abi_decode_owned_word_store_observed_exact |>
    Q.INST [`w` |-> `n2w c`] |>
    Q.INST [`sa` |-> `reload_st`, `sb` |-> `header_st`,
      `s` |-> `w`, `G` |-> `Gw`, `tn` |-> `tnw`, `value` |-> `Var cnt`] |>
    BETA_RULE) >>
  impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gp`
    (qx_choose_then `tnp` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "compose"
QED

Resume abi_decode_array_prepare_suffix_width_joint[compose]:
  qexistsl_tac [`OK t`,`Gp`,`tnp`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gv`,`v`,`tnv`] >>
      conj_tac >- simp[IgnAsm `t = _`] >>
      irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gw`,`w`,`tnw`] >>
      simp[IgnAsm `t = _`]) >>
  conj_tac
  >- (qx_gen_tac `obs` >> disch_tac >>
      `fn_has_code count_st guard_st obs /\ fn_has_code guard_st reload_st obs /\
       fn_has_code reload_st header_st obs` by simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `v` >> conj_tac >- simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `w` >> simp[IgnAsm `t = _`]) >>
  disj2_tac >> qexists_tac `t` >>
  suspend "certificate"
QED

Resume abi_decode_array_prepare_suffix_width_joint[certificate]:
  `p+c*stride <= LENGTH input_bytes` by simp[] >>
  `allocas_from lo t` by
    ((qpat_assum `t = _` SUBST1_TAC >>
     qpat_assum `allocas_from lo u` mp_tac >>
     simp[ptrDisciplineTheory.allocas_from_def,dynCopyExecTheory.mstore_control_fields] >> (gvs[ptrDisciplineTheory.allocas_from_def, dynCopyExecTheory.mstore_control_fields]))) >>
  `not_fresh_at header_st cnt` by
    (drule emitted_insts_emit_void >> strip_tac >>
     qpat_assum `not_fresh_at reload_st cnt` mp_tac >>
     qpat_assum `header_st.cs_next_var = reload_st.cs_next_var`
       (fn th => rewrite_tac[not_fresh_at_def, th])) >>
  `eval_operand (Var cnt) t = SOME (n2w c) /\ op_prov Gp (Var cnt) = NONE /\
   op_taint tnp (Var cnt) = {}` by
    (qpat_assum `!x. not_fresh_at reload_st x ==> _` (qspec_then `cnt` mp_tac) >>
     fs[IgnAsm `t = _`,eval_operand_def]) >>
  `mem_word_at (w2n dw) t.vs_memory = n2w c` by
    (qpat_assum `t = _` SUBST1_TAC >>
     simp[NoAsms, mem_word_at_eq_mload, abiEncoderPathPropsTheory.mload_inst_idx,
       mload_mstore_same]) >>
  `!x. not_fresh_at count_st x ==> lookup_var x t = lookup_var x u /\
       FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tnp (Var x) = op_taint tnu (Var x)` by
    (rpt strip_tac >> simp[IgnAsm `t = _`]) >>
  `tnp.t_mem SUBSET tnu.t_mem` by
    (qpat_assum `tnp.t_mem SUBSET tnw.t_mem` mp_tac >>
     qpat_assum `tnw.t_mem = tnv.t_mem` (rewrite_tac o single) >>
     qpat_assum `tnv.t_mem = tnu.t_mem` (rewrite_tac o single)) >>
  qpat_x_assum `t = _` kall_tac >>
  qpat_x_assum `tnp.t_mem = _` kall_tac >>
  qpat_x_assum `Gp = _` kall_tac >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `tnp.t_mem SUBSET tnu.t_mem`
    (irule o REWRITE_RULE[SUBSET_DEF]) >>
  first_assum ACCEPT_TAC
QED

Finalise abi_decode_array_prepare_suffix_width_joint

(* Canonical array metadata supplies the width bound at the count cut. *)
Theorem abi_decode_array_prepare_suffix_joint:
  abi_decode_dynarray_payload_guard head first stride hi count_st = ((),guard_st) /\
  emit_op MLOAD [Var addr] guard_st = (Var cnt,reload_st) /\
  emit_void MSTORE [Var dst;Var cnt] reload_st = ((),header_st) /\
  fn_has_code count_st header_st fn /\ fn_inst_ids_distinct fn /\
  (!obs. fn_has_code count_st header_st obs ==>
    fn_has_code count_st guard_st obs /\ fn_has_code guard_st reload_st obs /\
    fn_has_code reload_st header_st obs) /\
  ~ctx_has_dalloca ctx /\ ~u.vs_halted /\ u.vs_current_bb = count_st.cs_current_bb /\
  u.vs_inst_idx = LENGTH count_st.cs_current_insts /\ allocas_from lo u /\
  (^owned_decoder_state) count_st u Gu tnu /\ (?H. V H) /\ (^input_origin) u /\
  EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
  not_fresh_at count_st input /\ local_ptrs_reserved ce count_st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x) /\
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray child stride mem_sz dyn maxn /\
  abi_decoder_coherent ce env ce.ce_struct_fields
    (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  w2n dw + type_memory_size (ArrayTV tv (Dynamic maxn)) <= output_base+output_cap /\
  abi_decoder_operand_live count_st.cs_next_var head /\
  abi_decoder_operand_live count_st.cs_next_var hi /\ hi <> Lit 0w /\
  eval_operand head u = SOME (n2w p) /\ eval_operand hi u = SOME (n2w h) /\
  p < dimword (:256) /\ h < dimword (:256) /\ h <= LENGTH input_bytes /\
  eval_operand first u = SOME (n2w c) /\ c <= maxn /\
  op_prov Gu head = NONE /\ op_taint tnu head = {} /\
  op_prov Gu first = NONE /\ op_taint tnu first = {} /\
  op_prov Gu hi = NONE /\ op_taint tnu hi = {} /\
  not_fresh_at count_st addr /\ abi_decode_ptr_window Gu tnu u addr a 32 /\
  w2n a+32 <= u.vs_alloca_next /\ mem_word_at (w2n a) u.vs_memory = n2w c /\
  not_fresh_at count_st dst /\ lookup_var dst u = SOME dw /\ ptr_covers Gu tnu dst u 32 /\
  output_base <= w2n dw /\ w2n dw+32 <= output_base+output_cap /\
  w2n dw+32 <= u.vs_alloca_next /\
  (w2n input_word+LENGTH input_bytes <= w2n dw \/ w2n dw+32 <= w2n input_word) /\
  EVERY (\(aid,q,b,k,bytes). b+k <= w2n dw \/ w2n dw+32 <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= w2n dw \/ w2n dw+32 <= b) protected ==>
  ?r Gp tnp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,Gu,tnu) [] (r,Gp,tnp)) /\
    (!obs. fn_has_code count_st header_st obs ==> gas_path ctx obs u 0 r) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ p+c*stride <= h /\ p+c*stride <= LENGTH input_bytes /\
       ~t.vs_halted /\ t.vs_current_bb = header_st.cs_current_bb /\
       t.vs_inst_idx = LENGTH header_st.cs_current_insts /\ allocas_from lo t /\
       (^owned_decoder_state) header_st t Gp tnp /\ (^input_origin) t /\
       EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
       eval_operand (Var cnt) t = SOME (n2w c) /\ op_prov Gp (Var cnt) = NONE /\
       op_taint tnp (Var cnt) = {} /\ not_fresh_at header_st cnt /\
       mem_word_at (w2n dw) t.vs_memory = n2w c /\
       (!i. w2n dw <= i /\ i < w2n dw+32 ==> i NOTIN tnp.t_mem) /\
       (!x. not_fresh_at count_st x ==> lookup_var x t = lookup_var x u /\
         FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tnp (Var x) = op_taint tnu (Var x)) /\
       (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnp.t_mem ==>
         i IN tnu.t_mem)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `c * stride < dimword (:256)` by
    (drule_all abi_decode_array_prepare_count_stride >> simp[]) >>
  match_mp_tac (BETA_RULE abi_decode_array_prepare_suffix_width_joint) >>
  asm_rewrite_tac[]
QED
