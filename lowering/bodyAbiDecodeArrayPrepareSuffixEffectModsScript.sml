Theory bodyAbiDecodeArrayPrepareSuffixEffectMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeArrayPrepareSuffix[qualified]
  bodyFullAbiDecodeOwnedWordStoreObserved[qualified]
  bodyFullAbiDecodeLoopHeaderExact[qualified]
  ptrDiscipline[qualified,ignore_grammar] dynCopyExec[qualified,ignore_grammar]
  bodyFullAbiDecodeOwnedStateProps[qualified,ignore_grammar]
  bodyFullAbiDecodeGuardReadJoint bodyFullAbiDecodeBytesArithmetic
  abiDecoderDynarrayBound abiDecoderRange abiDecoderReentry
  exprSimWordBuiltins abiEncoder emitHelper emitHelperProps
  venomInst venomExecSemantics venomState words list rich_list arithmetic
  ASCIInumbers loweringStateRelDefs compileEnv exprLoweringProps
  abiDecodePtrBytesMember bodyPtrBopScalarCompile bodyPtrBopScalarSeq pred_set
  bodyFullAbiDecodeScalarObserved bodyFullAbiDecodeInputOrigin
  fragGasOriginPtrLoop fragGasPath valueEncodingProps venomMemProps
  assignBasePtrBytesPrefix instSeqPtrLo stateFrame finite_map allocaFootprint
  bodyFullAbiDecodeRelativeLoadExact[qualified]
Libs bodyAbiDecodeGuardedEffectSyntaxLib

local
  val old = concl
    bodyFullAbiDecodeOwnedWordStoreObservedTheory.abi_decode_owned_word_store_observed_exact
  val (pre,post) = dest_imp (#2 (strip_forall old))
  val (ws as [t,_,tnf],body) = strip_exists post
  val s = param (free_vars pre) "s"
  val tn = param (free_vars pre) "tn"
  val fields = ``^t.vs_alloca_next = ^s.vs_alloca_next /\
    ^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
    ^tnf.t_imm = ^tn.t_imm``
  val tm = rhs (concl (DEPTH_CONV BETA_CONV
    (mk_imp (pre,list_mk_exists (ws,mk_conj (body,fields))))))
in
  val store_all = list_mk_forall (free_vars tm,tm)
end

local
  val old = beta (concl
    bodyFullAbiDecodeArrayPrepareSuffixTheory.abi_decode_array_prepare_suffix_width_joint)
  val (pre,post) = dest_imp old
  val (ws as [_,_,tnp],body) = strip_exists post
  val (p,rest) = dest_conj body
  val (q,result) = dest_conj rest
  val (abort,ok) = dest_disj result
  val ([t],ok_body) = strip_exists ok
  val u = param (free_vars pre) "u"
  val tnu = param (free_vars pre) "tnu"
  val tm = checked "array suffix" old
    (mk_imp (pre,list_mk_exists (ws,mk_conj (p,mk_conj (q,
      mk_disj (abort,mk_exists (t,mk_conj (ok_body,effect u tnu t tnp))))))))
in
  val suffix_all = list_mk_forall (free_vars tm,tm)
end

(* Inputs are older than the emitted temporaries, which can still contain
   values from a previous iteration. *)
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
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  Cases_on `hi = Lit 0w` >- simp[] >>
  simp[abi_decode_dynarray_payload_guard_def,compile_abi_decode_range_check_def,
    comp_bind_def,comp_ignore_bind_def,emit_op_def,emit_void_def,
    fresh_var_def,fresh_id_def,emit_def,comp_return_def] >>
  strip_tac >> gvs[inst_extends_def,IS_PREFIX_APPEND,emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
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
    simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE,EQ_SYM_EQ] >>
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
  suspend "run_guard_code"
QED

Resume array_payload_guard_run[run_guard_code]:
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

Finalise array_payload_guard_run

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

(* The resource packet is shared by the old guard and counter-load contracts.
   Keep the quotation local; only the suffixed selector is exported. *)
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

(* Reuse the finite scalar certificate before projecting the ghost fields. *)
Theorem scalar_guard_owned_effect[local]:
  bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ fn_has_code sa sb fn /\ inst_extends sa sb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  allocas_from lo s /\ (^owned_decoder_state) sa s G tn /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  not_fresh_at sa input /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?u Gf tnf.
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb u Gf tnf /\ allocas_from lo u /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (bop_scalar_seq_run |>
    Q.INST [`D` |-> `<|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|>`]) >>
  disch_then (qspecl_then [`fn`,`PG`] strip_assume_tac) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      (emitted_insts sa sb) s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
       d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ 0 _ _ _ _ _ _ _ _ _` kall_tac >>
  drule bop_scalar_seq_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sb)` by
    metis_tac[bodyFullAbiDecodeScalarNoAllocaTheory.abi_decode_scalar_seq_no_alloca] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[bodyFullAbiDecodeClampMemoryTheory.abi_decode_scalar_seq_mem_ok] >>
  `ptrDiscipline$ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[]) >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` assume_tac) >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
   ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_memory = s.vs_memory` by
    (simp[Abbr `u`] >>
     qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[state_frame_def]) >>
  suspend "scalar_resources"
QED

Resume scalar_guard_owned_effect[scalar_resources]:
  `!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `u`,lookup_var_def,ptrDisciplineTheory.op_taint_def] >> gvs[]) >>
  `alloca_history fn s` by fs[] >>
  `alloca_history fn u` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sb`] >> simp[] >> gvs[inst_extends_def]) >>
  `(^owned_decoder_state) sb u G' tn'` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- (BETA_TAC >> asm_rewrite_tac[]) >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >> BETA_TAC >> asm_rewrite_tac[]) >>
  `allocas_from lo u` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `Abbrev (u = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      irule bodyFullAbiDecodeFiniteObservedTheory.abi_decode_finite_success_observed >>
      simp[] >> qexistsl_tac [`emitted_insts sa sb`,`sa`] >>
      fs[inst_extends_def,LENGTH_NIL,FILTER_EQ_NIL,EVERY_CONJ]) >>
  conj_tac
  >- (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
      first_assum ACCEPT_TAC) >>
  BETA_TAC >>
  qpat_assum `(^owned_decoder_state) sb u G' tn'` (assume_tac o BETA_RULE) >>
  asm_rewrite_tac[]
QED

Finalise scalar_guard_owned_effect

Theorem array_payload_guard_owned_effect[local]:
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
    tnv.t_stor = tn.t_stor /\ tnv.t_trans = tn.t_trans /\ tnv.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tnv (Var x) = op_taint tn (Var x)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all array_payload_guard_shape >> strip_tac >>
  qabbrev_tac `A = {head;first;hi;Lit (n2w stride)}` >>
  `?B. bop_scalar_seq {x | not_fresh_at sa x} A (emitted_insts sa sb) B` by
    (irule array_payload_guard_scalar >> simp[Abbr `A`] >>
     qexistsl_tac [`stride`,`first`,`head`,`hi`] >> simp[]) >>
  `!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[Abbr `A`] >> rpt strip_tac >>
     gvs[NoAsms,ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def]) >>
  `lo <= s.vs_alloca_next` by fs[] >>
  SUBGOAL_THEN
    ``(?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t) \/
      (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\ p + c * stride <= h)``
    STRIP_ASSUME_TAC >-
    (drule_all array_payload_guard_run >> simp[w2n_n2w,LESS_MOD])
  >- (disj1_tac >> drule_all member_scalar_revert_observed >>
      disch_then (qspecl_then [`explicit`,`PG`] ACCEPT_TAC)) >>
  disj2_tac >> drule_all (BETA_RULE scalar_guard_owned_effect) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `u` (qx_choose_then `Gf`
      (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS))))) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >> asm_rewrite_tac[]
QED

local
  val old = beta (concl bodyFullAbiDecodeLoopHeaderExactTheory.abi_decode_loop_counter_load_exact)
  val (pre,post) = dest_imp old
  val (ws as [_,_,tnf],body) = strip_exists post
  val tn = param (free_vars pre) "tn"
in
  val counter_load_effect = mk_imp (pre,list_mk_exists (ws,mk_conj (body,
    ``^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\ ^tnf.t_imm = ^tn.t_imm``)))
end

(* Normalizing the instruction cursor does not change the ghosts selected by
   assign_base_bytes_mload_seq. *)
Theorem counter_load_owned_effect[local]:
  ^counter_load_effect
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
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
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sb`] >> simp[mk_inst_def] >>
     gvs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `(^owned_decoder_state) sb t G' tn'` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- (BETA_TAC >> asm_rewrite_tac[]) >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> BETA_TAC >> asm_rewrite_tac[]) >>
  suspend "load_observer"
QED

Resume counter_load_owned_effect[load_observer]:
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
     rpt strip_tac >> drule_all bodyFullAbiDecodeFiniteObservedTheory.abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[Abbr `t`]) >>
  `run_inst_seq_mem_ok [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] s` by
    (drule emit_mload_mem_ok >>
     disch_then (qspec_then `s` mp_tac) >> simp[eval_operand_def]) >>
  `inst_seq_ptr <|d_stor := K (K {}); d_trans := K (K {});
      d_imm := K {}; d_ret := K {}|> lo ctx fn PG G tn
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] s G' tn'` by
    (irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>` >>
     qpat_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `s.vs_inst_idx` mp_tac) >>
     simp_tac bool_ss [venom_state_fupdselfid] >> simp[NoAsms]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
    simp[mk_inst_def,is_terminator_def] >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
      [mk_inst sa.cs_next_id MLOAD [Var counter] [out]] = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i [mk_inst sa.cs_next_id MLOAD [Var counter] [out]]` by
       (qpat_assum `[_] = pre ++ i::post` SUBST1_TAC >> simp[MEM_APPEND]) >>
     fs[mk_inst_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> irule fragGasOriginPtrDeadTheory.gas_origin_ptr_path_from_no_dead >>
     qpat_assum `Abbrev (t = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `sa` >> simp[] >>
     qpat_assum `ctx_has_dalloca ctx ==> !pre i post u. _` (mp_tac o SIMP_RULE (srw_ss()) []) >>
     simp[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >>
  qpat_assum `(^owned_decoder_state) sb t G' tn'` (assume_tac o BETA_RULE) >>
  asm_rewrite_tac[] >> simp[Abbr `t`,eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE]
QED

Finalise counter_load_owned_effect

Theorem abi_decode_array_prepare_suffix_width_joint_effect_mods:
  ^store_all ==> ^suffix_all
Proof
  disch_then (mk_asm "store_all") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fn_has_code count_st guard_st fn /\ fn_has_code guard_st reload_st fn /\
   fn_has_code reload_st header_st fn` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es u /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (BETA_RULE (Q.INST [`sa` |-> `count_st`, `sb` |-> `guard_st`,
    `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`] array_payload_guard_owned_effect)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `v` (qx_choose_then `Gv` (qx_choose_then `tnv`
      (map_every assume_tac o CONJUNCTS)))))
  >- (qexistsl_tac [`Abort Revert_abort v`,`Gv`,`tnv`] >>
      asm_rewrite_tac[] >> conj_tac
      >- (rpt strip_tac >> first_x_assum irule >> simp[]) >>
      disj1_tac >> qexists_tac `v` >> REFL_TAC) >>
  suspend "reload"
QED

Resume abi_decode_array_prepare_suffix_width_joint_effect_mods[reload]:
  drule_all array_payload_guard_shape >> strip_tac >>
  `(!x. not_fresh_at count_st x ==> not_fresh_at guard_st x) /\
   local_ptrs_reserved ce guard_st` by
    (conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `count_st` >> simp[]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `count_st` >> simp[]) >>
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
  mp_tac (Q.INST [`sa` |-> `guard_st`, `sb` |-> `reload_st`,
    `s` |-> `v`, `G` |-> `Gv`, `tn` |-> `tnv`, `counter` |-> `addr`,
    `out` |-> `cnt`] counter_load_owned_effect) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `w` (qx_choose_then `Gw`
    (qx_choose_then `tnw` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "store"
QED

Resume abi_decode_array_prepare_suffix_width_joint_effect_mods[store]:
  drule loweringShapeRulesTheory.emit_op_facts >> strip_tac >>
  qpat_x_assum `Var cnt = Var out` (SUBST_ALL_TAC o SYM o SIMP_RULE (srw_ss()) []) >>
  `not_fresh_at reload_st cnt /\ guard_st.cs_next_var <= reload_st.cs_next_var` by simp[] >>
  `(!x. not_fresh_at guard_st x ==> not_fresh_at reload_st x) /\
   local_ptrs_reserved ce reload_st` by
    (conj_tac
     >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `guard_st` >> simp[]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `guard_st` >> simp[]) >>
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
  asm "store_all" (mp_tac o Q.INST [`sa` |-> `reload_st`, `sb` |-> `header_st`,
    `s` |-> `w`, `G` |-> `Gw`, `tn` |-> `tnw`, `value` |-> `Var cnt`] o
    Q.INST [`w` |-> `n2w c`] o SPEC_ALL) >>
  impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gp`
    (qx_choose_then `tnp` (map_every assume_tac o CONJUNCTS)))) >>
  suspend "compose"
QED

Resume abi_decode_array_prepare_suffix_width_joint_effect_mods[compose]:
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

Resume abi_decode_array_prepare_suffix_width_joint_effect_mods[certificate]:
  `p+c*stride <= LENGTH input_bytes` by simp[] >>
  `allocas_from lo t` by
    (qpat_assum `t = _` SUBST1_TAC >>
     qpat_assum `allocas_from lo u` mp_tac >>
     simp[ptrDisciplineTheory.allocas_from_def,dynCopyExecTheory.mstore_control_fields] >>
     gvs[ptrDisciplineTheory.allocas_from_def,dynCopyExecTheory.mstore_control_fields]) >>
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
  `abi_decode_guarded_effect_core u tnu t tnp` by
    (simp[abi_decode_guarded_effect_core_def] >>
     qpat_assum `tnp.t_mem SUBSET tnu.t_mem` (assume_tac o REWRITE_RULE[SUBSET_DEF]) >>
     simp[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `tnp.t_mem SUBSET tnu.t_mem`
    (irule o REWRITE_RULE[SUBSET_DEF]) >>
  first_assum ACCEPT_TAC
QED

Finalise abi_decode_array_prepare_suffix_width_joint_effect_mods
