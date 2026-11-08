(* Robust ABI windows expose clean read bytes, not clean unused capacity. *)
Theory abiEncoderWindowLeavesPtr
Ancestors abiEncoderRobustWindowPtr abiEncoderBytesPtr representationCleanPtr
  abiEncoderWindowLeaves abiEncoderWindowContract abiEncoderWindow
  abiEncoderInput bodyPtrDefs valueEncoding contractABI list arithmetic
  straightFragmentFramePtr abiEncoderBytes abiEncoderBytesCode abiDecoderContract
  emitHelper compileEnv emitHelperProps exprLoweringProps rich_list abiDecodeStaticProps
  abiEncoderWindowBytes localPtrsProps abiEncoderRounding valueEncodingProps

Theorem abi_encoder_robust_word_read_clean:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input AbiPrimWord at av p cap m) ==>
  !a. p <= a /\ a < p+32 ==> a NOTIN ta
Proof
  rpt gen_tac >> disch_tac >>
  `!m. mem_agree_outside ta mem m ==> mem_bytes_at p 32 m = enc at av` by
    metis_tac[abi_encoder_window_word_iff] >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem abi_encoder_robust_copy_read_clean:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiCopy n) at av p cap m) ==>
  !a. p <= a /\ a < p+n ==> a NOTIN ta
Proof
  rpt gen_tac >> disch_tac >>
  `!m. mem_agree_outside ta mem m ==> mem_bytes_at p n m = enc at av` by
    metis_tac[abi_encoder_window_copy_iff] >>
  drule robust_mem_bytes_at_clean >> simp[]
QED

Theorem abi_encoder_robust_bytes_read_clean:
  (!m. mem_agree_outside ta mem m ==>
    abi_encoder_window_input (AbiBytestring maxlen) at av p cap m) ==>
  ?bs. av = BytesV bs /\
    (!m. mem_agree_outside ta mem m ==>
      mem_word_at p m = n2w (LENGTH bs) /\
      mem_bytes_at (p+32) (LENGTH bs) m = bs) /\
    (!a. p <= a /\ a < p+32+LENGTH bs ==> a NOTIN ta)
Proof
  rpt gen_tac >> disch_tac >>
  `mem_agree_outside ta mem mem` by simp[mem_agree_outside_def] >>
  first_assum drule >> rewrite_tac[abi_encoder_window_bytes_iff] >> strip_tac >>
  qexists_tac `bs` >> gvs[] >> (
  `!m. mem_agree_outside ta mem m ==>
    mem_word_at p m = n2w (LENGTH bs) /\
    mem_bytes_at (p+32) (LENGTH bs) m = bs` by
      (rpt strip_tac >> first_x_assum drule >>
       simp[abi_encoder_window_bytes_iff]) >>
  conj_tac >- asm_rewrite_tac[] >>
  `!m. mem_agree_outside ta mem m ==>
    mem_word_at p m = n2w (LENGTH bs)` by metis_tac[] >>
  drule robust_mem_word_at_clean >> disch_tac >>
  `!m. mem_agree_outside ta mem m ==>
    mem_bytes_at (p+32) (LENGTH bs) m = bs` by metis_tac[] >>
  drule robust_mem_bytes_at_clean >> disch_tac >>
  rpt strip_tac >>
  Cases_on `a < p+32`
  >- (qpat_x_assum `!i. p <= i /\ i < p+32 ==> _`
        (qspec_then `a` mp_tac) >> simp[]) >>
  qpat_x_assum `!i. p+32 <= i /\ _ ==> _` (qspec_then `a` mp_tac) >>
  simp[])
QED

(* A zero-byte copy still evaluates its address operands. *)
Theorem mcopy_taint_ok_operands_clean:
  taint_ok fn tn (mk_inst id MCOPY [dst;src;len] []) s ==>
  op_taint tn dst = {} /\ op_taint tn src = {} /\ op_taint tn len = {}
Proof
  simp[ptrDisciplineTheory.taint_ok_def, venomInstTheory.mk_inst_def] >>
  metis_tac[]
QED

Theorem zero_copy_tainted_source_rejected[local]:
  !fn s.
    ~taint_ok fn
      (entry_taint with t_var := FEMPTY |+ ("src",{0}))
      (mk_inst 0 MCOPY [Var "dst";Var "src";Lit 0w] []) s
Proof
  rpt gen_tac >> strip_tac >>
  drule mcopy_taint_ok_operands_clean >>
  simp[ptrDisciplineTheory.op_taint_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  EVAL_TAC
QED

(* A false-exit singleton fragment exposes control facts at that very endpoint. *)
Theorem frag_exec_ptr_singleton_control:
  frag_exec_ptr cx ctx PG sa sb
    (\g z v. g=G /\ z=tn /\ v=s)
    (\g z v. g=H /\ z=u /\ v=t) (\gt r. F) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  abiDecoderLoop$abi_decode_sim ctx fn s t
Proof
  simp_tac bool_ss [frag_exec_ptr_def, abiDecoderLoopTheory.abi_decode_sim_def] >>
  metis_tac[]
QED

Theorem frag_exec_ptr_false_exit_weaken:
  frag_exec_ptr cx ctx PG sa sb P Q (\gt r. F) ==>
  frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  simp_tac bool_ss [frag_exec_ptr_def] >> metis_tac[]
QED

Theorem abi_encode_bytes_straight_imm:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) sa = (out,sb) ==>
  dec_straight sa sb /\
  EVERY (\inst. !w w' tn. (step_taint inst w w' tn).t_imm = tn.t_imm)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule abi_encode_bytes_shape >> strip_tac >>
  conj_tac
  >- (simp[dec_straight_def] >> fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, ptrDisciplineTheory.step_taint_def,
    ptrDisciplineTheory.imm_taint_def, venomInstTheory.mk_inst_def]
QED

(* Window semantics and ghost facts are established at one execution endpoint. *)
Theorem abi_encoder_bytes_window_frag_ptr:
  compile_abi_encode_to_buf (Var dst) (Var src) (AbiBytestring maxlen) sa = (out,sb) /\
  abi_encoder_window_pre ctx fn sa sb (Var dst) (Var src)
    (AbiBytestring maxlen) at av p cap d s /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    abi_encoder_window_input (AbiBytestring maxlen) at av p cap m) /\
  ptr_covers G tn src s cap /\
  ptr_covers G tn dst s (LENGTH (enc at av)) /\ ~ctx_has_dalloca ctx ==>
  ?H u t.
    frag_exec_ptr cx ctx PG sa sb (\g z v. g=G /\ z=tn /\ v=s)
      (\g z v. g=H /\ z=u /\ v=t) R /\
    abi_encoder_window_result ctx fn sa sb out at av d s t /\
    op_taint u out = {} /\
    (!i. d <= i /\ i < d+LENGTH (enc at av) ==> i NOTIN u.t_mem) /\
    (!i. i < d \/ d+LENGTH (enc at av) <= i ==>
      (i IN u.t_mem <=> i IN tn.t_mem)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_encoder_robust_bytes_read_clean >> strip_tac >> gvs[] >>
  qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  `LENGTH (enc at (BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding, abi_encoder_window_bytes_iff] >>
  `32+LENGTH bs <= cap` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ s.vs_memory` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_bytes_iff, contractABITheory.abi_value_11] >>
     metis_tac[]) >>
  `s.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_ceil32_bounds] >>
  `not_fresh_at sa src /\ not_fresh_at sa dst` by metis_tac[] >>
  `lookup_var src s = SOME (n2w p) /\ lookup_var dst s = SOME (n2w d)` by
    fs[venomStateTheory.eval_operand_def] >>
  `mload p s = n2w (LENGTH bs)` by
    metis_tac[mem_word_at_eq_mload, mem_agree_outside_def] >>
  qpat_x_assum `!m. mem_agree_outside _ _ m ==> abi_encoder_window_input _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!m. mem_agree_outside _ _ m ==> _ /\ _` kall_tac >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `ptr_covers G tn src s (32+LENGTH bs)` by
    (qpat_assum `ptr_covers G tn src s cap` mp_tac >>
     simp_tac bool_ss [ptr_covers_def] >> strip_tac >>
     qexistsl_tac [`w`,`b`,`sz'`] >> asm_rewrite_tac[] >> decide_tac) >>
  `LENGTH bs+31 < dimword(:256) /\
   32+contractABI$ceil32 (LENGTH bs) < dimword(:256) /\
   p+32+LENGTH bs < dimword(:256) /\
   d+32+contractABI$ceil32 (LENGTH bs) < dimword(:256) /\
   (p+32+LENGTH bs <= d \/ d+32+contractABI$ceil32 (LENGTH bs) <= p)` by
    (gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >> (
  drule_at (Pat `ptr_covers _ _ _ _ (32+_)`) compile_abi_encode_bytestring_exact_frag_ptr >>
  disch_then drule >>
  disch_then (drule_at (Pat `lookup_var src s = _`)) >>
  disch_then (drule_at (Pat `lookup_var dst s = _`)) >>
  disch_then (qspecl_then [`cx`,`ctx`,`PG`,`\gt r. F`] mp_tac) >>
  (impl_tac >- (asm_simp_tac (srw_ss()) [] >> conj_tac
    >- metis_tac[] >> rpt strip_tac >>
    qpat_x_assum `!a. p <= a /\ _ ==> _` (qspec_then `i` mp_tac) >> simp[])) >>
  disch_then (qx_choose_then `H` (qx_choose_then `u` (qx_choose_then `t` strip_assume_tac))) >>
  drule_all frag_exec_ptr_singleton_control >> strip_tac >>
  drule abi_encode_bytes_straight_imm >> strip_tac >>
  `u.t_imm = tn.t_imm` by metis_tac[frag_exec_ptr_straight_imm_frame] >>
  `alloca_inv t /\ alloca_room ctx fn t` by
    metis_tac[alloca_inv_fields, alloca_room_fields] >>
  `abi_encoder_registered_effect (frag_ids sa sb)
    [(d,32+contractABI$ceil32 (LENGTH bs))] s t` by
    (irule window_bytes_effect >> asm_rewrite_tac[] >>
     qexistsl_tac [`LENGTH bs`,`p`] >> asm_rewrite_tac[]) >>
  `mem_bytes_at d (LENGTH (enc at (BytesV bs))) t.vs_memory = enc at (BytesV bs)` by
    (qpat_assum `t.vs_memory = _` (fn th => rewrite_tac[th]) >>
     irule window_bytes_input_memory >>
     qexistsl_tac [`cap`,`maxlen`] >> asm_rewrite_tac[] >>
     gvs[venomMemDefsTheory.regions_disjoint_def]) >>
  qexistsl_tac [`H`,`u`,`t`] >>
  conj_tac >- (irule frag_exec_ptr_false_exit_weaken >> first_assum ACCEPT_TAC) >>
  simp[abi_encoder_window_result_def] >>
  rpt strip_tac >> fs[] >> decide_tac)
QED
