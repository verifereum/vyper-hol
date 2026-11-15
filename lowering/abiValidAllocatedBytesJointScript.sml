(* Allocation-backed bytes decoding replays the fresh certificate on its actual run. *)
Theory abiValidAllocatedBytesJoint
Ancestors
  abiValidAllocatedLeaves abiValidAllocatedContract abiDecodePtrBytesJoint
  abiDecodeMemReentry abiDecodePtrReentry abiDecodePtrReentryGhost abiDecoderValidBytes abiDecoderString
  abiDecoderBytesTyped abiDecoderBytesFrame abiDecoderBytes abiDecoderBytesPhases
  abiDecoderReentry abiDecoderVarExtend
  abiDecoderVarSequence abiDecoderReentryPointer abiDecodePtrMemberFrame
  abiMalformedRecursiveInterface abiDecoderContract entryDecoderHistoryFrame
  abiValidAllocatedObservations ctorAbiActualWorld
  decoderGhostFramePtr
  exprSimPtrLiteralBuffer valueEncodingDefs loweringPosts
  fragGasCopyLoop fragGasOriginPtrDead bodyPtrDefs ptrDiscipline compileEnv
  loweringStateRelDefs exprLoweringProps venomState venomExecSemantics venomMemDefs
  contractABI vyperTypeABI emitHelperProps finite_map words list arithmetic

Theorem abi_valid_allocated_bytes_joint_observations:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?t G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ptr_covers G' tn' output t (type_memory_bytes ce ty) /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(d <= i /\ i < d+type_memory_bytes ce ty) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s.vs_alloca_next = t.vs_alloca_next /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_bytes_run >> strip_tac >>
  drule_all abi_valid_allocated_bytes_input >> strip_tac >>
  qhdtm_assum `abi_valid_allocated_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_entry_def]) >>
  `compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
      (DecBytestring n) st = ((),en)` by metis_tac[] >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all abi_malformed_allocated_bounds >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `B+L < dimword(:256)` by fs[abi_malformed_allocated_window_def] >>
  `n+32 <= abi_decode_bytes_copy_size n` by
    (irule (cj 3 abi_decoder_bytes_copy_size)) >>
  `B < dimword(:256) /\ d < dimword(:256) /\ p < dimword(:256) /\
    n+31 < dimword(:256)` by decide_tac >>
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  qabbrev_tac `ps = abi_decoder_prune_vars st.cs_next_var s` >>
  `abi_decoder_valid_bytes_pre n at (DROP p xs) payload st pos (Var output)
      MLOAD (Var source) hi B p d ps` by fs[Abbr `ps`] >>
  drule_all (abi_decoder_valid_bytes_sequence |>
    Q.INST [`opc` |-> `MLOAD`] |> SRULE []) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) ps = OK clean` >>
  drule abi_decoder_valid_bytes_facts >> strip_tac >>
  qhdtm_assum `EVERY`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [EVERY_DEF]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ps = eval_operand op s` by
    (rpt strip_tac >> simp[Abbr `ps`, abi_decoder_prune_eval]) >>
  `lookup_var source ps = SOME (n2w B) /\
   lookup_var output ps = SOME (n2w d) /\
   eval_operand pos ps = SOME (n2w p) /\ eval_operand hi ps = SOME (n2w L)` by
    (pure_rewrite_tac [GSYM (cj 2 eval_operand_def)] >>
     qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
       (fn th => pure_once_rewrite_tac
         (map (fn operand => UNDISCH (Q.SPEC operand th))
           [`Var source`, `Var output`, `pos`, `hi`])) >> simp[]) >>
  `fresh_vars_wrt st ps` by simp[Abbr `ps`, abi_decoder_prune_fresh] >>
  `ptr_covers G tn output ps (abi_decode_bytes_copy_size n)` by
    (simp[Abbr `ps`, abi_decode_ptr_prune_covers] >> metis_tac[]) >>
  `abi_decode_ptr_window G tn ps source (n2w B) L` by
    (fs[abi_decode_ptr_window_def] >>
     simp[Abbr `ps`, abi_decode_ptr_prune_covers]) >>
  `allocas_from lo ps` by
    (fs[Abbr `ps`, abi_decoder_prune_vars_def, allocas_from_def] >> metis_tac[]) >>
  mp_tac (abi_decode_bytes_success_joint |>
    Q.INST [`d` |-> `destination_word`] |>
    Q.INST [`sa` |-> `st`, `sb` |-> `en`, `src` |-> `source`, `dst` |-> `output`,
      `b` |-> `n2w B`, `h` |-> `L`, `destination_word` |-> `n2w d`,
      `cap` |-> `abi_decode_bytes_copy_size n`, `s` |-> `ps`, `u` |-> `clean`]) >>
  (impl_tac >- (simp[Abbr `ps`, abi_decoder_prune_vars_def, w2n_n2w,
      abi_decode_bytes_copy_size_def, contractABITheory.ceil32_def] >>
      fs[abi_decode_bytes_copy_size_def] >> decide_tac)) >>
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_bytes_joint_code >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
      ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
  `abi_decoder_vars_extend s.vs_vars ps s` by
    simp[Abbr `ps`, abi_decoder_prune_extension] >>
  drule_all abi_decoder_sequence_vars_extend >> strip_tac >>
  rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
  `actual = t with vs_inst_idx := s.vs_inst_idx` by fs[] >>
  qpat_x_assum `actual = _` SUBST_ALL_TAC >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
     (emitted_insts st en)` by fs[EVERY_MEM] >>
  mp_tac (Q.SPECL [`emitted_insts st en`, `s`,
    `t with vs_inst_idx := s.vs_inst_idx`] ctor_actual_sequence_world) >>
  (impl_tac >- simp[]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  mp_tac (Q.SPECL [`emitted_insts st en`, `s`,
    `t with vs_inst_idx := s.vs_inst_idx`] abi_valid_allocated_sequence_static) >>
  (impl_tac >- simp[]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  `t.vs_memory = clean.vs_memory` by fs[] >>
  `run_inst_seq_mem_ok (emitted_insts st en) s` by
    (drule_all abi_decode_sequence_mem_reentry >> simp[]) >>
  `inst_seq_ptr
      <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
      0 ctx func PG G tn (emitted_insts st en) s G' tn'` by
    (drule_all abi_decode_ptr_sequence_reentry >> simp[]) >>
  `t.vs_inst_idx = LENGTH en.cs_current_insts` by fs[abi_valid_allocated_post_def] >>
  `LENGTH st.cs_current_insts + LENGTH (emitted_insts st en) =
      LENGTH en.cs_current_insts` by decide_tac >>
  `t with vs_inst_idx := LENGTH en.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  `allocas_from lo t` by (fs[allocas_from_def] >> metis_tac[]) >>
  `!explicit. gas_origin_ptr_path
      (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
       lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\ allocas_from lo t` by
    (gen_tac >> drule_all run_inst_seq_origin_ptr_lift >>
     disch_then (qspec_then `explicit` mp_tac) >> simp[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')` by
    (rpt gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st en)` by fs[EVERY_MEM] >>
  drule_all abi_decode_bytes_position_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts en.cs_current_insts` by fs[inst_extends_def] >>
  `alloca_history func t` by
    (drule_all entry_straight_line_alloca_history >> fs[]) >>
  `lookup_var source t = SOME (n2w B) /\ lookup_var output t = SOME (n2w d)` by
    (conj_tac
     >- (qpat_assum `!op w. abi_decoder_operand_live st.cs_next_var op /\ _ ==> _`
           (qspecl_then [`Var source`, `n2w B`]
             (irule o SRULE [eval_operand_def])) >>
     simp[GSYM (cj 2 eval_operand_def)]) >>
     qpat_assum `!op w. abi_decoder_operand_live st.cs_next_var op /\ _ ==> _`
       (qspecl_then [`Var output`, `n2w d`]
         (irule o SRULE [eval_operand_def])) >>
     simp[GSYM (cj 2 eval_operand_def)]) >>
  `FLOOKUP G' source = FLOOKUP G source /\
   op_taint tn' (Var source) = op_taint tn (Var source) /\
   FLOOKUP G' output = FLOOKUP G output /\
   op_taint tn' (Var output) = op_taint tn (Var output)` by metis_tac[] >>
  `lookup_var source s = SOME (n2w B) /\ lookup_var output s = SOME (n2w d)` by
    fs[eval_operand_def] >>
  `ptr_covers G' tn' output t (type_memory_bytes ce ty)` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `abi_decode_ptr_window G' tn' t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G'`, `clean`, `tn'`] >> simp[] >>
     fs[abi_decode_ptr_window_def]) >>
  `LENGTH payload < dimword(:256)` by decide_tac >>
  `w2n (mload (B+p) ps) = LENGTH payload` by
    (qpat_assum `abi_decode_load MLOAD _ ps = _`
       (mp_tac o AP_TERM ``w2n : bytes32 -> num`` o
         PURE_REWRITE_RULE [abi_decode_load_def]) >>
     simp[w2n_n2w]) >>
  `!i. d <= i /\ i < d+32+contractABI$ceil32 (LENGTH payload) ==>
      i NOTIN tn'.t_mem` by
    (qpat_assum `abi_decode_ptr_window G' tn' clean output _ _`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o
         PURE_REWRITE_RULE [abi_decode_ptr_window_def]) >> simp[w2n_n2w]) >>
  assume_tac (Q.SPEC `LENGTH (payload:word8 list)`
    (GEN_ALL contractABITheory.le_ceil32)) >>
  `!i. d <= i /\ i < d+32+LENGTH payload ==> i NOTIN tn'.t_mem` by
    (gen_tac >> disch_tac >>
     qpat_assum `!j. _ ==> j NOTIN tn'.t_mem`
       (qspec_then `i` irule) >> decide_tac) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem` by
    (rpt strip_tac >> irule literal_clean_representation_robust >>
     conj_tac >- simp[] >>
     qexistsl_tac [`tn'.t_mem`, `t.vs_memory`] >> fs[val_footprint_def]) >>
  `!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem` by
    (rpt strip_tac >>
     qpat_assum `!mem. val_in_memory _ _ _ mem /\ val_in_memory _ _ _ mem ==> _`
       (qspec_then `mem` irule) >> simp[abi_decoder_string_memory]) >>
  `LENGTH payload <= n` by
    (qhdtm_assum `abi_decoder_valid_bytes_pre`
       (mp_tac o cj 4 o PURE_REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >> simp[]) >>
  `contractABI$ceil32 (LENGTH payload) <= contractABI$ceil32 n` by
    (irule vyperTypeABITheory.ceil32_mono >> simp[]) >>
  `32+contractABI$ceil32 (LENGTH payload) <= type_memory_bytes ce ty` by
    (fs[abi_decode_bytes_copy_size_def, contractABITheory.ceil32_def] >> decide_tac) >>
  `!i. ~(d <= i /\ i < d+type_memory_bytes ce ty) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >>
     `~(d <= i /\ i < d+32+contractABI$ceil32 (LENGTH payload))` by decide_tac >>
     qpat_assum `!i. _ ==> mem_bytes_at i 1 clean.vs_memory = _ /\ _`
       (qspec_then `i` mp_tac) >> simp[w2n_n2w]) >>
  `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at st x` by
       fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (ACCEPT_TAC o CONJUNCT2 o UNDISCH o Q.SPEC `x`)) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_allocated_bytes_joint:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?t G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s t /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ptr_covers G' tn' output t (type_memory_bytes ce ty) /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
      val_in_memory tv v d mem) /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. ~(d <= i /\ i < d+type_memory_bytes ce ty) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    s.vs_alloca_next = t.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_bytes_joint_observations >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_rewrite_tac[]
QED
