Theory abiEncoderWindowJoint
Ancestors
  abiEncoderWindowJointComplex abiEncoderWindowJointArray abiEncoderWindowJointLeaves abiEncoderAdmissible
  abiEncoderWindowArrayLayout pair
  exprSimAbiEncodeFramedLeaves abiBytesEncoderJointGhost
  abiEncoderWindowBytesMem abiEncoderWindowBytes abiEncoderWindowSequence
  abiEncoderWindowContract abiEncoderWindow abiEncoderRounding abiEncoderBytes
  abiBytestringCode representationCleanPtr reasonCopySourcePtr
  fragGasSeqPtr bodyPtrDefs ptrCoverage ptrSafetyTransport ghostPcTransportPtr
  exprLoweringProps loweringStateRelDefs memoryReadProps valueEncodingProps
  fragExec venomExecSemantics venomMemDefs venomState venomInst contractABI
  words list rich_list arithmetic finite_map pred_set

Theorem compile_abi_encode_to_buf_window_joint:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==>
    sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (contractABI$enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (contractABI$enc at av) ==>
    ?p. dst = Var p /\
      ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_strong_result ctx func st en out at av d s t /\
    abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (contractABI$enc at av) ==>
      i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (contractABI$enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  (qsuff_tac `(!ei. abi_encoder_admissible ei ==>
!dst src st out en ctx func s at av sb cap d G tn lo explicit PG.
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==>
    sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (contractABI$enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (contractABI$enc at av) ==>
    ?p. dst = Var p /\
      ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_strong_result ctx func st en out at av d s t /\
    abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (contractABI$enc at av) ==>
      i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (contractABI$enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
(!infos. abi_encoder_members_admissible infos ==>
 EVERY (\(ei,_,_,_).
!dst src st out en ctx func s at av sb cap d G tn lo explicit PG.
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==>
    sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (contractABI$enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (contractABI$enc at av) ==>
    ?p. dst = Var p /\
      ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
  (!inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\
    (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_strong_result ctx func st en out at av d s t /\
    abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\
    (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (contractABI$enc at av) ==>
      i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (contractABI$enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) infos)`
   >- (strip_tac >> strip_tac >>
       qpat_x_assum `!ei. abi_encoder_admissible ei ==> _`
         (qspec_then `ei` mp_tac) >>
       asm_rewrite_tac[] >>
       disch_then (qspecl_then [`dst`, `src`, `st`, `out`, `en`, `ctx`,
         `func`, `s`, `at`, `av`, `sb`, `cap`, `d`, `G`, `tn`, `lo`,
         `explicit`, `PG`] mp_tac) >> asm_rewrite_tac[])) >>
  ho_match_mp_tac abi_encoder_admissible_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`EVERY _ []`]
  >- simp_tac bool_ss [EVERY_DEF]
  >~ [`EVERY _ (_::_)`]
  >- (qpat_assum `abi_encoder_members_admissible (_::_)`
        (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_admissible_def]) >>
      pure_once_rewrite_tac [EVERY_DEF] >>
      CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> conj_tac
      >- (qpat_assum `abi_encoder_admissible ei ==> _`
          (fn th => qpat_assum `abi_encoder_admissible ei`
            (fn ad => ACCEPT_TAC (MP th ad)))) >>
      qpat_assum `abi_encoder_members_admissible infos ==> _`
        (fn th => qpat_assum `abi_encoder_members_admissible infos`
          (fn ad => ACCEPT_TAC (CONV_RULE
            (DEPTH_CONV PairRules.PBETA_CONV) (MP th ad)))))
  >~ [`compile_abi_encode_to_buf dst src AbiPrimWord st = (out,en)`]
  >- (irule (SIMP_RULE bool_ss [abi_encoder_admissible_def]
        compile_abi_encode_to_buf_word_window_joint) >>
       asm_rewrite_tac[] >>
       qexistsl_tac [`cap`, `dst`, `sb`, `src`] >> asm_rewrite_tac[])
  >~ [`compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,en)`]
  >- (irule (SIMP_RULE bool_ss [abi_encoder_admissible_def]
        compile_abi_encode_to_buf_copy_window_joint) >>
       asm_rewrite_tac[] >>
       qexistsl_tac [`cap`, `dst`, `sb`, `src`, `sz`] >> asm_rewrite_tac[])
  >~ [`compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en)`]
  >- (
  `abi_encoder_window_input (AbiBytestring maxlen) at av sb cap s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_bytes_iff]) >>
  qpat_x_assum `av = BytesV bs` SUBST_ALL_TAC >>
  `LENGTH (enc at (BytesV bs)) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  `0 < cap /\ 0 < LENGTH (enc at (BytesV bs))` by decide_tac >>
  `sb+cap <= s.vs_alloca_next /\
   regions_disjoint (sb,cap) (d,LENGTH (enc at (BytesV bs))) /\
   (?sp. src = Var sp /\ ptr_covers G tn sp s cap) /\
   (?dp. dst = Var dp /\ ptr_covers G tn dp s (LENGTH (enc at (BytesV bs))))` by
    metis_tac[] >>
  `abi_encoder_window_pre ctx func st en dst src (AbiBytestring maxlen)
    at (BytesV bs) sb cap d s` by
    (simp_tac bool_ss [abi_encoder_window_pre_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at sb mem = n2w (LENGTH bs) /\
    mem_bytes_at (sb+32) (LENGTH bs) mem = bs` by
    (gen_tac >> strip_tac >>
     qpat_assum `!mem. _ ==> abi_encoder_window_input _ _ _ _ _ mem`
       (qspec_then `mem` mp_tac) >>
     qpat_assum `mem_agree_outside tn.t_mem s.vs_memory mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[abi_encoder_window_bytes_iff]) >>
  `!i. sb <= i /\ i < sb+32 ==> i NOTIN tn.t_mem` by
    (mp_tac (Q.SPECL [`tn.t_mem`, `s.vs_memory`, `sb`,
       `n2w (LENGTH (bs:8 word list)):256 word`] robust_mem_word_at_clean) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `!i. sb+32 <= i /\ i < sb+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (mp_tac (Q.SPECL [`tn.t_mem`, `s.vs_memory`, `sb+32`,
       `LENGTH (bs:8 word list)`, `bs:8 word list`] robust_mem_bytes_at_clean) >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `!i. sb <= i /\ i < sb+32+LENGTH bs ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> Cases_on `i < sb+32` >> metis_tac[NOT_LESS]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `LENGTH bs <= contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_ceil32_bounds] >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   LENGTH bs+31 < dimword (:256) /\
   d+contractABI$ceil32 (LENGTH bs) < dimword (:256) /\
   32+LENGTH bs < dimword (:256) /\
   sb+32+LENGTH bs <= s.vs_alloca_next /\
   d+32+contractABI$ceil32 (LENGTH bs) <= s.vs_alloca_next /\
   sb+32+LENGTH bs < dimword (:256) /\
   d+32+contractABI$ceil32 (LENGTH bs) < dimword (:256)` by decide_tac >>
  `mload sb s = n2w (LENGTH bs) /\ read_memory (sb+32) (LENGTH bs) s = bs` by
    metis_tac[mem_word_at_eq_mload, read_memory_eq_mem_bytes_at] >>
  `regions_disjoint (sb,32+LENGTH bs) (d,32+contractABI$ceil32 (LENGTH bs))` by
    (qpat_assum `regions_disjoint (sb,cap) _` mp_tac >>
     qpat_assum `LENGTH (enc at (BytesV bs)) = _` mp_tac >>
     qpat_assum `32+LENGTH bs <= cap` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `LENGTH (enc at (BytesV bs)) = _`
       (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
     fs[regions_disjoint_def, Excl "enc_def"] >> decide_tac) >>
  drule_all abi_encode_framed_bytes_endpoint >> strip_tac >>
  rename1 `window_seq st en s raw` >>
  `run_inst_seq (emitted_insts st en) s = OK raw` by
    (qpat_assum `window_seq st en s raw` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_seq_def]) >>
  qpat_x_assum `src = Var sp` SUBST_ALL_TAC >>
  qpat_x_assum `dst = Var dp` SUBST_ALL_TAC >>
  `ptr_covers G tn sp s (32+LENGTH bs)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `cap` >> asm_rewrite_tac[]) >>
  `ptr_covers G tn dp s (32+contractABI$ceil32 (LENGTH bs))` by metis_tac[] >>
  `not_fresh_at st sp /\ not_fresh_at st dp` by metis_tac[] >>
  `w2n (n2w sb : 256 word) = sb /\ w2n (n2w d : 256 word) = d` by
    simp[w2n_n2w, LESS_MOD] >>
  mp_tac (Q.INST [`dst` |-> `Var dp`, `src` |-> `Var sp`,
    `cnt` |-> `LENGTH (bs:8 word list)`, `db` |-> `d`, `sb` |-> `sb`,
    `final` |-> `en`] (SPEC_ALL window_bytes_mem_checks)) >>
  (impl_tac >- (asm_rewrite_tac[] >> metis_tac[])) >> strip_tac >>
  mp_tac (Q.INST [`src` |-> `sp:string`, `dst` |-> `dp:string`,
    `p` |-> `(n2w sb : 256 word)`, `q` |-> `(n2w d : 256 word)`]
    (SPEC_ALL bytes_encoder_joint_ghosts)) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  drule compile_abi_bytestring_code >> strip_tac >>
  `!x. out = Var x ==> not_fresh_at en x` by
    (qpat_assum `out = Var (EL 8 _)` mp_tac >>
     qpat_assum `en.cs_next_var = st.cs_next_var+9` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compiler_var_names_EL, not_fresh_at_def]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st en) = []` by
    (qpat_assum `emitted_insts st en = _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bytestring_encoder_insts_def, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en)` by
    (qpat_assum `emitted_insts st en = _` (fn th => rewrite_tac[th]) >>
     MATCH_ACCEPT_TAC bytestring_encoder_straight) >>
  `s.vs_inst_idx + LENGTH (emitted_insts st en) = LENGTH en.cs_current_insts` by
    (qpat_assum `en.cs_current_insts = st.cs_current_insts ++ _` mp_tac >>
     qpat_assum `s.vs_inst_idx = LENGTH st.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[LENGTH_APPEND]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code st en func` mp_tac >>
     qpat_assum `same_blocks st en` mp_tac >>
     qpat_assum `en.cs_current_insts = st.cs_current_insts ++ _` mp_tac >>
     qpat_assum `s.vs_current_bb = st.cs_current_bb` mp_tac >>
     qpat_assum `s.vs_inst_idx = LENGTH st.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     rpt strip_tac >> qexists_tac `bb` >>
     asm_rewrite_tac[] >> metis_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) []
    (OK (raw with vs_inst_idx := LENGTH en.cs_current_insts),G',tn')` by
    (gen_tac >>
     qpat_assum `!D. inst_seq_ptr D _ _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     mp_tac (Q.SPECL [`emitted_insts st en`, `s`, `raw`, `G`, `tn`,
       `G'`, `tn'`, `ctx`, `func`, `bb`] run_inst_seq_gas_origin_ptr_path) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     qpat_assum `FILTER _ (emitted_insts st en) = []` mp_tac >>
     qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts st en) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> metis_tac[MAP]) >>
  qexistsl_tac [`raw with vs_inst_idx := LENGTH en.cs_current_insts`, `G'`, `tn'`] >>
  asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[ADD_ASSOC]
     )
  >~ [`compile_abi_encode_to_buf dst src (AbiDynArray _ _ _ _) st = (out,en)`]
  >-     (qpat_assum `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> abi_encoder_window_input _ _ _ _ _ mem`
       (qspec_then `s.vs_memory` mp_tac) >>
     simp_tac bool_ss [mem_agree_outside_def] >> strip_tac >>
     `?ty avs. at = Array NONE ty /\ av = ListV avs /\ 32 <= cap` by
       (qpat_assum `abi_encoder_window_input (AbiDynArray _ _ _ _) _ _ _ _ _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encoder_window_array_iff] >> metis_tac[]) >>
     qpat_x_assum `at = Array NONE ty` SUBST_ALL_TAC >>
     qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
     `0 < cap` by decide_tac >>
     `0 < LENGTH (enc (Array NONE ty) (ListV avs))` by
       (qpat_assum `abi_encoder_window_input (AbiDynArray _ _ _ _) _ _ _ _ _`
          (mp_then Any mp_tac window_array_layout) >>
        POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> asm_rewrite_tac[] >> decide_tac) >>
     `abi_encoder_window_pre ctx func st en dst src
        (AbiDynArray ei abi_sz mem_sz dyn) (Array NONE ty) (ListV avs) sb cap d s /\
      (?p. src = Var p /\ ptr_covers G tn p s cap) /\
      (?p. dst = Var p /\ ptr_covers G tn p s
        (LENGTH (enc (Array NONE ty) (ListV avs))))` by
       (qpat_x_assum `abi_encoder_admissible ei ==> _` kall_tac >>
        asm_rewrite_tac[abi_encoder_window_pre_def] >> metis_tac[]) >>
     `abi_encoder_admissible ei` by
       (qpat_assum `abi_encoder_admissible (AbiDynArray _ _ _ _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encoder_admissible_def] >> metis_tac[]) >>
     qpat_x_assum `abi_encoder_admissible ei ==> _`
       (fn ih => qpat_assum `abi_encoder_admissible ei`
         (fn ad => assume_tac (MP ih ad))) >>
     mp_tac (Q.INST [`ei` |-> `ei`, `asz` |-> `abi_sz`,
       `msz` |-> `mem_sz`, `active` |-> `dyn`, `cap` |-> `cap`,
       `dst` |-> `dst`, `sb` |-> `sb`, `src` |-> `src`,
       `st` |-> `st`, `en` |-> `en`, `out` |-> `out`,
       `ctx` |-> `ctx`, `func` |-> `func`, `s` |-> `s`,
       `at` |-> `Array NONE ty`, `av` |-> `ListV avs`, `d` |-> `d`,
       `G` |-> `G`, `tn` |-> `tn`, `lo` |-> `lo`,
       `explicit` |-> `explicit`, `PG` |-> `PG`]
       (SPEC_ALL compile_abi_encode_to_buf_array_window_joint)) >>
     (impl_tac >-
       (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
        qpat_x_assum `!dst src st out en ctx func s at av sb cap d G tn lo explicit PG. _`
          kall_tac >>
        asm_rewrite_tac[] >> metis_tac[])) >>
     disch_then MATCH_ACCEPT_TAC)
  >> suspend "complex_constructor"
QED

Resume compile_abi_encode_to_buf_window_joint[complex_constructor]:
  `abi_encoder_members_admissible infos` by
    (qpat_assum `abi_encoder_admissible (AbiComplex infos)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encoder_admissible_def]) >>
  qpat_x_assum `abi_encoder_members_admissible infos ==> _`
    (fn ih => qpat_assum `abi_encoder_members_admissible infos`
      (fn ad => assume_tac (CONV_RULE
        (DEPTH_CONV PairRules.PBETA_CONV)
        (PURE_REWRITE_RULE [EVERY_MEM, pairTheory.FORALL_PROD] (MP ih ad))))) >>
  suspend "complex_provider"
QED

Resume compile_abi_encode_to_buf_window_joint[complex_provider]:
  mp_tac (Q.INST [`infos` |-> `infos`]
    (SPEC_ALL compile_abi_encode_to_buf_complex_window_joint)) >>
  (impl_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!e. MEM e infos ==> _`
       (qspec_then `(ei,az,ms,dyn)` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [pairTheory.FST])) >>
  disch_then (qspecl_then [`dst`,`src`,`st`,`out`,`en`,`ctx`,`func`,
    `s`,`at`,`av`,`sb`,`cap`,`d`,`G`,`tn`,`lo`,`explicit`,`PG`] mp_tac) >>
  impl_tac
  >- (qpat_x_assum `!e. MEM e infos ==> _` kall_tac >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then MATCH_ACCEPT_TAC
QED

Finalise compile_abi_encode_to_buf_window_joint
