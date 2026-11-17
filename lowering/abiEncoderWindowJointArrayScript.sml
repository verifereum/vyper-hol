(* Joint actual-window array encoding with the full robust child contract. *)
Theory abiEncoderWindowJointArray
Ancestors
  abiEncoderWindowJointPhases abiEncoderWindowJointLeaves
  abiEncoderWindowArray abiEncoderWindowArrayLoop abiEncoderWindowArrayRound
  abiEncoderWindowArrayBody abiEncoderWindowArrayFinish abiEncoderWindowChild
  abiEncoderWindowArrayInvariant abiEncoderWindowArrayLayout abiEncoderWindowContract
  exprSimAbiEncodeFramedArray exprSimAbiEncodeFramedArrayBody
  exprSimAbiEncodeFramedArrayControl exprSimAbiEncodeExecFrame
  abiEncoderArrayCode abiEncoderArrayPhases abiEncoderArrayLoopCode
  abiEncoderArrayBodyCode abiEncoderArrayDynamicMemory abiEncoderArrayContext abiEncoderRegisteredEffect
  abiEncoderArrayDynamicLoop abiDecoderIndexInit abiDecoderDynamicLoopSetup abiEncoderWindowPhase context
  abiEncoderWindow bodyPtrDefs
  representationCleanPtr robustCopyTransportPtr fragGasSeqPtr fragGasOriginPtr fragExecPtr ptrCoverage ptrDiscipline
  decoderGhostFramePtr ghostPcTransportPtr ptrSafetyTransport
  loweringStateRelDefs exprLoweringProps emitHelper emitHelperProps freshWrites compileEnv
  venomExecSemantics venomState venomMemDefs venomInst
  contractABI valueEncodingProps words list rich_list finite_map pred_set arithmetic

Theorem compile_abi_encode_to_buf_array_window_joint:
  (!dst src st out en ctx func s at av sb cap d G tn lo explicit PG.
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
    ~ctx_has_dalloca ctx /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (0 < cap ==>
      sb + cap <= s.vs_alloca_next /\
      venomMemDefs$regions_disjoint
        (sb,cap) (d,LENGTH (contractABI$enc at av)) /\
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
      (0 < cap ==>
        venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
      venomMemDefs$regions_disjoint
        (d,LENGTH (contractABI$enc at av)) (b,sz)) /\
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
        (!id b sz.
          id IN window_alloca_sites func (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
          i < b \/ b + sz <= i) ==>
        (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
      tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\
      tn'.t_imm = tn.t_imm /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
  compile_abi_encode_to_buf dst src
    (AbiDynArray ei asz msz active) st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src
    (AbiDynArray ei asz msz active) at av sb cap d s /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input
      (AbiDynArray ei asz msz active) at av sb cap mem) /\
  (?p. src = Var p /\ ptr_covers G tn p s cap) /\
  (?p. dst = Var p /\
    ptr_covers G tn p s (LENGTH (contractABI$enc at av))) /\
  ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
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
      (!id b sz.
        id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
        i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule window_array_pre_root >> strip_tac >>
  qpat_x_assum `at = _` SUBST_ALL_TAC >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  `fn_has_code st en func /\
   abi_encoder_admissible (AbiDynArray ei asz msz active)` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     asm_rewrite_tac[]) >>
  drule_all abi_encode_array_context >> strip_tac >>
  drule_all window_array_loop_context >> strip_tac >>
  PairCases_on `ops` >>
  rename1 `abi_encode_array_prefix src dst st = ((pp,count_op),loop_st)` >>
  full_simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
  drule window_array_loop_code_bounds >> strip_tac >>
  `owner.cs_next_id <= en.cs_next_id` by decide_tac >>
  `~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts` by
    (qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_window_pre_def] >> strip_tac >>
     asm_rewrite_tac[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
    metis_tac[window_array_prefix_alloca_member] >>
  `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (irule window_array_alloca_site >>
     conj_tac >- decide_tac >>
     simp_tac bool_ss [LESS_EQ_REFL] >>
     qexists_tac `STRING #"%" (toString st.cs_next_var)` >>
     asm_rewrite_tac[]) >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
     (Array NONE ty) (ListV avs) sb cap s.vs_memory` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     asm_rewrite_tac[]) >>
  `32 <= cap /\ 32 <= LENGTH (enc (Array NONE ty) (ListV avs))` by
    (conj_tac
     >- (qpat_assum `abi_encoder_window_input _ _ _ _ _ _` mp_tac >>
         simp_tac (srw_ss()) [abi_encoder_window_array_iff] >>
         rpt strip_tac) >>
     drule window_array_layout >> strip_tac >> decide_tac) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     mem_word_at sb mem = n2w (LENGTH avs)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!mem. _ ==> abi_encoder_window_input _ _ _ _ _ mem`
       drule >>
     simp_tac (srw_ss()) [abi_encoder_window_array_iff]) >>
  `!i. sb <= i /\ i < sb + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_mem_word_at_clean] >>
  `(?p. src = Var p /\ ptr_covers G tn p s 32) /\
   (?p. dst = Var p /\ ptr_covers G tn p s 32)` by
    (conj_tac
     >- (qexists_tac `p` >> asm_rewrite_tac[] >>
         qpat_assum `ptr_covers G tn p s cap` mp_tac >>
         simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >>
         asm_rewrite_tac[] >>
         qexistsl_tac [`w`, `b`, `sz'`] >> asm_rewrite_tac[] >> decide_tac) >>
     qexists_tac `p'` >> asm_rewrite_tac[] >>
     qpat_assum `ptr_covers G tn p' s _` mp_tac >>
     simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >>
     asm_rewrite_tac[] >>
     qexistsl_tac [`w`, `b`, `sz'`] >> asm_rewrite_tac[] >> decide_tac) >>
  drule window_array_root_prefix_joint_strong >>
  disch_then (qspec_then `tn` mp_tac) >>
  disch_then drule >>
  disch_then (qspecl_then [`lo`, `explicit`, `PG`, `G`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
  strip_tac >>
  rename1 `window_phase ctx func st loop_st _ _ s prefix_s` >>
  rename1 `ptr_covers prefix_G prefix_tn _ prefix_s 32` >>
  `?index_en. abi_decode_index_init loop_st = (ip,index_en) /\
     fn_has_code loop_st index_en func /\
     index_en.cs_next_id = loop_st.cs_next_id + 2 /\
     index_en.cs_next_var = loop_st.cs_next_var + 1 /\
     (if active then abi_encode_array_tail_init count_op asz index_en = (dp,owner) /\
        fn_has_code index_en owner func
      else index_en = owner)` by
    (Cases_on `active` >> full_simp_tac bool_ss []
     >- (drule_all abi_encode_array_dynamic_init_context >> strip_tac >>
         full_simp_tac (srw_ss()) [] >> metis_tac[]) >>
     drule abi_decode_index_init_shape >> strip_tac >>
     qexists_tac `owner` >> asm_rewrite_tac[]) >>
  `?index_mid. emit_op ALLOCA [Lit 32w] loop_st = (ip,index_mid) /\
     emit_void MSTORE [ip;Lit 0w] index_mid = ((),index_en)` by
    (qpat_assum `abi_decode_index_init loop_st = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     Cases_on `emit_op ALLOCA [Lit 32w] loop_st` >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `MEM (mk_inst loop_st.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString loop_st.cs_next_var)]) (fn_insts func)` by
    metis_tac[window_array_index_alloca_member] >>
  `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (irule window_array_alloca_site >>
     conj_tac >- decide_tac >>
     conj_tac >- (Cases_on `active` >> full_simp_tac bool_ss [] >> decide_tac) >>
     qexists_tac `STRING #"%" (toString loop_st.cs_next_var)` >>
     asm_rewrite_tac[]) >>
  `alloca_inv prefix_s /\ alloca_room ctx func prefix_s /\
   ~prefix_s.vs_halted /\ prefix_s.vs_current_bb = loop_st.cs_current_bb /\
   prefix_s.vs_inst_idx = LENGTH loop_st.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  `!b sz. FLOOKUP prefix_s.vs_allocas loop_st.cs_next_id = SOME (b,sz) ==>
    sz = 32` by
    (qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ prefix_s` mp_tac >>
     simp_tac bool_ss [window_array_root_def, window_sizes32_def] >>
     rpt strip_tac >> metis_tac[]) >>
  drule window_cursor_init_joint >>
  disch_then (qspecl_then [`0w`, `Lit 0w`, `prefix_tn`] mp_tac) >>
  disch_then drule >>
  disch_then (qspec_then `prefix_s` mp_tac) >>
  disch_then drule >>
  disch_then (qspecl_then [`lo`, `explicit`, `ctx`, `PG`, `prefix_G`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >>
    simp_tac (srw_ss()) [eval_operand_def, op_taint_def]) >>
  strip_tac >>
  rename1 `window_phase ctx func loop_st index_en _ _ prefix_s index_s` >>
  rename1 `ptr_covers index_G index_tn _ index_s 32` >>
  `window_array_transition ctx func loop_st {loop_st.cs_next_id} [] prefix_s index_s` by
    (qpat_assum `window_phase ctx func loop_st index_en _ _ prefix_s index_s` mp_tac >>
     qpat_assum `FLOOKUP index_s.vs_allocas loop_st.cs_next_id = SOME (_,32)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_phase_def, window_array_transition_def] >>
     rpt strip_tac >> asm_rewrite_tac[] >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_registered_effect_def, window_sizes32_def] >>
     rpt strip_tac >> Cases_on `i = loop_st.cs_next_id` >>
     full_simp_tac (srw_ss()) [window_sizes32_def] >> metis_tac[]) >>
  `window_array_root ctx func loop_st (window_alloca_sites func (frag_ids st en))
     ei asz msz active ty avs src dst sb cap d prefix_s` by
    (irule window_array_root_owner_mono >>
     qexists_tac `st` >> asm_rewrite_tac[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  `window_array_root ctx func loop_st (window_alloca_sites func (frag_ids st en))
     ei asz msz active ty avs src dst sb cap d index_s` by
    (irule window_array_root_transition >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[SUBSET_DEF]) >>
  `window_array_root ctx func index_en (window_alloca_sites func (frag_ids st en))
     ei asz msz active ty avs src dst sb cap d index_s` by
    (irule window_array_root_owner_mono >>
     qexists_tac `loop_st` >> asm_rewrite_tac[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  `eval_operand count_op index_s = SOME (n2w (LENGTH avs))` by
    metis_tac[window_phase_operand] >>
  `!x. count_op = Var x ==> not_fresh_at index_en x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD] >>
  `op_taint index_tn count_op = {}` by
    (Cases_on `count_op` >>
     qpat_assum `index_tn.t_var = _` mp_tac >>
     qpat_assum `op_taint prefix_tn _ = {}` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [op_taint_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
  `op_prov index_G count_op = NONE` by
    (Cases_on `count_op` >> simp_tac (srw_ss()) [op_prov_def] >>
     qpat_assum `index_G = _` mp_tac >>
     qpat_assum `op_prov prefix_G _ = NONE` mp_tac >>
     qpat_assum `!x. Var _ = Var x ==> not_fresh_at loop_st x` mp_tac >>
     qpat_assum `ip = Var _` mp_tac >>
     qpat_assum `emit_op ALLOCA [Lit 32w] loop_st = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     fs[op_prov_def, not_fresh_at_def, FLOOKUP_UPDATE] >>
     metis_tac[LESS_EQ_REFL]) >>
  `active ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
    (strip_tac >>
     `MEM (mk_inst (loop_st.cs_next_id+2) ALLOCA [Lit 32w]
       [STRING #"%" (toString (loop_st.cs_next_var+1))]) (fn_insts func)` by
       (qpat_assum `if active then abi_encode_array_dynamic_init _ _ _ = _ else _` mp_tac >>
        qpat_assum `fn_has_code loop_st owner func` mp_tac >>
        qpat_assum `active` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [] >> rpt strip_tac >>
        drule_all window_array_dynamic_alloca_members >> simp[]) >>
     irule window_array_alloca_site >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     qexists_tac `STRING #"%" (toString (loop_st.cs_next_var+1))` >>
     metis_tac[]) >>
  `active ==> fn_has_code index_en owner func` by
    (qpat_assum `if active then abi_encode_array_tail_init _ _ _ = _ /\ _ else _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >> simp[]) >>
  `active ==> ?tail_s b p tail_G tail_tn.
    window_phase ctx func index_en owner {index_en.cs_next_id} [] index_s tail_s /\
    window_array_transition ctx func index_en {index_en.cs_next_id} [] index_s tail_s /\
    window_array_root ctx func index_en (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst sb cap d tail_s /\
    window_array_cursor T owner dp index_en.cs_next_id b
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) tail_s /\
    abi_encode_exec_frame func index_s tail_s /\
    dp = Var p /\ ptr_covers tail_G tail_tn p tail_s 32 /\
    allocas_from lo tail_s /\ lo <= tail_s.vs_alloca_next /\
    (!x. not_fresh_at index_en x ==>
      FLOOKUP tail_G x = FLOOKUP index_G x /\
      op_taint tail_tn (Var x) = op_taint index_tn (Var x)) /\
    tail_tn.t_mem = index_tn.t_mem DIFF {i | b <= i /\ i < b + 32} /\
    tail_tn.t_stor = index_tn.t_stor /\
    tail_tn.t_trans = index_tn.t_trans /\
    tail_tn.t_imm = index_tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (index_s,index_G,index_tn) [] (OK tail_s,tail_G,tail_tn)` by
    (strip_tac >>
     `abi_encode_array_tail_init count_op asz index_en = (dp,owner)` by
       (qpat_assum `if active then abi_encode_array_tail_init _ _ _ = _ /\ _ else _` mp_tac >>
        qpat_assum `active` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `~index_s.vs_halted /\ index_s.vs_current_bb = index_en.cs_current_bb /\
      index_s.vs_inst_idx = LENGTH index_en.cs_current_insts` by
       metis_tac[window_phase_control] >>
     drule window_array_root_tail_init_joint >>
     disch_then drule >>
     disch_then (qspecl_then [`index_tn`, `lo`, `explicit`, `PG`, `index_G`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> metis_tac[]) >>
     strip_tac >>
     rename1 `window_array_cursor T owner dp index_en.cs_next_id tail_b _ _ _ _ _ tail_s` >>
     rename1 `ptr_covers tail_G tail_tn tail_p tail_s 32` >>
     qexistsl_tac [`tail_s`, `tail_b`, `tail_p`, `tail_G`, `tail_tn`] >>
     asm_rewrite_tac[]) >>
  `?init_s init_G init_tn bd.
    window_array_transition ctx func index_en
      (if active then {index_en.cs_next_id} else {}) [] index_s init_s /\
    window_array_root ctx func index_en (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst sb cap d init_s /\
    window_array_cursor active owner dp (if active then index_en.cs_next_id else 0) bd
      (LENGTH avs * abi_member_head_size ty) sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) init_s /\
    abi_encode_exec_frame func index_s init_s /\
    (active ==> ?q. dp = Var q /\ ptr_covers init_G init_tn q init_s 32) /\
    ~init_s.vs_halted /\ init_s.vs_current_bb = owner.cs_current_bb /\
    init_s.vs_inst_idx = LENGTH owner.cs_current_insts /\
    allocas_from lo init_s /\ lo <= init_s.vs_alloca_next /\
    (!x. not_fresh_at index_en x ==>
      FLOOKUP init_G x = FLOOKUP index_G x /\
      op_taint init_tn (Var x) = op_taint index_tn (Var x)) /\
    init_tn.t_mem = index_tn.t_mem DIFF
      (if active then {i | bd <= i /\ i < bd + 32} else {}) /\
    init_tn.t_stor = index_tn.t_stor /\
    init_tn.t_trans = index_tn.t_trans /\
    init_tn.t_imm = index_tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (index_s,index_G,index_tn) [] (OK init_s,init_G,init_tn)` by
    (Cases_on `active`
     >- (qpat_x_assum `T ==> ?tail_s b p tail_G tail_tn. _` mp_tac >>
         simp_tac bool_ss [] >> strip_tac >>
         rename1 `window_array_cursor T owner dp index_en.cs_next_id tail_b _ _ _ _ _ tail_s` >>
         rename1 `ptr_covers tail_G tail_tn tail_p tail_s 32` >>
         qexistsl_tac [`tail_s`, `tail_G`, `tail_tn`, `tail_b`] >>
         asm_rewrite_tac[] >> metis_tac[window_phase_control]) >>
     `index_en = owner` by
       (qpat_assum `if F then abi_encode_array_tail_init _ _ _ = _ /\ _ else _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `~index_s.vs_halted /\ index_s.vs_current_bb = owner.cs_current_bb /\
      index_s.vs_inst_idx = LENGTH owner.cs_current_insts` by
       metis_tac[window_phase_control] >>
     qexistsl_tac [`index_s`, `index_G`, `index_tn`, `0`] >>
     simp_tac bool_ss [COND_CLAUSES, DIFF_EMPTY, window_array_cursor_def,
       abi_encode_exec_frame_refl] >>
     asm_rewrite_tac[] >> conj_tac
     >- (irule window_array_transition_refl >> metis_tac[window_phase_resources,
           window_phase_control]) >>
     gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >>
     metis_tac[window_phase_control]) >>
  `index_en.cs_next_var <= owner.cs_next_var` by
    (Cases_on `active` >> asm_rewrite_tac[] >> decide_tac) >>
  `window_array_root ctx func owner (window_alloca_sites func (frag_ids st en))
    ei asz msz active ty avs src dst sb cap d init_s` by
    (irule window_array_root_owner_mono >> qexists_tac `index_en` >>
     asm_rewrite_tac[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand count_op init_s = SOME (n2w (LENGTH avs))` by
    (irule window_array_transition_eval >> goal_assum (drule_at Any) >>
     asm_rewrite_tac[]) >>
  `op_taint init_tn count_op = {}` by
    (qpat_assum `!x. not_fresh_at index_en x ==> _ /\ _` mp_tac >>
     qpat_assum `!x. count_op = Var x ==> not_fresh_at index_en x` mp_tac >>
     qpat_assum `op_taint index_tn count_op = {}` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `count_op` >>
     simp_tac (srw_ss()) [op_taint_def] >> metis_tac[]) >>
  `op_prov init_G count_op = NONE` by
    (qpat_assum `!x. not_fresh_at index_en x ==> _ /\ _` mp_tac >>
     qpat_assum `!x. count_op = Var x ==> not_fresh_at index_en x` mp_tac >>
     qpat_assum `op_prov index_G count_op = NONE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `count_op` >>
     simp_tac (srw_ss()) [op_prov_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK index_s,index_G,index_tn)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (prefix_s,prefix_G,prefix_tn) _ _`
       (qspec_then `D` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK init_s,init_G,init_tn)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK index_s,index_G,index_tn)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (index_s,index_G,index_tn) _ _`
       (qspec_then `D` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  rename1 `FLOOKUP index_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` >>
  `window_array_cursor T index_en ip loop_st.cs_next_id bi 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) index_s` by
    (qpat_assum `window_array_root ctx func index_en _ _ _ _ _ _ _ _ _ _ _ _ index_s` mp_tac >>
     simp_tac bool_ss [window_array_root_def] >> strip_tac >>
     simp_tac bool_ss [window_array_cursor_def] >> asm_rewrite_tac[] >>
     conj_tac >- simp[] >>
     qpat_assum `!id b sz. id IN _ /\ FLOOKUP index_s.vs_allocas id = SOME (b,sz) ==> _` mp_tac >>
     qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `FLOOKUP index_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `window_array_cursor T index_en ip loop_st.cs_next_id bi 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) init_s` by
    (irule window_array_cursor_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     Cases_on `active` >> simp_tac (srw_ss()) [EVERY_DEF] >> decide_tac) >>
  `window_array_cursor T owner ip loop_st.cs_next_id bi 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) init_s` by
    (irule window_array_cursor_owner_mono >> goal_assum (drule_at Any) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `abi_encoder_array_prefix ty avs 0 d index_s.vs_memory` by
    (qpat_assum `window_array_root ctx func loop_st _ _ _ _ _ _ _ _ _ _ _ _ prefix_s` mp_tac >>
     qpat_assum `abi_encoder_array_prefix ty avs 0 d prefix_s.vs_memory` mp_tac >>
     qpat_assum `window_array_transition ctx func loop_st _ [] prefix_s index_s` mp_tac >>
     qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule abiEncoderWindowArrayEntryTheory.window_array_root_prefix_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[SUBSET_DEF]) >>
  `abi_encoder_array_prefix ty avs 0 d init_s.vs_memory` by
    (qpat_assum `window_array_root ctx func index_en _ _ _ _ _ _ _ _ _ _ _ _ index_s` mp_tac >>
     qpat_assum `abi_encoder_array_prefix ty avs 0 d index_s.vs_memory` mp_tac >>
     qpat_assum `window_array_transition ctx func index_en _ [] index_s init_s` mp_tac >>
     qpat_assum `active ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule abiEncoderWindowArrayEntryTheory.window_array_root_prefix_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     Cases_on `active` >> gvs[SUBSET_DEF]) >>
  `!x. count_op = Var x ==> not_fresh_at owner x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `~init_s.vs_halted /\ init_s.vs_current_bb = owner.cs_current_bb /\
    init_s.vs_inst_idx = LENGTH owner.cs_current_insts` by
    metis_tac[window_phase_control] >>
  drule_all abiEncoderWindowArrayEntryTheory.window_array_entry_header_run >>
  strip_tac >>
  `!D. ptr_safe_step D lo 0 ctx func PG init_G init_tn
    (mk_inst owner.cs_next_id JMP [Label (FST labels)] []) init_s` by
    (gen_tac >>
     qpat_assum `allocas_from lo init_s` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[ptrSafeRunTheory.ptr_safe_step_def, ptrSafeRunTheory.ptr_inst_ok_def,
       access_ok_def, taint_ok_def, mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, venomExecProofsTheory.step_jmp_behavior, jump_to_def]) >>
  `lookup_block init_s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := owner.cs_current_bb; bb_instructions := owner.cs_current_insts ++
      [mk_inst owner.cs_next_id JMP [Label (FST labels)] []]|>` by
    (qpat_assum `abi_encoder_array_loop_code func owner _ _ _ _ _ _` mp_tac >>
     qpat_assum `init_s.vs_current_bb = owner.cs_current_bb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encoder_array_loop_code_def] >> metis_tac[]) >>
  `get_instruction
    <|bb_label := owner.cs_current_bb; bb_instructions := owner.cs_current_insts ++
      [mk_inst owner.cs_next_id JMP [Label (FST labels)] []]|>
    init_s.vs_inst_idx = SOME (mk_inst owner.cs_next_id JMP [Label (FST labels)] [])` by
    (qpat_assum `init_s.vs_inst_idx = LENGTH owner.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  `mem_safe_step 0 ctx
    (mk_inst owner.cs_next_id JMP [Label (FST labels)] []) init_s` by
    (rpt (pop_assum kall_tac) >>
     simp[memSafeRunTheory.mem_safe_step_def,
      unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  `!fuel. step_inst fuel ctx
    (mk_inst owner.cs_next_id JMP [Label (FST labels)] []) init_s =
      OK (jump_to (FST labels) init_s)` by
    (rpt (pop_assum kall_tac) >> gen_tac >>
     simp[step_inst_non_invoke, mk_inst_def,
       venomExecProofsTheory.step_jmp_behavior]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
    (init_s,init_G,init_tn) []
    (OK (jump_to (FST labels) init_s),init_G,init_tn)` by
    (gen_tac >>
     qpat_assum `!D. ptr_safe_step D _ _ _ _ _ _ _ _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `mem_safe_step 0 ctx _ init_s` mp_tac >>
     qpat_assum `!fuel. step_inst fuel ctx _ init_s = _` mp_tac >>
     qpat_assum `lookup_block init_s.vs_current_bb _ = SOME _` mp_tac >>
     qpat_assum `get_instruction _ init_s.vs_inst_idx = SOME _` mp_tac >>
     qpat_assum `~init_s.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[gas_origin_ptr_edge_def, fragGasOriginTheory.gas_origin_edge_def,
       fragGasPathPtrTheory.gas_path_ptr_edge_def] >>
     conj_tac >> qexists_tac `0` >>
     simp[gasEventsTheory.gas_events_step_def, gasCountTheory.gas_count_step_def,
       mk_inst_def, is_terminator_def] >>
     metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (init_s,init_G,init_tn) []
    (OK (jump_to (FST labels) init_s),init_G,init_tn)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_edge _ _ _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `~init_s.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `~(jump_to (FST labels) init_s).vs_halted` by simp[jump_to_def] >>
     metis_tac[gas_origin_ptr_path_rules, APPEND]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (jump_to (FST labels) init_s),init_G,init_tn)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK init_s,init_G,init_tn)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (init_s,init_G,init_tn) _ _`
       (qspec_then `D` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  `mem_bytes_at sb cap prefix_s.vs_memory = mem_bytes_at sb cap s.vs_memory` by
    (qpat_assum `window_phase ctx func st loop_st _ _ s prefix_s` mp_tac >>
     qpat_assum `window_array_root ctx func loop_st _ _ _ _ _ _ _ _ _ _ _ _ prefix_s` mp_tac >>
     qpat_assum `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule abi_encoder_window_effect_bytes >>
     drule window_phase_effect >> strip_tac >>
     goal_assum (drule_at Any) >>
     gvs[window_array_root_def, SUBSET_DEF] >>
     conj_tac >- metis_tac[] >>
     gvs[regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at sb cap index_s.vs_memory = mem_bytes_at sb cap prefix_s.vs_memory` by
    (qpat_assum `window_array_transition ctx func loop_st _ _ prefix_s index_s` mp_tac >>
     qpat_assum `window_array_root ctx func index_en _ _ _ _ _ _ _ _ _ _ _ _ index_s` mp_tac >>
     qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule abi_encoder_window_effect_bytes >>
     drule window_array_transition_effect >> strip_tac >>
     goal_assum (drule_at Any) >>
     gvs[window_array_root_def] >> metis_tac[]) >>
  `mem_bytes_at sb cap init_s.vs_memory = mem_bytes_at sb cap index_s.vs_memory` by
    (qpat_assum `window_array_transition ctx func index_en _ [] index_s init_s` mp_tac >>
     qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ init_s` mp_tac >>
     qpat_assum `active ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule abi_encoder_window_effect_bytes >>
     drule window_array_transition_effect >> strip_tac >>
     goal_assum (drule_at Any) >>
     gvs[window_array_root_def] >> Cases_on `active` >> gvs[] >> metis_tac[]) >>
  `!a. sb <= a /\ a < sb + cap ==>
    (a IN prefix_tn.t_mem <=> a IN tn.t_mem)` by
    (qpat_assum `prefix_tn.t_mem = _` mp_tac >>
     qpat_assum `window_array_cursor T loop_st pp st.cs_next_id _ _ _ _ _ _ prefix_s` mp_tac >>
     qpat_assum `window_array_root ctx func loop_st _ _ _ _ _ _ _ _ _ _ _ _ prefix_s` mp_tac >>
     qpat_assum `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [window_array_cursor_def, window_array_root_def,
       regions_disjoint_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `!a. sb <= a /\ a < sb + cap ==>
    (a IN index_tn.t_mem <=> a IN prefix_tn.t_mem)` by
    (qpat_assum `index_tn.t_mem = _` mp_tac >>
     qpat_assum `window_array_cursor T index_en ip loop_st.cs_next_id bi _ _ _ _ _ index_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [window_array_cursor_def, regions_disjoint_def] >>
     rpt strip_tac >> simp[] >> decide_tac) >>
  `!a. sb <= a /\ a < sb + cap ==>
    (a IN init_tn.t_mem <=> a IN index_tn.t_mem)` by
    (qpat_assum `init_tn.t_mem = _` mp_tac >>
     qpat_assum `window_array_cursor active owner dp _ bd _ _ _ _ _ init_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >>
     simp_tac (srw_ss()) [window_array_cursor_def, regions_disjoint_def] >>
     rpt strip_tac >> simp[] >> decide_tac) >>
  `!mem. mem_agree_outside init_tn.t_mem init_s.vs_memory mem ==>
    abi_encoder_window_input (AbiDynArray ei asz msz active)
      (Array NONE ty) (ListV avs) sb cap mem` by
    (qpat_assum `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> abi_encoder_window_input _ _ _ _ _ mem` mp_tac >>
     qpat_assum `!a. sb <= a /\ a < sb + cap ==> (a IN prefix_tn.t_mem <=> _)` mp_tac >>
     qpat_assum `!a. sb <= a /\ a < sb + cap ==> (a IN index_tn.t_mem <=> _)` mp_tac >>
     qpat_assum `!a. sb <= a /\ a < sb + cap ==> (a IN init_tn.t_mem <=> _)` mp_tac >>
     qpat_assum `mem_bytes_at sb cap init_s.vs_memory = _` mp_tac >>
     qpat_assum `mem_bytes_at sb cap index_s.vs_memory = _` mp_tac >>
     qpat_assum `mem_bytes_at sb cap prefix_s.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `mem_bytes_at sb cap init_s.vs_memory = mem_bytes_at sb cap s.vs_memory` by metis_tac[] >>
     `!i. i < cap ==> (sb+i IN init_tn.t_mem <=> sb+i IN tn.t_mem)` by
       (rpt strip_tac >> `sb <= sb+i /\ sb+i < sb+cap` by decide_tac >> metis_tac[]) >>
     drule_all copied_window_agree_witness >>
     disch_then (qx_choose_then `mix` strip_assume_tac) >>
     `abi_encoder_window_input (AbiDynArray ei asz msz active)
       (Array NONE ty) (ListV avs) sb cap mix` by metis_tac[] >>
     drule abi_encoder_window_input_mem_agree >>
     disch_then irule >> asm_rewrite_tac[]) >>
  `!x. not_fresh_at st x ==>
    FLOOKUP init_G x = FLOOKUP G x /\
    op_taint init_tn (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at st x ==> FLOOKUP prefix_G x = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at index_en x ==> FLOOKUP init_G x = _ /\ _` mp_tac >>
     qpat_assum `index_G = _` mp_tac >>
     qpat_assum `index_tn.t_var = _` mp_tac >>
     qpat_assum `ip = Var _` mp_tac >>
     qpat_assum `loop_st.cs_next_var = st.cs_next_var + 2` mp_tac >>
     qpat_assum `index_en.cs_next_var = loop_st.cs_next_var + 1` mp_tac >>
     qpat_assum `emit_op ALLOCA [Lit 32w] loop_st = (ip,index_mid)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def, op_taint_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     `x <> STRING #"%" (toString loop_st.cs_next_var)` by
       (strip_tac >> gvs[]) >>
     metis_tac[]) >>
  `abi_encode_exec_frame func s (jump_to (FST labels) init_s)` by
    (qpat_assum `abi_encode_exec_frame func s prefix_s` mp_tac >>
     qpat_assum `abi_encode_exec_frame func prefix_s index_s` mp_tac >>
     qpat_assum `abi_encode_exec_frame func index_s init_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[jump_to_def, abi_encode_exec_frame_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def] >>
     rpt strip_tac >> gvs[]) >>
  `!mem. mem_agree_outside init_tn.t_mem
      (jump_to (FST labels) init_s).vs_memory mem ==>
    abi_encoder_window_input (AbiDynArray ei asz msz active)
      (Array NONE ty) (ListV avs) sb cap mem` by
    (qpat_assum `!mem. mem_agree_outside init_tn.t_mem init_s.vs_memory mem ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[jump_to_def]) >>
  `(?q. src = Var q /\ ptr_covers init_G init_tn q (jump_to (FST labels) init_s) cap) /\
   (?q. dst = Var q /\ ptr_covers init_G init_tn q (jump_to (FST labels) init_s)
     (LENGTH (enc (Array NONE ty) (ListV avs))))` by
    (qpat_assum `ptr_covers G tn p s cap` mp_tac >>
     qpat_assum `ptr_covers G tn p' s _` mp_tac >>
     qpat_assum `src = Var p` mp_tac >> qpat_assum `dst = Var p'` mp_tac >>
     qpat_assum `window_array_root ctx func st _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ init_s` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP init_G x = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[window_array_root_def, ptr_covers_def, eval_operand_def,
       lookup_var_def, jump_to_def] >> metis_tac[]) >>
  `?q. ip = Var q /\ ptr_covers init_G init_tn q init_s 32` by
    (qpat_assum `ptr_covers index_G index_tn _ index_s 32` mp_tac >>
     qpat_assum `ip = Var _` mp_tac >>
     qpat_assum `not_fresh_at index_en _` mp_tac >>
     qpat_assum `!x. not_fresh_at index_en x ==> FLOOKUP init_G x = _ /\ _` mp_tac >>
     qpat_assum `window_array_cursor T owner ip _ bi _ _ _ _ _ init_s` mp_tac >>
     qpat_assum `eval_operand ip index_s = SOME (n2w bi)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[window_array_cursor_def, ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `window_array_cursor T loop_st pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) index_s` by
    (irule window_array_cursor_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[EVERY_DEF] >> decide_tac) >>
  `window_array_cursor T index_en pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) index_s` by
    (irule window_array_cursor_owner_mono >> goal_assum (drule_at Any) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  `window_array_cursor T index_en pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) init_s` by
    (irule window_array_cursor_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> Cases_on `active` >>
     simp_tac (srw_ss()) [EVERY_DEF] >> decide_tac) >>
  `?q. pp = Var q /\ ptr_covers init_G init_tn q init_s 32` by
    (qpat_assum `ptr_covers prefix_G prefix_tn _ prefix_s 32` mp_tac >>
     qpat_assum `pp = Var _` mp_tac >>

     qpat_assum `index_G = _` mp_tac >>
     qpat_assum `index_tn.t_var = _` mp_tac >>
     rpt (qpat_x_assum `ip = Var _` mp_tac) >>
     qpat_assum `emit_op ALLOCA [Lit 32w] loop_st = (ip,index_mid)` mp_tac >>
     qpat_assum `index_en.cs_next_var = loop_st.cs_next_var + 1` mp_tac >>
     qpat_assum `!x. not_fresh_at index_en x ==> FLOOKUP init_G x = _ /\ _` mp_tac >>
     qpat_assum `window_array_cursor T loop_st pp _ b _ _ _ _ _ prefix_s` mp_tac >>
     qpat_assum `window_array_cursor T index_en pp _ b _ _ _ _ _ init_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[window_array_cursor_def, ptr_covers_def, eval_operand_def,
       not_fresh_at_def, op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `(!i. b <= i /\ i < b + 32 ==> i NOTIN init_tn.t_mem) /\
   (!i. bi <= i /\ i < bi + 32 ==> i NOTIN init_tn.t_mem) /\
   (active ==> !i. bd <= i /\ i < bd + 32 ==> i NOTIN init_tn.t_mem)` by
    (qpat_assum `init_tn.t_mem = _` mp_tac >>
     qpat_assum `index_tn.t_mem = _` mp_tac >>
     qpat_assum `prefix_tn.t_mem = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[pred_setTheory.IN_DIFF, pred_setTheory.IN_UNION,
       pred_setTheory.GSPECIFICATION]) >>
  `(?q. pp = Var q /\ ptr_covers init_G init_tn q (jump_to (FST labels) init_s) 32) /\
   (?q. ip = Var q /\ ptr_covers init_G init_tn q (jump_to (FST labels) init_s) 32) /\
   (active ==> ?q. dp = Var q /\ ptr_covers init_G init_tn q (jump_to (FST labels) init_s) 32)` by
    (qpat_assum `pp = Var _` mp_tac >>
     qpat_assum `ptr_covers init_G init_tn _ init_s 32` mp_tac >>
     rpt (qpat_x_assum `ptr_covers init_G init_tn _ init_s 32` mp_tac) >>
     rpt (qpat_x_assum `ip = Var _` mp_tac) >>
     qpat_assum `active ==> ?q. dp = Var q /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [ptr_covers_def, eval_operand_def, lookup_var_def, jump_to_def] >>
     metis_tac[]) >>
  (* The finite iterator selects its runtime endpoint and ghosts together.
     The universal dead mask belongs inside each selected triple. *)
  `window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) (jump_to (FST labels) init_s)` by
    (`window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
        (LENGTH (enc (Array NONE ty) (ListV avs))) init_s` by
       (irule window_array_cursor_owner_mono >> qexists_tac `index_en` >>
        asm_rewrite_tac[] >> rpt strip_tac >> irule not_fresh_at_mono >>
        qexists_tac `index_en` >> asm_rewrite_tac[]) >>
     qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ init_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[window_array_cursor_def, jump_to_def, eval_operand_def, lookup_var_def]) >>
  qabbrev_tac `P = \k u. ?g nt.
    window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst ip loop_st.cs_next_id bi
      dp (if active then index_en.cs_next_id else 0) bd count_op (FST labels) sb cap d k u /\
    abi_encode_exec_frame func s u /\
    window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
      (LENGTH (enc (Array NONE ty) (ListV avs))) u /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    op_taint nt count_op = {} /\ op_prov g count_op = NONE /\
    (?q. pp = Var q /\ ptr_covers g nt q u 32) /\
    (!i. b <= i /\ i < b + 32 ==> i NOTIN nt.t_mem) /\
    (?q. ip = Var q /\ ptr_covers g nt q u 32) /\
    (!i. bi <= i /\ i < bi + 32 ==> i NOTIN nt.t_mem) /\
    (active ==> (?q. dp = Var q /\ ptr_covers g nt q u 32) /\
      (!i. bd <= i /\ i < bd + 32 ==> i NOTIN nt.t_mem)) /\
    (?q. src = Var q /\ ptr_covers g nt q u cap) /\
    (?q. dst = Var q /\ ptr_covers g nt q u
      (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!mem. mem_agree_outside nt.t_mem u.vs_memory mem ==>
      abi_encoder_window_input (AbiDynArray ei asz msz active)
        (Array NONE ty) (ListV avs) sb cap mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP g x = FLOOKUP G x /\ op_taint nt (Var x) = op_taint tn (Var x)) /\
    (!i. d <= i /\ i < d + 32 + k * abi_member_head_size ty ==>
      i NOTIN nt.t_mem) /\
    (!i. d + 32 + LENGTH avs * abi_member_head_size ty <= i /\
      i < d + 32 + LENGTH avs * abi_member_head_size ty +
        SUM (MAP (abi_member_tail_size ty) (TAKE k avs)) ==>
      i NOTIN nt.t_mem) /\
    (!i. (i < d \/ d + LENGTH (enc (Array NONE ty) (ListV avs)) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP u.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN nt.t_mem <=> i IN tn.t_mem)) /\
    nt.t_stor = tn.t_stor /\ nt.t_trans = tn.t_trans /\ nt.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,g,nt)` >>
  `P 0 (jump_to (FST labels) init_s)` by
    (simp_tac bool_ss [Abbr `P`] >>
     qexistsl_tac [`init_G`, `init_tn`] >>
     asm_rewrite_tac[] >>
     conj_tac >-
       (qpat_assum `allocas_from lo init_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[jump_to_def, ptrDisciplineTheory.allocas_from_def]) >>
     conj_tac >-
       (qpat_assum `lo <= init_s.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[jump_to_def]) >>
     simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES,
       arithmeticTheory.ADD_CLAUSES, listTheory.TAKE_0, listTheory.MAP,
       listTheory.SUM, pred_setTheory.IN_DIFF, pred_setTheory.IN_UNION,
       pred_setTheory.GSPECIFICATION] >>
     asm_rewrite_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (qpat_assum `active ==> ?q. dp = Var q /\ ptr_covers _ _ _ (jump_to _ _) 32` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >>
        rpt strip_tac >> asm_rewrite_tac[]) >>
     conj_tac >- (POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     qpat_assum `window_array_cursor T loop_st pp _ b _ _ _ _ _ prefix_s` mp_tac >>
     qpat_assum `window_array_cursor T owner ip _ bi _ _ _ _ _ init_s` mp_tac >>
     qpat_assum `window_array_cursor active _ dp _ bd _ _ _ _ _ init_s` mp_tac >>
     qpat_assum `window_array_transition ctx func loop_st _ [] prefix_s index_s` mp_tac >>
     qpat_assum `window_array_transition ctx func index_en _ [] index_s init_s` mp_tac >>
     qpat_assum `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `active ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_cursor_def, window_array_transition_def,
       abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] >>
     rpt strip_tac >>
     (qpat_x_assum `!id b sz. id IN _ /\ _ ==> _`
       (assume_tac o SIMP_RULE (srw_ss()) [jump_to_def]) >>
      `FLOOKUP init_s.vs_allocas st.cs_next_id = SOME (b,32)` by metis_tac[] >>
      (SUBGOAL_THEN ``i < b \/ b + 32 <= i`` assume_tac >-
        metis_tac[]) >>
      (SUBGOAL_THEN ``i < bi \/ bi + 32 <= i`` assume_tac >-
        metis_tac[]) >>
      (SUBGOAL_THEN ``active ==> i < bd \/ bd + 32 <= i`` assume_tac >-
        (Cases_on `active` >> metis_tac[])) >>
      (SUBGOAL_THEN ``i < d \/ d + LENGTH (enc (Array NONE ty) (ListV avs)) <= i``
        assume_tac >- decide_tac) >>
      qpat_assum `32 <= LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
      ntac 4 (pop_assum mp_tac) >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      Cases_on `active` >> simp_tac (srw_ss()) [] >>
      rpt strip_tac >> fs[]) ) >>
  `!k u. k <= LENGTH avs /\ P k u ==>
    window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u
      (jump_to (if k < LENGTH avs then FST (SND labels) else SND (SND labels))
        (abi_encode_array_header_state
          (STRING #"%" (toString owner.cs_next_var))
          (STRING #"%" (toString (owner.cs_next_var+1)))
          (STRING #"%" (toString (owner.cs_next_var+2))) k (LENGTH avs) u))` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `P k u` mp_tac >> simp_tac bool_ss [Abbr `P`] >> strip_tac >>
     qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
     qpat_assum `k <= LENGTH avs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule window_array_header_run >>
     fs[abi_encoder_array_loop_code_def, window_array_inv_def,
       window_array_cursor_def, window_array_root_def,
       abi_encoder_window_array_iff, contractABITheory.valid_length_def,
       venomStateTheory.mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
     conj_tac >- simp[not_fresh_at_def] >>
     asm_rewrite_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`count_op`, `owner.cs_next_id+1`, `ip`, `n2w bi`] >>
     asm_rewrite_tac[] >>
     conj_tac >- simp[] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  (* Header ghosts are selected from the input ghosts, before every D. *)
  `!k u hg ht.
    k <= LENGTH avs /\
    window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
      ei asz msz active ty avs src dst ip loop_st.cs_next_id bi
      dp (if active then index_en.cs_next_id else 0) bd count_op (FST labels) sb cap d k u /\
    allocas_from lo u /\ op_taint ht count_op = {} /\
    op_prov hg count_op = NONE /\
    (?q. ip = Var q /\ ptr_covers hg ht q u 32) /\
    (!i. bi <= i /\ i < bi + 32 ==> i NOTIN ht.t_mem) ==>
    ?jg jt.
      (!x. not_fresh_at owner x ==>
        FLOOKUP jg x = FLOOKUP hg x /\ op_taint jt (Var x) = op_taint ht (Var x)) /\
      jt.t_mem = ht.t_mem /\ jt.t_stor = ht.t_stor /\
      jt.t_trans = ht.t_trans /\ jt.t_imm = ht.t_imm /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,hg,ht) []
      (OK (jump_to (if k < LENGTH avs then FST (SND labels) else SND (SND labels))
        (abi_encode_array_header_state
          (STRING #"%" (toString owner.cs_next_var))
          (STRING #"%" (toString (owner.cs_next_var+1)))
          (STRING #"%" (toString (owner.cs_next_var+2))) k (LENGTH avs) u)),jg,jt)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [window_array_inv_def, window_array_cursor_def] >> strip_tac >>
     qabbrev_tac `iv = STRING #"%" (toString owner.cs_next_var)` >>
     qabbrev_tac `cmp = STRING #"%" (toString (owner.cs_next_var+1))` >>
     qabbrev_tac `done = STRING #"%" (toString (owner.cs_next_var+2))` >>
     qabbrev_tac `ld = mk_inst (owner.cs_next_id+1) MLOAD [ip] [iv]` >>
     qabbrev_tac `lt = mk_inst (owner.cs_next_id+2) LT [Var iv;count_op] [cmp]` >>
     qabbrev_tac `iz = mk_inst (owner.cs_next_id+3) ISZERO [Var cmp] [done]` >>
     qabbrev_tac `r1 = update_var iv (n2w k) u` >>
     qabbrev_tac `r2 = update_var cmp (bool_to_word (k < LENGTH avs)) r1` >>
     qabbrev_tac `r3 = update_var done (bool_to_word (~(k < LENGTH avs))) r2` >>
     qabbrev_tac `g1 = step_prov PG hg ld r1` >>
     qabbrev_tac `t1 = step_taint ld u r1 ht` >>
     qabbrev_tac `g2 = step_prov PG g1 lt r2` >>
     qabbrev_tac `t2 = step_taint lt r1 r2 t1` >>
     qabbrev_tac `g3 = step_prov PG g2 iz r3` >>
     qabbrev_tac `t3 = step_taint iz r2 r3 t2` >>
     `!x. not_fresh_at owner x ==> x <> iv /\ x <> cmp /\ x <> done` by
       (simp_tac (srw_ss()) [not_fresh_at_def, Abbr `iv`, Abbr `cmp`, Abbr `done`] >>
        metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
     `!x. not_fresh_at owner x ==>
       FLOOKUP g3 x = FLOOKUP hg x /\ op_taint t3 (Var x) = op_taint ht (Var x)` by
       (rpt strip_tac >>
        `x <> iv /\ x <> cmp /\ x <> done` by
          (qpat_assum `!x. not_fresh_at owner x ==> x <> iv /\ _` mp_tac >>
           qpat_assum `not_fresh_at owner x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        asm_simp_tac (srw_ss()) [Abbr `g3`, Abbr `g2`, Abbr `g1`,
          Abbr `t3`, Abbr `t2`, Abbr `t1`, step_prov_other_output,
          step_taint_other_output, Abbr `ld`, Abbr `lt`, Abbr `iz`, mk_inst_def]) >>
     `t3.t_stor = ht.t_stor /\ t3.t_trans = ht.t_trans /\ t3.t_imm = ht.t_imm` by
       simp_tac (srw_ss()) [Abbr `t3`, Abbr `t2`, Abbr `t1`,
         step_taint_nonmemory_frame, Abbr `ld`, Abbr `lt`, Abbr `iz`, mk_inst_def] >>
     `count_op <> Var iv` by
       (qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
        simp_tac (srw_ss()) [Abbr `iv`, not_fresh_at_def] >>
        disch_then (qspec_then `STRING #"%" (toString owner.cs_next_var)` mp_tac) >>
        simp_tac (srw_ss()) []) >>
     `mload bi u = n2w k` by
       (asm_rewrite_tac[venomStateTheory.mload_def] >>
        metis_tac[valueEncodingDefsTheory.mem_word_at_def]) >>
     `step_inst_base ld u = OK r1` by
       (simp_tac (srw_ss()) [Abbr `ld`, Abbr `r1`, step_inst_base_opcode_eqs, mk_inst_def,
         exec_read1_def] >> asm_rewrite_tac[] >>
        simp_tac (srw_ss()) [w2n_n2w] >>
        `bi MOD dimword(:256) = bi` by (irule arithmeticTheory.LESS_MOD >> asm_rewrite_tac[]) >>
        asm_rewrite_tac[]) >>
     `LENGTH avs < dimword (:256) /\ k < dimword (:256)` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
        qpat_assum `k <= LENGTH avs` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def] >> rpt strip_tac >>
        fs[abi_encoder_window_array_iff, contractABITheory.valid_length_def] >>
        decide_tac) >>
     `eval_operand count_op r1 = SOME (n2w (LENGTH avs))` by
       simp[Abbr `r1`, slot_copy_operand_update] >>
     `eval_operand (Var iv) r1 = SOME (n2w k)` by
       simp_tac (srw_ss()) [Abbr `r1`, slot_copy_operand_update] >>
     `step_inst_base lt r1 = OK r2` by
       (qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        qpat_assum `eval_operand count_op r1 = _` mp_tac >>
        qpat_assum `eval_operand (Var iv) r1 = _` mp_tac >>
        qpat_assum `LENGTH avs < dimword (:256)` mp_tac >>
        qpat_assum `k < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[Abbr `lt`, Abbr `r2`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, w2n_n2w]) >>
     `step_inst_base iz r2 = OK r3` by
       (qpat_assum `Abbrev (iz = _)` mp_tac >>
        qpat_assum `Abbrev (r3 = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[Abbr `iz`, Abbr `r3`, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure1_def, eval_operand_def, Abbr `r2`, lookup_var_update_var] >>
        Cases_on `k < LENGTH avs` >> simp[bool_to_word_def]) >>
     `run_inst_seq [ld;lt;iz] u = OK r3` by
       (qpat_assum `step_inst_base ld u = OK r1` mp_tac >>
        qpat_assum `step_inst_base lt r1 = OK r2` mp_tac >>
        qpat_assum `step_inst_base iz r2 = OK r3` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[exprLoweringPropsTheory.run_inst_seq_def]) >>
     `op_prov g1 (Var iv) = NONE` by
       simp_tac (srw_ss()) [Abbr `g1`, Abbr `ld`, step_prov_def,
         set_prov_def, out_prov_def, mk_inst_def, op_prov_def, FLOOKUP_DRESTRICT] >>
     `op_prov g1 count_op = NONE` by
       (qpat_assum `op_prov hg count_op = NONE` mp_tac >>
        qpat_assum `Abbrev (g1 = _)` mp_tac >>
        qpat_assum `Abbrev (ld = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        Cases_on `count_op` >>
        fs[Abbr `g1`, Abbr `ld`, step_prov_def, set_prov_def,
          out_prov_def, mk_inst_def, op_prov_def, FLOOKUP_DRESTRICT]) >>
     `op_taint t1 (Var iv) = {} /\ t1.t_mem = ht.t_mem /\
      t1.t_stor = ht.t_stor /\ t1.t_trans = ht.t_trans` by
       (qpat_assum `eval_operand ip u = SOME (n2w bi)`
          (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
        simp_tac (srw_ss()) [w2n_n2w] >>
        disch_then (qspecl_then [`ht`, `owner.cs_next_id+1`, `iv`] mp_tac) >>
        `bi MOD dimword (:256) = bi` by
          (irule arithmeticTheory.LESS_MOD >> asm_rewrite_tac[]) >>
        simp_tac (srw_ss()) [w2n_n2w] >> asm_rewrite_tac[] >>
        simp_tac (srw_ss()) [Abbr `t1`, Abbr `ld`, Abbr `r1`] >>
        asm_rewrite_tac[]) >>
     `t3.t_mem = ht.t_mem` by
       (qpat_assum `t1.t_mem = ht.t_mem` mp_tac >>
        qpat_assum `Abbrev (t2 = _)` mp_tac >>
        qpat_assum `Abbrev (t3 = _)` mp_tac >>
        qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (iz = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        qpat_assum `Abbrev (r3 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `new_site_bytes r1 r2 = {}` by
          simp[Abbr `r2`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
            EXTENSION, SF CONJ_ss] >>
        `new_site_bytes r2 r3 = {}` by
          simp[Abbr `r3`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
            EXTENSION, SF CONJ_ss] >>
        simp[Abbr `t3`, Abbr `t2`, Abbr `lt`, Abbr `iz`, step_taint_def,
          LET_THM, mem_taint_def, step_writes_def, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          range_bytes_def, written_taint_def]) >>
     `op_taint t1 count_op = {}` by
       (qpat_assum `op_taint ht count_op = {}` mp_tac >>
        qpat_assum `count_op <> Var iv` mp_tac >>
        qpat_assum `Abbrev (t1 = _)` mp_tac >>
        qpat_assum `Abbrev (ld = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        Cases_on `count_op` >>
        fs[Abbr `t1`, Abbr `ld`, step_taint_def, set_var_taint_def,
          op_taint_def, mk_inst_def, FLOOKUP_UPDATE]) >>
     `op_taint t2 (Var cmp) = {} /\ op_taint t3 (Var done) = {}` by
       (simp_tac (srw_ss()) [Abbr `t2`, Abbr `t3`, Abbr `lt`, Abbr `iz`,
         step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
         mk_inst_def, FLOOKUP_UPDATE, LET_THM] >>
        Cases_on `eval_operand (Var iv) r1` >>
        Cases_on `eval_operand (Var cmp) r2` >> simp_tac (srw_ss()) []) >>
     `!D j. ptr_inst_ok D lo 0 ctx func hg ht ld (u with vs_inst_idx := j)` by
       (rpt gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
        conj_tac >-
          (qpat_assum `allocas_from lo u` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
        qexists_tac `0` >>
        simp[] >> qpat_x_assum `ip = Var _` SUBST_ALL_TAC >>
        simp[Abbr `ld`, wordLoadStorePtrTheory.ptr_inst_ok_mload]) >>
     `!D j. ptr_inst_ok D lo 0 ctx func g1 t1 lt (r1 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_prov g1 (Var iv) = NONE` mp_tac >>
        qpat_assum `op_prov g1 count_op = NONE` mp_tac >>
        qpat_assum `op_taint t1 (Var iv) = {}` mp_tac >>
        qpat_assum `op_taint t1 count_op = {}` mp_tac >>
        qpat_assum `allocas_from lo u` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base lt r1 = OK r2` mp_tac >>
        qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (r1 = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base lt (r1 with vs_inst_idx := j) =
          OK (r2 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `lt`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ r1 = OK r2`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `lt`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >-
          (Cases_on `count_op` >> fs[op_prov_def, FLOOKUP_DEF]) >>
        conj_tac >- (rpt strip_tac >> metis_tac[]) >>
        fs[allocas_from_def, Abbr `r1`, update_var_def] >>
        simp[GSYM mk_inst_def, step_inst_non_invoke,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def] >>
        fs[Abbr `r2`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D j. ptr_inst_ok D lo 0 ctx func g2 t2 iz (r2 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint t2 (Var cmp) = {}` mp_tac >>
        qpat_assum `allocas_from lo u` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base iz r2 = OK r3` mp_tac >>
        qpat_assum `Abbrev (iz = _)` mp_tac >>
        qpat_assum `Abbrev (r1 = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        qpat_assum `Abbrev (r3 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base iz (r2 with vs_inst_idx := j) =
          OK (r3 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `iz`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ r2 = OK r3`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `iz`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        fs[allocas_from_def, Abbr `r1`, Abbr `r2`, update_var_def] >>
        simp[GSYM mk_inst_def, step_inst_non_invoke,
          instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def] >>
        fs[Abbr `r3`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `bi + 32 <= u.vs_alloca_next` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
        qpat_assum `FLOOKUP u.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def, alloca_inv_def,
          alloca_next_valid_def] >> metis_tac[]) >>
     `run_inst_seq_mem_ok [ld;lt;iz] u` by
       (qpat_assum `step_inst_base ld u = OK r1` mp_tac >>
        qpat_assum `step_inst_base lt r1 = OK r2` mp_tac >>
        qpat_assum `step_inst_base iz r2 = OK r3` mp_tac >>
        qpat_assum `bi + 32 <= u.vs_alloca_next` mp_tac >>
        qpat_assum `bi < dimword (:256)` mp_tac >>
        qpat_assum `eval_operand ip u = SOME (n2w bi)` mp_tac >>
        qpat_assum `Abbrev (ld = _)` mp_tac >>
        qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (iz = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
        simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def, Abbr `ld`, Abbr `lt`,
          Abbr `iz`, mk_inst_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, w2n_n2w]) >>
     `!D j. inst_seq_ptr D lo ctx func PG hg ht [ld;lt;iz]
       (u with vs_inst_idx := j) g3 t3` by
       (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func hg ht ld _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func g1 t1 lt _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func g2 t2 iz _` mp_tac >>
        qpat_assum `step_inst_base ld u = OK r1` mp_tac >>
        qpat_assum `step_inst_base lt r1 = OK r2` mp_tac >>
        qpat_assum `step_inst_base iz r2 = OK r3` mp_tac >>
        qpat_assum `Abbrev (ld = _)` mp_tac >>
        qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (iz = _)` mp_tac >>
        qpat_assum `Abbrev (g1 = _)` mp_tac >>
        qpat_assum `Abbrev (g2 = _)` mp_tac >>
        qpat_assum `Abbrev (g3 = _)` mp_tac >>
        qpat_assum `Abbrev (t1 = _)` mp_tac >>
        qpat_assum `Abbrev (t2 = _)` mp_tac >>
        qpat_assum `Abbrev (t3 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `ld`, Abbr `lt`, Abbr `iz`, mk_inst_def] >>
        simp[inst_seq_ptr_def, instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          Abbr `g1`, Abbr `g2`, Abbr `g3`, Abbr `t1`, Abbr `t2`, Abbr `t3`]) >>
     qabbrev_tac `jnz = mk_inst (owner.cs_next_id+4) JNZ
       [Var done;Label (SND (SND labels));Label (FST (SND labels))] []` >>
     qabbrev_tac `hbb = <|bb_label := FST labels;
       bb_instructions := [ld;lt;iz;jnz]|>` >>
     `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb` by
       (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
        qpat_assum `u.vs_current_bb = FST labels` mp_tac >>
        qpat_assum `Abbrev (iv = _)` mp_tac >>
        qpat_assum `Abbrev (cmp = _)` mp_tac >>
        qpat_assum `Abbrev (done = _)` mp_tac >>
        qpat_assum `Abbrev (ld = _)` mp_tac >>
        qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (iz = _)` mp_tac >>
        qpat_assum `Abbrev (jnz = _)` mp_tac >>
        qpat_assum `Abbrev (hbb = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
        simp[Abbr `hbb`, Abbr `ld`, Abbr `lt`, Abbr `iz`, Abbr `jnz`,
          Abbr `iv`, Abbr `cmp`, Abbr `done`,
          abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def]) >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,hg,ht) []
       (OK (r3 with vs_inst_idx := 3),g3,t3)` by
       (gen_tac >>
        qpat_assum `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb` mp_tac >>
        qpat_assum `~u.vs_halted` mp_tac >>
        qpat_assum `u.vs_inst_idx = 0` mp_tac >>
        qpat_assum `run_inst_seq [ld;lt;iz] u = OK r3` mp_tac >>
        qpat_assum `run_inst_seq_mem_ok [ld;lt;iz] u` mp_tac >>
        qpat_assum `!D j. inst_seq_ptr D lo ctx func PG hg ht [ld;lt;iz] _ g3 t3` mp_tac >>
        qpat_assum `Abbrev (ld = _)` mp_tac >>
        qpat_assum `Abbrev (lt = _)` mp_tac >>
        qpat_assum `Abbrev (iz = _)` mp_tac >>
        qpat_assum `Abbrev (hbb = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `inst_seq_ptr D lo ctx func PG hg ht [ld;lt;iz] u g3 t3` by
          (first_x_assum (qspecl_then [`D`, `u.vs_inst_idx`] mp_tac) >> simp[]) >>
        mp_tac (Q.SPECL [`[ld;lt;iz]`, `u`, `r3`, `hg`, `ht`, `g3`, `t3`,
          `ctx`, `func`, `hbb`] run_inst_seq_gas_origin_ptr_path) >>
        simp[Abbr `hbb`, Abbr `ld`, Abbr `lt`, Abbr `iz`, mk_inst_def,
          is_terminator_def, isPREFIX]) >>
     qabbrev_tac `hs = r3 with vs_inst_idx := 3` >>
     qabbrev_tac `target = if k < LENGTH avs then FST (SND labels)
       else SND (SND labels)` >>
     `eval_operand (Var done) hs = SOME (bool_to_word (~(k < LENGTH avs)))` by
       simp_tac (srw_ss()) [Abbr `hs`, Abbr `r3`, eval_operand_def,
         lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     `step_inst_base jnz hs = OK (jump_to target hs)` by
       (qpat_assum `eval_operand (Var done) hs = _` mp_tac >>
        qpat_assum `Abbrev (jnz = _)` mp_tac >>
        qpat_assum `Abbrev (target = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        mp_tac (Q.SPECL [`hs`, `Var done`,
          `SND (SND (labels:string#string#string))`,
          `FST (SND (labels:string#string#string))`, `owner.cs_next_id+4`,
          `bool_to_word (~(k < LENGTH (avs:abi_value list)))`]
          venomExecProofsTheory.step_jnz_behavior) >>
        simp[Abbr `jnz`, mk_inst_def] >>
        Cases_on `k < LENGTH avs` >> simp[bool_to_word_def, Abbr `target`]) >>
     `!D. ptr_inst_ok D lo 0 ctx func g3 t3 jnz hs` by
       (gen_tac >>
        qpat_assum `op_taint t3 (Var done) = {}` mp_tac >>
        qpat_assum `allocas_from lo u` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base jnz hs = OK (jump_to target hs)` mp_tac >>
        qpat_assum `Abbrev (jnz = _)` mp_tac >>
        qpat_assum `Abbrev (hs = _)` mp_tac >>
        qpat_assum `Abbrev (r1 = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        qpat_assum `Abbrev (r3 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `jnz`, mk_inst_def] >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
        conj_tac >-
          (gen_tac >> Cases_on `op` >> fs[op_taint_def] >> metis_tac[]) >>
        fs[allocas_from_def, Abbr `hs`, Abbr `r1`, Abbr `r2`, Abbr `r3`,
          update_var_def] >>
        simp[GSYM mk_inst_def, step_inst_non_invoke, jump_to_def] >>
        first_assum ACCEPT_TAC) >>
     `~hs.vs_halted /\ lookup_block hs.vs_current_bb func.fn_blocks = SOME hbb /\
       get_instruction hbb hs.vs_inst_idx = SOME jnz` by
       (qpat_assum `~u.vs_halted` mp_tac >>
        qpat_assum `lookup_block u.vs_current_bb func.fn_blocks = SOME hbb` mp_tac >>
        qpat_assum `Abbrev (hs = _)` mp_tac >>
        qpat_assum `Abbrev (hbb = _)` mp_tac >>
        qpat_assum `Abbrev (r1 = _)` mp_tac >>
        qpat_assum `Abbrev (r2 = _)` mp_tac >>
        qpat_assum `Abbrev (r3 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `hs`, Abbr `r1`, Abbr `r2`, Abbr `r3`, venomStateTheory.update_var_def,
          Abbr `hbb`, get_instruction_def]) >>
     `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (hs,g3,t3) []
       (OK (jump_to target hs),g3,t3)` by
       (gen_tac >>
        qpat_assum `~hs.vs_halted` mp_tac >>
        qpat_assum `lookup_block hs.vs_current_bb func.fn_blocks = SOME hbb` mp_tac >>
        qpat_assum `get_instruction hbb hs.vs_inst_idx = SOME jnz` mp_tac >>
        qpat_assum `step_inst_base jnz hs = OK (jump_to target hs)` mp_tac >>
        qpat_assum `!D. ptr_inst_ok D lo 0 ctx func g3 t3 jnz hs` mp_tac >>
        qpat_assum `Abbrev (jnz = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `jnz`, mk_inst_def] >>
        rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
        >- (rewrite_tac[fragGasOriginTheory.gas_origin_edge_def] >> simp[] >>
            qexists_tac `0` >>
            simp[step_inst_non_invoke, memSafeRunTheory.mem_safe_step_non_invoke] >>
            simp[mk_inst_def, gasEventsTheory.gas_events_step_def,
              unitTransformDefsTheory.inst_mem_below_frontier_def,
              memSafeRunTheory.inst_dload_in_section_def,
              contextCodegenRelTheory.source_memory_read_ranges_def,
              codegenRelTheory.source_memory_write_ranges_def, is_terminator_def] >>
            metis_tac[]) >>
        rewrite_tac[fragGasPathPtrTheory.gas_path_ptr_edge_def] >> simp[] >>
        qexists_tac `0` >>
        simp[step_inst_non_invoke, ptrSafeRunTheory.ptr_safe_step_def] >>
        simp[mk_inst_def, gasCountTheory.gas_count_step_def,
          is_terminator_def] >> metis_tac[]) >>
     qexistsl_tac [`g3`, `t3`] >> asm_rewrite_tac[] >> gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,hg,ht) [] _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_edge _ (hs,g3,t3) [] _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `~hs.vs_halted` mp_tac >>
     qpat_assum `Abbrev (hs = _)` mp_tac >>
     qpat_assum `Abbrev (target = _)` mp_tac >>
     qpat_assum `Abbrev (r1 = _)` mp_tac >>
     qpat_assum `Abbrev (r2 = _)` mp_tac >>
     qpat_assum `Abbrev (r3 = _)` mp_tac >>
     qpat_assum `Abbrev (iv = _)` mp_tac >>
     qpat_assum `Abbrev (cmp = _)` mp_tac >>
     qpat_assum `Abbrev (done = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (hs,g3,t3) []
       (OK (jump_to target hs),g3,t3)` by
       (`~(jump_to target hs).vs_halted` by simp[jump_to_def] >>
        metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,hg,ht) []
       (OK (jump_to target hs),g3,t3)` by
       (fs[Abbr `hs`] >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
     qpat_assum `gas_origin_ptr_path _ (u,hg,ht) [] _` mp_tac >>
     fs[Abbr `hs`, Abbr `target`, Abbr `r1`, Abbr `r2`, Abbr `r3`,
       Abbr `iv`, Abbr `cmp`, Abbr `done`, jump_to_def, update_var_def,
       abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def]) >>
  `!k u. k < LENGTH avs /\ P k u ==>
    ?v. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u v /\ P (SUC k) v` by
    (rpt gen_tac >> strip_tac >>
     `k <= LENGTH avs` by decide_tac >>
     qpat_assum `P k u` mp_tac >> simp_tac bool_ss [Abbr `P`] >>
     disch_then (qx_choose_then `kg` (qx_choose_then `kt` strip_assume_tac)) >>
     qpat_assum `!k u hg ht. _`
       (qspecl_then [`k`, `u`, `kg`, `kt`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >> asm_rewrite_tac[]) >>
     disch_then (qx_choose_then `hg` (qx_choose_then `ht` strip_assume_tac)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,kg,kt) [] _`
       (assume_tac o SIMP_RULE (srw_ss()) [ASSUME ``k < LENGTH (avs:abi_value list)``]) >>
     qmatch_assum_abbrev_tac
       `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,kg,kt) [] (OK hu,hg,ht)` >>
     `window_array_transition ctx func owner
       (window_alloca_sites func (frag_ids st en))
       [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u hu` by
       (qpat_assum `!k u. k <= LENGTH avs /\ P k u ==> _`
          (qspecl_then [`k`, `u`] mp_tac) >>
        impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
        qpat_assum `k < LENGTH avs` mp_tac >> qpat_assum `Abbrev (hu = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[Abbr `hu`] >> metis_tac[]) >>
     `window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
       ei asz msz active ty avs src dst ip loop_st.cs_next_id bi
       dp (if active then index_en.cs_next_id else 0) bd count_op
       (FST (SND labels)) sb cap d k hu` by
       (simp_tac bool_ss [Abbr `hu`] >> irule window_array_header_inv >>
        conj_tac >-
          (POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def] >>
           metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
        conj_tac >-
          (qexists_tac `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]` >>
           first_assum ACCEPT_TAC) >>
        qexists_tac `FST labels` >> first_assum ACCEPT_TAC) >>
     `hu.vs_memory = u.vs_memory /\ hu.vs_allocas = u.vs_allocas /\
      hu.vs_alloca_next = u.vs_alloca_next /\ abi_encode_exec_frame func u hu` by
       (qpat_assum `Abbrev (hu = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[Abbr `hu`, jump_to_def, abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
          update_var_def, abi_encode_exec_frame_def,
          exprLoweringPropsTheory.pending_alloca_size_def,
          exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def]) >>
     `allocas_from lo hu /\ lo <= hu.vs_alloca_next` by
       (qpat_assum `hu.vs_allocas = u.vs_allocas` mp_tac >>
        qpat_assum `hu.vs_alloca_next = u.vs_alloca_next` mp_tac >>
        qpat_assum `allocas_from lo u` mp_tac >> qpat_assum `lo <= u.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[allocas_from_def] >> metis_tac[]) >>
     `!root span. not_fresh_at owner root /\ ptr_covers kg kt root u span ==>
       ptr_covers hg ht root hu span` by
       (qx_genl_tac [`root`, `span`] >> strip_tac >>
        qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP hg x = _ /\ _` mp_tac >>
        qpat_assum `window_array_transition _ _ owner _ _ u hu` mp_tac >>
        qpat_assum `not_fresh_at owner root` mp_tac >>
        qpat_assum `ptr_covers kg kt root u span` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >>
        metis_tac[window_array_transition_vars]) >>
     `!mem. mem_agree_outside ht.t_mem hu.vs_memory mem ==>
       abi_encoder_window_input (AbiDynArray ei asz msz active)
         (Array NONE ty) (ListV avs) sb cap mem` by
       (qpat_assum `!mem. mem_agree_outside kt.t_mem u.vs_memory mem ==> _` mp_tac >>
        qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
        qpat_assum `hu.vs_memory = u.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK hu,hg,ht)` by
       (gen_tac >>
        qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,kg,kt)`
          (qspec_then `D` mp_tac) >>
        qpat_assum `!D. gas_origin_ptr_path _ (u,kg,kt) [] (OK hu,hg,ht)`
          (qspec_then `D` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
     `window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
       (LENGTH (enc (Array NONE ty) (ListV avs))) hu` by
       (irule window_array_cursor_word >>
        reverse conj_tac >-
          (goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
        asm_rewrite_tac[] >>
        qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ u` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[window_array_cursor_def]) >>
     qpat_assum `window_array_inv ctx func owner _ ei asz msz active ty avs src dst
       ip _ bi dp _ bd count_op _ sb cap d k hu`
       (strip_assume_tac o REWRITE_RULE [window_array_inv_def]) >>
     `(?q. src = Var q /\ ptr_covers hg ht q hu cap) /\
      (?q. dst = Var q /\ ptr_covers hg ht q hu
        (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
      (?q. ip = Var q /\ ptr_covers hg ht q hu 32) /\
      (?q. pp = Var q /\ ptr_covers hg ht q hu 32) /\
      (active ==> ?q. dp = Var q /\ ptr_covers hg ht q hu 32)` by
       (qpat_assum `!root span. _` mp_tac >>
        qpat_assum `window_array_root _ _ owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_cursor T owner ip _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_cursor active owner dp _ _ _ _ _ _ _ hu` mp_tac >>
        rpt (qpat_x_assum `ptr_covers kg kt _ u _` mp_tac) >>
        rpt (qpat_x_assum `src = Var _` mp_tac) >>
        rpt (qpat_x_assum `dst = Var _` mp_tac) >>
        rpt (qpat_x_assum `ip = Var _` mp_tac) >>
        rpt (qpat_x_assum `pp = Var _` mp_tac) >>
        qpat_assum `active ==> (?q. dp = Var q /\ _) /\ _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def, window_array_cursor_def] >>
        rpt strip_tac >> metis_tac[]) >>
     `?coords addressed.
       abi_encode_array_addresses ip src dst asz msz body_st = (coords,addressed) /\
       fn_has_code body_st addressed func /\
       addressed.cs_next_var = body_st.cs_next_var + 7 /\
       addressed.cs_next_id = body_st.cs_next_id + 7 /\
       addressed.cs_next_var <= body_end.cs_next_var /\
       addressed.cs_next_id <= body_end.cs_next_id` by
       (qpat_assum `if active then abi_encode_array_dynamic_body _ _ _ _ _ _ _ _ = _ else _` mp_tac >>
        qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
          mp_tac >>
        qpat_assum `abi_encoder_admissible (AbiDynArray ei asz msz active)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `active` >> simp_tac bool_ss [abi_encoder_array_loop_code_def,
          Once abiEncoderAdmissibleTheory.abi_encoder_admissible_def] >> rpt strip_tac
        >- (drule_all abiEncoderArrayDynamicMemoryTheory.abi_encode_array_dynamic_body_context >>
            strip_tac >> qexistsl_tac [`coords`, `addressed`] >>
            asm_rewrite_tac[] >> decide_tac) >>
        drule_all abi_encode_array_static_body_context >> strip_tac >>
        qexistsl_tac [`coords`, `prepared`] >> asm_rewrite_tac[]) >>
     `!x. not_fresh_at owner x ==> not_fresh_at body_st x` by
       (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
          mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
        irule not_fresh_at_mono >> qexists_tac `owner` >> asm_rewrite_tac[] >> decide_tac) >>
     `eval_operand ip hu = SOME (n2w bi) /\ bi < dimword (:256) /\
      mload bi hu = n2w k /\ eval_operand src hu = SOME (n2w sb) /\
      eval_operand dst hu = SOME (n2w d) /\
      (!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x)` by
       (qpat_assum `window_array_cursor T owner ip _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_root _ _ owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def, window_array_root_def,
          mload_def, valueEncodingDefsTheory.mem_word_at_def] >>
        rpt strip_tac >> metis_tac[]) >>
     `?raw. window_pure_seq body_st addressed hu raw /\
       eval_operand (FST (FST coords)) raw = SOME (n2w k) /\
       eval_operand (SND (FST coords)) raw = SOME (n2w (sb+32+k*msz)) /\
       eval_operand (FST (SND coords)) raw = SOME (n2w (d+32)) /\
       eval_operand (SND (SND coords)) raw = SOME (n2w (d+32+k*asz)) /\
       (!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/
         FST (SND coords) = Var x \/ SND (SND coords) = Var x ==>
         not_fresh_at addressed x) /\
       (!x. ~not_fresh_at addressed x ==> lookup_var x raw = lookup_var x hu)` by
       (mp_tac (Q.INST [`ip` |-> `ip:operand`, `src` |-> `src:operand`,
          `dst` |-> `dst:operand`, `asz` |-> `asz:num`, `msz` |-> `msz:num`,
          `st` |-> `body_st`, `en` |-> `addressed`,
          `coords` |-> `coords:((operand#operand)#(operand#operand))`,
          `s` |-> `hu:venom_state`, `slot` |-> `bi:num`, `j` |-> `k:num`,
          `sb` |-> `sb:num`, `d` |-> `d:num`] window_array_addresses_pure_observed) >>
        impl_tac >- asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
     rename1 `window_pure_seq body_st addressed hu araw` >>
     qabbrev_tac `a0 = STRING #"%" (toString body_st.cs_next_var)` >>
     qabbrev_tac `a1 = STRING #"%" (toString (body_st.cs_next_var+1))` >>
     qabbrev_tac `a2 = STRING #"%" (toString (body_st.cs_next_var+2))` >>
     qabbrev_tac `a3 = STRING #"%" (toString (body_st.cs_next_var+3))` >>
     qabbrev_tac `a4 = STRING #"%" (toString (body_st.cs_next_var+4))` >>
     qabbrev_tac `a5 = STRING #"%" (toString (body_st.cs_next_var+5))` >>
     qabbrev_tac `a6 = STRING #"%" (toString (body_st.cs_next_var+6))` >>
     `coords = ((Var a0,Var a3),(Var a4,Var a6)) /\
      emitted_insts body_st addressed =
       [mk_inst body_st.cs_next_id MLOAD [ip] [a0];
        mk_inst (body_st.cs_next_id+1) ADD [src;Lit 32w] [a1];
        mk_inst (body_st.cs_next_id+2) MUL [Var a0;Lit (n2w msz)] [a2];
        mk_inst (body_st.cs_next_id+3) ADD [Var a1;Var a2] [a3];
        mk_inst (body_st.cs_next_id+4) ADD [dst;Lit 32w] [a4];
        mk_inst (body_st.cs_next_id+5) MUL [Var a0;Lit (n2w asz)] [a5];
        mk_inst (body_st.cs_next_id+6) ADD [Var a4;Var a5] [a6]]` by
       (simp_tac bool_ss [Abbr `a0`, Abbr `a1`, Abbr `a2`, Abbr `a3`,
          Abbr `a4`, Abbr `a5`, Abbr `a6`] >>
        qpat_assum `abi_encode_array_addresses ip src dst asz msz body_st = (coords,addressed)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [abi_encode_array_addresses_def,
          abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM,
          emitHelperTheory.emit_op_def,
          fresh_var_def, fresh_id_def, emit_def] >>
        rpt (pairarg_tac >> gvs[]) >> strip_tac >>
        qpat_x_assum `_ = coords` (SUBST1_TAC o SYM) >>
        qpat_x_assum `_ = addressed` (SUBST1_TAC o SYM) >>
        simp_tac bool_ss [exprLoweringPropsTheory.emitted_insts_def] >>
        pure_rewrite_tac [GSYM APPEND_ASSOC] >>
        simp_tac (srw_ss()) [DROP_LENGTH_APPEND, GSYM ADD_ASSOC]) >>
     `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` by
       (simp_tac (srw_ss()) [Abbr `a0`, Abbr `a1`, Abbr `a2`, Abbr `a3`, Abbr `a4`,
          Abbr `a5`, Abbr `a6`, ASCIInumbersTheory.toString_inj]) >>
     `!x. not_fresh_at body_st x ==>
       x <> a0 /\ x <> a1 /\ x <> a2 /\ x <> a3 /\
       x <> a4 /\ x <> a5 /\ x <> a6` by
       (simp_tac (srw_ss()) [not_fresh_at_def, Abbr `a0`, Abbr `a1`,
          Abbr `a2`, Abbr `a3`, Abbr `a4`, Abbr `a5`, Abbr `a6`] >>
        metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
     qabbrev_tac `ar1 = update_var a0 (n2w k) hu` >>
     qabbrev_tac `ar2 = update_var a1 (n2w (sb+32)) ar1` >>
     `step_inst_base (mk_inst body_st.cs_next_id MLOAD [ip] [a0]) hu = OK ar1` by
       (qpat_assum `eval_operand ip hu = SOME (n2w bi)` mp_tac >>
        qpat_assum `mload bi hu = n2w k` mp_tac >>
        qpat_assum `bi < dimword (:256)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[Abbr `ar1`, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
          w2n_n2w, arithmeticTheory.LESS_MOD]) >>
     `eval_operand src ar1 = SOME (n2w sb)` by
       (qpat_assum `eval_operand src hu = SOME (n2w sb)` mp_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `!x. not_fresh_at body_st x ==> x <> a0 /\ _` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        Cases_on `src` >> fs[Abbr `ar1`, eval_operand_def, lookup_var_update_var] >>
        metis_tac[]) >>
     `step_inst_base (mk_inst (body_st.cs_next_id+1) ADD [src;Lit 32w] [a1]) ar1 = OK ar2` by
       (qpat_assum `eval_operand src ar1 = SOME (n2w sb)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[Abbr `ar2`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operands_def, eval_operand_def, word_add_n2w]) >>
     qabbrev_tac `ar3 = update_var a2 (n2w (k*msz)) ar2` >>
     qabbrev_tac `ar4 = update_var a3 (n2w (sb+32+k*msz)) ar3` >>
     qabbrev_tac `ar5 = update_var a4 (n2w (d+32)) ar4` >>
     qabbrev_tac `ar6 = update_var a5 (n2w (k*asz)) ar5` >>
     qabbrev_tac `ar7 = update_var a6 (n2w (d+32+k*asz)) ar6` >>
     `lookup_var a0 ar2 = SOME (n2w k) /\
      lookup_var a1 ar3 = SOME (n2w (sb+32)) /\
      lookup_var a2 ar3 = SOME (n2w (k*msz)) /\
      lookup_var a0 ar5 = SOME (n2w k) /\
      lookup_var a4 ar6 = SOME (n2w (d+32)) /\
      lookup_var a5 ar6 = SOME (n2w (k*asz))` by
       (qpat_assum `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` mp_tac >>
        simp_tac bool_ss [Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, Abbr `ar4`,
          Abbr `ar5`, Abbr `ar6`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[ALL_DISTINCT, lookup_var_update_var]) >>
     `eval_operand dst ar4 = SOME (n2w d)` by
       (qpat_assum `eval_operand dst hu = SOME (n2w d)` mp_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `!x. not_fresh_at body_st x ==> x <> a0 /\ _` mp_tac >>
        simp_tac bool_ss [Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, Abbr `ar4`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        Cases_on `dst` >> fs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
     `step_inst_base (mk_inst (body_st.cs_next_id+2) MUL [Var a0;Lit (n2w msz)] [a2]) ar2 = OK ar3 /\
      step_inst_base (mk_inst (body_st.cs_next_id+3) ADD [Var a1;Var a2] [a3]) ar3 = OK ar4 /\
      step_inst_base (mk_inst (body_st.cs_next_id+4) ADD [dst;Lit 32w] [a4]) ar4 = OK ar5 /\
      step_inst_base (mk_inst (body_st.cs_next_id+5) MUL [Var a0;Lit (n2w asz)] [a5]) ar5 = OK ar6 /\
      step_inst_base (mk_inst (body_st.cs_next_id+6) ADD [Var a4;Var a5] [a6]) ar6 = OK ar7` by
       (qpat_assum `lookup_var a0 ar2 = _` mp_tac >>
        qpat_assum `lookup_var a1 ar3 = _` mp_tac >>
        qpat_assum `lookup_var a2 ar3 = _` mp_tac >>
        qpat_assum `lookup_var a0 ar5 = _` mp_tac >>
        qpat_assum `lookup_var a4 ar6 = _` mp_tac >>
        qpat_assum `lookup_var a5 ar6 = _` mp_tac >>
        qpat_assum `eval_operand dst ar4 = _` mp_tac >>
        qpat_assum `Abbrev (ar3 = _)` mp_tac >>
        qpat_assum `Abbrev (ar4 = _)` mp_tac >>
        qpat_assum `Abbrev (ar5 = _)` mp_tac >>
        qpat_assum `Abbrev (ar6 = _)` mp_tac >>
        qpat_assum `Abbrev (ar7 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `ar3`, Abbr `ar4`, Abbr `ar5`, Abbr `ar6`, Abbr `ar7`,
          step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
          eval_operands_def, eval_operand_def, word_add_n2w, word_mul_n2w]) >>
     `run_inst_seq (emitted_insts body_st addressed) hu = OK ar7` by
       (qpat_assum `emitted_insts body_st addressed = _` mp_tac >>
        qpat_assum `step_inst_base _ hu = OK ar1` mp_tac >>
        qpat_assum `step_inst_base _ ar1 = OK ar2` mp_tac >>
        qpat_assum `step_inst_base _ ar2 = OK ar3` mp_tac >>
        qpat_assum `step_inst_base _ ar3 = OK ar4` mp_tac >>
        qpat_assum `step_inst_base _ ar4 = OK ar5` mp_tac >>
        qpat_assum `step_inst_base _ ar5 = OK ar6` mp_tac >>
        qpat_assum `step_inst_base _ ar6 = OK ar7` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[exprLoweringPropsTheory.run_inst_seq_def]) >>
     `araw = ar7` by
       (qpat_assum `window_pure_seq body_st addressed hu araw` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts body_st addressed) hu = OK ar7` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiEncoderWindowSequenceTheory.window_pure_seq_def,
          abiEncoderWindowSequenceTheory.window_seq_def]) >>
     qabbrev_tac `ai0 = mk_inst body_st.cs_next_id MLOAD [ip] [a0]` >>
     qabbrev_tac `ai1 = mk_inst (body_st.cs_next_id+1) ADD [src;Lit 32w] [a1]` >>
     qabbrev_tac `ai2 = mk_inst (body_st.cs_next_id+2) MUL [Var a0;Lit (n2w msz)] [a2]` >>
     qabbrev_tac `ai3 = mk_inst (body_st.cs_next_id+3) ADD [Var a1;Var a2] [a3]` >>
     qabbrev_tac `ai4 = mk_inst (body_st.cs_next_id+4) ADD [dst;Lit 32w] [a4]` >>
     qabbrev_tac `ai5 = mk_inst (body_st.cs_next_id+5) MUL [Var a0;Lit (n2w asz)] [a5]` >>
     qabbrev_tac `ai6 = mk_inst (body_st.cs_next_id+6) ADD [Var a4;Var a5] [a6]` >>
     qabbrev_tac `ag1 = step_prov PG hg ai0 ar1` >>
     qabbrev_tac `at1 = step_taint ai0 hu ar1 ht` >>
     qabbrev_tac `ag2 = step_prov PG ag1 ai1 ar2` >>
     qabbrev_tac `at2 = step_taint ai1 ar1 ar2 at1` >>
     qabbrev_tac `ag3 = step_prov PG ag2 ai2 ar3` >>
     qabbrev_tac `at3 = step_taint ai2 ar2 ar3 at2` >>
     qabbrev_tac `ag4 = step_prov PG ag3 ai3 ar4` >>
     qabbrev_tac `at4 = step_taint ai3 ar3 ar4 at3` >>
     qabbrev_tac `ag5 = step_prov PG ag4 ai4 ar5` >>
     qabbrev_tac `at5 = step_taint ai4 ar4 ar5 at4` >>
     qabbrev_tac `ag6 = step_prov PG ag5 ai5 ar6` >>
     qabbrev_tac `at6 = step_taint ai5 ar5 ar6 at5` >>
     qabbrev_tac `ag7 = step_prov PG ag6 ai6 ar7` >>
     qabbrev_tac `at7 = step_taint ai6 ar6 ar7 at6` >>
     `op_taint at1 (Var a0) = {} /\ at1.t_mem = ht.t_mem /\
      at1.t_stor = ht.t_stor /\ at1.t_trans = ht.t_trans` by
       (qpat_assum `!i. bi <= i /\ i < bi+32 ==> i NOTIN kt.t_mem` mp_tac >>
        qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
        qpat_assum `eval_operand ip hu = SOME (n2w bi)` mp_tac >>
        qpat_assum `mload bi hu = n2w k` mp_tac >>
        qpat_assum `bi < dimword (:256)` mp_tac >>
        qpat_assum `Abbrev (at1 = _)` mp_tac >>
        qpat_assum `Abbrev (ai0 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        qpat_assum `eval_operand ip hu = SOME (n2w bi)`
          (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
        simp_tac (srw_ss()) [w2n_n2w] >>
        disch_then (qspecl_then [`ht`, `body_st.cs_next_id`, `a0`] mp_tac) >>
        `bi MOD dimword (:256) = bi` by
          (irule arithmeticTheory.LESS_MOD >> asm_rewrite_tac[]) >>
        asm_simp_tac (srw_ss()) [w2n_n2w, Abbr `at1`, Abbr `ai0`, Abbr `ar1`]) >>
     `new_site_bytes ar1 ar2 = {} /\ new_site_bytes ar2 ar3 = {} /\
      new_site_bytes ar3 ar4 = {} /\ new_site_bytes ar4 ar5 = {} /\
      new_site_bytes ar5 ar6 = {} /\ new_site_bytes ar6 ar7 = {}` by
       (simp_tac bool_ss [Abbr `ar2`, Abbr `ar3`, Abbr `ar4`,
          Abbr `ar5`, Abbr `ar6`, Abbr `ar7`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]) >>
     `op_taint at2 (Var a0) = {} /\ op_taint at5 (Var a0) = {}` by
       (qpat_assum `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` mp_tac >>
        qpat_assum `op_taint at1 (Var a0) = {}` mp_tac >>
        simp_tac bool_ss [Abbr `at5`, Abbr `at4`, Abbr `at3`, Abbr `at2`,
          Abbr `ai4`, Abbr `ai3`, Abbr `ai2`, Abbr `ai1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[ALL_DISTINCT] >>
        asm_simp_tac (srw_ss()) [step_taint_other_output, mk_inst_def]) >>
     `at2 = at1 with t_var := at1.t_var |+ (a1,{}) /\
      at3 = at2 with t_var := at2.t_var |+ (a2,{}) /\
      at4 = at3 with t_var := at3.t_var |+ (a3,{}) /\
      at5 = at4 with t_var := at4.t_var |+ (a4,{}) /\
      at6 = at5 with t_var := at5.t_var |+ (a5,{}) /\
      at7 = at6 with t_var := at6.t_var |+ (a6,{})` by
       (rpt conj_tac >| [
          simp_tac bool_ss [Abbr `at2`, Abbr `ai1`],
          simp_tac bool_ss [Abbr `at3`, Abbr `ai2`],
          simp_tac bool_ss [Abbr `at4`, Abbr `ai3`],
          simp_tac bool_ss [Abbr `at5`, Abbr `ai4`],
          simp_tac bool_ss [Abbr `at6`, Abbr `ai5`],
          simp_tac bool_ss [Abbr `at7`, Abbr `ai6`]] >>
        qpat_assum `op_taint at2 (Var a0) = {}` mp_tac >>
        qpat_assum `op_taint at5 (Var a0) = {}` mp_tac >>
        rpt (qpat_x_assum `new_site_bytes _ _ = {}` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
          mem_taint_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def,
          written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
          range_bytes_def, taint_component_equality, DRESTRICT_UNIV,
          op_taint_def] >>
        BasicProvers.PURE_CASE_TAC >>
        asm_rewrite_tac[optionTheory.option_case_def] >> fs[op_taint_def]) >>
     `!x. not_fresh_at body_st x ==>
       FLOOKUP ag7 x = FLOOKUP hg x /\
       op_taint at7 (Var x) = op_taint ht (Var x) /\
       op_taint at1 (Var x) = op_taint ht (Var x)` by
       (gen_tac >> disch_tac >>
        `x <> a0 /\ x <> a1 /\ x <> a2 /\ x <> a3 /\
         x <> a4 /\ x <> a5 /\ x <> a6` by
          (qpat_assum `!x. not_fresh_at body_st x ==> x <> a0 /\ _` mp_tac >>
           qpat_assum `not_fresh_at body_st x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        qpat_assum `x <> a0` mp_tac >> qpat_assum `x <> a1` mp_tac >>
        qpat_assum `x <> a2` mp_tac >> qpat_assum `x <> a3` mp_tac >>
        qpat_assum `x <> a4` mp_tac >> qpat_assum `x <> a5` mp_tac >>
        qpat_assum `x <> a6` mp_tac >>
        simp_tac bool_ss [Abbr `ag7`, Abbr `ag6`, Abbr `ag5`, Abbr `ag4`,
          Abbr `ag3`, Abbr `ag2`, Abbr `ag1`, Abbr `at7`, Abbr `at6`,
          Abbr `at5`, Abbr `at4`, Abbr `at3`, Abbr `at2`, Abbr `at1`,
          Abbr `ai0`, Abbr `ai1`, Abbr `ai2`, Abbr `ai3`, Abbr `ai4`,
          Abbr `ai5`, Abbr `ai6`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_simp_tac (srw_ss()) [step_prov_other_output, step_taint_other_output,
          mk_inst_def]) >>
     `op_taint ht src = {} /\ op_taint ht dst = {}` by
       (qpat_assum `ptr_covers hg ht _ hu cap` mp_tac >>
        qpat_assum `ptr_covers hg ht _ hu (LENGTH (enc (Array NONE ty) (ListV avs)))` mp_tac >>
        rpt (qpat_x_assum `src = Var _` mp_tac) >>
        rpt (qpat_x_assum `dst = Var _` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >> metis_tac[]) >>
     `op_taint at1 src = {} /\ op_taint at1 dst = {}` by
       (qpat_assum `!x. not_fresh_at body_st x ==> FLOOKUP ag7 x = _ /\ _` mp_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `op_taint ht src = {}` mp_tac >>
        qpat_assum `op_taint ht dst = {}` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        Cases_on `src` >> Cases_on `dst` >> fs[op_taint_def] >> metis_tac[]) >>
     `op_taint at2 (Var a0) = {} /\
      op_taint at3 (Var a1) = {} /\ op_taint at3 (Var a2) = {} /\
      op_taint at4 dst = {} /\ op_taint at5 (Var a0) = {} /\
      op_taint at6 (Var a4) = {} /\ op_taint at6 (Var a5) = {} /\
      (!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {})` by
       (qpat_assum `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` mp_tac >>
        qpat_assum `!x. not_fresh_at body_st x ==> x <> a0 /\ _` mp_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `op_taint at1 (Var a0) = {}` mp_tac >>
        qpat_assum `op_taint at1 dst = {}` mp_tac >>
        qpat_assum `at2 = _` mp_tac >> qpat_assum `at3 = _` mp_tac >>
        qpat_assum `at4 = _` mp_tac >> qpat_assum `at5 = _` mp_tac >>
        qpat_assum `at6 = _` mp_tac >> qpat_assum `at7 = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[ALL_DISTINCT, op_taint_def, FLOOKUP_UPDATE] >>
        Cases_on `dst` >> fs[op_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
     `op_prov ag1 (Var a0) = NONE` by
       simp_tac (srw_ss()) [Abbr `ag1`, Abbr `ai0`, step_prov_def,
         set_prov_def, out_prov_def, mk_inst_def, op_prov_def, FLOOKUP_DRESTRICT] >>
     `!D j. ptr_inst_ok D lo 0 ctx func hg ht ai0 (hu with vs_inst_idx := j)` by
       (rpt gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
        conj_tac >-
          (qpat_assum `allocas_from lo hu` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
        qexists_tac `0` >> simp[] >>
        qpat_x_assum `ip = Var _` SUBST_ALL_TAC >>
        simp[Abbr `ai0`, wordLoadStorePtrTheory.ptr_inst_ok_mload]) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag1 at1 ai1
       (ar1 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint at1 src = {}` mp_tac >>
        qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base ai1 ar1 = OK ar2` mp_tac >>
        qpat_assum `Abbrev (ai1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base ai1 (ar1 with vs_inst_idx := j) =
          OK (ar2 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `ai1`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ ar1 = OK ar2`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        `step_inst 0 ctx ai1 (ar1 with vs_inst_idx := j) =
          OK (ar2 with vs_inst_idx := j)` by
          (simp[step_inst_non_invoke, Abbr `ai1`, mk_inst_def] >>
           qpat_assum `step_inst_base _ (ar1 with vs_inst_idx := j) = _`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [Abbr `ai1`, mk_inst_def] th])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ai1`, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >- (gen_tac >> Cases_on `op = src` >> fs[] >>
          Cases_on `op = Lit 32w` >> fs[op_taint_def]) >>
        fs[allocas_from_def, Abbr `ar1`, Abbr `ar2`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag2 at2 ai2
       (ar2 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint at2 (Var a0) = {}` mp_tac >>
        qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base ai2 ar2 = OK ar3` mp_tac >>
        qpat_assum `Abbrev (ai2 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        qpat_assum `Abbrev (ar3 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base ai2 (ar2 with vs_inst_idx := j) =
          OK (ar3 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `ai2`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ ar2 = OK ar3`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        `step_inst 0 ctx ai2 (ar2 with vs_inst_idx := j) =
          OK (ar3 with vs_inst_idx := j)` by
          (simp[step_inst_non_invoke, Abbr `ai2`, mk_inst_def] >>
           qpat_assum `step_inst_base _ (ar2 with vs_inst_idx := j) = _`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [Abbr `ai2`, mk_inst_def] th])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ai2`, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >- (gen_tac >> Cases_on `op = Var a0` >> fs[] >>
          Cases_on `op = Lit (n2w msz)` >> fs[op_taint_def]) >>
        fs[allocas_from_def, Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag3 at3 ai3
       (ar3 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint at3 (Var a1) = {}` mp_tac >>
        qpat_assum `op_taint at3 (Var a2) = {}` mp_tac >>
        qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base ai3 ar3 = OK ar4` mp_tac >>
        qpat_assum `Abbrev (ai3 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        qpat_assum `Abbrev (ar3 = _)` mp_tac >>
        qpat_assum `Abbrev (ar4 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base ai3 (ar3 with vs_inst_idx := j) =
          OK (ar4 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `ai3`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ ar3 = OK ar4`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        `step_inst 0 ctx ai3 (ar3 with vs_inst_idx := j) =
          OK (ar4 with vs_inst_idx := j)` by
          (simp[step_inst_non_invoke, Abbr `ai3`, mk_inst_def] >>
           qpat_assum `step_inst_base _ (ar3 with vs_inst_idx := j) = _`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [Abbr `ai3`, mk_inst_def] th])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ai3`, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >- (gen_tac >> Cases_on `op = Var a1` >> fs[] >>
          Cases_on `op = Var a2` >> fs[op_taint_def]) >>
        fs[allocas_from_def, Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, Abbr `ar4`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag4 at4 ai4
       (ar4 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint at4 dst = {}` mp_tac >>
        qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base ai4 ar4 = OK ar5` mp_tac >>
        qpat_assum `Abbrev (ai4 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        qpat_assum `Abbrev (ar3 = _)` mp_tac >>
        qpat_assum `Abbrev (ar4 = _)` mp_tac >>
        qpat_assum `Abbrev (ar5 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base ai4 (ar4 with vs_inst_idx := j) =
          OK (ar5 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `ai4`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ ar4 = OK ar5`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        `step_inst 0 ctx ai4 (ar4 with vs_inst_idx := j) =
          OK (ar5 with vs_inst_idx := j)` by
          (simp[step_inst_non_invoke, Abbr `ai4`, mk_inst_def] >>
           qpat_assum `step_inst_base _ (ar4 with vs_inst_idx := j) = _`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [Abbr `ai4`, mk_inst_def] th])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ai4`, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >- (gen_tac >> Cases_on `op = dst` >> fs[] >>
          Cases_on `op = Lit 32w` >> fs[op_taint_def]) >>
        fs[allocas_from_def, Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, Abbr `ar4`, Abbr `ar5`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag5 at5 ai5
       (ar5 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint at5 (Var a0) = {}` mp_tac >>
        qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base ai5 ar5 = OK ar6` mp_tac >>
        qpat_assum `Abbrev (ai5 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        qpat_assum `Abbrev (ar3 = _)` mp_tac >>
        qpat_assum `Abbrev (ar4 = _)` mp_tac >>
        qpat_assum `Abbrev (ar5 = _)` mp_tac >>
        qpat_assum `Abbrev (ar6 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base ai5 (ar5 with vs_inst_idx := j) =
          OK (ar6 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `ai5`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ ar5 = OK ar6`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        `step_inst 0 ctx ai5 (ar5 with vs_inst_idx := j) =
          OK (ar6 with vs_inst_idx := j)` by
          (simp[step_inst_non_invoke, Abbr `ai5`, mk_inst_def] >>
           qpat_assum `step_inst_base _ (ar5 with vs_inst_idx := j) = _`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [Abbr `ai5`, mk_inst_def] th])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ai5`, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >- (gen_tac >> Cases_on `op = Var a0` >> fs[] >>
          Cases_on `op = Lit (n2w asz)` >> fs[op_taint_def]) >>
        fs[allocas_from_def, Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, Abbr `ar4`, Abbr `ar5`, Abbr `ar6`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag6 at6 ai6
       (ar6 with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint at6 (Var a4) = {}` mp_tac >>
        qpat_assum `op_taint at6 (Var a5) = {}` mp_tac >>
        qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `step_inst_base ai6 ar6 = OK ar7` mp_tac >>
        qpat_assum `Abbrev (ai6 = _)` mp_tac >>
        qpat_assum `Abbrev (ar1 = _)` mp_tac >>
        qpat_assum `Abbrev (ar2 = _)` mp_tac >>
        qpat_assum `Abbrev (ar3 = _)` mp_tac >>
        qpat_assum `Abbrev (ar4 = _)` mp_tac >>
        qpat_assum `Abbrev (ar5 = _)` mp_tac >>
        qpat_assum `Abbrev (ar6 = _)` mp_tac >>
        qpat_assum `Abbrev (ar7 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst_base ai6 (ar6 with vs_inst_idx := j) =
          OK (ar7 with vs_inst_idx := j)` by
          (simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
             instIdxIndepTheory.exec_result_map_def, Abbr `ai6`, mk_inst_def,
             is_terminator_def] >>
           qpat_assum `step_inst_base _ ar6 = OK ar7`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [mk_inst_def] th,
               instIdxIndepTheory.exec_result_map_def])) >>
        `step_inst 0 ctx ai6 (ar6 with vs_inst_idx := j) =
          OK (ar7 with vs_inst_idx := j)` by
          (simp[step_inst_non_invoke, Abbr `ai6`, mk_inst_def] >>
           qpat_assum `step_inst_base _ (ar6 with vs_inst_idx := j) = _`
             (fn th => simp_tac (srw_ss()) [SIMP_RULE (srw_ss()) [Abbr `ai6`, mk_inst_def] th])) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ai6`, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac >- (gen_tac >> Cases_on `op = Var a4` >> fs[] >>
          Cases_on `op = Var a5` >> fs[op_taint_def]) >>
        fs[allocas_from_def, Abbr `ar1`, Abbr `ar2`, Abbr `ar3`, Abbr `ar4`, Abbr `ar5`, Abbr `ar6`, Abbr `ar7`, update_var_def] >> first_assum ACCEPT_TAC) >>
     `bi + 32 <= hu.vs_alloca_next` by
       (qpat_assum `window_array_cursor T owner ip _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def, window_array_root_def,
          alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
     `run_inst_seq_mem_ok [ai0;ai1;ai2;ai3;ai4;ai5;ai6] hu` by
       (
        qpat_assum `step_inst_base _ hu = OK ar1` mp_tac >>
        qpat_assum `step_inst_base _ ar1 = OK ar2` mp_tac >>
        qpat_assum `step_inst_base _ ar2 = OK ar3` mp_tac >>
        qpat_assum `step_inst_base _ ar3 = OK ar4` mp_tac >>
        qpat_assum `step_inst_base _ ar4 = OK ar5` mp_tac >>
        qpat_assum `step_inst_base _ ar5 = OK ar6` mp_tac >>
        qpat_assum `step_inst_base _ ar6 = OK ar7` mp_tac >>
        qpat_assum `bi + 32 <= hu.vs_alloca_next` mp_tac >>
        qpat_assum `bi < dimword (:256)` mp_tac >>
        qpat_assum `eval_operand ip hu = SOME (n2w bi)` mp_tac >>
        qpat_assum `Abbrev (ai0 = _)` mp_tac >>
        qpat_assum `Abbrev (ai1 = _)` mp_tac >>
        qpat_assum `Abbrev (ai2 = _)` mp_tac >>
        qpat_assum `Abbrev (ai3 = _)` mp_tac >>
        qpat_assum `Abbrev (ai4 = _)` mp_tac >>
        qpat_assum `Abbrev (ai5 = _)` mp_tac >>
        qpat_assum `Abbrev (ai6 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `ai0`, Abbr `ai1`, Abbr `ai2`, Abbr `ai3`, Abbr `ai4`, Abbr `ai5`, Abbr `ai6`, mk_inst_def] >>
        simp[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
        simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, w2n_n2w]) >>
     `!D j. inst_seq_ptr D lo ctx func PG hg ht [ai0;ai1;ai2;ai3;ai4;ai5;ai6]
       (hu with vs_inst_idx := j) ag7 at7` by
       (
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func hg ht ai0 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag1 at1 ai1 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag2 at2 ai2 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag3 at3 ai3 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag4 at4 ai4 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag5 at5 ai5 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag6 at6 ai6 _` mp_tac >>
        qpat_assum `step_inst_base _ hu = OK ar1` mp_tac >>
        qpat_assum `step_inst_base _ ar1 = OK ar2` mp_tac >>
        qpat_assum `step_inst_base _ ar2 = OK ar3` mp_tac >>
        qpat_assum `step_inst_base _ ar3 = OK ar4` mp_tac >>
        qpat_assum `step_inst_base _ ar4 = OK ar5` mp_tac >>
        qpat_assum `step_inst_base _ ar5 = OK ar6` mp_tac >>
        qpat_assum `step_inst_base _ ar6 = OK ar7` mp_tac >>
        qpat_assum `Abbrev (ai0 = _)` mp_tac >>
        qpat_assum `Abbrev (ai1 = _)` mp_tac >>
        qpat_assum `Abbrev (ai2 = _)` mp_tac >>
        qpat_assum `Abbrev (ai3 = _)` mp_tac >>
        qpat_assum `Abbrev (ai4 = _)` mp_tac >>
        qpat_assum `Abbrev (ai5 = _)` mp_tac >>
        qpat_assum `Abbrev (ai6 = _)` mp_tac >>
        qpat_assum `Abbrev (ag1 = _)` mp_tac >>
        qpat_assum `Abbrev (ag2 = _)` mp_tac >>
        qpat_assum `Abbrev (ag3 = _)` mp_tac >>
        qpat_assum `Abbrev (ag4 = _)` mp_tac >>
        qpat_assum `Abbrev (ag5 = _)` mp_tac >>
        qpat_assum `Abbrev (ag6 = _)` mp_tac >>
        qpat_assum `Abbrev (ag7 = _)` mp_tac >>
        qpat_assum `Abbrev (at1 = _)` mp_tac >>
        qpat_assum `Abbrev (at2 = _)` mp_tac >>
        qpat_assum `Abbrev (at3 = _)` mp_tac >>
        qpat_assum `Abbrev (at4 = _)` mp_tac >>
        qpat_assum `Abbrev (at5 = _)` mp_tac >>
        qpat_assum `Abbrev (at6 = _)` mp_tac >>
        qpat_assum `Abbrev (at7 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `ai0`, Abbr `ai1`, Abbr `ai2`, Abbr `ai3`, Abbr `ai4`, Abbr `ai5`, Abbr `ai6`, mk_inst_def] >>
        simp[inst_seq_ptr_def, instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, is_terminator_def,
          Abbr `ag1`, Abbr `ag2`, Abbr `ag3`, Abbr `ag4`, Abbr `ag5`, Abbr `ag6`, Abbr `ag7`, Abbr `at1`, Abbr `at2`, Abbr `at3`, Abbr `at4`, Abbr `at5`, Abbr `at6`, Abbr `at7`]) >>
     `body_st.cs_current_bb = FST (SND labels) /\ body_st.cs_current_insts = []` by
       (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
          mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encoder_array_loop_code_def] >> metis_tac[]) >>
     `?abb. lookup_block hu.vs_current_bb func.fn_blocks = SOME abb /\
       isPREFIX [ai0;ai1;ai2;ai3;ai4;ai5;ai6]
         (DROP hu.vs_inst_idx abb.bb_instructions)` by
       (qpat_assum `fn_has_code body_st addressed func` mp_tac >>
        qpat_assum `window_pure_seq body_st addressed hu araw` mp_tac >>
        qpat_assum `emitted_insts body_st addressed = _` mp_tac >>
        qpat_assum `hu.vs_current_bb = FST (SND labels)` mp_tac >>
        qpat_assum `hu.vs_inst_idx = 0` mp_tac >>
        qpat_assum `body_st.cs_current_bb = FST (SND labels)` mp_tac >>
        qpat_assum `body_st.cs_current_insts = []` mp_tac >>
        simp_tac bool_ss [Abbr `ai0`, Abbr `ai1`, Abbr `ai2`, Abbr `ai3`, Abbr `ai4`, Abbr `ai5`, Abbr `ai6`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abiEncoderWindowSequenceTheory.window_pure_seq_def,
          abiEncoderWindowSequenceTheory.window_seq_def, fragExecTheory.fn_has_code_def,
          exprLoweringPropsTheory.emitted_insts_def] >>
        rpt strip_tac >> gvs[] >> metis_tac[]) >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (hu,hg,ht) []
       (OK (ar7 with vs_inst_idx := hu.vs_inst_idx + 7),ag7,at7)` by
       (gen_tac >>
        qpat_assum `lookup_block hu.vs_current_bb func.fn_blocks = SOME abb` mp_tac >>
        qpat_assum `isPREFIX [ai0;ai1;ai2;ai3;ai4;ai5;ai6] _` mp_tac >>
        qpat_assum `~hu.vs_halted` mp_tac >>
        qpat_assum `run_inst_seq (emitted_insts body_st addressed) hu = OK ar7` mp_tac >>
        qpat_assum `emitted_insts body_st addressed = _` mp_tac >>
        qpat_assum `run_inst_seq_mem_ok [ai0;ai1;ai2;ai3;ai4;ai5;ai6] hu` mp_tac >>
        qpat_assum `!D j. inst_seq_ptr D lo ctx func PG hg ht _ _ ag7 at7` mp_tac >>
        qpat_assum `Abbrev (ai0 = _)` mp_tac >>
        qpat_assum `Abbrev (ai1 = _)` mp_tac >>
        qpat_assum `Abbrev (ai2 = _)` mp_tac >>
        qpat_assum `Abbrev (ai3 = _)` mp_tac >>
        qpat_assum `Abbrev (ai4 = _)` mp_tac >>
        qpat_assum `Abbrev (ai5 = _)` mp_tac >>
        qpat_assum `Abbrev (ai6 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `inst_seq_ptr D lo ctx func PG hg ht [ai0;ai1;ai2;ai3;ai4;ai5;ai6] hu ag7 at7` by
          (first_x_assum (qspecl_then [`D`, `hu.vs_inst_idx`] mp_tac) >> simp[]) >>
        qpat_x_assum `emitted_insts body_st addressed = _` SUBST_ALL_TAC >>
        mp_tac (Q.SPECL [`[ai0;ai1;ai2;ai3;ai4;ai5;ai6]`, `hu`, `ar7`,
          `hg`, `ht`, `ag7`, `at7`, `ctx`, `func`, `abb`]
          run_inst_seq_gas_origin_ptr_path) >>
        fs[Abbr `ai0`, Abbr `ai1`, Abbr `ai2`, Abbr `ai3`, Abbr `ai4`, Abbr `ai5`, Abbr `ai6`, mk_inst_def, is_terminator_def]) >>
     `LENGTH addressed.cs_current_insts = 7` by
       (qpat_assum `emitted_insts body_st addressed = _` mp_tac >>
        qpat_assum `body_st.cs_current_insts = []` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[exprLoweringPropsTheory.emitted_insts_def] >> strip_tac >> simp[]) >>
     qabbrev_tac `addr_s = ar7 with vs_inst_idx := LENGTH addressed.cs_current_insts` >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (hu,hg,ht) []
       (OK addr_s,ag7,at7)` by
       (qpat_assum `!D. gas_origin_ptr_path _ (hu,hg,ht) [] _` mp_tac >>
        qpat_assum `hu.vs_inst_idx = 0` mp_tac >>
        qpat_assum `LENGTH addressed.cs_current_insts = 7` mp_tac >>
        simp_tac bool_ss [Abbr `addr_s`] >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `window_pure_seq body_st addressed hu ar7` by
       (qpat_assum `window_pure_seq body_st addressed hu araw` mp_tac >>
        qpat_assum `araw = ar7` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `alloca_inv hu /\ alloca_room ctx func hu` by
       (qpat_assum `window_array_transition ctx func owner _ _ u hu` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_array_transition_resources]) >>
     `window_phase ctx func body_st addressed {} [] hu addr_s` by
       (simp_tac bool_ss [Abbr `addr_s`] >> irule window_pure_seq_phase >>
        qpat_assum `window_pure_seq body_st addressed hu ar7` mp_tac >>
        qpat_assum `fn_has_code body_st addressed func` mp_tac >>
        qpat_assum `alloca_inv hu` mp_tac >>
        qpat_assum `alloca_room ctx func hu` mp_tac >>
        qpat_assum `~hu.vs_halted` mp_tac >>
        qpat_assum `hu.vs_current_bb = FST (SND labels)` mp_tac >>
        qpat_assum `body_st.cs_current_bb = FST (SND labels)` mp_tac >>
        qpat_assum `hu.vs_inst_idx = 0` mp_tac >>
        qpat_assum `body_st.cs_current_insts = []` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `!root span. not_fresh_at body_st root /\ ptr_covers hg ht root hu span ==>
       ptr_covers ag7 at7 root addr_s span` by
       (simp_tac bool_ss [Abbr `addr_s`] >>
        qpat_assum `!x. not_fresh_at body_st x ==> FLOOKUP ag7 x = _ /\ _` mp_tac >>
        qpat_assum `window_pure_seq body_st addressed hu ar7` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abiEncoderWindowSequenceTheory.window_pure_seq_def,
          abiEncoderWindowSequenceTheory.window_seq_def, ptr_covers_def,
          lookup_var_def] >> rpt strip_tac >> fs[] >> metis_tac[]) >>
     `!x. not_fresh_at body_st x ==> FLOOKUP ag1 x = FLOOKUP hg x /\
       FLOOKUP ag2 x = FLOOKUP hg x /\
       FLOOKUP ag3 x = FLOOKUP hg x /\
       FLOOKUP ag4 x = FLOOKUP hg x /\
       FLOOKUP ag5 x = FLOOKUP hg x /\
       FLOOKUP ag6 x = FLOOKUP hg x` by
       (gen_tac >> disch_tac >>
        `x <> a0 /\ x <> a1 /\ x <> a2 /\ x <> a3 /\
         x <> a4 /\ x <> a5 /\ x <> a6` by
          (qpat_assum `!x. not_fresh_at body_st x ==> x <> a0 /\ _` mp_tac >>
           qpat_assum `not_fresh_at body_st x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        qpat_assum `x <> a0` mp_tac >> qpat_assum `x <> a1` mp_tac >>
        qpat_assum `x <> a2` mp_tac >> qpat_assum `x <> a3` mp_tac >>
        qpat_assum `x <> a4` mp_tac >> qpat_assum `x <> a5` mp_tac >>
        simp_tac bool_ss [Abbr `ag6`, Abbr `ag5`, Abbr `ag4`, Abbr `ag3`, Abbr `ag2`, Abbr `ag1`, Abbr `ai0`, Abbr `ai1`, Abbr `ai2`, Abbr `ai3`, Abbr `ai4`, Abbr `ai5`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_simp_tac (srw_ss()) [step_prov_other_output, mk_inst_def]) >>
     `op_prov ag1 src = op_prov hg src /\
      op_prov ag4 dst = op_prov hg dst` by
       (qpat_assum `!x. not_fresh_at body_st x ==> FLOOKUP ag1 x = _ /\ _` mp_tac >>
        qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at body_st x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        Cases_on `src` >> Cases_on `dst` >> fs[op_prov_def] >> metis_tac[]) >>
     `?spb spsz. op_prov hg src = SOME (spb,spsz)` by
       (qpat_assum `ptr_covers hg ht _ hu cap` mp_tac >>
        rpt (qpat_x_assum `src = Var _` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [ptr_covers_def, op_prov_def] >> rpt strip_tac >> fs[] >> metis_tac[]) >>
     `?dpb dpsz. op_prov hg dst = SOME (dpb,dpsz)` by
       (qpat_assum `ptr_covers hg ht _ hu (LENGTH (enc (Array NONE ty) (ListV avs)))` mp_tac >>
        rpt (qpat_x_assum `dst = Var _` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [ptr_covers_def, op_prov_def] >> rpt strip_tac >> fs[] >> metis_tac[]) >>
     `op_prov ag2 (Var a1) = SOME (spb,spsz)` by
       (qpat_assum `op_prov ag1 src = op_prov hg src` mp_tac >>
        qpat_assum `op_prov hg src = SOME (spb,spsz)` mp_tac >>
        simp_tac bool_ss [Abbr `ag2`, Abbr `ai1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
          mk_inst_def, op_prov_def, FLOOKUP_UPDATE]) >>
     `op_prov ag3 (Var a1) = SOME (spb,spsz)` by
       (qpat_assum `op_prov ag2 (Var a1) = SOME (spb,spsz)` mp_tac >>
        qpat_assum `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` mp_tac >>
        simp_tac bool_ss [Abbr `ag3`, Abbr `ai2`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[op_prov_def, step_prov_other_output, mk_inst_def, ALL_DISTINCT]) >>
     `op_prov ag4 (Var a3) = SOME (spb,spsz)` by
       (qpat_assum `op_prov ag3 (Var a1) = SOME (spb,spsz)` mp_tac >>
        simp_tac bool_ss [Abbr `ag4`, Abbr `ai3`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
          mk_inst_def, op_prov_def, FLOOKUP_UPDATE]) >>
     `op_prov ag5 (Var a4) = SOME (dpb,dpsz)` by
       (qpat_assum `op_prov ag4 dst = op_prov hg dst` mp_tac >>
        qpat_assum `op_prov hg dst = SOME (dpb,dpsz)` mp_tac >>
        simp_tac bool_ss [Abbr `ag5`, Abbr `ai4`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
          mk_inst_def, op_prov_def, FLOOKUP_UPDATE]) >>
     `op_prov ag6 (Var a4) = SOME (dpb,dpsz)` by
       (qpat_assum `op_prov ag5 (Var a4) = SOME (dpb,dpsz)` mp_tac >>
        qpat_assum `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` mp_tac >>
        simp_tac bool_ss [Abbr `ag6`, Abbr `ai5`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[op_prov_def, step_prov_other_output, mk_inst_def, ALL_DISTINCT]) >>
     `op_prov ag7 (Var a6) = SOME (dpb,dpsz)` by
       (qpat_assum `op_prov ag6 (Var a4) = SOME (dpb,dpsz)` mp_tac >>
        simp_tac bool_ss [Abbr `ag7`, Abbr `ai6`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
          mk_inst_def, op_prov_def, FLOOKUP_UPDATE]) >>
     `op_prov ag7 (Var a3) = SOME (spb,spsz) /\
      op_prov ag7 (Var a4) = SOME (dpb,dpsz) /\
      op_prov ag7 (Var a0) = NONE` by
       (rpt conj_tac >| [
          qpat_assum `op_prov ag4 (Var a3) = SOME (spb,spsz)` mp_tac >>
          simp_tac bool_ss [Abbr `ag7`, Abbr `ag6`, Abbr `ag5`,
            Abbr `ai6`, Abbr `ai5`, Abbr `ai4`],
          qpat_assum `op_prov ag6 (Var a4) = SOME (dpb,dpsz)` mp_tac >>
          simp_tac bool_ss [Abbr `ag7`, Abbr `ai6`],
          qpat_assum `op_prov ag1 (Var a0) = NONE` mp_tac >>
          simp_tac bool_ss [Abbr `ag7`, Abbr `ag6`, Abbr `ag5`, Abbr `ag4`,
            Abbr `ag3`, Abbr `ag2`, Abbr `ai6`, Abbr `ai5`, Abbr `ai4`,
            Abbr `ai3`, Abbr `ai2`, Abbr `ai1`]] >>
        qpat_assum `ALL_DISTINCT [a0;a1;a2;a3;a4;a5;a6]` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[op_prov_def, step_prov_other_output, mk_inst_def, ALL_DISTINCT]) >>
     `at1.t_imm = ht.t_imm` by
       (simp_tac bool_ss [Abbr `at1`, Abbr `ai0`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[step_taint_def, imm_taint_def, mk_inst_def, LET_THM]) >>
     `at7.t_mem = ht.t_mem /\ at7.t_stor = ht.t_stor /\
      at7.t_trans = ht.t_trans /\ at7.t_imm = ht.t_imm` by
       (qpat_assum `at1.t_mem = ht.t_mem` mp_tac >>
        qpat_assum `at1.t_stor = ht.t_stor` mp_tac >>
        qpat_assum `at1.t_trans = ht.t_trans` mp_tac >>
        qpat_assum `at1.t_imm = ht.t_imm` mp_tac >>
        qpat_assum `at2 = _` mp_tac >> qpat_assum `at3 = _` mp_tac >>
        qpat_assum `at4 = _` mp_tac >> qpat_assum `at5 = _` mp_tac >>
        qpat_assum `at6 = _` mp_tac >> qpat_assum `at7 = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[]) >>
     `addr_s.vs_memory = hu.vs_memory /\ addr_s.vs_allocas = hu.vs_allocas /\
      addr_s.vs_alloca_next = hu.vs_alloca_next` by
       (qpat_assum `window_pure_seq body_st addressed hu ar7` mp_tac >>
        simp_tac bool_ss [Abbr `addr_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiEncoderWindowSequenceTheory.window_pure_seq_def]) >>
     `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
       abi_encoder_window_input (AbiDynArray ei asz msz active)
         (Array NONE ty) (ListV avs) sb cap mem` by
       (qpat_assum `!mem. mem_agree_outside ht.t_mem hu.vs_memory mem ==> _` mp_tac >>
        qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
        qpat_assum `addr_s.vs_memory = hu.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `32+k*msz <= cap` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `k < LENGTH avs` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def] >> rpt strip_tac >>
        drule_all window_array_live_child >> strip_tac >> decide_tac) >>
     qabbrev_tac `child_cap = MIN msz (cap-(32+k*msz))` >>
     `child_cap <= msz /\ 32+k*msz+child_cap <= cap` by
       (qpat_assum `32+k*msz <= cap` mp_tac >>
        simp_tac bool_ss [Abbr `child_cap`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [MIN_DEF] >> decide_tac) >>
     `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
       abi_encoder_window_input ei ty (EL k avs)
         (sb+32+k*msz) child_cap mem` by
       (gen_tac >> disch_tac >>
        qpat_assum `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==> _`
          (qspec_then `mem` mp_tac) >>
        qpat_assum `mem_agree_outside at7.t_mem addr_s.vs_memory mem` mp_tac >>
        qpat_assum `k < LENGTH avs` mp_tac >>
        simp_tac bool_ss [Abbr `child_cap`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        rpt strip_tac >>
        `abi_encoder_window_input (AbiDynArray ei asz msz active)
          (Array NONE ty) (ListV avs) sb cap mem` by metis_tac[] >>
        drule_all window_array_live_child >>
        disch_then (qx_choose_then `ccap` strip_assume_tac) >>
        `ccap <= MIN msz (cap-(32+k*msz))` by
          (simp_tac (srw_ss()) [MIN_DEF] >> decide_tac) >>
        metis_tac[abi_encoder_window_input_capacity]) >>
     `eval_operand (Var a0) addr_s = SOME (n2w k) /\
      eval_operand (Var a3) addr_s = SOME (n2w (sb+32+k*msz)) /\
      eval_operand (Var a4) addr_s = SOME (n2w (d+32)) /\
      eval_operand (Var a6) addr_s = SOME (n2w (d+32+k*asz))` by
       (qpat_assum `eval_operand (FST (FST coords)) araw = _` mp_tac >>
        qpat_assum `eval_operand (SND (FST coords)) araw = _` mp_tac >>
        qpat_assum `eval_operand (FST (SND coords)) araw = _` mp_tac >>
        qpat_assum `eval_operand (SND (SND coords)) araw = _` mp_tac >>
        qpat_assum `coords = ((Var a0,Var a3),(Var a4,Var a6))` mp_tac >>
        qpat_assum `araw = ar7` mp_tac >>
        simp_tac bool_ss [Abbr `addr_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        rpt strip_tac >> fs[]) >>
     `op_taint at7 (Var a3) = {}` by
       (qpat_assum `!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {}`
          (qspec_then `a3` mp_tac) >> simp_tac (srw_ss()) []) >>
     `hu.vs_alloca_next < dimword (:256)` by
       (qpat_assum `alloca_room ctx func hu` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [alloca_room_def] >>
        rpt strip_tac >> decide_tac) >>
     `sb+cap <= hu.vs_alloca_next /\
      d+LENGTH (enc (Array NONE ty) (ListV avs)) <= hu.vs_alloca_next` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def] >> metis_tac[]) >>
     `sb < dimword (:256) /\ d < dimword (:256)` by
       (qpat_assum `sb+cap <= hu.vs_alloca_next` mp_tac >>
        qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= hu.vs_alloca_next` mp_tac >>
        qpat_assum `hu.vs_alloca_next < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `sb MOD dimword (:256) = sb /\ d MOD dimword (:256) = d` by
       (conj_tac >> irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
     `spb <= sb /\ sb+cap <= spb+spsz /\
      dpb <= d /\ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= dpb+dpsz` by
       (qpat_assum `ptr_covers hg ht _ hu cap` mp_tac >>
        qpat_assum `ptr_covers hg ht _ hu (LENGTH (enc (Array NONE ty) (ListV avs)))` mp_tac >>
        qpat_assum `op_prov hg src = SOME (spb,spsz)` mp_tac >>
        qpat_assum `op_prov hg dst = SOME (dpb,dpsz)` mp_tac >>
        qpat_assum `eval_operand src hu = SOME (n2w sb)` mp_tac >>
        qpat_assum `eval_operand dst hu = SOME (n2w d)` mp_tac >>
        qpat_assum `sb MOD dimword (:256) = sb` mp_tac >>
        qpat_assum `d MOD dimword (:256) = d` mp_tac >>
        rpt (qpat_x_assum `src = Var _` mp_tac) >>
        rpt (qpat_x_assum `dst = Var _` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        gvs[ptr_covers_def, op_prov_def, eval_operand_def, lookup_var_def, w2n_n2w]) >>
     `0 < child_cap ==> ptr_covers ag7 at7 a3 addr_s child_cap` by
       (disch_tac >>
        `sb+32+k*msz < dimword (:256)` by
          (qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
           qpat_assum `sb+cap <= hu.vs_alloca_next` mp_tac >>
           qpat_assum `hu.vs_alloca_next < dimword (:256)` mp_tac >>
           qpat_assum `0 < child_cap` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        `(sb+32+k*msz) MOD dimword (:256) = sb+32+k*msz` by
          (irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
        qpat_assum `eval_operand (Var a3) addr_s = SOME (n2w (sb+32+k*msz))` mp_tac >>
        qpat_assum `op_prov ag7 (Var a3) = SOME (spb,spsz)` mp_tac >>
        qpat_assum `op_taint at7 (Var a3) = {}` mp_tac >>
        qpat_assum `spb <= sb` mp_tac >>
        qpat_assum `sb+cap <= spb+spsz` mp_tac >>
        qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
        qpat_assum `(sb+32+k*msz) MOD dimword (:256) = sb+32+k*msz` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp_tac bool_ss [ptr_covers_def] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`n2w (sb+32+k*msz)`, `spb`, `spsz`] >>
        fs[op_prov_def, eval_operand_def, lookup_var_def, w2n_n2w] >> decide_tac) >>
     `allocas_from lo addr_s /\ lo <= addr_s.vs_alloca_next` by
       (qpat_assum `allocas_from lo hu` mp_tac >>
        qpat_assum `lo <= hu.vs_alloca_next` mp_tac >>
        qpat_assum `addr_s.vs_allocas = hu.vs_allocas` mp_tac >>
        qpat_assum `addr_s.vs_alloca_next = hu.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[allocas_from_def] >> metis_tac[]) >>
     `window_array_root ctx func body_st (window_alloca_sites func (frag_ids st en))
       ei asz msz active ty avs src dst sb cap d hu` by
       (irule window_array_root_owner_mono >>
        qexists_tac `owner` >> conj_tac >> first_assum ACCEPT_TAC) >>
     `window_array_root ctx func body_st (window_alloca_sites func (frag_ids st en))
       ei asz msz active ty avs src dst sb cap d addr_s` by
       (irule window_array_root_prepare >> qexistsl_tac [`addressed`, `hu`] >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `window_array_transition ctx func body_st {} [] hu addr_s` by
       (qpat_assum `window_phase ctx func body_st addressed {} [] hu addr_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_array_pure_phase_transition]) >>
     `window_array_transition ctx func owner {} [] hu addr_s` by
       (irule window_array_transition_owner_weaken >>
        qexists_tac `body_st` >> conj_tac >> first_assum ACCEPT_TAC) >>
     `window_array_root ctx func owner (window_alloca_sites func (frag_ids st en))
       ei asz msz active ty avs src dst sb cap d addr_s` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_root_transition >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
     `alloca_inv addr_s /\ alloca_room ctx func addr_s /\
      ~addr_s.vs_halted /\ addr_s.vs_current_bb = addressed.cs_current_bb /\
      addr_s.vs_inst_idx = LENGTH addressed.cs_current_insts` by
       (qpat_assum `window_phase ctx func body_st addressed {} [] hu addr_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_phase_def] >> metis_tac[]) >>
     `not_fresh_at addressed a0 /\ not_fresh_at addressed a3 /\
      not_fresh_at addressed a4 /\ not_fresh_at addressed a6` by
       (qpat_assum `!x. FST (FST coords) = Var x \/ SND (FST coords) = Var x \/ _ ==>
          not_fresh_at addressed x` mp_tac >>
        qpat_assum `coords = ((Var a0,Var a3),(Var a4,Var a6))` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[] >> metis_tac[]) >>
     reverse (Cases_on `active`) >-
       (qpat_assum `if F then abi_encode_array_dynamic_body _ _ _ _ _ _ _ _ = _ else _` mp_tac >>
        simp_tac bool_ss [] >> strip_tac >>
        `?ignored. compile_abi_encode_to_buf (Var a6) (Var a3) ei addressed =
          (ignored,body_end) /\ fn_has_code addressed body_end func /\ idx = Var a0` by
          (qpat_assum `abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end)`
             mp_tac >>
           qpat_assum `abi_encoder_admissible (AbiDynArray ei asz msz F)` mp_tac >>
           qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
             mp_tac >>
           qpat_assum `abi_encode_array_addresses ip src dst asz msz body_st = (coords,addressed)`
             mp_tac >>
           qpat_assum `coords = ((Var a0,Var a3),(Var a4,Var a6))` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `abi_encoder_static_leaf ei /\ fn_has_code body_st body_end func` by
             fs[Once abiEncoderAdmissibleTheory.abi_encoder_admissible_def,
               abi_encoder_array_loop_code_def] >>
           drule_all abi_encode_array_static_body_context >> strip_tac >>
           qpat_assum `abi_encoder_static_leaf ei` (fn th =>
             qpat_assum `compile_abi_encode_static_info _ _ ei _ = _`
               (assume_tac o PURE_REWRITE_RULE
                 [MATCH_MP abiEncoderAdmissibleTheory.abi_encode_static_info_agrees th])) >>
           gvs[] >> metis_tac[]) >>
        `abi_encoder_window_input (AbiDynArray ei asz msz F)
          (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` by
          (qpat_assum `window_array_root ctx func body_st _ _ _ _ _ _ _ _ _ _ _ _ addr_s`
             mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def] >> metis_tac[]) >>
        `asz = abi_member_head_size ty /\ ~is_dynamic ty` by
          (qpat_assum `abi_encoder_window_input (AbiDynArray ei asz msz F)
             (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_encoder_window_array_iff]) >>
        `32+k*asz+LENGTH (enc ty (EL k avs)) <=
          LENGTH (enc (Array NONE ty) (ListV avs))` by
          (qpat_assum `abi_encoder_window_input (AbiDynArray ei asz msz F)
             (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` mp_tac >>
           qpat_assum `asz = abi_member_head_size ty` mp_tac >>
           qpat_assum `~is_dynamic ty` mp_tac >> qpat_assum `k < LENGTH avs` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           drule_all window_array_prefix_step_geometry >> strip_tac >>
           drule window_array_layout >> strip_tac >> fs[] >> res_tac >> decide_tac) >>
        `op_taint at7 (Var a6) = {}` by
          (qpat_assum `!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {}`
             (qspec_then `a6` mp_tac) >> simp_tac (srw_ss()) []) >>
        `0 < LENGTH (enc ty (EL k avs)) ==>
          ptr_covers ag7 at7 a6 addr_s (LENGTH (enc ty (EL k avs)))` by
          (disch_tac >>
           `d+32+k*asz < dimword (:256)` by
             (qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
              qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= hu.vs_alloca_next` mp_tac >>
              qpat_assum `hu.vs_alloca_next < dimword (:256)` mp_tac >>
              qpat_assum `0 < LENGTH (enc ty (EL k avs))` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
           `(d+32+k*asz) MOD dimword (:256) = d+32+k*asz` by
             (irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
           qpat_assum `eval_operand (Var a6) addr_s = SOME (n2w (d+32+k*asz))` mp_tac >>
           qpat_assum `op_prov ag7 (Var a6) = SOME (dpb,dpsz)` mp_tac >>
           qpat_assum `op_taint at7 (Var a6) = {}` mp_tac >>
           qpat_assum `dpb <= d` mp_tac >>
           qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= dpb+dpsz` mp_tac >>
           qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           qpat_assum `(d+32+k*asz) MOD dimword (:256) = d+32+k*asz` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           simp_tac bool_ss [ptr_covers_def] >>
           conj_tac >- first_assum ACCEPT_TAC >>
           qexistsl_tac [`n2w (d+32+k*asz)`, `dpb`, `dpsz`] >>
           fs[op_prov_def, eval_operand_def, lookup_var_def, w2n_n2w] >> decide_tac) >>
        `st.cs_next_id <= addressed.cs_next_id /\ body_end.cs_next_id <= en.cs_next_id` by
          (qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
           qpat_assum `owner.cs_next_id = loop_st.cs_next_id + (if F then 5 else 2)` mp_tac >>
           qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
             mp_tac >>
           qpat_assum `addressed.cs_next_id = body_st.cs_next_id+7` mp_tac >>
           qpat_assum `body_end.cs_next_id+6 = loop_end.cs_next_id` mp_tac >>
           qpat_assum `en.cs_next_id = loop_end.cs_next_id+4` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [abi_encoder_array_loop_code_def] >>
           rpt strip_tac >> decide_tac) >>
        `abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap addr_s.vs_memory` by
          (qpat_assum `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
             abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap mem`
             (qspec_then `addr_s.vs_memory` mp_tac) >>
           simp_tac (srw_ss()) [mem_agree_outside_def]) >>
        `!x. Var a3 = Var x \/ Var a6 = Var x ==> not_fresh_at addressed x` by
          (qpat_assum `not_fresh_at addressed a3` mp_tac >>
           qpat_assum `not_fresh_at addressed a6` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
        `abi_encoder_window_pre ctx func addressed body_end (Var a6) (Var a3) ei ty
          (EL k avs) (sb+32+k*msz) child_cap (d+32+k*asz) addr_s` by
          (qpat_assum `window_array_root ctx func body_st _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
           qpat_assum `abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap addr_s.vs_memory`
             mp_tac >>
           qpat_assum `eval_operand (Var a3) addr_s = SOME (n2w (sb+32+k*msz))` mp_tac >>
           qpat_assum `eval_operand (Var a6) addr_s = SOME (n2w (d+32+k*asz))` mp_tac >>
           qpat_assum `!x. Var a3 = Var x \/ Var a6 = Var x ==> not_fresh_at addressed x` mp_tac >>
           qpat_assum `fn_has_code addressed body_end func` mp_tac >>
           qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
           qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           qpat_assum `st.cs_next_id <= addressed.cs_next_id` mp_tac >>
           qpat_assum `body_end.cs_next_id <= en.cs_next_id` mp_tac >>
           qpat_assum `~addr_s.vs_halted` mp_tac >>
           qpat_assum `addr_s.vs_current_bb = addressed.cs_current_bb` mp_tac >>
           qpat_assum `addr_s.vs_inst_idx = LENGTH addressed.cs_current_insts` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> rpt strip_tac >>
           simp_tac bool_ss [abi_encoder_window_pre_def] >> asm_rewrite_tac[] >>
           rpt conj_tac
           >- (qpat_assum `abi_encoder_admissible (AbiDynArray ei asz msz F)` mp_tac >>
               simp_tac bool_ss [Once abiEncoderAdmissibleTheory.abi_encoder_admissible_def] >>
               simp_tac bool_ss [])
           >- decide_tac
           >- decide_tac
           >- (qpat_assum `regions_disjoint (sb,cap) (d,_)` mp_tac >>
               qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
               qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >>
               pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           rpt strip_tac >>
           `inst.inst_id IN window_alloca_sites func (frag_ids st en)` by
             (qpat_assum `MEM inst (fn_insts func)` mp_tac >>
              qpat_assum `inst.inst_opcode = ALLOCA` mp_tac >>
              qpat_assum `inst.inst_id IN frag_ids addressed body_end` mp_tac >>
              qpat_assum `st.cs_next_id <= addressed.cs_next_id` mp_tac >>
              qpat_assum `body_end.cs_next_id <= en.cs_next_id` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
              rpt strip_tac >>
              (decide_tac ORELSE (qexists_tac `inst` >> simp[]))) >>
           `sz = 32 /\ regions_disjoint (sb,cap) (b,sz) /\
            regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by metis_tac[] >>
           asm_rewrite_tac[] >>
           qpat_assum `regions_disjoint (sb,cap) (b,sz)` mp_tac >>
           qpat_assum `regions_disjoint (d,_) (b,sz)` mp_tac >>
           qpat_assum `sz = 32` mp_tac >>
           qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
           qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
        qpat_assum `!dst src st out en ctx func s at av sb cap d G tn lo explicit PG. _`
          (qspecl_then [`Var a6`, `Var a3`, `addressed`, `ignored`, `body_end`,
            `ctx`, `func`, `addr_s`, `ty`, `EL k avs`, `sb+32+k*msz`, `child_cap`,
            `d+32+k*asz`, `ag7`, `at7`, `lo`, `explicit`, `PG`] mp_tac) >>
        impl_tac >-
          (qpat_assum `abi_encoder_window_pre ctx func addressed body_end (Var a6) (Var a3) ei ty
             (EL k avs) (sb+32+k*msz) child_cap (d+32+k*asz) addr_s` mp_tac >>
           qpat_assum `compile_abi_encode_to_buf (Var a6) (Var a3) ei addressed = (ignored,body_end)` mp_tac >>
           qpat_assum `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
             abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap mem` mp_tac >>
           qpat_assum `0 < child_cap ==> ptr_covers ag7 at7 a3 addr_s child_cap` mp_tac >>
           qpat_assum `0 < LENGTH (enc ty (EL k avs)) ==> ptr_covers ag7 at7 a6 addr_s _` mp_tac >>
           qpat_assum `op_taint at7 (Var a3) = {}` mp_tac >>
           qpat_assum `op_taint at7 (Var a6) = {}` mp_tac >>
           qpat_assum `allocas_from lo addr_s` mp_tac >>
           qpat_assum `lo <= addr_s.vs_alloca_next` mp_tac >>
           qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           rpt disch_tac >>
           qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
             (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
           asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
           rpt strip_tac >> metis_tac[]) >>
        disch_then (qx_choose_then `child_s` (qx_choose_then `childG`
          (qx_choose_then `childtn` strip_assume_tac))) >>
        `window_alloca_sites func (frag_ids addressed body_end) SUBSET
          window_alloca_sites func (frag_ids st en)` by
          (qpat_assum `st.cs_next_id <= addressed.cs_next_id` mp_tac >>
           qpat_assum `body_end.cs_next_id <= en.cs_next_id` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_alloca_sites_mono >>
           simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >>
           decide_tac) >>
        `window_array_transition ctx func body_st
          (window_alloca_sites func (frag_ids addressed body_end))
          [(d+32+k*asz,LENGTH (enc ty (EL k avs)))] addr_s child_s` by
          (qpat_assum `window_strong_result ctx func addressed body_end ignored ty
             (EL k avs) (d+32+k*asz) addr_s child_s` mp_tac >>
           qpat_assum `addressed.cs_next_var = body_st.cs_next_var+7` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_child_transition >> asm_rewrite_tac[] >>
           conj_tac >- decide_tac >> qexists_tac `ignored` >> first_assum ACCEPT_TAC) >>
        `abi_encoder_array_prefix ty avs k d addr_s.vs_memory` by
          (qpat_assum `abi_encoder_array_prefix ty avs k d hu.vs_memory` mp_tac >>
           qpat_assum `addr_s.vs_memory = hu.vs_memory` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `abi_encoder_array_prefix ty avs k d child_s.vs_memory` by
          (qpat_assum `window_array_root ctx func body_st _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
           qpat_assum `abi_encoder_array_prefix ty avs k d addr_s.vs_memory` mp_tac >>
           qpat_assum `window_array_transition ctx func body_st _ _ addr_s child_s` mp_tac >>
           qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           qpat_assum `~is_dynamic ty` mp_tac >>
           qpat_assum `asz = abi_member_head_size ty` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           metis_tac[window_array_static_prefix_frame]) >>
        `mem_bytes_at (d+32+k*asz) (LENGTH (enc ty (EL k avs))) child_s.vs_memory =
          enc ty (EL k avs)` by
          (qpat_assum `window_strong_result ctx func addressed body_end ignored ty
             (EL k avs) (d+32+k*asz) addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[window_strong_result_public, abi_encoder_window_result_output]) >>
        `abi_encoder_array_prefix ty avs (SUC k) d child_s.vs_memory` by
          (qpat_assum `abi_encoder_window_input (AbiDynArray ei asz msz F)
             (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` mp_tac >>
           qpat_assum `abi_encoder_array_prefix ty avs k d child_s.vs_memory` mp_tac >>
           qpat_assum `mem_bytes_at (d+32+k*asz) _ child_s.vs_memory = _` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           qpat_assum `~is_dynamic ty` mp_tac >>
           qpat_assum `asz = abi_member_head_size ty` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           metis_tac[window_array_prefix_static_advance]) >>
        `regions_disjoint (sb,cap)
          (d+32+k*asz,LENGTH (enc ty (EL k avs)))` by
          (qpat_assum `window_array_root ctx func body_st _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
           qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def] >> rpt strip_tac >>
           qpat_assum `regions_disjoint (sb,cap) (d,_)` mp_tac >>
           qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
        `window_array_root ctx func body_st (window_alloca_sites func (frag_ids st en))
          ei asz msz F ty avs src dst sb cap d child_s` by
          (qpat_assum `window_array_root ctx func body_st _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func body_st _ _ addr_s child_s` mp_tac >>
           qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
           qpat_assum `regions_disjoint (sb,cap) (d+32+k*asz,_)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_root_transition >>
           goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
           simp[]) >>
        `alloca_inv child_s /\ alloca_room ctx func child_s /\
          window_alloca_growth addr_s child_s` by
          (qpat_assum `window_array_transition ctx func body_st _ _ addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[window_array_transition_resources]) >>
        `!i r. FLOOKUP addr_s.vs_allocas i = SOME r ==>
          FLOOKUP child_s.vs_allocas i = SOME r` by
          (qpat_assum `window_array_transition ctx func body_st _ _ addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
        `allocas_from lo child_s /\ lo <= child_s.vs_alloca_next` by
          (qpat_assum `allocas_from lo addr_s` mp_tac >>
           qpat_assum `lo <= addr_s.vs_alloca_next` mp_tac >>
           qpat_assum `window_alloca_growth addr_s child_s` mp_tac >>
           qpat_assum `!i r. FLOOKUP addr_s.vs_allocas i = SOME r ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [allocas_from_def, window_alloca_growth_def] >>
           rpt disch_tac >> conj_tac >-
             (rpt strip_tac >> Cases_on `FLOOKUP addr_s.vs_allocas aid` >>
              metis_tac[optionTheory.SOME_11, LESS_EQ_TRANS]) >>
           metis_tac[LESS_EQ_TRANS]) >>
        `eval_operand (Var a0) child_s = SOME (n2w k)` by
          (qpat_assum `window_strong_result ctx func addressed body_end ignored ty
             (EL k avs) (d+32+k*asz) addr_s child_s` mp_tac >>
           qpat_assum `not_fresh_at addressed a0` mp_tac >>
           qpat_assum `eval_operand (Var a0) addr_s = SOME (n2w k)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac (srw_ss()) [eval_operand_def] >>
           metis_tac[window_strong_result_public, abi_encoder_window_result_vars]) >>
        `op_prov childG (Var a0) = NONE /\ op_taint childtn (Var a0) = {}` by
          (qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP childG x = _ /\ _`
             (qspec_then `a0` mp_tac) >>
           qpat_assum `op_prov ag7 (Var a0) = NONE` mp_tac >>
           qpat_assum `!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {}`
             (qspec_then `a0` mp_tac) >>
           qpat_assum `not_fresh_at addressed a0` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[op_prov_def]) >>
        `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK child_s,childG,childtn)` by
          (gen_tac >>
           qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK hu,hg,ht)`
             (qspec_then `D` mp_tac) >>
           qpat_assum `!D. gas_origin_ptr_path _ (hu,hg,ht) [] (OK addr_s,ag7,at7)`
             (qspec_then `D` mp_tac) >>
           qpat_assum `!D. gas_origin_ptr_path _ (addr_s,ag7,at7) [] (OK child_s,childG,childtn)`
             (qspec_then `D` mp_tac) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids addressed body_end))
          [(d+32+k*asz,LENGTH (enc ty (EL k avs)))] addr_s child_s` by
          (irule window_array_transition_owner_weaken >>
           qexists_tac `body_st` >> conj_tac >> first_assum ACCEPT_TAC) >>
        `window_array_root ctx func owner (window_alloca_sites func (frag_ids st en))
          ei asz msz F ty avs src dst sb cap d child_s` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner _ _ addr_s child_s` mp_tac >>
           qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
           qpat_assum `regions_disjoint (sb,cap) (d+32+k*asz,_)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_root_transition >>
           goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
        `!root span. not_fresh_at addressed root /\
          ptr_covers ag7 at7 root addr_s span ==>
          ptr_covers childG childtn root child_s span` by
          (qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP childG x = _ /\ _` mp_tac >>
           qpat_assum `window_strong_result ctx func addressed body_end ignored ty
             (EL k avs) (d+32+k*asz) addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >>
           metis_tac[window_strong_result_public, abi_encoder_window_result_vars]) >>
        `abi_encode_exec_frame func hu addr_s` by
          (simp_tac (srw_ss()) [Abbr `addr_s`] >>
           qpat_assum `window_pure_seq body_st addressed hu ar7` mp_tac >>
           qpat_assum `abi_encode_array_addresses ip src dst asz msz body_st = (coords,addressed)`
             mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule abi_encode_framed_ordinary_pure_sequence >>
           asm_rewrite_tac[] >> metis_tac[abi_encode_framed_array_addresses_opcodes]) >>
        `abi_encode_exec_frame func s child_s` by
          (qpat_assum `abi_encode_exec_frame func s u` mp_tac >>
           qpat_assum `abi_encode_exec_frame func u hu` mp_tac >>
           qpat_assum `abi_encode_exec_frame func hu addr_s` mp_tac >>
           qpat_assum `abi_encode_exec_frame func addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[abi_encode_exec_frame_trans]) >>
        `!id b sz. id IN window_alloca_sites func (frag_ids addressed body_end) /\
          FLOOKUP child_s.vs_allocas id = SOME (b,sz) ==>
          regions_disjoint (sb,cap) (b,sz)` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
           qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def, SUBSET_DEF] >> rpt strip_tac >>
           metis_tac[]) >>
        `mem_bytes_at sb cap child_s.vs_memory = mem_bytes_at sb cap addr_s.vs_memory` by
          (qpat_assum `window_array_transition ctx func owner _ _ addr_s child_s` mp_tac >>
           qpat_assum `regions_disjoint (sb,cap) (d+32+k*asz,_)` mp_tac >>
           qpat_assum `!id b sz. id IN window_alloca_sites func (frag_ids addressed body_end) /\
             FLOOKUP child_s.vs_allocas id = SOME (b,sz) ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule abi_encoder_window_effect_bytes >>
           qexistsl_tac [`window_alloca_sites func (frag_ids addressed body_end)`,
             `[(d+32+k*asz,LENGTH (enc ty (EL k avs)))]`] >>
           simp[] >> full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
           metis_tac[window_array_transition_effect]) >>
        `!i. sb <= i /\ i < sb+cap ==>
          (i IN childtn.t_mem <=> i IN at7.t_mem)` by
          (gen_tac >> strip_tac >>
           qpat_assum `!i. (i < d+32+k*asz \/ d+32+k*asz+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==> (i IN childtn.t_mem <=> i IN at7.t_mem)`
             (qspec_then `i` mp_tac) >> impl_tac >-
            (conj_tac >-
             (qpat_assum `regions_disjoint (sb,cap) (d+32+k*asz,_)` mp_tac >>
              qpat_assum `sb <= i` mp_tac >> qpat_assum `i < sb+cap` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           rpt strip_tac >>
           rename1 `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` >>
           `regions_disjoint (sb,cap) (scratch_b,scratch_sz)` by
             (qpat_assum `!id b sz. id IN window_alloca_sites func (frag_ids addressed body_end) /\
                FLOOKUP child_s.vs_allocas id = SOME (b,sz) ==> _`
                (qspecl_then [`aid`, `scratch_b`, `scratch_sz`] mp_tac) >>
              impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
           pop_assum mp_tac >> qpat_assum `sb <= i` mp_tac >>
           qpat_assum `i < sb+cap` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           simp[]) >>
        `!mem. mem_agree_outside childtn.t_mem child_s.vs_memory mem ==>
          abi_encoder_window_input (AbiDynArray ei asz msz F)
            (Array NONE ty) (ListV avs) sb cap mem` by
          (gen_tac >> strip_tac >>
           mp_tac (Q.SPECL [`at7.t_mem`, `childtn.t_mem`, `addr_s.vs_memory`,
             `child_s.vs_memory`, `sb`, `sb`, `cap`, `mem`]
             copied_window_agree_witness) >>
           impl_tac >-
             (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >-
               (rpt strip_tac >>
                qpat_assum `!i. sb <= i /\ i < sb+cap ==> _`
                  (qspec_then `sb+i` mp_tac) >>
                qpat_assum `i < cap` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
              first_assum ACCEPT_TAC) >>
           disch_then (qx_choose_then `mix` strip_assume_tac) >>
           `abi_encoder_window_input (AbiDynArray ei asz msz F)
             (Array NONE ty) (ListV avs) sb cap mix` by
             (qpat_assum `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
                abi_encoder_window_input (AbiDynArray ei asz msz F)
                  (Array NONE ty) (ListV avs) sb cap mem`
                (qspec_then `mix` irule) >> first_assum ACCEPT_TAC) >>
           qpat_assum `abi_encoder_window_input _ _ _ _ _ mix` mp_tac >>
           qpat_assum `mem_bytes_at sb cap mix = mem_bytes_at sb cap mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[abi_encoder_window_input_mem_agree]) >>
        `!cop csite cslot cvalue.
          window_array_cursor T owner cop csite cslot cvalue sb cap d
            (LENGTH (enc (Array NONE ty) (ListV avs))) hu /\
          csite NOTIN window_alloca_sites func (frag_ids addressed body_end) ==>
          window_array_cursor T owner cop csite cslot cvalue sb cap d
            (LENGTH (enc (Array NONE ty) (ListV avs))) child_s` by
          (qx_genl_tac [`cop`, `csite`, `cslot`, `cvalue`] >> strip_tac >>
           `window_array_cursor T owner cop csite cslot cvalue sb cap d
             (LENGTH (enc (Array NONE ty) (ListV avs))) addr_s` by
             (qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ hu` mp_tac >>
              qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              metis_tac[window_array_cursor_frame, EVERY_DEF, NOT_IN_EMPTY]) >>
           `regions_disjoint (cslot,32)
             (d+32+k*asz,LENGTH (enc ty (EL k avs)))` by
             (qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ addr_s` mp_tac >>
              qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
              qpat_assum `regions_disjoint (d,_) (cslot,32)` mp_tac >>
              qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner _ _ addr_s child_s` mp_tac >>
           qpat_assum `csite NOTIN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
           qpat_assum `regions_disjoint (cslot,32) (d+32+k*asz,_)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           metis_tac[window_array_cursor_frame, EVERY_DEF]) >>
        `loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids addressed body_end) /\
          st.cs_next_id NOTIN window_alloca_sites func (frag_ids addressed body_end)` by
          (qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
           qpat_assum `owner.cs_next_id = loop_st.cs_next_id + (if F then 5 else 2)` mp_tac >>
           qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
             mp_tac >>
           qpat_assum `addressed.cs_next_id = body_st.cs_next_id+7` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           qpat_assum `_ IN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
           qpat_assum `addressed.cs_next_id = body_st.cs_next_id+7` mp_tac >>
           qpat_assum `body_st.cs_next_id = owner.cs_next_id+5` mp_tac >>
           qpat_assum `owner.cs_next_id = loop_st.cs_next_id+2` mp_tac >>
           qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
           rpt strip_tac >> disj1_tac >> disj1_tac >> decide_tac) >>
        `window_array_cursor T owner ip loop_st.cs_next_id bi k sb cap d
          (LENGTH (enc (Array NONE ty) (ListV avs))) child_s /\
          window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
            (LENGTH (enc (Array NONE ty) (ListV avs))) child_s` by
          (qpat_assum `!cop csite cslot cvalue. _` mp_tac >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ hu` mp_tac >>
           qpat_assum `window_array_cursor T owner pp st.cs_next_id b 0 _ _ _ _ hu` mp_tac >>
           qpat_assum `loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
           qpat_assum `st.cs_next_id NOTIN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        `~child_s.vs_halted /\ child_s.vs_current_bb = body_end.cs_current_bb /\
          child_s.vs_inst_idx = LENGTH body_end.cs_current_insts` by
          (qpat_assum `window_strong_result ctx func addressed body_end ignored ty
             (EL k avs) (d+32+k*asz) addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[window_phase_strong_result, window_phase_control]) >>
        `eval_operand ip child_s = SOME (n2w bi) /\ bi < dimword (:256) /\
          FLOOKUP child_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` by
          (qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_cursor_def] >>
           metis_tac[]) >>
        `owner.cs_next_var <= body_end.cs_next_var` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
             mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >> decide_tac) >>
        `!x. ip = Var x ==> not_fresh_at body_end x` by
          (qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ child_s` mp_tac >>
           qpat_assum `owner.cs_next_var <= body_end.cs_next_var` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_cursor_def] >>
           rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
        qabbrev_tac `nv = STRING #"%" (toString body_end.cs_next_var)` >>
        `~not_fresh_at body_end nv` by
          (qpat_assum `Abbrev (nv = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `nv`, not_fresh_at_def] >>
           metis_tac[LESS_EQ_REFL]) >>
        `ip <> Var nv` by
          (qpat_assum `!x. ip = Var x ==> not_fresh_at body_end x` (qspec_then `nv` mp_tac) >>
           qpat_assum `~not_fresh_at body_end nv` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        qabbrev_tac `bai = mk_inst body_end.cs_next_id ADD [Var a0;Lit 1w] [nv]` >>
        qabbrev_tac `bsi = mk_inst (body_end.cs_next_id+1) MSTORE [ip;Var nv] []` >>
        qabbrev_tac `bji = mk_inst (body_end.cs_next_id+2) JMP [Label (FST labels)] []` >>
        qabbrev_tac `br1 = update_var nv (n2w (SUC k)) child_s` >>
        qabbrev_tac `br2 = mstore bi (n2w (SUC k)) br1` >>
        qabbrev_tac `back_s = jump_to (FST labels) br2` >>
        `!x. not_fresh_at owner x ==> not_fresh_at body_st x /\
          not_fresh_at addressed x` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
           qpat_assum `addressed.cs_next_var = body_st.cs_next_var+7` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           metis_tac[not_fresh_at_mono, LESS_EQ_ADD, LESS_EQ_TRANS]) >>
        `?iq. ip = Var iq /\ ptr_covers childG childtn iq child_s 32` by
          (rpt (qpat_x_assum `ptr_covers hg ht _ hu 32` mp_tac) >>
           rpt (qpat_x_assum `ip = Var _` mp_tac) >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ hu` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x /\ _` mp_tac >>
           qpat_assum `!root span. not_fresh_at body_st root /\ ptr_covers hg ht root hu span ==> _` mp_tac >>
           qpat_assum `!root span. not_fresh_at addressed root /\ ptr_covers ag7 at7 root addr_s span ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >> metis_tac[]) >>
        qabbrev_tac `bbb = <|bb_label := body_end.cs_current_bb;
          bb_instructions := body_end.cs_current_insts ++ [bai;bsi;bji]|>` >>
        `lookup_block child_s.vs_current_bb func.fn_blocks = SOME bbb` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
           qpat_assum `child_s.vs_current_bb = body_end.cs_current_bb` mp_tac >>
           qpat_assum `Abbrev (a0 = _)` mp_tac >> qpat_assum `Abbrev (nv = _)` mp_tac >>
           qpat_assum `Abbrev (bai = _)` mp_tac >> qpat_assum `Abbrev (bsi = _)` mp_tac >>
           qpat_assum `Abbrev (bji = _)` mp_tac >> qpat_assum `Abbrev (bbb = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           fs[Abbr `bbb`, Abbr `bai`, Abbr `bsi`, Abbr `bji`, Abbr `a0`, Abbr `nv`,
             abiDecoderExecutionTheory.abi_decode_backedge_insts_def]) >>
        `LENGTH avs < dimword (:256)` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def] >> rpt strip_tac >>
           fs[abi_encoder_window_array_iff, contractABITheory.valid_length_def]) >>
        `?hdr_bb. lookup_block (FST labels) func.fn_blocks = SOME hdr_bb /\
          phi_prefix_length hdr_bb.bb_instructions = 0` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           qmatch_asmsub_abbrev_tac `lookup_block (FST labels) func.fn_blocks = SOME header_bb` >>
           qexists_tac `header_bb` >> asm_rewrite_tac[] >>
           simp[Abbr `header_bb`, abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
             phi_prefix_length_def, mk_inst_def]) >>
        `bi+32 <= child_s.vs_alloca_next` by
          (qpat_assum `alloca_inv child_s` mp_tac >>
           qpat_assum `FLOOKUP child_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
        mp_tac (Q.INST [
          `s` |-> `child_s`, `G` |-> `childG`, `tn` |-> `childtn`,
          `t` |-> `back_s`, `bb` |-> `bbb`,
          `prefix` |-> `body_end.cs_current_insts`,
          `id` |-> `body_end.cs_next_id`, `iv` |-> `a0`, `nv` |-> `nv`,
          `ip` |-> `iq`, `slot` |-> `bi`,
          `hdr` |-> `FST (labels:string # string # string)`,
          `nitems` |-> `LENGTH (avs:abi_value list)`, `k` |-> `k`, `ctx` |-> `ctx`,
          `func` |-> `func`, `lo` |-> `lo`, `explicit` |-> `explicit`,
          `PG` |-> `PG`] window_array_backedge_joint) >>
        impl_tac >-
          (qpat_assum `lookup_block child_s.vs_current_bb func.fn_blocks = SOME bbb` mp_tac >>
           rpt (qpat_x_assum `lookup_block (FST labels) func.fn_blocks = SOME _` mp_tac) >>
           rpt (qpat_x_assum `phi_prefix_length _.bb_instructions = 0` mp_tac) >>
           qpat_assum `child_s.vs_inst_idx = LENGTH body_end.cs_current_insts` mp_tac >>
           qpat_assum `~child_s.vs_halted` mp_tac >>
           qpat_assum `eval_operand (Var a0) child_s = SOME (n2w k)` mp_tac >>
           qpat_assum `eval_operand ip child_s = SOME (n2w bi)` mp_tac >>
           qpat_assum `ip = Var iq` mp_tac >>
           qpat_assum `ip <> Var nv` mp_tac >>
           qpat_assum `ptr_covers childG childtn iq child_s 32` mp_tac >>
           qpat_assum `bi+32 <= child_s.vs_alloca_next` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           qpat_assum `LENGTH avs < dimword (:256)` mp_tac >>
           qpat_assum `op_prov childG (Var a0) = NONE` mp_tac >>
           qpat_assum `op_taint childtn (Var a0) = {}` mp_tac >>
           qpat_assum `alloca_inv child_s` mp_tac >>
           qpat_assum `alloca_room ctx func child_s` mp_tac >>
           qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
           qpat_assum `allocas_from lo child_s` mp_tac >>
           qpat_assum `lo <= child_s.vs_alloca_next` mp_tac >>
           qpat_assum `Abbrev (bbb = _)` mp_tac >>
           qpat_assum `Abbrev (bai = _)` mp_tac >>
           qpat_assum `Abbrev (bsi = _)` mp_tac >>
           qpat_assum `Abbrev (bji = _)` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `bbb`, Abbr `bai`, Abbr `bsi`, Abbr `bji`,
             Abbr `back_s`, Abbr `br2`, Abbr `br1`,
             abiDecoderExecutionTheory.abi_decode_backedge_insts_def] >>
           metis_tac[]) >>
        disch_then (qx_choose_then `bg2` (qx_choose_then `bt2` strip_assume_tac)) >>
        `!x. not_fresh_at owner x ==> x <> nv` by
          (qpat_assum `owner.cs_next_var <= body_end.cs_next_var` mp_tac >>
           qpat_assum `~not_fresh_at body_end nv` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[not_fresh_at_mono]) >>
        `window_array_transition ctx func owner {loop_st.cs_next_id} [] child_s back_s` by
          (qpat_assum `lookup_block child_s.vs_current_bb func.fn_blocks = SOME bbb` mp_tac >>
           qpat_assum `lookup_block (FST labels) func.fn_blocks = SOME _` mp_tac >>
           rpt (qpat_x_assum `phi_prefix_length _.bb_instructions = 0` mp_tac) >>
           qpat_assum `child_s.vs_inst_idx = LENGTH body_end.cs_current_insts` mp_tac >>
           qpat_assum `~child_s.vs_halted` mp_tac >>
           qpat_assum `eval_operand (Var a0) child_s = SOME (n2w k)` mp_tac >>
           qpat_assum `eval_operand ip child_s = SOME (n2w bi)` mp_tac >>
           qpat_assum `ip <> Var nv` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           qpat_assum `LENGTH avs < dimword (:256)` mp_tac >>
           qpat_assum `bi < dimword (:256)` mp_tac >>
           qpat_assum `FLOOKUP child_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
           qpat_assum `alloca_inv child_s` mp_tac >>
           qpat_assum `alloca_room ctx func child_s` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> x <> nv` mp_tac >>
           qpat_assum `Abbrev (bbb = _)` mp_tac >>
           qpat_assum `Abbrev (bai = _)` mp_tac >>
           qpat_assum `Abbrev (bsi = _)` mp_tac >>
           qpat_assum `Abbrev (bji = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `window_array_transition ctx func owner {loop_st.cs_next_id} [] child_s
             (jump_to (FST labels) (mstore (w2n (n2w bi : bytes32)) (n2w (SUC k))
               (update_var nv (n2w (SUC k)) child_s)))` suffices_by
             fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`, w2n_n2w] >>
           irule window_array_backedge_run >>
           asm_rewrite_tac[] >>
           fs[Abbr `bbb`, Abbr `bai`, Abbr `bsi`, Abbr `bji`,
             abiDecoderExecutionTheory.abi_decode_backedge_insts_def] >>
           metis_tac[]) >>
        `eval_operand count_op child_s = SOME (n2w (LENGTH avs))` by
          (qpat_assum `eval_operand count_op hu = SOME (n2w (LENGTH avs))` mp_tac >>
           qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
           qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner _ _ addr_s child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `eval_operand count_op addr_s = SOME (n2w (LENGTH avs))` by
             metis_tac[window_array_transition_eval] >>
           metis_tac[window_array_transition_eval]) >>
        `window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
          ei asz msz F ty avs src dst ip loop_st.cs_next_id bi
          dp 0 bd count_op (FST labels) sb cap d (SUC k) back_s` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
           qpat_assum `abi_encoder_array_prefix ty avs (SUC k) d child_s.vs_memory` mp_tac >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ child_s` mp_tac >>
           qpat_assum `eval_operand count_op child_s = SOME (n2w (LENGTH avs))` mp_tac >>
           qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> x <> nv` mp_tac >>
           qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
           qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] child_s back_s` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`] >>
           irule window_array_backedge_inv >> asm_rewrite_tac[] >>
           fs[window_array_cursor_def]) >>
        `abi_encode_exec_frame func s back_s` by
          (qpat_assum `abi_encode_exec_frame func s child_s` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `abi_encode_exec_frame func child_s back_s` by
             simp[Abbr `back_s`, Abbr `br2`, Abbr `br1`,
               abi_encode_framed_array_backedge] >>
           metis_tac[abi_encode_exec_frame_trans]) >>
        `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK back_s,bg2,bt2)` by
          (gen_tac >>
           qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK child_s,childG,childtn)`
             (qspec_then `D` mp_tac) >>
           qpat_assum `!D. gas_origin_ptr_path _ (child_s,childG,childtn) [] (OK back_s,bg2,bt2)`
             (qspec_then `D` mp_tac) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
        `mem_bytes_at sb cap back_s.vs_memory = mem_bytes_at sb cap child_s.vs_memory` by
          (qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ child_s` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
           Cases_on `cap = 0` >- fs[valueEncodingDefsTheory.mem_bytes_at_def] >>
           `sb+cap <= bi \/ bi+32 <= sb` by fs[regions_disjoint_def] >>
           simp_tac bool_ss [Abbr `back_s`, Abbr `br2`, Abbr `br1`, jump_to_def] >>
           `mem_bytes_at sb cap (mstore bi (n2w (SUC k))
              (update_var nv (n2w (SUC k)) child_s)).vs_memory =
             mem_bytes_at sb cap (update_var nv (n2w (SUC k)) child_s).vs_memory` by
             metis_tac[mstore_mem_bytes_at_disjoint] >>
           fs[update_var_def]) >>
        `!i. sb <= i /\ i < sb+cap ==>
          (i IN bt2.t_mem <=> i IN childtn.t_mem)` by
          (qpat_assum `bt2.t_mem = childtn.t_mem DIFF _` mp_tac >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ child_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_cursor_def, regions_disjoint_def] >>
           rpt strip_tac >>
           simp[IN_DIFF, GSPECIFICATION] >> decide_tac) >>
        `!mem. mem_agree_outside bt2.t_mem back_s.vs_memory mem ==>
          abi_encoder_window_input (AbiDynArray ei asz msz F)
            (Array NONE ty) (ListV avs) sb cap mem` by
          (gen_tac >> strip_tac >>
           mp_tac (Q.SPECL [`childtn.t_mem`, `bt2.t_mem`, `child_s.vs_memory`,
             `back_s.vs_memory`, `sb`, `sb`, `cap`, `mem`]
             copied_window_agree_witness) >>
           impl_tac >-
             (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >-
               (rpt strip_tac >>
                qpat_assum `!i. sb <= i /\ i < sb+cap ==> _`
                  (qspec_then `sb+i` mp_tac) >>
                qpat_assum `i < cap` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
              first_assum ACCEPT_TAC) >>
           disch_then (qx_choose_then `witness_mem` strip_assume_tac) >>
           `abi_encoder_window_input (AbiDynArray ei asz msz F)
              (Array NONE ty) (ListV avs) sb cap witness_mem` by
             (qpat_assum `!mem. mem_agree_outside childtn.t_mem child_s.vs_memory mem ==>
                abi_encoder_window_input (AbiDynArray ei asz msz F)
                  (Array NONE ty) (ListV avs) sb cap mem`
               (qspec_then `witness_mem` irule) >> first_assum ACCEPT_TAC) >>
           qpat_assum `abi_encoder_window_input _ _ _ _ _ witness_mem` mp_tac >>
           qpat_assum `mem_bytes_at sb cap witness_mem = mem_bytes_at sb cap mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[abi_encoder_window_input_mem_agree]) >>
        `!x. not_fresh_at owner x ==>
          FLOOKUP bg2 x = FLOOKUP childG x /\
          op_taint bt2 (Var x) = op_taint childtn (Var x) /\
          lookup_var x back_s = lookup_var x child_s` by
          (rpt strip_tac >>
           qpat_assum `!x. x <> nv ==> FLOOKUP bg2 x = _ /\ _` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> x <> nv` mp_tac >>
           qpat_assum `not_fresh_at owner x` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`, jump_to_def,
             mstore_def, write_memory_with_expansion_def, update_var_def,
             lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
        `!root span. not_fresh_at owner root /\
          ptr_covers childG childtn root child_s span ==>
          ptr_covers bg2 bt2 root back_s span` by
          (qx_genl_tac [`root`, `span`] >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = _ /\ _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
           metis_tac[]) >>
        `allocas_from lo back_s /\ lo <= back_s.vs_alloca_next` by
          (qpat_assum `allocas_from lo child_s` mp_tac >>
           qpat_assum `lo <= child_s.vs_alloca_next` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >> qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`, jump_to_def,
             mstore_def, write_memory_with_expansion_def, update_var_def, allocas_from_def] >>
           first_assum ACCEPT_TAC) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] addr_s child_s` by
          (qpat_assum `window_array_transition ctx func owner _ _ addr_s child_s` mp_tac >>
           qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
           qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_transition_region >>
           goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
           fs[AC ADD_COMM ADD_ASSOC, MULT_COMM]) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] hu addr_s` by
          (qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_transition_region >>
           goal_assum (drule_at Any) >> simp[]) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] child_s back_s` by
          (qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] child_s back_s` mp_tac >>
           qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_transition_region >>
           goal_assum (drule_at Any) >> simp[]) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u back_s` by
          (qpat_assum `window_array_transition ctx func owner _ _ u hu` mp_tac >>
           qpat_assum `window_array_transition ctx func owner _ _ hu addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids st en)) _ addr_s child_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids st en)) _ child_s back_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[window_array_transition_trans]) >>
        `!op. (!x. op = Var x ==> not_fresh_at owner x) ==>
          op_taint bt2 op = op_taint childtn op /\ op_prov bg2 op = op_prov childG op` by
          (gen_tac >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = _ /\ _` mp_tac >>
           qpat_assum `!x. op = Var x ==> not_fresh_at owner x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `op` >>
           simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
        `LENGTH (enc ty (EL k avs)) = asz /\
          LENGTH (enc (Array NONE ty) (ListV avs)) = 32+LENGTH avs*asz` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
           qpat_assum `~is_dynamic ty` mp_tac >>
           qpat_assum `asz = abi_member_head_size ty` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def] >> rpt strip_tac >>
           `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs` by
             metis_tac[window_array_member_layout] >>
           `abi_encoder_layout_valid ty (EL k avs)` by fs[LIST_REL_EL_EQN, EL_REPLICATE] >>
           `LENGTH (enc ty (EL k avs)) = asz` by
             fs[abiEncoderOpenInputTheory.abi_encoder_layout_valid_def, abiDecodeRangesTheory.abi_member_head_size_def] >>
           `SUM (MAP (abi_member_tail_size ty) avs) = 0` by
             (simp[SUM_eq_0, MEM_MAP] >> rpt strip_tac >>
              fs[abiDecodeRangesTheory.abi_member_tail_size_def]) >>
           drule window_array_layout >> fs[Excl "enc_def"]) >>
        `!i. d <= i /\ i < d+32+k*asz ==>
          i NOTIN childtn.t_mem` by
          (gen_tac >> strip_tac >>
           qpat_assum `!i. (i < d+32+k*asz \/ d+32+k*asz+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==> (i IN childtn.t_mem <=> i IN at7.t_mem)`
             (qspec_then `i` mp_tac) >> impl_tac >-
             (conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
              rpt strip_tac >>
              rename1 `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` >>
              `regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs)))
                (scratch_b,scratch_sz)` by
                (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
                 qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
                 qpat_assum `aid IN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
                 qpat_assum `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >>
                 simp_tac bool_ss [window_array_root_def, SUBSET_DEF] >> metis_tac[]) >>
              `k*asz <= LENGTH avs*asz` by simp[] >>
              qpat_assum `regions_disjoint (d,_) (scratch_b,scratch_sz)` mp_tac >>
              qpat_assum `LENGTH (enc (Array NONE ty) (ListV avs)) = _` mp_tac >>
              qpat_assum `d <= i` mp_tac >> qpat_assum `i < d+32+k*asz` mp_tac >>
              qpat_assum `k*asz <= LENGTH avs*asz` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           qpat_assum `!i. d <= i /\ i < d+32+k*abi_member_head_size ty ==> i NOTIN kt.t_mem`
             (qspec_then `i` mp_tac) >>
           qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
           qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
           qpat_assum `asz = abi_member_head_size ty` mp_tac >>
           qpat_assum `d <= i` mp_tac >> qpat_assum `i < d+32+k*asz` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[AC ADD_COMM ADD_ASSOC, MULT_COMM] >> metis_tac[]) >>
        `!i. d <= i /\ i < d+32+SUC k*asz ==> i NOTIN bt2.t_mem` by
          (gen_tac >> strip_tac >>
           `i NOTIN childtn.t_mem` by
             (Cases_on `i < d+32+k*asz`
              >- (qpat_assum `!i. d <= i /\ i < d+32+k*asz ==> i NOTIN childtn.t_mem`
                    (qspec_then `i` mp_tac) >> simp[]) >>
              qpat_assum `!i. d+32+k*asz <= i /\ i < d+32+k*asz+LENGTH (enc ty (EL k avs)) ==> _`
                (qspec_then `i` mp_tac) >>
              qpat_assum `LENGTH (enc ty (EL k avs)) = asz` mp_tac >>
              qpat_assum `i < d+32+SUC k*asz` mp_tac >>
              qpat_assum `~(i < d+32+k*asz)` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
           qpat_assum `bt2.t_mem = childtn.t_mem DIFF _` mp_tac >>
           qpat_assum `i NOTIN childtn.t_mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `!x. not_fresh_at owner x ==>
          FLOOKUP bg2 x = FLOOKUP kg x /\
          op_taint bt2 (Var x) = op_taint kt (Var x)` by
          (gen_tac >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP childG x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at body_st x ==> FLOOKUP ag7 x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP hg x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `not_fresh_at owner x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `!root span. not_fresh_at owner root /\
          ptr_covers kg kt root u span ==> ptr_covers bg2 bt2 root back_s span` by
          (qx_genl_tac [`root`, `span`] >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = FLOOKUP kg x /\ _` mp_tac >>
           qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids st en)) _ u back_s` mp_tac >>
           qpat_assum `not_fresh_at owner root` mp_tac >>
           qpat_assum `ptr_covers kg kt root u span` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
           metis_tac[window_array_transition_vars]) >>
        `op_taint bt2 count_op = {} /\ op_prov bg2 count_op = NONE` by
          (qpat_assum `op_taint kt count_op = {}` mp_tac >>
           qpat_assum `op_prov kg count_op = NONE` mp_tac >>
           qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = FLOOKUP kg x /\ _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `count_op` >>
           simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
        `window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
          (LENGTH (enc (Array NONE ty) (ListV avs))) back_s` by
          (qpat_assum `window_array_cursor T owner pp st.cs_next_id b 0 _ _ _ _ child_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] child_s back_s` mp_tac >>
           qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_cursor_frame >>
           goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
        `!cop csite cslot cvalue.
          window_array_cursor T owner cop csite cslot cvalue sb cap d
            (LENGTH (enc (Array NONE ty) (ListV avs))) child_s /\
          csite NOTIN window_alloca_sites func (frag_ids addressed body_end) /\
          (!i. cslot <= i /\ i < cslot+32 ==> i NOTIN at7.t_mem) ==>
          !i. cslot <= i /\ i < cslot+32 ==> i NOTIN childtn.t_mem` by
          (qx_genl_tac [`cop`, `csite`, `cslot`, `cvalue`] >> strip_tac >>
           gen_tac >> strip_tac >>
           qpat_assum `!i. (i < d+32+k*asz \/ d+32+k*asz+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==> (i IN childtn.t_mem <=> i IN at7.t_mem)`
             (qspec_then `i` mp_tac) >> impl_tac >-
             (conj_tac >-
               (qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ child_s` mp_tac >>
                qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
                qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >>
                simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
                qpat_assum `regions_disjoint (d,_) (cslot,32)` mp_tac >>
                qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
                qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >>
                pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
              rpt strip_tac >>
              rename1 `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` >>
              `csite <> aid` by
                (qpat_assum `csite NOTIN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
                 qpat_assum `aid IN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
              `cslot+32 <= scratch_b \/ scratch_b+scratch_sz <= cslot` by
                (qpat_assum `alloca_inv child_s` mp_tac >>
                 qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ child_s` mp_tac >>
                 qpat_assum `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` mp_tac >>
                 qpat_assum `csite <> aid` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >>
                 simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def,
                   window_array_cursor_def] >> metis_tac[]) >>
              rpt (qpat_x_assum `cslot+32 <= scratch_b` mp_tac) >>
              rpt (qpat_x_assum `scratch_b+scratch_sz <= cslot` mp_tac) >>
              qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
           qpat_assum `!i. cslot <= i /\ i < cslot+32 ==> i NOTIN at7.t_mem`
             (qspec_then `i` mp_tac) >>
           qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `(!i. b <= i /\ i < b+32 ==> i NOTIN bt2.t_mem) /\
          (!i. bi <= i /\ i < bi+32 ==> i NOTIN bt2.t_mem)` by
          (`!i. b <= i /\ i < b+32 ==> i NOTIN childtn.t_mem` by
             (qpat_assum `!cop csite cslot cvalue. _`
                (qspecl_then [`pp`, `st.cs_next_id`, `b`, `0`] mp_tac) >>
              qpat_assum `window_array_cursor T owner pp st.cs_next_id b 0 _ _ _ _ child_s` mp_tac >>
              qpat_assum `st.cs_next_id NOTIN window_alloca_sites func (frag_ids addressed body_end)` mp_tac >>
              qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN kt.t_mem` mp_tac >>
              qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
              qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
           qpat_assum `bt2.t_mem = childtn.t_mem DIFF _` mp_tac >>
           qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN childtn.t_mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF, GSPECIFICATION] >> metis_tac[]) >>
        `!i. (i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i) /\
          (!aid scratch_b scratch_sz.
            aid IN window_alloca_sites func (frag_ids st en) /\
            FLOOKUP back_s.vs_allocas aid = SOME (scratch_b,scratch_sz) ==>
            i < scratch_b \/ scratch_b+scratch_sz <= i) ==>
          (i IN bt2.t_mem <=> i IN tn.t_mem)` by
          (gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
           `!aid r. FLOOKUP u.vs_allocas aid = SOME r ==>
             FLOOKUP back_s.vs_allocas aid = SOME r` by
             (qpat_assum `window_array_transition ctx func owner
                (window_alloca_sites func (frag_ids st en)) _ u back_s` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
           `!aid r. FLOOKUP child_s.vs_allocas aid = SOME r ==>
             FLOOKUP back_s.vs_allocas aid = SOME r` by
             (qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] child_s back_s` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
           `~(bi <= i /\ i < bi+32)` by
             (qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _`
                (qspecl_then [`loop_st.cs_next_id`, `bi`, `32`] mp_tac) >>
              qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
              qpat_assum `FLOOKUP child_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
              qpat_assum `!aid r. FLOOKUP child_s.vs_allocas aid = SOME r ==> _` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
              `i < bi \/ bi+32 <= i` by metis_tac[] >> decide_tac) >>
           `i IN childtn.t_mem <=> i IN at7.t_mem` by
             (qpat_assum `!i. (i < d+32+k*asz \/ d+32+k*asz+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==> (i IN childtn.t_mem <=> i IN at7.t_mem)`
                (qspec_then `i` mp_tac) >> impl_tac >-
                (conj_tac >-
                  (qpat_assum `i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i` mp_tac >>
                   qpat_assum `32+k*asz+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
                   POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
                 qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _` mp_tac >>
                 qpat_assum `!aid r. FLOOKUP child_s.vs_allocas aid = SOME r ==> _` mp_tac >>
                 qpat_assum `window_alloca_sites func (frag_ids addressed body_end) SUBSET _` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >> simp[]) >>
           `i IN kt.t_mem <=> i IN tn.t_mem` by
             (qpat_assum `!i. _ ==> (i IN kt.t_mem <=> i IN tn.t_mem)`
                (qspec_then `i` mp_tac) >> impl_tac >-
                (conj_tac >- first_assum ACCEPT_TAC >>
                 qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _` mp_tac >>
                 qpat_assum `!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> _` mp_tac >>
                 POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >> simp[]) >>
           qpat_assum `bt2.t_mem = childtn.t_mem DIFF _` mp_tac >>
           qpat_assum `~(bi <= i /\ i < bi+32)` mp_tac >>
           qpat_assum `i IN childtn.t_mem <=> i IN at7.t_mem` mp_tac >>
           qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
           qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
           qpat_assum `i IN kt.t_mem <=> i IN tn.t_mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF, GSPECIFICATION] >> decide_tac) >>
        `(?q. src = Var q /\ ptr_covers bg2 bt2 q back_s cap) /\
          (?q. dst = Var q /\ ptr_covers bg2 bt2 q back_s
            (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
          (?q. ip = Var q /\ ptr_covers bg2 bt2 q back_s 32) /\
          (?q. pp = Var q /\ ptr_covers bg2 bt2 q back_s 32)` by
          (qpat_assum `!root span. not_fresh_at owner root /\ ptr_covers kg kt root u span ==> _` mp_tac >>
           qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
           qpat_assum `window_array_cursor T owner ip _ _ _ _ _ _ _ hu` mp_tac >>
           qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ hu` mp_tac >>
           rpt (qpat_x_assum `ptr_covers kg kt _ u _` mp_tac) >>
           rpt (qpat_x_assum `src = Var _` mp_tac) >>
           rpt (qpat_x_assum `dst = Var _` mp_tac) >>
           rpt (qpat_x_assum `ip = Var _` mp_tac) >>
           rpt (qpat_x_assum `pp = Var _` mp_tac) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def, window_array_cursor_def] >>
           rpt strip_tac >> metis_tac[]) >>
        `st.cs_next_var <= owner.cs_next_var` by
          (qpat_assum `if F then abi_encode_array_dynamic_init _ _ _ = _ else _` mp_tac >>
           qpat_assum `loop_st.cs_next_var = st.cs_next_var+2` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [] >> rpt strip_tac >>
           drule abi_decode_index_init_shape >> simp[] >> decide_tac) >>
        `!x. not_fresh_at st x ==>
          FLOOKUP bg2 x = FLOOKUP G x /\ op_taint bt2 (Var x) = op_taint tn (Var x)` by
          (gen_tac >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = FLOOKUP kg x /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at st x ==> FLOOKUP kg x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `not_fresh_at st x` mp_tac >>
           qpat_assum `st.cs_next_var <= owner.cs_next_var` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
        `bt2.t_stor = tn.t_stor /\ bt2.t_trans = tn.t_trans /\ bt2.t_imm = tn.t_imm` by
          (qpat_assum `bt2.t_stor = childtn.t_stor` mp_tac >>
           qpat_assum `bt2.t_trans = childtn.t_trans` mp_tac >>
           qpat_assum `bt2.t_imm = childtn.t_imm` mp_tac >>
           qpat_assum `childtn.t_stor = at7.t_stor` mp_tac >>
           qpat_assum `childtn.t_trans = at7.t_trans` mp_tac >>
           qpat_assum `childtn.t_imm = at7.t_imm` mp_tac >>
           qpat_assum `at7.t_stor = ht.t_stor` mp_tac >>
           qpat_assum `at7.t_trans = ht.t_trans` mp_tac >>
           qpat_assum `at7.t_imm = ht.t_imm` mp_tac >>
           qpat_assum `ht.t_stor = kt.t_stor` mp_tac >>
           qpat_assum `ht.t_trans = kt.t_trans` mp_tac >>
           qpat_assum `ht.t_imm = kt.t_imm` mp_tac >>
           qpat_assum `kt.t_stor = tn.t_stor` mp_tac >>
           qpat_assum `kt.t_trans = tn.t_trans` mp_tac >>
           qpat_assum `kt.t_imm = tn.t_imm` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `!values. SUM (MAP (abi_member_tail_size ty) values) = 0` by
          (qpat_assum `~is_dynamic ty` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
           rpt strip_tac >> simp[SUM_eq_0, MEM_MAP] >> rpt strip_tac >>
           fs[abiDecodeRangesTheory.abi_member_tail_size_def]) >>
        qpat_assum `asz = abi_member_head_size ty` SUBST_ALL_TAC >>
        qpat_assum `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en)) _ u back_s` mp_tac >>
        qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ back_s` mp_tac >>
        qpat_assum `abi_encode_exec_frame func s back_s` mp_tac >>
        qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ back_s` mp_tac >>
        qpat_assum `allocas_from lo back_s` mp_tac >>
        qpat_assum `lo <= back_s.vs_alloca_next` mp_tac >>
        qpat_assum `op_taint bt2 count_op = {}` mp_tac >>
        qpat_assum `op_prov bg2 count_op = NONE` mp_tac >>
        rpt (qpat_x_assum `ptr_covers bg2 bt2 _ back_s _` mp_tac) >>
        rpt (qpat_x_assum `src = Var _` mp_tac) >>
        rpt (qpat_x_assum `dst = Var _` mp_tac) >>
        rpt (qpat_x_assum `ip = Var _` mp_tac) >>
        rpt (qpat_x_assum `pp = Var _` mp_tac) >>
        qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN bt2.t_mem` mp_tac >>
        qpat_assum `!i. bi <= i /\ i < bi+32 ==> i NOTIN bt2.t_mem` mp_tac >>
        qpat_assum `!mem. mem_agree_outside bt2.t_mem back_s.vs_memory mem ==> _` mp_tac >>
        qpat_assum `!x. not_fresh_at st x ==> FLOOKUP bg2 x = FLOOKUP G x /\ _` mp_tac >>
        qpat_assum `!i. d <= i /\ i < d+32+SUC k*abi_member_head_size ty ==> i NOTIN bt2.t_mem` mp_tac >>
        qpat_assum `!i. _ ==> (i IN bt2.t_mem <=> i IN tn.t_mem)` mp_tac >>
        qpat_assum `bt2.t_stor = tn.t_stor` mp_tac >>
        qpat_assum `bt2.t_trans = tn.t_trans` mp_tac >>
        qpat_assum `bt2.t_imm = tn.t_imm` mp_tac >>
        qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK back_s,bg2,bt2)` mp_tac >>
        qpat_assum `!values. SUM (MAP (abi_member_tail_size ty) values) = 0` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        qexists_tac `back_s` >> conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`bg2`, `bt2`] >>
        asm_rewrite_tac[] >>
        asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
        rpt strip_tac >> decide_tac) >>
     `?ops prepared child_len child_end.
       abi_encode_array_tail (Var a4) dp addressed = (ops,prepared) /\
       compile_abi_encode_to_buf (SND ops) (Var a3) ei prepared = (child_len,child_end) /\
       abi_encode_child_suffix (Var a6) dp (FST ops) child_len child_end = (child_len,body_end) /\
       idx = Var a0 /\ fn_has_code addressed prepared func /\
       fn_has_code prepared child_end func /\ fn_has_code child_end body_end func /\
       prepared.cs_next_id = addressed.cs_next_id+2 /\
       prepared.cs_next_var = addressed.cs_next_var+2 /\
       prepared.cs_next_id <= child_end.cs_next_id /\
       prepared.cs_next_var <= child_end.cs_next_var /\
       child_end.cs_next_id+3 = body_end.cs_next_id /\
       child_end.cs_next_var+1 = body_end.cs_next_var /\
       body_end.cs_blocks = child_end.cs_blocks /\
       body_end.cs_current_bb = child_end.cs_current_bb /\
       abi_decoder_operand_live child_end.cs_next_var child_len` by
       (qpat_assum `if T then abi_encode_array_dynamic_body _ _ _ _ _ _ _ _ = _ else _` mp_tac >>
        qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
        qpat_assum `abi_encode_array_addresses ip src dst asz msz body_st = (coords,addressed)` mp_tac >>
        qpat_assum `coords = ((Var a0,Var a3),(Var a4,Var a6))` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
        drule_all abiEncoderArrayDynamicMemoryTheory.abi_encode_array_dynamic_body_context >>
        strip_tac >> gvs[] >> metis_tac[]) >>
     qabbrev_tac `off = LENGTH avs * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) (TAKE k avs))` >>
     `eval_operand dp addr_s = SOME (n2w bd) /\ bd < dimword (:256) /\
      mem_word_at bd addr_s.vs_memory = n2w off /\
      (!x. dp = Var x ==> not_fresh_at addressed x)` by
       (qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `T ==> ?q. dp = Var q /\ ptr_covers hg ht q hu 32` mp_tac >>
        qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `window_pure_seq body_st addressed hu ar7` mp_tac >>
        qpat_assum `addressed.cs_next_var = body_st.cs_next_var+7` mp_tac >>
        simp_tac bool_ss [Abbr `addr_s`, Abbr `off`] >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def,
          abiEncoderWindowSequenceTheory.window_pure_seq_def,
          abiEncoderWindowSequenceTheory.window_seq_def, instIdxIndepTheory.eval_op_inst_idx] >>
        rpt strip_tac >>
        `body_st.cs_next_var <= addressed.cs_next_var` by decide_tac >>
        gvs[eval_operand_def] >>
        irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `body_st` >>
        asm_simp_tac (srw_ss()) []) >>
     `?offset middle child_dst.
       emit_op MLOAD [dp] addressed = (offset,middle) /\
       emit_op ADD [Var a4;offset] middle = (child_dst,prepared) /\
       ops = (offset,child_dst)` by
       (qpat_assum `abi_encode_array_tail (Var a4) dp addressed = (ops,prepared)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abiEncoderArrayTailTheory.abi_encode_array_tail_def,
          comp_bind_def, comp_return_def, LET_THM] >>
        rpt (pairarg_tac >> gvs[]) >> strip_tac >> metis_tac[]) >>
     `?tail_raw. window_pure_seq addressed prepared addr_s tail_raw /\
       eval_operand (FST ops) tail_raw = SOME (n2w off) /\
       eval_operand (SND ops) tail_raw = SOME (n2w (d+32+off)) /\
       (!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at prepared x) /\
       (!x. ~not_fresh_at prepared x ==> lookup_var x tail_raw = lookup_var x addr_s)` by
       (qpat_assum `abi_encode_array_tail (Var a4) dp addressed = (ops,prepared)` mp_tac >>
        qpat_assum `eval_operand dp addr_s = SOME (n2w bd)` mp_tac >>
        qpat_assum `bd < dimword (:256)` mp_tac >>
        qpat_assum `mem_word_at bd addr_s.vs_memory = n2w off` mp_tac >>
        qpat_assum `eval_operand (Var a4) addr_s = SOME (n2w (d+32))` mp_tac >>
        qpat_assum `not_fresh_at addressed a4` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `mload bd addr_s = n2w off` by metis_tac[GSYM mem_word_at_eq_mload] >>
        `!x. Var a4 = Var x ==> not_fresh_at addressed x` by simp[] >>
        drule_all window_array_tail_pure_observed >> strip_tac >>
        goal_assum (drule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `emit_op MLOAD [dp] addressed = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD [Var a4;offset] middle = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qabbrev_tac `ov = STRING #"%" (toString addressed.cs_next_var)` >>
     qabbrev_tac `cv = STRING #"%" (toString middle.cs_next_var)` >>
     `offset = Var ov /\ child_dst = Var cv` by
       (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qabbrev_tac `ti1 = mk_inst addressed.cs_next_id MLOAD [dp] [ov]` >>
     qabbrev_tac `ti2 = mk_inst middle.cs_next_id ADD [Var a4;offset] [cv]` >>
     `emitted_insts addressed prepared = [ti1;ti2]` by
       (qpat_assum `middle.cs_current_insts = addressed.cs_current_insts ++ _` mp_tac >>
        qpat_assum `prepared.cs_current_insts = middle.cs_current_insts ++ _` mp_tac >>
        simp_tac bool_ss [Abbr `ti1`, Abbr `ti2`, Abbr `ov`, Abbr `cv`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
     `?load_s. step_inst_base ti1 addr_s = OK load_s /\
       step_inst_base ti2 load_s = OK tail_raw` by
       (qpat_assum `window_pure_seq addressed prepared addr_s tail_raw` mp_tac >>
        qpat_assum `emitted_insts addressed prepared = [ti1;ti2]` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiEncoderWindowSequenceTheory.window_pure_seq_def,
          abiEncoderWindowSequenceTheory.window_seq_def, run_inst_seq_def, AllCaseEqs()] >>
        metis_tac[]) >>
     `load_s = update_var ov (n2w off) addr_s` by
       (qpat_assum `step_inst_base ti1 addr_s = OK load_s` mp_tac >>
        qpat_assum `eval_operand dp addr_s = SOME (n2w bd)` mp_tac >>
        qpat_assum `mem_word_at bd addr_s.vs_memory = n2w off` mp_tac >>
        qpat_assum `bd < dimword (:256)` mp_tac >>
        simp_tac bool_ss [Abbr `ti1`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[step_inst_base_opcode_eqs, exec_read1_def,
          w2n_n2w, LESS_MOD, GSYM mem_word_at_eq_mload]) >>
     qabbrev_tac `tail_s = tail_raw with vs_inst_idx := LENGTH prepared.cs_current_insts` >>
     `window_phase ctx func addressed prepared {} [] addr_s tail_s` by
       (simp_tac bool_ss [Abbr `tail_s`] >> irule window_pure_seq_phase >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `!x. not_fresh_at addressed x ==> x <> ov /\ x <> cv` by
       (qpat_assum `middle.cs_next_var = addressed.cs_next_var+1` mp_tac >>
        simp_tac bool_ss [Abbr `ov`, Abbr `cv`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
        metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
     `ov <> cv` by
       (qpat_assum `middle.cs_next_var = addressed.cs_next_var+1` mp_tac >>
        simp_tac bool_ss [Abbr `ov`, Abbr `cv`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
        `addressed.cs_next_var <> middle.cs_next_var` by decide_tac >>
        metis_tac[listTheory.CONS_11,
          REWRITE_RULE [FUN_EQ_THM, combinTheory.o_DEF, combinTheory.I_THM]
            ASCIInumbersTheory.num_dec_string]) >>
     `ov <> a4 /\ cv <> a4` by
       (qpat_assum `!x. not_fresh_at addressed x ==> _` mp_tac >>
        qpat_assum `not_fresh_at addressed a4` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `eval_operand (Var a4) load_s = SOME (n2w (d+32)) /\
      eval_operand offset load_s = SOME (n2w off)` by
       (qpat_assum `load_s = update_var ov (n2w off) addr_s` mp_tac >>
        qpat_assum `eval_operand (Var a4) addr_s = SOME (n2w (d+32))` mp_tac >>
        qpat_assum `ov <> a4` mp_tac >> qpat_assum `offset = Var ov` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
        gvs[eval_operand_def, lookup_var_def]) >>
     `tail_raw = update_var cv (n2w (d+32+off)) load_s` by
       (qpat_assum `step_inst_base ti2 load_s = OK tail_raw` mp_tac >>
        qpat_assum `eval_operand (Var a4) load_s = SOME (n2w (d+32))` mp_tac >>
        qpat_assum `eval_operand offset load_s = SOME (n2w off)` mp_tac >>
        simp_tac bool_ss [Abbr `ti2`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[step_inst_base_opcode_eqs, exec_pure2_def, word_add_n2w]) >>
     `!i. bd <= i /\ i < bd+32 ==> i NOTIN at7.t_mem` by
       (qpat_assum `T ==> (?q. dp = Var q /\ ptr_covers kg kt q u 32) /\ _` mp_tac >>
        qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
        qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     qabbrev_tac `tg1 = step_prov PG ag7 ti1 load_s` >>
     qabbrev_tac `tt1 = step_taint ti1 addr_s load_s at7` >>
     qabbrev_tac `tg2 = step_prov PG tg1 ti2 tail_raw` >>
     qabbrev_tac `tt2 = step_taint ti2 load_s tail_raw tt1` >>
     `op_taint tt1 (Var ov) = {} /\ tt1.t_mem = at7.t_mem /\
      tt1.t_stor = at7.t_stor /\ tt1.t_trans = at7.t_trans` by
       (qpat_assum `!i. bd <= i /\ i < bd+32 ==> i NOTIN at7.t_mem` mp_tac >>
        qpat_assum `eval_operand dp addr_s = SOME (n2w bd)` mp_tac >>
        qpat_assum `mem_word_at bd addr_s.vs_memory = n2w off` mp_tac >>
        qpat_assum `bd < dimword (:256)` mp_tac >>
        qpat_assum `load_s = update_var ov (n2w off) addr_s` mp_tac >>
        simp_tac bool_ss [Abbr `tt1`, Abbr `ti1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        qpat_assum `eval_operand dp addr_s = SOME (n2w bd)`
          (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
        simp_tac (srw_ss()) [w2n_n2w, LESS_MOD, GSYM mem_word_at_eq_mload] >>
        disch_then (qspecl_then [`at7`, `addressed.cs_next_id`, `ov`] mp_tac) >> simp[]) >>
     `op_taint at7 (Var a4) = {}` by
       (qpat_assum `!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {}`
          (qspec_then `a4` mp_tac) >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `op_taint tt1 (Var a4) = {} /\ op_taint tt1 offset = {}` by
       (qpat_assum `op_taint at7 (Var a4) = {}` mp_tac >>
        qpat_assum `op_taint tt1 (Var ov) = {}` mp_tac >>
        qpat_assum `offset = Var ov` mp_tac >> qpat_assum `ov <> a4` mp_tac >>
        simp_tac bool_ss [Abbr `tt1`, Abbr `ti1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_simp_tac (srw_ss()) [step_taint_other_output, mk_inst_def]) >>
     `new_site_bytes load_s tail_raw = {}` by
       (qpat_assum `tail_raw = update_var cv (n2w (d+32+off)) load_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
        simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]) >>
     `tt2 = tt1 with t_var := tt1.t_var |+ (cv,{})` by
       (qpat_assum `op_taint tt1 (Var a4) = {}` mp_tac >>
        qpat_assum `op_taint tt1 offset = {}` mp_tac >>
        qpat_assum `new_site_bytes load_s tail_raw = {}` mp_tac >>
        simp_tac bool_ss [Abbr `tt2`, Abbr `ti2`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp[step_taint_def, set_var_taint_def, out_taint_def,
          mem_taint_def, step_writes_def, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
          written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
        CASE_TAC >> simp[taint_component_equality]) >>
     `tt1.t_imm = at7.t_imm` by
       (simp_tac bool_ss [Abbr `tt1`, Abbr `ti1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[step_taint_def, imm_taint_def, mk_inst_def]) >>
     `tt2.t_mem = at7.t_mem /\ tt2.t_stor = at7.t_stor /\
      tt2.t_trans = at7.t_trans /\ tt2.t_imm = at7.t_imm` by
       (qpat_assum `tt2 = tt1 with t_var := _` mp_tac >>
        qpat_assum `tt1.t_mem = at7.t_mem` mp_tac >>
        qpat_assum `tt1.t_stor = at7.t_stor` mp_tac >>
        qpat_assum `tt1.t_trans = at7.t_trans` mp_tac >>
        qpat_assum `tt1.t_imm = at7.t_imm` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `op_taint tt2 offset = {} /\ op_taint tt2 child_dst = {}` by
       (qpat_assum `tt2 = tt1 with t_var := _` mp_tac >>
        qpat_assum `op_taint tt1 (Var ov) = {}` mp_tac >>
        qpat_assum `offset = Var ov` mp_tac >>
        qpat_assum `child_dst = Var cv` mp_tac >>
        qpat_assum `ov <> cv` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        gvs[op_taint_def, FLOOKUP_UPDATE]) >>
     `!x. not_fresh_at addressed x ==>
       FLOOKUP tg2 x = FLOOKUP ag7 x /\
       op_taint tt2 (Var x) = op_taint at7 (Var x)` by
       (rpt strip_tac >>
        `x <> ov /\ x <> cv` by
          (qpat_assum `!x. not_fresh_at addressed x ==> x <> ov /\ _` mp_tac >>
           qpat_assum `not_fresh_at addressed x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        qpat_assum `x <> ov` mp_tac >> qpat_assum `x <> cv` mp_tac >>
        simp_tac bool_ss [Abbr `tg2`, Abbr `tg1`, Abbr `tt2`, Abbr `tt1`,
          Abbr `ti1`, Abbr `ti2`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_simp_tac (srw_ss()) [step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
     `?dq. dp = Var dq /\ ptr_covers ag7 at7 dq addr_s 32` by
       (qpat_assum `T ==> ?q. dp = Var q /\ ptr_covers hg ht q hu 32` mp_tac >>
        qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `!root span. not_fresh_at body_st root /\ ptr_covers hg ht root hu span ==> _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >> metis_tac[]) >>
     `bd+32 <= addr_s.vs_alloca_next` by
       (qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `alloca_inv hu` mp_tac >>
        qpat_assum `addr_s.vs_alloca_next = hu.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def, alloca_inv_def, alloca_next_valid_def] >>
        rpt strip_tac >> metis_tac[]) >>
     `run_inst_seq_mem_ok [ti1;ti2] addr_s` by
       (qpat_assum `step_inst_base ti1 addr_s = OK load_s` mp_tac >>
        qpat_assum `step_inst_base ti2 load_s = OK tail_raw` mp_tac >>
        qpat_assum `eval_operand dp addr_s = SOME (n2w bd)` mp_tac >>
        qpat_assum `bd < dimword (:256)` mp_tac >>
        qpat_assum `bd+32 <= addr_s.vs_alloca_next` mp_tac >>
        simp_tac bool_ss [Abbr `ti1`, Abbr `ti2`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
        qpat_assum `step_inst_base (mk_inst _ MLOAD _ _) addr_s = OK load_s`
          (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
        qpat_assum `step_inst_base (mk_inst _ ADD _ _) load_s = OK tail_raw`
          (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
        asm_simp_tac (srw_ss()) [unitTransformDefsTheory.inst_mem_below_frontier_def,
          memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def,
          codegenRelTheory.fixed_source_write_range_def,
          w2n_n2w, LESS_MOD]) >>
     `!j. step_inst_base ti1 (addr_s with vs_inst_idx := j) =
       OK (load_s with vs_inst_idx := j) /\
       step_inst_base ti2 (load_s with vs_inst_idx := j) =
       OK (tail_raw with vs_inst_idx := j)` by
       (qpat_assum `step_inst_base ti1 addr_s = OK load_s` mp_tac >>
        qpat_assum `step_inst_base ti2 load_s = OK tail_raw` mp_tac >>
        simp_tac bool_ss [Abbr `ti1`, Abbr `ti2`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
          instIdxIndepTheory.exec_result_map_def, mk_inst_def, is_terminator_def]) >>
     `!D j. ptr_inst_ok D lo 0 ctx func ag7 at7 ti1
       (addr_s with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `ptr_covers ag7 at7 _ addr_s 32` mp_tac >>
        qpat_assum `dp = Var _` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `allocas_from lo addr_s` mp_tac >>
        simp_tac bool_ss [Abbr `ti1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
        irule ptr_inst_ok_lower_bound_transport >>
        conj_tac >- (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
        qexists_tac `0` >>
        asm_simp_tac (srw_ss()) [allocas_from_def] >>
        irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[]) >>
     `!D j. ptr_inst_ok D lo 0 ctx func tg1 tt1 ti2
       (load_s with vs_inst_idx := j)` by
       (rpt gen_tac >>
        qpat_assum `op_taint tt1 (Var a4) = {}` mp_tac >>
        qpat_assum `op_taint tt1 offset = {}` mp_tac >>
        qpat_assum `allocas_from lo addr_s` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `!j. step_inst_base ti1 _ = _ /\ step_inst_base ti2 _ = _` mp_tac >>
        qpat_assum `load_s = update_var ov (n2w off) addr_s` mp_tac >>
        qpat_assum `tail_raw = update_var cv (n2w (d+32+off)) load_s` mp_tac >>
        qpat_assum `Abbrev (ti2 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `step_inst 0 ctx ti2 (load_s with vs_inst_idx := j) =
          OK (tail_raw with vs_inst_idx := j)` by
          (asm_simp_tac (srw_ss()) [step_inst_non_invoke, Abbr `ti2`, mk_inst_def]) >>
        simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `ti2`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def] >>
        conj_tac
        >- (gen_tac >> Cases_on `op = Var a4` >> fs[] >>
            Cases_on `op = offset` >> fs[]) >>
        fs[allocas_from_def, update_var_def] >> first_assum ACCEPT_TAC) >>
     `!D. inst_seq_ptr D lo ctx func PG ag7 at7 [ti1;ti2] addr_s tg2 tt2` by
       (gen_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag7 at7 ti1 _` mp_tac >>
        qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func tg1 tt1 ti2 _` mp_tac >>
        qpat_assum `step_inst_base ti1 addr_s = OK load_s` mp_tac >>
        qpat_assum `!j. step_inst_base ti1 _ = _ /\ step_inst_base ti2 _ = _` mp_tac >>
        qpat_assum `Abbrev (tg1 = _)` mp_tac >>
        qpat_assum `Abbrev (tt1 = _)` mp_tac >>
        qpat_assum `Abbrev (tg2 = _)` mp_tac >>
        qpat_assum `Abbrev (tt2 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        pure_rewrite_tac[inst_seq_ptr_def] >>
        qpat_assum `step_inst_base ti1 addr_s = OK load_s`
          (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
        simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
          step_taint_inst_idx_right] >>
        map_every (fn q => qpat_assum q (fn th =>
          pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
          [`Abbrev (tg1 = _)`, `Abbrev (tt1 = _)`] >>
        qpat_assum `!j. step_inst_base ti1 _ = _ /\ step_inst_base ti2 _ = _`
          (fn th => pure_rewrite_tac[th]) >>
        simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
          step_taint_inst_idx_right] >>
        map_every (fn q => qpat_assum q (fn th =>
          pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
          [`Abbrev (tg2 = _)`, `Abbrev (tt2 = _)`] >>
        conj_tac
        >- (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func ag7 at7 ti1 _`
              (qspecl_then [`D`, `addr_s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
        metis_tac[]) >>
     `prepared.cs_current_insts = addressed.cs_current_insts ++ [ti1;ti2] /\
      prepared.cs_current_bb = addressed.cs_current_bb` by
       (qpat_assum `window_pure_seq addressed prepared addr_s tail_raw` mp_tac >>
        qpat_assum `emitted_insts addressed prepared = [ti1;ti2]` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [abiEncoderWindowSequenceTheory.window_pure_seq_def, abiEncoderWindowSequenceTheory.window_seq_def,
          emitted_insts_def, inst_extends_def] >> rpt strip_tac >> metis_tac[]) >>
     `?tbb. lookup_block addr_s.vs_current_bb func.fn_blocks = SOME tbb /\
       isPREFIX [ti1;ti2] (DROP addr_s.vs_inst_idx tbb.bb_instructions)` by
       (map_every (fn pat => qpat_assum pat mp_tac)
          [`fn_has_code addressed prepared func`, `prepared.cs_current_insts = _`,
           `prepared.cs_current_bb = _`, `addr_s.vs_current_bb = _`,
           `addr_s.vs_inst_idx = _`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rw[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND] >>
        qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
        asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (addr_s,ag7,at7) [] (OK tail_s,tg2,tt2)` by
       (gen_tac >>
        qpat_assum `lookup_block addr_s.vs_current_bb func.fn_blocks = SOME tbb` mp_tac >>
        qpat_assum `isPREFIX [ti1;ti2] _` mp_tac >>
        qpat_assum `~addr_s.vs_halted` mp_tac >>
        qpat_assum `window_pure_seq addressed prepared addr_s tail_raw` mp_tac >>
        qpat_assum `emitted_insts addressed prepared = [ti1;ti2]` mp_tac >>
        qpat_assum `run_inst_seq_mem_ok [ti1;ti2] addr_s` mp_tac >>
        qpat_assum `!D. inst_seq_ptr D lo ctx func PG ag7 at7 _ _ tg2 tt2` mp_tac >>
        qpat_assum `addr_s.vs_inst_idx = LENGTH addressed.cs_current_insts` mp_tac >>
        qpat_assum `prepared.cs_current_insts = addressed.cs_current_insts ++ [ti1;ti2]` mp_tac >>
        qpat_assum `Abbrev (ti1 = _)` mp_tac >>
        qpat_assum `Abbrev (ti2 = _)` mp_tac >>
        qpat_assum `Abbrev (tail_s = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `run_inst_seq [ti1;ti2] addr_s = OK tail_raw` by
          (fs[abiEncoderWindowSequenceTheory.window_pure_seq_def,
             abiEncoderWindowSequenceTheory.window_seq_def] >> metis_tac[]) >>
        `inst_seq_ptr D lo ctx func PG ag7 at7 [ti1;ti2] addr_s tg2 tt2` by metis_tac[] >>
        mp_tac (Q.SPECL [`[ti1;ti2]`, `addr_s`, `tail_raw`,
          `ag7`, `at7`, `tg2`, `tt2`, `ctx`, `func`, `tbb`]
          run_inst_seq_gas_origin_ptr_path) >>
        fs[Abbr `ti1`, Abbr `ti2`, Abbr `tail_s`, mk_inst_def, is_terminator_def] >>
        metis_tac[]) >>
     `tail_s.vs_memory = addr_s.vs_memory /\
      tail_s.vs_allocas = addr_s.vs_allocas /\
      tail_s.vs_alloca_next = addr_s.vs_alloca_next /\
      (!x. not_fresh_at addressed x ==> lookup_var x tail_s = lookup_var x addr_s)` by
       (qpat_assum `window_pure_seq addressed prepared addr_s tail_raw` mp_tac >>
        simp_tac bool_ss [Abbr `tail_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiEncoderWindowSequenceTheory.window_pure_seq_def,
          abiEncoderWindowSequenceTheory.window_seq_def, lookup_var_def]) >>
     `window_array_transition ctx func owner {} [] addr_s tail_s` by
       (`window_array_transition ctx func addressed {} [] addr_s tail_s` by
          (qpat_assum `window_phase ctx func addressed prepared {} [] addr_s tail_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_array_pure_phase_transition]) >>
        irule window_array_transition_owner_weaken >> qexists_tac `addressed` >>
        qpat_assum `window_array_transition ctx func addressed {} [] addr_s tail_s` mp_tac >>
        qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x` mp_tac >>
        qpat_assum `addressed.cs_next_var = body_st.cs_next_var+7` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD]) >>
     `window_array_root ctx func owner (window_alloca_sites func (frag_ids st en))
       ei asz msz T ty avs src dst sb cap d tail_s` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
        qpat_assum `window_array_transition ctx func owner {} [] addr_s tail_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_root_transition >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
     `alloca_inv tail_s /\ alloca_room ctx func tail_s /\
      ~tail_s.vs_halted /\ tail_s.vs_current_bb = prepared.cs_current_bb /\
      tail_s.vs_inst_idx = LENGTH prepared.cs_current_insts` by
       (qpat_assum `window_phase ctx func addressed prepared {} [] addr_s tail_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_phase_def] >> metis_tac[]) >>
     `!mem. mem_agree_outside tt2.t_mem tail_s.vs_memory mem ==>
       abi_encoder_window_input ei ty (EL k avs)
         (sb+32+k*msz) child_cap mem` by
       (qpat_assum `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
          abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap mem` mp_tac >>
        qpat_assum `tt2.t_mem = at7.t_mem` mp_tac >>
        qpat_assum `tail_s.vs_memory = addr_s.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `eval_operand (Var a3) tail_s = SOME (n2w (sb+32+k*msz)) /\
      eval_operand child_dst tail_s = SOME (n2w (d+32+off)) /\
      eval_operand offset tail_s = SOME (n2w off)` by
       (qpat_assum `eval_operand (Var a3) addr_s = SOME (n2w (sb+32+k*msz))` mp_tac >>
        qpat_assum `eval_operand (SND ops) tail_raw = SOME (n2w (d+32+off))` mp_tac >>
        qpat_assum `eval_operand (FST ops) tail_raw = SOME (n2w off)` mp_tac >>
        qpat_assum `ops = (offset,child_dst)` mp_tac >>
        qpat_assum `not_fresh_at addressed a3` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> lookup_var x tail_s = lookup_var x addr_s` mp_tac >>
        simp_tac bool_ss [Abbr `tail_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[instIdxIndepTheory.eval_op_inst_idx, eval_operand_def] >> metis_tac[]) >>
     `op_taint tt2 (Var a3) = {}` by
       (qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP tg2 x = _ /\ _` mp_tac >>
        qpat_assum `not_fresh_at addressed a3` mp_tac >>
        qpat_assum `op_taint at7 (Var a3) = {}` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `0 < child_cap ==> ptr_covers tg2 tt2 a3 tail_s child_cap` by
       (qpat_assum `0 < child_cap ==> ptr_covers ag7 at7 a3 addr_s child_cap` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP tg2 x = _ /\ _` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> lookup_var x tail_s = lookup_var x addr_s` mp_tac >>
        qpat_assum `not_fresh_at addressed a3` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >> metis_tac[]) >>
     `abi_encoder_window_input (AbiDynArray ei asz msz T)
       (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ addr_s`
          mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def] >> metis_tac[]) >>
     `asz = abi_member_head_size ty /\ is_dynamic ty` by
       (qpat_assum `abi_encoder_window_input (AbiDynArray ei asz msz T)
          (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_encoder_window_array_iff]) >>
     `32+off+LENGTH (enc ty (EL k avs)) <=
        LENGTH (enc (Array NONE ty) (ListV avs)) /\
      k*abi_member_head_size ty+32 <= off` by
       (qpat_assum `abi_encoder_window_input (AbiDynArray ei asz msz T)
          (Array NONE ty) (ListV avs) sb cap addr_s.vs_memory` mp_tac >>
        qpat_assum `k < LENGTH avs` mp_tac >>
        qpat_assum `is_dynamic ty` mp_tac >>
        simp_tac bool_ss [Abbr `off`] >> POP_ASSUM_LIST (K ALL_TAC) >>
        rpt strip_tac >> drule_all window_array_prefix_step_geometry >>
        disch_then (mp_tac o CONJUNCT1) >>
        asm_rewrite_tac[] >> rpt strip_tac >> decide_tac) >>
     `op_prov tg1 (Var a4) = SOME (dpb,dpsz)` by
       (qpat_assum `op_prov ag7 (Var a4) = SOME (dpb,dpsz)` mp_tac >>
        qpat_assum `ov <> a4` mp_tac >>
        simp_tac bool_ss [Abbr `tg1`, Abbr `ti1`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[op_prov_def, step_prov_other_output, mk_inst_def]) >>
     `op_prov tg2 child_dst = SOME (dpb,dpsz)` by
       (qpat_assum `op_prov tg1 (Var a4) = SOME (dpb,dpsz)` mp_tac >>
        qpat_assum `child_dst = Var cv` mp_tac >>
        simp_tac bool_ss [Abbr `tg2`, Abbr `ti2`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
          mk_inst_def, op_prov_def, FLOOKUP_UPDATE]) >>
     `0 < LENGTH (enc ty (EL k avs)) ==>
       ptr_covers tg2 tt2 cv tail_s (LENGTH (enc ty (EL k avs)))` by
       (disch_tac >>
        `d+32+off < dimword (:256)` by
          (qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
           qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= hu.vs_alloca_next` mp_tac >>
           qpat_assum `hu.vs_alloca_next < dimword (:256)` mp_tac >>
           qpat_assum `0 < LENGTH (enc ty (EL k avs))` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        qpat_assum `eval_operand child_dst tail_s = SOME (n2w (d+32+off))` mp_tac >>
        qpat_assum `op_prov tg2 child_dst = SOME (dpb,dpsz)` mp_tac >>
        qpat_assum `op_taint tt2 child_dst = {}` mp_tac >>
        qpat_assum `child_dst = Var cv` mp_tac >>
        qpat_assum `dpb <= d` mp_tac >>
        qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= dpb+dpsz` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        qpat_assum `d+32+off < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        gvs[ptr_covers_def, op_prov_def, eval_operand_def, lookup_var_def, w2n_n2w,
          arithmeticTheory.LESS_MOD] >> decide_tac) >>
     `st.cs_next_id <= prepared.cs_next_id /\ child_end.cs_next_id <= en.cs_next_id` by
       (qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
        qpat_assum `owner.cs_next_id = loop_st.cs_next_id + (if T then 5 else 2)` mp_tac >>
        qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
        qpat_assum `addressed.cs_next_id = body_st.cs_next_id+7` mp_tac >>
        qpat_assum `prepared.cs_next_id = addressed.cs_next_id+2` mp_tac >>
        qpat_assum `child_end.cs_next_id+3 = body_end.cs_next_id` mp_tac >>
        qpat_assum `body_end.cs_next_id+6 = loop_end.cs_next_id` mp_tac >>
        qpat_assum `en.cs_next_id = loop_end.cs_next_id+4` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [abi_encoder_array_loop_code_def] >>
        rpt strip_tac >> decide_tac) >>
     `!x. Var a3 = Var x \/ child_dst = Var x ==> not_fresh_at prepared x` by
       (qpat_assum `not_fresh_at addressed a3` mp_tac >>
        qpat_assum `prepared.cs_next_var = addressed.cs_next_var+2` mp_tac >>
        qpat_assum `!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `ops = (offset,child_dst)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD]) >>
     `abi_encoder_window_input ei ty (EL k avs)
       (sb+32+k*msz) child_cap tail_s.vs_memory` by
       (qpat_assum `!mem. mem_agree_outside tt2.t_mem tail_s.vs_memory mem ==>
          abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap mem`
          (qspec_then `tail_s.vs_memory` mp_tac) >>
        simp_tac (srw_ss()) [mem_agree_outside_def]) >>
     `abi_encoder_window_pre ctx func prepared child_end child_dst (Var a3) ei ty
       (EL k avs) (sb+32+k*msz) child_cap (d+32+off) tail_s` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ tail_s` mp_tac >>
        qpat_assum `abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap tail_s.vs_memory` mp_tac >>
        qpat_assum `eval_operand (Var a3) tail_s = SOME (n2w (sb+32+k*msz))` mp_tac >>
        qpat_assum `eval_operand child_dst tail_s = SOME (n2w (d+32+off))` mp_tac >>
        qpat_assum `!x. Var a3 = Var x \/ child_dst = Var x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `fn_has_code prepared child_end func` mp_tac >>
        qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        qpat_assum `st.cs_next_id <= prepared.cs_next_id` mp_tac >>
        qpat_assum `child_end.cs_next_id <= en.cs_next_id` mp_tac >>
        qpat_assum `~tail_s.vs_halted` mp_tac >>
        qpat_assum `tail_s.vs_current_bb = prepared.cs_current_bb` mp_tac >>
        qpat_assum `tail_s.vs_inst_idx = LENGTH prepared.cs_current_insts` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def, window_sizes32_def] >> rpt strip_tac >>
        simp_tac bool_ss [abi_encoder_window_pre_def] >> asm_rewrite_tac[] >>
        rpt conj_tac
        >- (qpat_assum `abi_encoder_admissible (AbiDynArray ei asz msz T)` mp_tac >>
            simp_tac bool_ss [Once abiEncoderAdmissibleTheory.abi_encoder_admissible_def] >>
            simp_tac bool_ss [])
        >- decide_tac
        >- decide_tac
        >- (qpat_assum `regions_disjoint (sb,cap) (d,_)` mp_tac >>
            qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
            qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
        rpt strip_tac >>
        `inst.inst_id IN window_alloca_sites func (frag_ids st en)` by
          (qpat_assum `MEM inst (fn_insts func)` mp_tac >>
           qpat_assum `inst.inst_opcode = ALLOCA` mp_tac >>
           qpat_assum `inst.inst_id IN frag_ids prepared child_end` mp_tac >>
           qpat_assum `st.cs_next_id <= prepared.cs_next_id` mp_tac >>
           qpat_assum `child_end.cs_next_id <= en.cs_next_id` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac (srw_ss()) [window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
           rpt strip_tac >>
           (decide_tac ORELSE (qexists_tac `inst` >> simp[]))) >>
        `sz = 32 /\ regions_disjoint (sb,cap) (b,sz) /\
         regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,sz)` by metis_tac[] >>
        asm_rewrite_tac[] >>
        qpat_assum `regions_disjoint (sb,cap) (b,sz)` mp_tac >>
        qpat_assum `regions_disjoint (d,_) (b,sz)` mp_tac >>
        qpat_assum `sz = 32` mp_tac >>
        qpat_assum `32+k*msz+child_cap <= cap` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
     `allocas_from lo tail_s /\ lo <= tail_s.vs_alloca_next` by
       (qpat_assum `allocas_from lo addr_s` mp_tac >>
        qpat_assum `lo <= addr_s.vs_alloca_next` mp_tac >>
        qpat_assum `tail_s.vs_allocas = addr_s.vs_allocas` mp_tac >>
        qpat_assum `tail_s.vs_alloca_next = addr_s.vs_alloca_next` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[allocas_from_def] >> metis_tac[]) >>
     qpat_assum `!dst src st out en ctx func s at av sb cap d G tn lo explicit PG. _`
       (qspecl_then [`child_dst`, `Var a3`, `prepared`, `child_len`, `child_end`,
         `ctx`, `func`, `tail_s`, `ty`, `EL k avs`, `sb+32+k*msz`, `child_cap`,
         `d+32+off`, `tg2`, `tt2`, `lo`, `explicit`, `PG`] mp_tac) >>
     impl_tac >-
       (qpat_assum `abi_encoder_window_pre ctx func prepared child_end child_dst (Var a3) ei ty
          (EL k avs) (sb+32+k*msz) child_cap (d+32+off) tail_s` mp_tac >>
        qpat_assum `compile_abi_encode_to_buf (SND ops) (Var a3) ei prepared = (child_len,child_end)` mp_tac >>
        qpat_assum `ops = (offset,child_dst)` mp_tac >>
        qpat_assum `child_dst = Var cv` mp_tac >>
        qpat_assum `!mem. mem_agree_outside tt2.t_mem tail_s.vs_memory mem ==>
          abi_encoder_window_input ei ty (EL k avs) (sb+32+k*msz) child_cap mem` mp_tac >>
        qpat_assum `0 < child_cap ==> ptr_covers tg2 tt2 a3 tail_s child_cap` mp_tac >>
        qpat_assum `0 < LENGTH (enc ty (EL k avs)) ==> ptr_covers tg2 tt2 cv tail_s _` mp_tac >>
        qpat_assum `op_taint tt2 (Var a3) = {}` mp_tac >>
        qpat_assum `op_taint tt2 child_dst = {}` mp_tac >>
        qpat_assum `allocas_from lo tail_s` mp_tac >>
        qpat_assum `lo <= tail_s.vs_alloca_next` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
        qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
        asm_rewrite_tac[] >> simp_tac (srw_ss()) [] >>
        rpt strip_tac >> metis_tac[pairTheory.SND]) >>
     disch_then (qx_choose_then `child_s` (qx_choose_then `childG`
       (qx_choose_then `childtn` strip_assume_tac))) >>
     `window_alloca_sites func (frag_ids prepared child_end) SUBSET
       window_alloca_sites func (frag_ids st en)` by
       (qpat_assum `st.cs_next_id <= prepared.cs_next_id` mp_tac >>
        qpat_assum `child_end.cs_next_id <= en.cs_next_id` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_alloca_sites_mono >>
        simp_tac (srw_ss()) [SUBSET_DEF, abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
     `owner.cs_next_var <= prepared.cs_next_var` by
       (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
        qpat_assum `addressed.cs_next_var = body_st.cs_next_var+7` mp_tac >>
        qpat_assum `prepared.cs_next_var = addressed.cs_next_var+2` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [abi_encoder_array_loop_code_def] >>
        rpt strip_tac >> decide_tac) >>
     `window_array_transition ctx func owner
       (window_alloca_sites func (frag_ids prepared child_end))
       [(d+32+off,LENGTH (enc ty (EL k avs)))] tail_s child_s` by
       (qpat_assum `window_strong_result ctx func prepared child_end child_len ty
          (EL k avs) (d+32+off) tail_s child_s` mp_tac >>
        qpat_assum `owner.cs_next_var <= prepared.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_child_transition >> asm_rewrite_tac[] >>
        qexists_tac `child_len` >> first_assum ACCEPT_TAC) >>
     `regions_disjoint (sb,cap) (d+32+off,LENGTH (enc ty (EL k avs)))` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ tail_s` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_root_def] >>
        rpt strip_tac >>
        qpat_assum `regions_disjoint (sb,cap) (d,_)` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
     `window_array_root ctx func owner (window_alloca_sites func (frag_ids st en))
       ei asz msz T ty avs src dst sb cap d child_s` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ tail_s` mp_tac >>
        qpat_assum `window_array_transition ctx func owner _ _ tail_s child_s` mp_tac >>
        qpat_assum `window_alloca_sites func (frag_ids prepared child_end) SUBSET _` mp_tac >>
        qpat_assum `regions_disjoint (sb,cap) (d+32+off,_)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_root_transition >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
     `alloca_inv child_s /\ alloca_room ctx func child_s /\
       window_alloca_growth tail_s child_s` by
       (qpat_assum `window_array_transition ctx func owner _ _ tail_s child_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_array_transition_resources]) >>
     `!i r. FLOOKUP tail_s.vs_allocas i = SOME r ==>
       FLOOKUP child_s.vs_allocas i = SOME r` by
       (qpat_assum `window_array_transition ctx func owner _ _ tail_s child_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
     `allocas_from lo child_s /\ lo <= child_s.vs_alloca_next` by
       (qpat_assum `allocas_from lo tail_s` mp_tac >>
        qpat_assum `lo <= tail_s.vs_alloca_next` mp_tac >>
        qpat_assum `window_alloca_growth tail_s child_s` mp_tac >>
        qpat_assum `!i r. FLOOKUP tail_s.vs_allocas i = SOME r ==> _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [allocas_from_def, window_alloca_growth_def] >>
        rpt disch_tac >> conj_tac >-
          (rpt strip_tac >> Cases_on `FLOOKUP tail_s.vs_allocas aid` >>
           metis_tac[optionTheory.SOME_11, LESS_EQ_TRANS]) >> metis_tac[LESS_EQ_TRANS]) >>
     `!root span. not_fresh_at prepared root /\ ptr_covers tg2 tt2 root tail_s span ==>
       ptr_covers childG childtn root child_s span` by
       (qpat_assum `!x. not_fresh_at prepared x ==> FLOOKUP childG x = _ /\ _` mp_tac >>
        qpat_assum `window_strong_result ctx func prepared child_end child_len ty
          (EL k avs) (d+32+off) tail_s child_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
        rpt strip_tac >> metis_tac[window_strong_result_public, abi_encoder_window_result_vars]) >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK child_s,childG,childtn)` by
       (gen_tac >>
        qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK hu,hg,ht)` (qspec_then `D` mp_tac) >>
        qpat_assum `!D. gas_origin_ptr_path _ (hu,hg,ht) [] (OK addr_s,ag7,at7)` (qspec_then `D` mp_tac) >>
        qpat_assum `!D. gas_origin_ptr_path _ (addr_s,ag7,at7) [] (OK tail_s,tg2,tt2)` (qspec_then `D` mp_tac) >>
        qpat_assum `!D. gas_origin_ptr_path _ (tail_s,tg2,tt2) [] (OK child_s,childG,childtn)` (qspec_then `D` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
     `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` by
       (qpat_assum `prepared.cs_next_var = addressed.cs_next_var+2` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_ADD]) >>
     `!x. not_fresh_at prepared x ==> not_fresh_at child_end x` by
       (qpat_assum `prepared.cs_next_var <= child_end.cs_next_var` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
     `~child_s.vs_halted /\ child_s.vs_current_bb = child_end.cs_current_bb /\
      child_s.vs_inst_idx = LENGTH child_end.cs_current_insts /\
      eval_operand child_len child_s = SOME (n2w (LENGTH (enc ty (EL k avs)))) /\
      mem_bytes_at (d+32+off) (LENGTH (enc ty (EL k avs))) child_s.vs_memory = enc ty (EL k avs)` by
       (qpat_assum `window_strong_result ctx func prepared child_end child_len ty
          (EL k avs) (d+32+off) tail_s child_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_strong_result_public, abi_encoder_window_result_control,
          abi_encoder_window_result_output]) >>
     `!root span. not_fresh_at addressed root /\ ptr_covers ag7 at7 root addr_s span ==>
       ptr_covers childG childtn root child_s span` by
       (qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP tg2 x = _ /\ _` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> lookup_var x tail_s = lookup_var x addr_s` mp_tac >>
        qpat_assum `!root span. not_fresh_at prepared root /\ ptr_covers tg2 tt2 root tail_s span ==> _` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
        rpt strip_tac >> metis_tac[]) >>
     `op_taint at7 (Var a6) = {}` by
       (qpat_assum `!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {}`
          (qspec_then `a6` mp_tac) >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` by
       (qpat_assum `k*abi_member_head_size ty+32 <= off` mp_tac >>
        qpat_assum `asz = abi_member_head_size ty` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[] >> decide_tac) >>
     `ptr_covers ag7 at7 a6 addr_s 32` by
       (`d+32+k*asz < dimword (:256)` by
          (qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
           qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= hu.vs_alloca_next` mp_tac >>
           qpat_assum `hu.vs_alloca_next < dimword (:256)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        qpat_assum `op_prov ag7 (Var a6) = SOME (dpb,dpsz)` mp_tac >>
        qpat_assum `op_taint at7 (Var a6) = {}` mp_tac >>
        qpat_assum `eval_operand (Var a6) addr_s = SOME (n2w (d+32+k*asz))` mp_tac >>
        qpat_assum `dpb <= d` mp_tac >>
        qpat_assum `d+LENGTH (enc (Array NONE ty) (ListV avs)) <= dpb+dpsz` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        qpat_assum `d+32+k*asz < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        simp_tac bool_ss [ptr_covers_def] >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`n2w (d+32+k*asz)`, `dpb`, `dpsz`] >>
        fs[op_prov_def, eval_operand_def, lookup_var_def, w2n_n2w, LESS_MOD] >> decide_tac) >>
     `ptr_covers childG childtn a6 child_s 32 /\
      ptr_covers childG childtn dq child_s 32` by
       (qpat_assum `!root span. not_fresh_at addressed root /\ ptr_covers ag7 at7 root addr_s span ==> _` mp_tac >>
        qpat_assum `ptr_covers ag7 at7 a6 addr_s 32` mp_tac >>
        qpat_assum `ptr_covers ag7 at7 dq addr_s 32` mp_tac >>
        qpat_assum `not_fresh_at addressed a6` mp_tac >>
        qpat_assum `!x. dp = Var x ==> not_fresh_at addressed x` mp_tac >>
        qpat_assum `dp = Var dq` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `!x. Var a6 = Var x \/ dp = Var x \/ offset = Var x ==>
       not_fresh_at prepared x` by
       (qpat_assum `not_fresh_at addressed a6` mp_tac >>
        qpat_assum `!x. dp = Var x ==> not_fresh_at addressed x` mp_tac >>
        qpat_assum `!x. FST ops = Var x \/ SND ops = Var x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `ops = (offset,child_dst)` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >>
        rpt strip_tac >> metis_tac[pairTheory.FST]) >>
     `eval_operand (Var a6) child_s = SOME (n2w (d+32+k*asz)) /\
      eval_operand dp child_s = SOME (n2w bd) /\
      eval_operand offset child_s = SOME (n2w off)` by
       (qpat_assum `window_phase ctx func addressed prepared {} [] addr_s tail_s` mp_tac >>
        qpat_assum `window_strong_result ctx func prepared child_end child_len ty
          (EL k avs) (d+32+off) tail_s child_s` mp_tac >>
        qpat_assum `not_fresh_at addressed a6` mp_tac >>
        qpat_assum `!x. dp = Var x ==> not_fresh_at addressed x` mp_tac >>
        qpat_assum `!x. Var a6 = Var x \/ dp = Var x \/ offset = Var x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `eval_operand (Var a6) addr_s = SOME (n2w (d+32+k*asz))` mp_tac >>
        qpat_assum `eval_operand dp addr_s = SOME (n2w bd)` mp_tac >>
        qpat_assum `eval_operand offset tail_s = SOME (n2w off)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `window_phase ctx func prepared child_end
          (window_alloca_sites func (frag_ids prepared child_end))
          [(d+32+off,LENGTH (enc ty (EL k avs)))] tail_s child_s` by
          (irule window_phase_strong_result >> qexists_tac `child_len` >>
           first_assum ACCEPT_TAC) >>
        `!x. Var a6 = Var x ==> not_fresh_at addressed x` by simp[] >>
        rpt conj_tac >> metis_tac[window_phase_operand]) >>
     `FLOOKUP child_s.vs_allocas index_en.cs_next_id = SOME (bd,32)` by
       (qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `addr_s.vs_allocas = hu.vs_allocas` mp_tac >>
        qpat_assum `tail_s.vs_allocas = addr_s.vs_allocas` mp_tac >>
        qpat_assum `!i r. FLOOKUP tail_s.vs_allocas i = SOME r ==> _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >> metis_tac[]) >>
     `d+32+k*asz+32 <= child_s.vs_alloca_next /\
      bd+32 <= child_s.vs_alloca_next` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        qpat_assum `FLOOKUP child_s.vs_allocas index_en.cs_next_id = SOME (bd,32)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_root_def, alloca_inv_def, alloca_next_valid_def] >>
        rpt strip_tac >> metis_tac[LESS_EQ_TRANS]) >>
     `regions_disjoint (d+32+k*asz,32) (bd,32)` by
       (qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
        qpat_assum `regions_disjoint (d,_) (bd,32)` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
     `!x. Var a6 = Var x \/ Var dq = Var x \/ offset = Var x \/
       child_len = Var x ==> not_fresh_at child_end x` by
       (qpat_assum `!x. Var a6 = Var x \/ dp = Var x \/ offset = Var x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `!x. not_fresh_at prepared x ==> not_fresh_at child_end x` mp_tac >>
        qpat_assum `!x. child_len = Var x ==> not_fresh_at child_end x` mp_tac >>
        qpat_assum `dp = Var dq` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `op_taint childtn offset = {}` by
       (qpat_assum `!x. not_fresh_at prepared x ==> FLOOKUP childG x = _ /\ _` mp_tac >>
        qpat_assum `!x. Var a6 = Var x \/ dp = Var x \/ offset = Var x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `offset = Var ov` mp_tac >>
        qpat_assum `op_taint tt2 offset = {}` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `abi_encode_child_suffix (Var a6) (Var dq) offset child_len child_end =
       (child_len,body_end)` by
       (qpat_assum `abi_encode_child_suffix (Var a6) dp (FST ops) child_len child_end = _` mp_tac >>
        qpat_assum `ops = (offset,child_dst)` mp_tac >>
        qpat_assum `dp = Var dq` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) []) >>
     mp_tac (Q.INST [`head` |-> `a6`, `dp` |-> `dq`, `offset` |-> `offset`,
       `len` |-> `child_len`, `st` |-> `child_end`, `out` |-> `child_len`,
       `en` |-> `body_end`, `func` |-> `func`, `s` |-> `child_s`,
       `h` |-> `d+32+k*asz`, `slot` |-> `bd`, `off` |-> `off`,
       `n` |-> `LENGTH (enc ty (EL k avs))`, `G` |-> `childG`, `tn` |-> `childtn`,
       `site` |-> `index_en.cs_next_id`, `ctx` |-> `ctx`, `lo` |-> `lo`,
       `explicit` |-> `explicit`, `PG` |-> `PG`] window_child_suffix_joint) >>
     impl_tac >-
       (qpat_assum `abi_encode_child_suffix (Var a6) (Var dq) offset child_len child_end = _` mp_tac >>
        qpat_assum `fn_has_code child_end body_end func` mp_tac >>
        qpat_assum `eval_operand (Var a6) child_s = SOME (n2w (d+32+k*asz))` mp_tac >>
        qpat_assum `eval_operand dp child_s = SOME (n2w bd)` mp_tac >>
        qpat_assum `dp = Var dq` mp_tac >>
        qpat_assum `eval_operand offset child_s = SOME (n2w off)` mp_tac >>
        qpat_assum `eval_operand child_len child_s = SOME (n2w (LENGTH (enc ty (EL k avs))))` mp_tac >>
        qpat_assum `!x. Var a6 = Var x \/ Var dq = Var x \/ offset = Var x \/ _ ==> _` mp_tac >>
        qpat_assum `ptr_covers childG childtn a6 child_s 32` mp_tac >>
        qpat_assum `ptr_covers childG childtn dq child_s 32` mp_tac >>
        qpat_assum `op_taint childtn offset = {}` mp_tac >>
        qpat_assum `op_taint childtn child_len = {}` mp_tac >>
        qpat_assum `FLOOKUP child_s.vs_allocas index_en.cs_next_id = SOME (bd,32)` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= child_s.vs_alloca_next` mp_tac >>
        qpat_assum `bd+32 <= child_s.vs_alloca_next` mp_tac >>
        qpat_assum `regions_disjoint (d+32+k*asz,32) (bd,32)` mp_tac >>
        qpat_assum `alloca_inv child_s` mp_tac >>
        qpat_assum `alloca_room ctx func child_s` mp_tac >>
        qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
        qpat_assum `allocas_from lo child_s` mp_tac >>
        qpat_assum `lo <= child_s.vs_alloca_next` mp_tac >>
        qpat_assum `~child_s.vs_halted` mp_tac >>
        qpat_assum `child_s.vs_current_bb = child_end.cs_current_bb` mp_tac >>
        qpat_assum `child_s.vs_inst_idx = LENGTH child_end.cs_current_insts` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> asm_rewrite_tac[] >> metis_tac[]) >>
     disch_then (qx_choose_then `body_s` (qx_choose_then `bodyG`
       (qx_choose_then `bodytn` strip_assume_tac))) >>
     `window_array_transition ctx func child_end {index_en.cs_next_id}
       [(d+32+k*asz,32)] child_s body_s` by
       (qpat_assum `window_phase ctx func child_end body_end {index_en.cs_next_id}
          [(d+32+k*asz,32)] child_s body_s` mp_tac >>
        qpat_assum `FLOOKUP body_s.vs_allocas index_en.cs_next_id = SOME (bd,32)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_phase_sizes_transition >> conj_tac
        >- simp[window_sizes32_def] >>
        qexists_tac `body_end` >> asm_rewrite_tac[]) >>
     `!x. not_fresh_at owner x ==> not_fresh_at child_end x` by
       (qpat_assum `owner.cs_next_var <= prepared.cs_next_var` mp_tac >>
        qpat_assum `!x. not_fresh_at prepared x ==> not_fresh_at child_end x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[not_fresh_at_mono]) >>
     `window_array_transition ctx func owner {index_en.cs_next_id}
       [(d+32+k*asz,32)] child_s body_s` by
       (irule window_array_transition_owner_weaken >>
        goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
     qabbrev_tac `round_ids =
       window_alloca_sites func (frag_ids prepared child_end) UNION
       {index_en.cs_next_id}` >>
     `window_array_transition ctx func owner round_ids
       [(d+32+k*asz,32);(d+32+off,LENGTH (enc ty (EL k avs)))]
       tail_s child_s` by
       (qpat_assum `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids prepared child_end))
          [(d+32+off,LENGTH (enc ty (EL k avs)))] tail_s child_s` mp_tac >>
        qpat_assum `Abbrev (round_ids = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_transition_enlarge >>
        goal_assum (drule_at Any) >>
        simp[Abbr `round_ids`, EVERY_DEF]) >>
     `window_array_transition ctx func owner round_ids
       [(d+32+k*asz,32);(d+32+off,LENGTH (enc ty (EL k avs)))]
       child_s body_s` by
       (qpat_assum `window_array_transition ctx func owner {index_en.cs_next_id}
          [(d+32+k*asz,32)] child_s body_s` mp_tac >>
        qpat_assum `Abbrev (round_ids = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_transition_enlarge >>
        goal_assum (drule_at Any) >>
        simp[Abbr `round_ids`, EVERY_DEF]) >>
     `window_array_transition ctx func owner round_ids
       [(d+32+k*asz,32);(d+32+off,LENGTH (enc ty (EL k avs)))]
       addr_s tail_s` by
       (qpat_assum `window_array_transition ctx func owner {} [] addr_s tail_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_transition_enlarge >>
        goal_assum (drule_at Any) >> simp[EVERY_DEF]) >>
     `window_array_transition ctx func owner round_ids
       [(d+32+k*asz,32);(d+32+off,LENGTH (enc ty (EL k avs)))]
       addr_s body_s` by
       (qpat_assum `window_array_transition ctx func owner round_ids _ addr_s tail_s` mp_tac >>
        qpat_assum `window_array_transition ctx func owner round_ids _ tail_s child_s` mp_tac >>
        qpat_assum `window_array_transition ctx func owner round_ids _ child_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_array_transition_trans]) >>
     `mem_bytes_at (d+32+off) (LENGTH (enc ty (EL k avs))) child_s.vs_memory =
       enc ty (EL k avs)` by
       (qpat_assum `window_strong_result ctx func prepared child_end child_len ty
          (EL k avs) (d+32+off) tail_s child_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_strong_result_public, abi_encoder_window_result_output]) >>
     `d+32+k*asz+32 <= d+32+off /\
       (d+32+off+LENGTH (enc ty (EL k avs)) <= bd \/
        bd+32 <= d+32+off)` by
       (qpat_assum `k*abi_member_head_size ty+32 <= off` mp_tac >>
        qpat_assum `asz = abi_member_head_size ty` mp_tac >>
        qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
        qpat_assum `regions_disjoint (d,_) (bd,32)` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        qpat_assum `k*abi_member_head_size ty+32 <= off` mp_tac >>
        qpat_assum `asz = abi_member_head_size ty` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_rewrite_tac[] >>
        qpat_assum `regions_disjoint (d,_) (bd,32)` mp_tac >>
        pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
     `mem_bytes_at (d+32+off) (LENGTH (enc ty (EL k avs))) body_s.vs_memory =
       enc ty (EL k avs)` by
       (qpat_assum `body_s.vs_memory = _` mp_tac >>
        qpat_assum `mem_bytes_at (d+32+off) _ child_s.vs_memory = _` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+32+off` mp_tac >>
        rpt (qpat_x_assum `d+32+off+LENGTH (enc ty (EL k avs)) <= bd` mp_tac) >>
        rpt (qpat_x_assum `bd+32 <= d+32+off` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        asm_rewrite_tac[] >>
        `mem_bytes_at (d+32+off) (LENGTH (enc ty (EL k avs)))
          (mstore (d+32+k*asz) (n2w off) child_s).vs_memory =
          mem_bytes_at (d+32+off) (LENGTH (enc ty (EL k avs))) child_s.vs_memory` by
          metis_tac[mstore_mem_bytes_at_disjoint] >>
        metis_tac[mstore_mem_bytes_at_disjoint]) >>
     `abi_encoder_array_prefix ty avs k d addr_s.vs_memory` by
       (qpat_assum `abi_encoder_array_prefix ty avs k d hu.vs_memory` mp_tac >>
        qpat_assum `addr_s.vs_memory = hu.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `round_ids SUBSET window_alloca_sites func (frag_ids st en)` by
       (qpat_assum `window_alloca_sites func (frag_ids prepared child_end) SUBSET _` mp_tac >>
        qpat_assum `T ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
        qpat_assum `Abbrev (round_ids = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `round_ids`, UNION_SUBSET]) >>
     `abi_encoder_array_prefix ty avs (SUC k) d body_s.vs_memory` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
        qpat_assum `abi_encoder_array_prefix ty avs k d addr_s.vs_memory` mp_tac >>
        qpat_assum `k < LENGTH avs` mp_tac >>
        qpat_assum `round_ids SUBSET window_alloca_sites func (frag_ids st en)` mp_tac >>
        qpat_assum `window_array_transition ctx func owner round_ids _ addr_s body_s` mp_tac >>
        qpat_assum `mem_word_at (d+32+k*asz) body_s.vs_memory = n2w off` mp_tac >>
        qpat_assum `mem_bytes_at (d+32+off) _ body_s.vs_memory = _` mp_tac >>
        qpat_assum `asz = abi_member_head_size ty` mp_tac >>
        qpat_assum `Abbrev (off = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        qpat_x_assum `asz = _` SUBST_ALL_TAC >>
        qpat_x_assum `Abbrev (off = _)`
          (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        full_simp_tac bool_ss [ADD_ASSOC] >>
        irule window_array_dynamic_prefix_finish >>
        qpat_assum `window_array_root _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ addr_s`
          (irule_at Any) >>
        qpat_assum `window_array_transition _ _ _ _ _ addr_s body_s`
          (irule_at Any) >>
        asm_rewrite_tac[]) >>
     `window_array_transition ctx func owner
       (window_alloca_sites func (frag_ids st en))
       [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] addr_s body_s` by
       (qpat_assum `window_array_transition ctx func owner round_ids _ addr_s body_s` mp_tac >>
        qpat_assum `round_ids SUBSET window_alloca_sites func (frag_ids st en)` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_transition_region >> goal_assum (drule_at Any) >>
        simp[Excl "enc_def"] >> decide_tac) >>
     `window_array_root ctx func owner (window_alloca_sites func (frag_ids st en))
       ei asz msz T ty avs src dst sb cap d body_s` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ addr_s` mp_tac >>
        qpat_assum `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en)) _ addr_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_root_transition >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
        simp[] >> fs[window_array_root_def]) >>
     `abi_encode_exec_frame func hu addr_s` by
       (simp_tac (srw_ss()) [Abbr `addr_s`] >>
        qpat_assum `window_pure_seq body_st addressed hu ar7` mp_tac >>
        qpat_assum `abi_encode_array_addresses ip src dst asz msz body_st = (coords,addressed)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule abi_encode_framed_ordinary_pure_sequence >>
        asm_rewrite_tac[] >> metis_tac[abi_encode_framed_array_addresses_opcodes]) >>
     `abi_encode_exec_frame func addr_s tail_s` by
       (simp_tac (srw_ss()) [Abbr `tail_s`] >>
        qpat_assum `window_pure_seq addressed prepared addr_s tail_raw` mp_tac >>
        qpat_assum `abi_encode_array_tail (Var a4) dp addressed = (ops,prepared)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule abi_encode_framed_ordinary_pure_sequence >>
        asm_rewrite_tac[] >> metis_tac[abi_encode_framed_array_tail_opcodes]) >>
     `abi_encode_exec_frame func s body_s` by
       (qpat_assum `abi_encode_exec_frame func s u` mp_tac >>
        qpat_assum `abi_encode_exec_frame func u hu` mp_tac >>
        qpat_assum `abi_encode_exec_frame func hu addr_s` mp_tac >>
        qpat_assum `abi_encode_exec_frame func addr_s tail_s` mp_tac >>
        qpat_assum `abi_encode_exec_frame func tail_s child_s` mp_tac >>
        qpat_assum `abi_encode_exec_frame func child_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_encode_exec_frame_trans]) >>
     `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK body_s,bodyG,bodytn)` by
       (gen_tac >>
        qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK child_s,childG,childtn)`
          (qspec_then `D` mp_tac) >>
        qpat_assum `!D. gas_origin_ptr_path _ (child_s,childG,childtn) [] (OK body_s,bodyG,bodytn)`
          (qspec_then `D` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
     `!x. not_fresh_at addressed x ==>
       FLOOKUP bodyG x = FLOOKUP ag7 x /\
       op_taint bodytn (Var x) = op_taint at7 (Var x)` by
       (qpat_assum `!x. not_fresh_at child_end x ==> FLOOKUP bodyG x = _ /\ _` mp_tac >>
        qpat_assum `!x. not_fresh_at prepared x ==> FLOOKUP childG x = _ /\ _` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP tg2 x = _ /\ _` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `!x. not_fresh_at prepared x ==> not_fresh_at child_end x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `!root span. not_fresh_at addressed root /\ ptr_covers ag7 at7 root addr_s span ==>
       ptr_covers bodyG bodytn root body_s span` by
       (qpat_assum `!x. not_fresh_at child_end x ==> FLOOKUP bodyG x = _ /\ _` mp_tac >>
        qpat_assum `window_array_transition ctx func child_end _ _ child_s body_s` mp_tac >>
        qpat_assum `!root span. not_fresh_at addressed root /\ ptr_covers ag7 at7 root addr_s span ==> _` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `!x. not_fresh_at prepared x ==> not_fresh_at child_end x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `ptr_covers childG childtn root child_s span` by metis_tac[] >>
        `not_fresh_at child_end root` by metis_tac[] >>
        qpat_assum `!x. not_fresh_at child_end x ==> FLOOKUP bodyG x = _ /\ _`
          (qspec_then `root` mp_tac) >>
        qpat_assum `not_fresh_at child_end root` mp_tac >>
        qpat_assum `ptr_covers childG childtn root child_s span` mp_tac >>
        qpat_assum `window_array_transition ctx func child_end _ _ child_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
        rpt strip_tac >> metis_tac[window_array_transition_vars]) >>
     `window_array_transition ctx func owner round_ids
       [(d+32+k*asz,32);(d+32+off,LENGTH (enc ty (EL k avs)))] hu body_s` by
       (`window_array_transition ctx func owner round_ids
         [(d+32+k*asz,32);(d+32+off,LENGTH (enc ty (EL k avs)))] hu addr_s` by
          (qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_transition_enlarge >>
           goal_assum (drule_at Any) >> simp[]) >>
        qpat_assum `window_array_transition ctx func owner round_ids _ hu addr_s` mp_tac >>
        qpat_assum `window_array_transition ctx func owner round_ids _ addr_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[window_array_transition_trans]) >>
     `!cop csite cslot cvalue.
       window_array_cursor T owner cop csite cslot cvalue sb cap d
         (LENGTH (enc (Array NONE ty) (ListV avs))) hu /\ csite NOTIN round_ids ==>
       window_array_cursor T owner cop csite cslot cvalue sb cap d
         (LENGTH (enc (Array NONE ty) (ListV avs))) body_s` by
       (qx_genl_tac [`cop`, `csite`, `cslot`, `cvalue`] >> strip_tac >>
        qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_transition ctx func owner round_ids _ hu body_s` mp_tac >>
        qpat_assum `csite NOTIN round_ids` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        irule window_array_cursor_frame >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
        asm_rewrite_tac[] >> simp_tac (srw_ss()) [EVERY_DEF] >>
        qpat_assum `window_array_cursor T owner cop csite cslot cvalue _ _ _ _ hu` mp_tac >>
        simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
        qpat_assum `regions_disjoint (d,_) (cslot,32)` mp_tac >>
        qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
        qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
     `loop_st.cs_next_id NOTIN round_ids /\ st.cs_next_id NOTIN round_ids` by
       (qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
        qpat_assum `index_en.cs_next_id = loop_st.cs_next_id+2` mp_tac >>
        qpat_assum `owner.cs_next_id = loop_st.cs_next_id+(if T then 5 else 2)` mp_tac >>
        qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
        qpat_assum `addressed.cs_next_id = body_st.cs_next_id+7` mp_tac >>
        qpat_assum `prepared.cs_next_id = addressed.cs_next_id+2` mp_tac >>
        qpat_assum `Abbrev (round_ids = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        fs[Abbr `round_ids`, abi_encoder_array_loop_code_def,
          window_alloca_sites_def, abiEncoderPropsTheory.frag_ids_def] >>
        rpt strip_tac >> decide_tac) >>
     `window_array_cursor T owner ip loop_st.cs_next_id bi k sb cap d
       (LENGTH (enc (Array NONE ty) (ListV avs))) body_s /\
      window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
       (LENGTH (enc (Array NONE ty) (ListV avs))) body_s` by
       (qpat_assum `!cop csite cslot cvalue. _` mp_tac >>
        qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_cursor T owner pp st.cs_next_id b 0 _ _ _ _ hu` mp_tac >>
        qpat_assum `loop_st.cs_next_id NOTIN round_ids` mp_tac >>
        qpat_assum `st.cs_next_id NOTIN round_ids` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `off+LENGTH (enc ty (EL k avs)) = LENGTH avs*abi_member_head_size ty+
       SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))` by
       (qpat_assum `k < LENGTH avs` mp_tac >> qpat_assum `is_dynamic ty` mp_tac >>
        qpat_assum `Abbrev (off = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `TAKE (SUC k) avs = TAKE k avs ++ [EL k avs]` by
          simp[rich_listTheory.TAKE_SUC, TAKE1_DROP] >>
        asm_simp_tac bool_ss [Abbr `off`, MAP_APPEND, MAP, SUM_APPEND, SUM,
          abiDecodeRangesTheory.abi_member_tail_size_def, ADD_ASSOC, ADD_CLAUSES]) >>
     `window_array_cursor T owner dp index_en.cs_next_id bd
       (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs))) sb cap d
       (LENGTH (enc (Array NONE ty) (ListV avs))) body_s` by
       (qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        qpat_assum `window_array_transition ctx func owner round_ids _ hu body_s` mp_tac >>
        qpat_assum `mem_word_at bd body_s.vs_memory = n2w (off+LENGTH (enc ty (EL k avs)))` mp_tac >>
        qpat_assum `off+LENGTH (enc ty (EL k avs)) = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        full_simp_tac bool_ss [] >>
        irule window_array_cursor_word >> reverse conj_tac
        >- (goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
        asm_rewrite_tac[]) >>
     `~body_s.vs_halted /\ body_s.vs_current_bb = body_end.cs_current_bb /\
      body_s.vs_inst_idx = LENGTH body_end.cs_current_insts /\
      alloca_inv body_s /\ alloca_room ctx func body_s` by
       (qpat_assum `window_phase ctx func child_end body_end _ _ child_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_phase_def] >> metis_tac[]) >>
     `eval_operand (Var a0) child_s = SOME (n2w k)` by
       (qpat_assum `window_strong_result ctx func prepared child_end child_len ty
          (EL k avs) (d+32+off) tail_s child_s` mp_tac >>
        qpat_assum `not_fresh_at addressed a0` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> lookup_var x tail_s = lookup_var x addr_s` mp_tac >>
        qpat_assum `eval_operand (Var a0) addr_s = SOME (n2w k)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [eval_operand_def] >>
        rpt strip_tac >> metis_tac[window_strong_result_public, abi_encoder_window_result_vars]) >>
     `not_fresh_at child_end a0` by
       (qpat_assum `not_fresh_at addressed a0` mp_tac >>
        qpat_assum `!x. not_fresh_at addressed x ==> not_fresh_at prepared x` mp_tac >>
        qpat_assum `!x. not_fresh_at prepared x ==> not_fresh_at child_end x` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     `eval_operand (Var a0) body_s = SOME (n2w k)` by
       (qpat_assum `eval_operand (Var a0) child_s = SOME (n2w k)` mp_tac >>
        qpat_assum `not_fresh_at child_end a0` mp_tac >>
        qpat_assum `window_array_transition ctx func child_end _ _ child_s body_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [eval_operand_def] >>
        metis_tac[window_array_transition_vars]) >>
     `op_prov bodyG (Var a0) = NONE /\ op_taint bodytn (Var a0) = {}` by
       (qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP bodyG x = _ /\ _` mp_tac >>
        qpat_assum `not_fresh_at addressed a0` mp_tac >>
        qpat_assum `op_prov ag7 (Var a0) = NONE` mp_tac >>
        qpat_assum `!x. MEM x [a0;a1;a2;a3;a4;a5;a6] ==> op_taint at7 (Var x) = {}`
          (qspec_then `a0` mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[op_prov_def] >> metis_tac[]) >>
        `eval_operand ip body_s = SOME (n2w bi) /\ bi < dimword (:256) /\
          FLOOKUP body_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` by
          (qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ body_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_cursor_def] >>
           metis_tac[]) >>
        `owner.cs_next_var <= body_end.cs_next_var` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels`
             mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >> decide_tac) >>
        `!x. ip = Var x ==> not_fresh_at body_end x` by
          (qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ body_s` mp_tac >>
           qpat_assum `owner.cs_next_var <= body_end.cs_next_var` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_cursor_def] >>
           rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
        qabbrev_tac `nv = STRING #"%" (toString body_end.cs_next_var)` >>
        `~not_fresh_at body_end nv` by
          (qpat_assum `Abbrev (nv = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `nv`, not_fresh_at_def] >>
           metis_tac[LESS_EQ_REFL]) >>
        `ip <> Var nv` by
          (qpat_assum `!x. ip = Var x ==> not_fresh_at body_end x` (qspec_then `nv` mp_tac) >>
           qpat_assum `~not_fresh_at body_end nv` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
        qabbrev_tac `bai = mk_inst body_end.cs_next_id ADD [Var a0;Lit 1w] [nv]` >>
        qabbrev_tac `bsi = mk_inst (body_end.cs_next_id+1) MSTORE [ip;Var nv] []` >>
        qabbrev_tac `bji = mk_inst (body_end.cs_next_id+2) JMP [Label (FST labels)] []` >>
        qabbrev_tac `br1 = update_var nv (n2w (SUC k)) body_s` >>
        qabbrev_tac `br2 = mstore bi (n2w (SUC k)) br1` >>
        qabbrev_tac `back_s = jump_to (FST labels) br2` >>
        `!x. not_fresh_at owner x ==> not_fresh_at body_st x /\
          not_fresh_at addressed x` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
           qpat_assum `addressed.cs_next_var = body_st.cs_next_var+7` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           metis_tac[not_fresh_at_mono, LESS_EQ_ADD, LESS_EQ_TRANS]) >>
        `?iq. ip = Var iq /\ ptr_covers bodyG bodytn iq body_s 32` by
          (rpt (qpat_x_assum `ptr_covers hg ht _ hu 32` mp_tac) >>
           rpt (qpat_x_assum `ip = Var _` mp_tac) >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ hu` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x /\ _` mp_tac >>
           qpat_assum `!root span. not_fresh_at body_st root /\ ptr_covers hg ht root hu span ==> _` mp_tac >>
           qpat_assum `!root span. not_fresh_at addressed root /\ ptr_covers ag7 at7 root addr_s span ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >> metis_tac[]) >>
        qabbrev_tac `bbb = <|bb_label := body_end.cs_current_bb;
          bb_instructions := body_end.cs_current_insts ++ [bai;bsi;bji]|>` >>
        `lookup_block body_s.vs_current_bb func.fn_blocks = SOME bbb` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
           qpat_assum `body_s.vs_current_bb = body_end.cs_current_bb` mp_tac >>
           qpat_assum `Abbrev (a0 = _)` mp_tac >> qpat_assum `Abbrev (nv = _)` mp_tac >>
           qpat_assum `Abbrev (bai = _)` mp_tac >> qpat_assum `Abbrev (bsi = _)` mp_tac >>
           qpat_assum `Abbrev (bji = _)` mp_tac >> qpat_assum `Abbrev (bbb = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           fs[Abbr `bbb`, Abbr `bai`, Abbr `bsi`, Abbr `bji`, Abbr `a0`, Abbr `nv`,
             abiDecoderExecutionTheory.abi_decode_backedge_insts_def]) >>
        `LENGTH avs < dimword (:256)` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ body_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def] >> rpt strip_tac >>
           fs[abi_encoder_window_array_iff, contractABITheory.valid_length_def]) >>
        `?hdr_bb. lookup_block (FST labels) func.fn_blocks = SOME hdr_bb /\
          phi_prefix_length hdr_bb.bb_instructions = 0` by
          (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >>
           qmatch_asmsub_abbrev_tac `lookup_block (FST labels) func.fn_blocks = SOME header_bb` >>
           qexists_tac `header_bb` >> asm_rewrite_tac[] >>
           simp[Abbr `header_bb`, abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
             phi_prefix_length_def, mk_inst_def]) >>
        `bi+32 <= body_s.vs_alloca_next` by
          (qpat_assum `alloca_inv body_s` mp_tac >>
           qpat_assum `FLOOKUP body_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
     `?backG backtn.
       abi_encode_exec_frame func body_s back_s /\
       allocas_from lo back_s /\ lo <= back_s.vs_alloca_next /\
       (!x. x <> nv ==> FLOOKUP backG x = FLOOKUP bodyG x /\
         op_taint backtn (Var x) = op_taint bodytn (Var x)) /\
       FLOOKUP backG nv = NONE /\ op_taint backtn (Var nv) = {} /\
       backtn.t_mem = bodytn.t_mem DIFF {i | bi <= i /\ i < bi+32} /\
       backtn.t_stor = bodytn.t_stor /\ backtn.t_trans = bodytn.t_trans /\
       backtn.t_imm = bodytn.t_imm /\
       !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (body_s,bodyG,bodytn) [] (OK back_s,backG,backtn)` by
       (irule (Q.INST [
          `s` |-> `body_s`, `G` |-> `bodyG`, `tn` |-> `bodytn`,
          `t` |-> `back_s`, `bb` |-> `bbb`,
          `prefix` |-> `body_end.cs_current_insts`,
          `id` |-> `body_end.cs_next_id`, `iv` |-> `a0`, `nv` |-> `nv`,
          `ip` |-> `iq`, `slot` |-> `bi`,
          `hdr` |-> `FST (labels:string # string # string)`,
          `nitems` |-> `LENGTH (avs:abi_value list)`, `k` |-> `k`, `ctx` |-> `ctx`,
          `func` |-> `func`, `lo` |-> `lo`, `explicit` |-> `explicit`,
          `PG` |-> `PG`] window_array_backedge_joint) >>
          (qpat_assum `lookup_block body_s.vs_current_bb func.fn_blocks = SOME bbb` mp_tac >>
           rpt (qpat_x_assum `lookup_block (FST labels) func.fn_blocks = SOME _` mp_tac) >>
           rpt (qpat_x_assum `phi_prefix_length _.bb_instructions = 0` mp_tac) >>
           qpat_assum `body_s.vs_inst_idx = LENGTH body_end.cs_current_insts` mp_tac >>
           qpat_assum `~body_s.vs_halted` mp_tac >>
           qpat_assum `eval_operand (Var a0) body_s = SOME (n2w k)` mp_tac >>
           qpat_assum `eval_operand ip body_s = SOME (n2w bi)` mp_tac >>
           qpat_assum `ip = Var iq` mp_tac >>
           qpat_assum `ip <> Var nv` mp_tac >>
           qpat_assum `ptr_covers bodyG bodytn iq body_s 32` mp_tac >>
           qpat_assum `bi+32 <= body_s.vs_alloca_next` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           qpat_assum `LENGTH avs < dimword (:256)` mp_tac >>
           qpat_assum `op_prov bodyG (Var a0) = NONE` mp_tac >>
           qpat_assum `op_taint bodytn (Var a0) = {}` mp_tac >>
           qpat_assum `alloca_inv body_s` mp_tac >>
           qpat_assum `alloca_room ctx func body_s` mp_tac >>
           qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
           qpat_assum `allocas_from lo body_s` mp_tac >>
           qpat_assum `lo <= body_s.vs_alloca_next` mp_tac >>
           qpat_assum `Abbrev (bbb = _)` mp_tac >>
           qpat_assum `Abbrev (bai = _)` mp_tac >>
           qpat_assum `Abbrev (bsi = _)` mp_tac >>
           qpat_assum `Abbrev (bji = _)` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `bbb`, Abbr `bai`, Abbr `bsi`, Abbr `bji`,
             Abbr `back_s`, Abbr `br2`, Abbr `br1`,
             abiDecoderExecutionTheory.abi_decode_backedge_insts_def] >>
           metis_tac[])) >>
     rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (body_s,bodyG,bodytn) [] (OK back_s,bg2,bt2)` >>
        `!x. not_fresh_at owner x ==> x <> nv` by
          (qpat_assum `owner.cs_next_var <= body_end.cs_next_var` mp_tac >>
           qpat_assum `~not_fresh_at body_end nv` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[not_fresh_at_mono]) >>
        `window_array_transition ctx func owner {loop_st.cs_next_id} [] body_s back_s` by
          (qpat_assum `lookup_block body_s.vs_current_bb func.fn_blocks = SOME bbb` mp_tac >>
           qpat_assum `lookup_block (FST labels) func.fn_blocks = SOME _` mp_tac >>
           rpt (qpat_x_assum `phi_prefix_length _.bb_instructions = 0` mp_tac) >>
           qpat_assum `body_s.vs_inst_idx = LENGTH body_end.cs_current_insts` mp_tac >>
           qpat_assum `~body_s.vs_halted` mp_tac >>
           qpat_assum `eval_operand (Var a0) body_s = SOME (n2w k)` mp_tac >>
           qpat_assum `eval_operand ip body_s = SOME (n2w bi)` mp_tac >>
           qpat_assum `ip <> Var nv` mp_tac >>
           qpat_assum `k < LENGTH avs` mp_tac >>
           qpat_assum `LENGTH avs < dimword (:256)` mp_tac >>
           qpat_assum `bi < dimword (:256)` mp_tac >>
           qpat_assum `FLOOKUP body_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
           qpat_assum `alloca_inv body_s` mp_tac >>
           qpat_assum `alloca_room ctx func body_s` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> x <> nv` mp_tac >>
           qpat_assum `Abbrev (bbb = _)` mp_tac >>
           qpat_assum `Abbrev (bai = _)` mp_tac >>
           qpat_assum `Abbrev (bsi = _)` mp_tac >>
           qpat_assum `Abbrev (bji = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `window_array_transition ctx func owner {loop_st.cs_next_id} [] body_s
             (jump_to (FST labels) (mstore (w2n (n2w bi : bytes32)) (n2w (SUC k))
               (update_var nv (n2w (SUC k)) body_s)))` suffices_by
             fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`, w2n_n2w] >>
           irule window_array_backedge_run >>
           asm_rewrite_tac[] >>
           fs[Abbr `bbb`, Abbr `bai`, Abbr `bsi`, Abbr `bji`,
             abiDecoderExecutionTheory.abi_decode_backedge_insts_def] >>
           metis_tac[]) >>
        `eval_operand count_op body_s = SOME (n2w (LENGTH avs))` by
          (qpat_assum `eval_operand count_op hu = SOME (n2w (LENGTH avs))` mp_tac >>
           qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
           qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner _ _ addr_s body_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `eval_operand count_op addr_s = SOME (n2w (LENGTH avs))` by
             metis_tac[window_array_transition_eval] >>
           metis_tac[window_array_transition_eval]) >>
     `window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
       ei asz msz T ty avs src dst ip loop_st.cs_next_id bi
       dp index_en.cs_next_id bd count_op (FST labels) sb cap d (SUC k) back_s` by
       (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ body_s` mp_tac >>
        qpat_assum `abi_encoder_array_prefix ty avs (SUC k) d body_s.vs_memory` mp_tac >>
        qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ body_s` mp_tac >>
        qpat_assum `window_array_cursor T owner dp index_en.cs_next_id bd _ _ _ _ _ body_s` mp_tac >>
        qpat_assum `eval_operand count_op body_s = SOME (n2w (LENGTH avs))` mp_tac >>
        qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
        qpat_assum `!x. not_fresh_at owner x ==> x <> nv` mp_tac >>
        qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
        qpat_assum `index_en.cs_next_id = loop_st.cs_next_id+2` mp_tac >>
        qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] body_s back_s` mp_tac >>
        qpat_assum `Abbrev (back_s = _)` mp_tac >>
        qpat_assum `Abbrev (br2 = _)` mp_tac >>
        qpat_assum `Abbrev (br1 = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        full_simp_tac bool_ss [Abbr `back_s`, Abbr `br2`, Abbr `br1`] >>
        irule window_array_backedge_inv >>
        asm_simp_tac (srw_ss()) [Excl "enc_def", ADD_COMM] >> metis_tac[]) >>
     `!mem. mem_agree_outside tt2.t_mem tail_s.vs_memory mem ==>
       abi_encoder_window_input (AbiDynArray ei asz msz T)
         (Array NONE ty) (ListV avs) sb cap mem` by
       (qpat_assum `!mem. mem_agree_outside at7.t_mem addr_s.vs_memory mem ==>
          abi_encoder_window_input (AbiDynArray ei asz msz T) _ _ _ _ mem` mp_tac >>
        qpat_assum `tt2.t_mem = at7.t_mem` mp_tac >>
        qpat_assum `tail_s.vs_memory = addr_s.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `!id b sz. id IN window_alloca_sites func (frag_ids prepared child_end) /\
          FLOOKUP child_s.vs_allocas id = SOME (b,sz) ==>
          regions_disjoint (sb,cap) (b,sz)` by
          (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
           qpat_assum `window_alloca_sites func (frag_ids prepared child_end) SUBSET _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def, SUBSET_DEF] >> rpt strip_tac >>
           metis_tac[]) >>
        `mem_bytes_at sb cap child_s.vs_memory = mem_bytes_at sb cap tail_s.vs_memory` by
          (qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids prepared child_end))
             [(d+32+off,LENGTH (enc ty (EL k avs)))] tail_s child_s` mp_tac >>
           qpat_assum `regions_disjoint (sb,cap) (d+32+off,_)` mp_tac >>
           qpat_assum `!id b sz. id IN window_alloca_sites func (frag_ids prepared child_end) /\
             FLOOKUP child_s.vs_allocas id = SOME (b,sz) ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule abi_encoder_window_effect_bytes >>
           qexistsl_tac [`window_alloca_sites func (frag_ids prepared child_end)`,
             `[(d+32+off,LENGTH (enc ty (EL k avs)))]`] >>
           simp[] >> full_simp_tac bool_ss [AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
           metis_tac[window_array_transition_effect]) >>
        `!i. sb <= i /\ i < sb+cap ==>
          (i IN childtn.t_mem <=> i IN tt2.t_mem)` by
          (gen_tac >> strip_tac >>
           qpat_assum `!i. (i < d+32+off \/ d+32+off+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==> (i IN childtn.t_mem <=> i IN tt2.t_mem)`
             (qspec_then `i` mp_tac) >> impl_tac >-
            (conj_tac >-
             (qpat_assum `regions_disjoint (sb,cap) (d+32+off,_)` mp_tac >>
              qpat_assum `sb <= i` mp_tac >> qpat_assum `i < sb+cap` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >>
              pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           rpt strip_tac >>
           rename1 `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` >>
           `regions_disjoint (sb,cap) (scratch_b,scratch_sz)` by
             (qpat_assum `!id b sz. id IN window_alloca_sites func (frag_ids prepared child_end) /\
                FLOOKUP child_s.vs_allocas id = SOME (b,sz) ==> _`
                (qspecl_then [`aid`, `scratch_b`, `scratch_sz`] mp_tac) >>
              impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
           pop_assum mp_tac >> qpat_assum `sb <= i` mp_tac >>
           qpat_assum `i < sb+cap` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
           simp[]) >>
        `!mem. mem_agree_outside childtn.t_mem child_s.vs_memory mem ==>
          abi_encoder_window_input (AbiDynArray ei asz msz T)
            (Array NONE ty) (ListV avs) sb cap mem` by
          (gen_tac >> strip_tac >>
           mp_tac (Q.SPECL [`tt2.t_mem`, `childtn.t_mem`, `tail_s.vs_memory`,
             `child_s.vs_memory`, `sb`, `sb`, `cap`, `mem`]
             copied_window_agree_witness) >>
           impl_tac >-
             (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >-
               (rpt strip_tac >>
                qpat_assum `!i. sb <= i /\ i < sb+cap ==> _`
                  (qspec_then `sb+i` mp_tac) >>
                qpat_assum `i < cap` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
              first_assum ACCEPT_TAC) >>
           disch_then (qx_choose_then `mix` strip_assume_tac) >>
           `abi_encoder_window_input (AbiDynArray ei asz msz T)
             (Array NONE ty) (ListV avs) sb cap mix` by
             (qpat_assum `!mem. mem_agree_outside tt2.t_mem tail_s.vs_memory mem ==>
                abi_encoder_window_input (AbiDynArray ei asz msz T)
                  (Array NONE ty) (ListV avs) sb cap mem`
                (qspec_then `mix` irule) >> first_assum ACCEPT_TAC) >>
           qpat_assum `abi_encoder_window_input _ _ _ _ _ mix` mp_tac >>
           qpat_assum `mem_bytes_at sb cap mix = mem_bytes_at sb cap mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[abi_encoder_window_input_mem_agree]) >>

     `regions_disjoint (sb,cap) (d+32+k*asz,32) /\
      regions_disjoint (sb,cap) (bd,32)` by
       (conj_tac
        >- (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
            qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_root_def] >>
            rpt strip_tac >>
            qpat_assum `regions_disjoint (sb,cap) (d,_)` mp_tac >>
            qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
        qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[window_array_cursor_def]) >>
     `mem_bytes_at sb cap body_s.vs_memory = mem_bytes_at sb cap child_s.vs_memory` by
       (qpat_assum `body_s.vs_memory = _` mp_tac >>
        qpat_assum `regions_disjoint (sb,cap) (d+32+k*asz,32)` mp_tac >>
        qpat_assum `regions_disjoint (sb,cap) (bd,32)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        Cases_on `cap = 0` >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
        asm_simp_tac (srw_ss()) [regions_disjoint_def, Excl "enc_def"] >>
        rpt strip_tac >> asm_rewrite_tac[] >>
        `mem_bytes_at sb cap (mstore (d+32+k*asz) (n2w off) child_s).vs_memory =
          mem_bytes_at sb cap child_s.vs_memory` by metis_tac[mstore_mem_bytes_at_disjoint] >>
        metis_tac[mstore_mem_bytes_at_disjoint]) >>
     `!i. sb <= i /\ i < sb+cap ==>
       (i IN bodytn.t_mem <=> i IN tt2.t_mem)` by
       (gen_tac >> strip_tac >>
        qpat_assum `!i. sb <= i /\ i < sb+cap ==> (i IN childtn.t_mem <=> i IN tt2.t_mem)`
          (qspec_then `i` mp_tac) >>
        qpat_assum `bodytn.t_mem = childtn.t_mem DIFF _` mp_tac >>
        qpat_assum `regions_disjoint (sb,cap) (d+32+k*asz,32)` mp_tac >>
        qpat_assum `regions_disjoint (sb,cap) (bd,32)` mp_tac >>
        qpat_assum `sb <= i` mp_tac >> qpat_assum `i < sb+cap` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [regions_disjoint_def, IN_DIFF, IN_UNION, GSPECIFICATION,
          Excl "enc_def"] >>
        rpt strip_tac >>
        `~(d+32+k*asz <= i /\ i < d+32+k*asz+32) /\
         ~(bd <= i /\ i < bd+32)` by decide_tac >>
        full_simp_tac (srw_ss())
          [IN_DIFF, IN_UNION, GSPECIFICATION, Excl "enc_def"]) >>
     `!mem. mem_agree_outside bodytn.t_mem body_s.vs_memory mem ==>
       abi_encoder_window_input (AbiDynArray ei asz msz T)
         (Array NONE ty) (ListV avs) sb cap mem` by
       (gen_tac >> strip_tac >>
        mp_tac (Q.SPECL [`tt2.t_mem`, `bodytn.t_mem`, `tail_s.vs_memory`,
          `body_s.vs_memory`, `sb`, `sb`, `cap`, `mem`] copied_window_agree_witness) >>
        impl_tac
        >- (conj_tac
            >- (qpat_assum `mem_bytes_at sb cap body_s.vs_memory = mem_bytes_at sb cap child_s.vs_memory` mp_tac >>
                qpat_assum `mem_bytes_at sb cap child_s.vs_memory = mem_bytes_at sb cap tail_s.vs_memory` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
            conj_tac
            >- (rpt strip_tac >>
                qpat_assum `!i. sb <= i /\ i < sb+cap ==> (i IN bodytn.t_mem <=> i IN tt2.t_mem)`
                  (qspec_then `sb+i` mp_tac) >>
                qpat_assum `i < cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
            first_assum ACCEPT_TAC) >>
        disch_then (qx_choose_then `mix` strip_assume_tac) >>
        `abi_encoder_window_input (AbiDynArray ei asz msz T)
          (Array NONE ty) (ListV avs) sb cap mix` by
          (qpat_assum `!mem. mem_agree_outside tt2.t_mem tail_s.vs_memory mem ==>
             abi_encoder_window_input (AbiDynArray ei asz msz T) _ _ _ _ mem`
             (qspec_then `mix` irule) >> first_assum ACCEPT_TAC) >>
        qpat_assum `abi_encoder_window_input _ _ _ _ _ mix` mp_tac >>
        qpat_assum `mem_bytes_at sb cap mix = mem_bytes_at sb cap mem` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_encoder_window_input_mem_agree]) >>
     `!i. d <= i /\ i < d+LENGTH (enc (Array NONE ty) (ListV avs)) /\
       (i < d+32+off \/ d+32+off+LENGTH (enc ty (EL k avs)) <= i) ==>
       (i IN childtn.t_mem <=> i IN kt.t_mem)` by
       (gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
        qpat_assum `!i. (i < d+32+off \/ d+32+off+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==>
          (i IN childtn.t_mem <=> i IN tt2.t_mem)` (qspec_then `i` mp_tac) >>
        impl_tac
        >- (conj_tac >- decide_tac >>
            rpt strip_tac >>
            rename1 `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` >>
            `regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs)))
              (scratch_b,scratch_sz)` by
              (qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ child_s` mp_tac >>
               qpat_assum `window_alloca_sites func (frag_ids prepared child_end) SUBSET _` mp_tac >>
               qpat_assum `aid IN window_alloca_sites func (frag_ids prepared child_end)` mp_tac >>
               qpat_assum `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >>
               simp_tac bool_ss [window_array_root_def, SUBSET_DEF] >> metis_tac[]) >>
            qpat_assum `regions_disjoint (d,_) (scratch_b,scratch_sz)` mp_tac >>
            qpat_assum `d <= i` mp_tac >>
            qpat_assum `i < d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
        qpat_assum `tt2.t_mem = at7.t_mem` mp_tac >>
        qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
        qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `asz = 32` by
       (qpat_assum `asz = abi_member_head_size ty` mp_tac >>
        qpat_assum `is_dynamic ty` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiDecodeRangesTheory.abi_member_head_size_def]) >>
     `!i. d <= i /\ i < d+32+SUC k*abi_member_head_size ty ==>
       i NOTIN bodytn.t_mem` by
       (gen_tac >> strip_tac >> Cases_on `i < d+32+k*asz`
        >- (`i NOTIN childtn.t_mem` by
              (qpat_assum `!i. d <= i /\ i < d+LENGTH (enc (Array NONE ty) (ListV avs)) /\ _ ==>
                 (i IN childtn.t_mem <=> i IN kt.t_mem)` (qspec_then `i` mp_tac) >>
               qpat_assum `!i. d <= i /\ i < d+32+k*abi_member_head_size ty ==> i NOTIN kt.t_mem`
                 (qspec_then `i` mp_tac) >>
               qpat_assum `asz = abi_member_head_size ty` mp_tac >>
               qpat_assum `d+32+k*asz+32 <= d+32+off` mp_tac >>
               qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
               qpat_assum `d <= i` mp_tac >> qpat_assum `i < d+32+k*asz` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
               `d <= i /\ i < d+LENGTH (enc (Array NONE ty) (ListV avs)) /\ i < d+32+off` by decide_tac >>
               metis_tac[]) >>
            qpat_assum `i NOTIN childtn.t_mem` mp_tac >>
            qpat_assum `bodytn.t_mem = childtn.t_mem DIFF _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        qpat_assum `bodytn.t_mem = childtn.t_mem DIFF _` mp_tac >>
        qpat_assum `asz = 32` mp_tac >>
        qpat_assum `asz = abi_member_head_size ty` mp_tac >>
        qpat_assum `~(i < d+32+k*asz)` mp_tac >>
        qpat_assum `i < d+32+SUC k*abi_member_head_size ty` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac (srw_ss()) [MULT_CLAUSES, IN_DIFF, IN_UNION, GSPECIFICATION,
          Excl "enc_def"] >>
        rpt strip_tac >>
        `d+32+k*asz <= i /\ i < d+32+k*asz+32` by (gvs[] >> decide_tac) >>
        gvs[IN_DIFF, IN_UNION, GSPECIFICATION, Excl "enc_def"] >> metis_tac[]) >>
     `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\
       i < d+32+LENGTH avs*abi_member_head_size ty+
         SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs)) ==>
       i NOTIN bodytn.t_mem` by
       (gen_tac >> strip_tac >>
        `i < d+32+off+LENGTH (enc ty (EL k avs))` by
          (qpat_assum `off+LENGTH (enc ty (EL k avs)) = _` mp_tac >>
           qpat_assum `i < d+32+LENGTH avs*abi_member_head_size ty+_` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        `i NOTIN childtn.t_mem` by
          (Cases_on `i < d+32+off`
           >- (qpat_assum `!i. d <= i /\ i < d+LENGTH (enc (Array NONE ty) (ListV avs)) /\ _ ==>
                 (i IN childtn.t_mem <=> i IN kt.t_mem)` (qspec_then `i` mp_tac) >>
               qpat_assum `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\
                 i < d+32+LENGTH avs*abi_member_head_size ty+
                   SUM (MAP (abi_member_tail_size ty) (TAKE k avs)) ==> i NOTIN kt.t_mem`
                 (qspec_then `i` mp_tac) >>
               qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
               qpat_assum `d+32+LENGTH avs*abi_member_head_size ty <= i` mp_tac >>
               qpat_assum `i < d+32+off` mp_tac >>
               qpat_assum `Abbrev (off = _)` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
               full_simp_tac bool_ss [Abbr `off`, ADD_ASSOC] >>
               `d <= i /\ i < d+LENGTH (enc (Array NONE ty) (ListV avs))` by decide_tac >>
               metis_tac[]) >>
           qpat_assum `!i. d+32+off <= i /\ i < d+32+off+LENGTH (enc ty (EL k avs)) ==> i NOTIN childtn.t_mem`
             (qspec_then `i` mp_tac) >>
           qpat_assum `~(i < d+32+off)` mp_tac >>
           qpat_assum `i < d+32+off+LENGTH (enc ty (EL k avs))` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        qpat_assum `i NOTIN childtn.t_mem` mp_tac >>
        qpat_assum `bodytn.t_mem = childtn.t_mem DIFF _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `!csite cslot.
       FLOOKUP child_s.vs_allocas csite = SOME (cslot,32) /\
       csite NOTIN window_alloca_sites func (frag_ids prepared child_end) /\
       regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (cslot,32) /\
       (!i. cslot <= i /\ i < cslot+32 ==> i NOTIN tt2.t_mem) ==>
       !i. cslot <= i /\ i < cslot+32 ==> i NOTIN childtn.t_mem` by
       (qx_genl_tac [`csite`, `cslot`] >> strip_tac >> gen_tac >> strip_tac >>
        qpat_assum `!i. (i < d+32+off \/ d+32+off+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==>
          (i IN childtn.t_mem <=> i IN tt2.t_mem)` (qspec_then `i` mp_tac) >>
        impl_tac
        >- (conj_tac
            >- (qpat_assum `regions_disjoint (d,_) (cslot,32)` mp_tac >>
                qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
                qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
            rpt strip_tac >>
            rename1 `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` >>
            `csite <> aid` by
              (qpat_assum `csite NOTIN window_alloca_sites func (frag_ids prepared child_end)` mp_tac >>
               qpat_assum `aid IN window_alloca_sites func (frag_ids prepared child_end)` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
            `regions_disjoint (cslot,32) (scratch_b,scratch_sz)` by
              (qpat_assum `alloca_inv child_s` mp_tac >>
               qpat_assum `FLOOKUP child_s.vs_allocas csite = SOME (cslot,32)` mp_tac >>
               qpat_assum `FLOOKUP child_s.vs_allocas aid = SOME (scratch_b,scratch_sz)` mp_tac >>
               qpat_assum `csite <> aid` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >>
               simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def, regions_disjoint_def] >>
               metis_tac[]) >>
            qpat_assum `regions_disjoint (cslot,32) (scratch_b,scratch_sz)` mp_tac >>
            qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
        qpat_assum `!i. cslot <= i /\ i < cslot+32 ==> i NOTIN tt2.t_mem`
          (qspec_then `i` mp_tac) >>
        qpat_assum `cslot <= i` mp_tac >> qpat_assum `i < cslot+32` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `!aid r. FLOOKUP hu.vs_allocas aid = SOME r ==> FLOOKUP child_s.vs_allocas aid = SOME r` by
       (qpat_assum `!i r. FLOOKUP tail_s.vs_allocas i = SOME r ==> FLOOKUP child_s.vs_allocas i = SOME r` mp_tac >>
        qpat_assum `tail_s.vs_allocas = addr_s.vs_allocas` mp_tac >>
        qpat_assum `addr_s.vs_allocas = hu.vs_allocas` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids prepared child_end) /\
      st.cs_next_id NOTIN window_alloca_sites func (frag_ids prepared child_end)` by
       (qpat_assum `loop_st.cs_next_id NOTIN round_ids` mp_tac >>
        qpat_assum `st.cs_next_id NOTIN round_ids` mp_tac >>
        qpat_assum `Abbrev (round_ids = _)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> fs[Abbr `round_ids`]) >>
     `(!i. b <= i /\ i < b+32 ==> i NOTIN bodytn.t_mem) /\
      (!i. bi <= i /\ i < bi+32 ==> i NOTIN bodytn.t_mem) /\
      (!i. bd <= i /\ i < bd+32 ==> i NOTIN bodytn.t_mem)` by
       (`(!i. b <= i /\ i < b+32 ==> i NOTIN childtn.t_mem) /\
         (!i. bi <= i /\ i < bi+32 ==> i NOTIN childtn.t_mem)` by
          (qpat_assum `!csite cslot. _ ==>
             !i. cslot <= i /\ i < cslot+32 ==> i NOTIN childtn.t_mem` mp_tac >>
           qpat_assum `window_array_cursor T owner pp st.cs_next_id b 0 _ _ _ _ hu` mp_tac >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ hu` mp_tac >>
           qpat_assum `!aid r. FLOOKUP hu.vs_allocas aid = SOME r ==> _` mp_tac >>
           qpat_assum `loop_st.cs_next_id NOTIN window_alloca_sites func (frag_ids prepared child_end)` mp_tac >>
           qpat_assum `st.cs_next_id NOTIN window_alloca_sites func (frag_ids prepared child_end)` mp_tac >>
           qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN kt.t_mem` mp_tac >>
           qpat_assum `!i. bi <= i /\ i < bi+32 ==> i NOTIN kt.t_mem` mp_tac >>
           qpat_assum `tt2.t_mem = at7.t_mem` mp_tac >>
           qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
           qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_cursor_def] >>
           rpt (disch_then strip_assume_tac) >>
           `FLOOKUP child_s.vs_allocas st.cs_next_id = SOME (b,32) /\
            FLOOKUP child_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` by
             (qpat_assum `!aid r. FLOOKUP hu.vs_allocas aid = SOME r ==> _` mp_tac >>
              qpat_assum `FLOOKUP hu.vs_allocas st.cs_next_id = SOME (b,32)` mp_tac >>
              qpat_assum `FLOOKUP hu.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
              POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
           conj_tac
           >- (qpat_assum `!csite cslot. _ ==>
                 !i. cslot <= i /\ i < cslot+32 ==> i NOTIN childtn.t_mem`
                 (qspecl_then [`st.cs_next_id`, `b`] mp_tac) >> simp[]) >>
           qpat_assum `!csite cslot. _ ==>
             !i. cslot <= i /\ i < cslot+32 ==> i NOTIN childtn.t_mem`
             (qspecl_then [`loop_st.cs_next_id`, `bi`] mp_tac) >> simp[]) >>
        qpat_assum `bodytn.t_mem = childtn.t_mem DIFF _` mp_tac >>
        qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN childtn.t_mem` mp_tac >>
        qpat_assum `!i. bi <= i /\ i < bi+32 ==> i NOTIN childtn.t_mem` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF, IN_UNION, GSPECIFICATION] >> metis_tac[]) >>
        `abi_encode_exec_frame func s back_s` by
          (qpat_assum `abi_encode_exec_frame func s body_s` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `abi_encode_exec_frame func body_s back_s` by
             simp[Abbr `back_s`, Abbr `br2`, Abbr `br1`,
               abi_encode_framed_array_backedge] >>
           metis_tac[abi_encode_exec_frame_trans]) >>
        `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK back_s,bg2,bt2)` by
          (gen_tac >>
           qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK body_s,bodyG,bodytn)`
             (qspec_then `D` mp_tac) >>
           qpat_assum `!D. gas_origin_ptr_path _ (body_s,bodyG,bodytn) [] (OK back_s,bg2,bt2)`
             (qspec_then `D` mp_tac) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
        `mem_bytes_at sb cap back_s.vs_memory = mem_bytes_at sb cap body_s.vs_memory` by
          (qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ body_s` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
           Cases_on `cap = 0` >- fs[valueEncodingDefsTheory.mem_bytes_at_def] >>
           `sb+cap <= bi \/ bi+32 <= sb` by fs[regions_disjoint_def] >>
           simp_tac bool_ss [Abbr `back_s`, Abbr `br2`, Abbr `br1`, jump_to_def] >>
           `mem_bytes_at sb cap (mstore bi (n2w (SUC k))
              (update_var nv (n2w (SUC k)) body_s)).vs_memory =
             mem_bytes_at sb cap (update_var nv (n2w (SUC k)) body_s).vs_memory` by
             metis_tac[mstore_mem_bytes_at_disjoint] >>
           fs[update_var_def]) >>
        `!i. sb <= i /\ i < sb+cap ==>
          (i IN bt2.t_mem <=> i IN bodytn.t_mem)` by
          (qpat_assum `bt2.t_mem = bodytn.t_mem DIFF _` mp_tac >>
           qpat_assum `window_array_cursor T owner ip loop_st.cs_next_id bi k _ _ _ _ body_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_cursor_def, regions_disjoint_def] >>
           rpt strip_tac >>
           `~(bi <= i /\ i < bi+32)` by decide_tac >>
           simp[IN_DIFF, GSPECIFICATION]) >>
        `!mem. mem_agree_outside bt2.t_mem back_s.vs_memory mem ==>
          abi_encoder_window_input (AbiDynArray ei asz msz T)
            (Array NONE ty) (ListV avs) sb cap mem` by
          (gen_tac >> strip_tac >>
           mp_tac (Q.SPECL [`bodytn.t_mem`, `bt2.t_mem`, `body_s.vs_memory`,
             `back_s.vs_memory`, `sb`, `sb`, `cap`, `mem`]
             copied_window_agree_witness) >>
           impl_tac >-
             (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >-
               (rpt strip_tac >>
                qpat_assum `!i. sb <= i /\ i < sb+cap ==> _`
                  (qspec_then `sb+i` mp_tac) >>
                qpat_assum `i < cap` mp_tac >>
                POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
              first_assum ACCEPT_TAC) >>
           disch_then (qx_choose_then `witness_mem` strip_assume_tac) >>
           `abi_encoder_window_input (AbiDynArray ei asz msz T)
              (Array NONE ty) (ListV avs) sb cap witness_mem` by
             (qpat_assum `!mem. mem_agree_outside bodytn.t_mem body_s.vs_memory mem ==>
                abi_encoder_window_input (AbiDynArray ei asz msz T)
                  (Array NONE ty) (ListV avs) sb cap mem`
               (qspec_then `witness_mem` irule) >> first_assum ACCEPT_TAC) >>
           qpat_assum `abi_encoder_window_input _ _ _ _ _ witness_mem` mp_tac >>
           qpat_assum `mem_bytes_at sb cap witness_mem = mem_bytes_at sb cap mem` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[abi_encoder_window_input_mem_agree]) >>
        `!x. not_fresh_at owner x ==>
          FLOOKUP bg2 x = FLOOKUP bodyG x /\
          op_taint bt2 (Var x) = op_taint bodytn (Var x) /\
          lookup_var x back_s = lookup_var x body_s` by
          (rpt strip_tac >>
           qpat_assum `!x. x <> nv ==> FLOOKUP bg2 x = _ /\ _` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> x <> nv` mp_tac >>
           qpat_assum `not_fresh_at owner x` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >>
           qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`, jump_to_def,
             mstore_def, write_memory_with_expansion_def, update_var_def,
             lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
        `!root span. not_fresh_at owner root /\
          ptr_covers bodyG bodytn root body_s span ==>
          ptr_covers bg2 bt2 root back_s span` by
          (qx_genl_tac [`root`, `span`] >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = _ /\ _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
           metis_tac[]) >>
        `allocas_from lo back_s /\ lo <= back_s.vs_alloca_next` by
          (qpat_assum `allocas_from lo body_s` mp_tac >>
           qpat_assum `lo <= body_s.vs_alloca_next` mp_tac >>
           qpat_assum `Abbrev (back_s = _)` mp_tac >>
           qpat_assum `Abbrev (br2 = _)` mp_tac >> qpat_assum `Abbrev (br1 = _)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           fs[Abbr `back_s`, Abbr `br2`, Abbr `br1`, jump_to_def,
             mstore_def, write_memory_with_expansion_def, update_var_def, allocas_from_def] >>
           first_assum ACCEPT_TAC) >>

        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] hu addr_s` by
          (qpat_assum `window_array_transition ctx func owner {} [] hu addr_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_transition_region >>
           goal_assum (drule_at Any) >> simp[]) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] body_s back_s` by
          (qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] body_s back_s` mp_tac >>
           qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_transition_region >>
           goal_assum (drule_at Any) >> simp[]) >>
        `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en))
          [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u back_s` by
          (qpat_assum `window_array_transition ctx func owner _ _ u hu` mp_tac >>
           qpat_assum `window_array_transition ctx func owner _ _ hu addr_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids st en)) _ addr_s body_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids st en)) _ body_s back_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           metis_tac[window_array_transition_trans]) >>
        `!op. (!x. op = Var x ==> not_fresh_at owner x) ==>
          op_taint bt2 op = op_taint bodytn op /\ op_prov bg2 op = op_prov bodyG op` by
          (gen_tac >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = _ /\ _` mp_tac >>
           qpat_assum `!x. op = Var x ==> not_fresh_at owner x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `op` >>
           simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
        `!x. not_fresh_at owner x ==>
          FLOOKUP bg2 x = FLOOKUP kg x /\
          op_taint bt2 (Var x) = op_taint kt (Var x)` by
          (gen_tac >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at addressed x ==> FLOOKUP bodyG x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at body_st x ==> FLOOKUP ag7 x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP hg x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at owner x ==> not_fresh_at body_st x /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `not_fresh_at owner x` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `!root span. not_fresh_at owner root /\
          ptr_covers kg kt root u span ==> ptr_covers bg2 bt2 root back_s span` by
          (qx_genl_tac [`root`, `span`] >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = FLOOKUP kg x /\ _` mp_tac >>
           qpat_assum `window_array_transition ctx func owner
             (window_alloca_sites func (frag_ids st en)) _ u back_s` mp_tac >>
           qpat_assum `not_fresh_at owner root` mp_tac >>
           qpat_assum `ptr_covers kg kt root u span` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
           metis_tac[window_array_transition_vars]) >>
        `op_taint bt2 count_op = {} /\ op_prov bg2 count_op = NONE` by
          (qpat_assum `op_taint kt count_op = {}` mp_tac >>
           qpat_assum `op_prov kg count_op = NONE` mp_tac >>
           qpat_assum `!x. count_op = Var x ==> not_fresh_at owner x` mp_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = FLOOKUP kg x /\ _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `count_op` >>
           simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
        `window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
          (LENGTH (enc (Array NONE ty) (ListV avs))) back_s` by
          (qpat_assum `window_array_cursor T owner pp st.cs_next_id b 0 _ _ _ _ body_s` mp_tac >>
           qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] body_s back_s` mp_tac >>
           qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           irule window_array_cursor_frame >>
           goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>

     `!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> FLOOKUP back_s.vs_allocas aid = SOME r` by
       (qpat_assum `window_array_transition ctx func owner
          (window_alloca_sites func (frag_ids st en)) _ u back_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
     `!aid r. FLOOKUP body_s.vs_allocas aid = SOME r ==> FLOOKUP back_s.vs_allocas aid = SOME r` by
       (qpat_assum `window_array_transition ctx func owner {loop_st.cs_next_id} [] body_s back_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
     `!aid r. FLOOKUP child_s.vs_allocas aid = SOME r ==> FLOOKUP back_s.vs_allocas aid = SOME r` by
       (qpat_assum `window_array_transition ctx func owner {index_en.cs_next_id} _ child_s body_s` mp_tac >>
        qpat_assum `!aid r. FLOOKUP body_s.vs_allocas aid = SOME r ==> _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        metis_tac[window_array_transition_effect, abi_encoder_registered_effect_allocated]) >>
     `index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` by
       (qpat_assum `T ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     `!i. (i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i) /\
       (!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\
         FLOOKUP back_s.vs_allocas aid = SOME (scratch_b,scratch_sz) ==>
         i < scratch_b \/ scratch_b+scratch_sz <= i) ==>
       (i IN bt2.t_mem <=> i IN tn.t_mem)` by
       (gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
        `~(d+32+k*asz <= i /\ i < d+32+k*asz+32)` by
          (qpat_assum `i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i` mp_tac >>
           qpat_assum `d+32+k*asz+32 <= d+LENGTH (enc (Array NONE ty) (ListV avs))` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        `~(bd <= i /\ i < bd+32)` by
          (qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _`
             (qspecl_then [`index_en.cs_next_id`, `bd`, `32`] mp_tac) >>
           qpat_assum `index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
           qpat_assum `FLOOKUP body_s.vs_allocas index_en.cs_next_id = SOME (bd,32)` mp_tac >>
           qpat_assum `!aid r. FLOOKUP body_s.vs_allocas aid = SOME r ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `i < bd \/ bd+32 <= i` by metis_tac[] >> decide_tac) >>
        `~(bi <= i /\ i < bi+32)` by
          (qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _`
             (qspecl_then [`loop_st.cs_next_id`, `bi`, `32`] mp_tac) >>
           qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
           qpat_assum `FLOOKUP body_s.vs_allocas loop_st.cs_next_id = SOME (bi,32)` mp_tac >>
           qpat_assum `!aid r. FLOOKUP body_s.vs_allocas aid = SOME r ==> _` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
           `i < bi \/ bi+32 <= i` by metis_tac[] >> decide_tac) >>
        `i IN childtn.t_mem <=> i IN tt2.t_mem` by
          (qpat_assum `!i. (i < d+32+off \/ d+32+off+LENGTH (enc ty (EL k avs)) <= i) /\ _ ==>
             (i IN childtn.t_mem <=> i IN tt2.t_mem)` (qspec_then `i` mp_tac) >>
           impl_tac
           >- (conj_tac
               >- (qpat_assum `i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i` mp_tac >>
                   qpat_assum `32+off+LENGTH (enc ty (EL k avs)) <= _` mp_tac >>
                   POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
               qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _` mp_tac >>
               qpat_assum `!aid r. FLOOKUP child_s.vs_allocas aid = SOME r ==> _` mp_tac >>
               qpat_assum `window_alloca_sites func (frag_ids prepared child_end) SUBSET _` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [SUBSET_DEF] >> metis_tac[]) >>
           simp[]) >>
        `i IN kt.t_mem <=> i IN tn.t_mem` by
          (qpat_assum `!i. _ ==> (i IN kt.t_mem <=> i IN tn.t_mem)` (qspec_then `i` mp_tac) >>
           impl_tac
           >- (conj_tac >- first_assum ACCEPT_TAC >>
               qpat_assum `!aid scratch_b scratch_sz. aid IN window_alloca_sites func (frag_ids st en) /\ _ ==> _` mp_tac >>
               qpat_assum `!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> _` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
           simp[]) >>
        qpat_assum `bt2.t_mem = bodytn.t_mem DIFF _` mp_tac >>
        qpat_assum `bodytn.t_mem = childtn.t_mem DIFF _` mp_tac >>
        qpat_assum `~(d+32+k*asz <= i /\ i < d+32+k*asz+32)` mp_tac >>
        qpat_assum `~(bd <= i /\ i < bd+32)` mp_tac >>
        qpat_assum `~(bi <= i /\ i < bi+32)` mp_tac >>
        qpat_assum `i IN childtn.t_mem <=> i IN tt2.t_mem` mp_tac >>
        qpat_assum `tt2.t_mem = at7.t_mem` mp_tac >>
        qpat_assum `at7.t_mem = ht.t_mem` mp_tac >>
        qpat_assum `ht.t_mem = kt.t_mem` mp_tac >>
        qpat_assum `i IN kt.t_mem <=> i IN tn.t_mem` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF, IN_UNION, GSPECIFICATION]) >>
     `bodytn.t_stor = at7.t_stor /\ bodytn.t_trans = at7.t_trans /\
      bodytn.t_imm = at7.t_imm` by
       (qpat_assum `bodytn.t_stor = childtn.t_stor` mp_tac >>
        qpat_assum `bodytn.t_trans = childtn.t_trans` mp_tac >>
        qpat_assum `bodytn.t_imm = childtn.t_imm` mp_tac >>
        qpat_assum `childtn.t_stor = tt2.t_stor` mp_tac >>
        qpat_assum `childtn.t_trans = tt2.t_trans` mp_tac >>
        qpat_assum `childtn.t_imm = tt2.t_imm` mp_tac >>
        qpat_assum `tt2.t_stor = at7.t_stor` mp_tac >>
        qpat_assum `tt2.t_trans = at7.t_trans` mp_tac >>
        qpat_assum `tt2.t_imm = at7.t_imm` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
        `(?q. src = Var q /\ ptr_covers bg2 bt2 q back_s cap) /\
          (?q. dst = Var q /\ ptr_covers bg2 bt2 q back_s
            (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
          (?q. ip = Var q /\ ptr_covers bg2 bt2 q back_s 32) /\
          (?q. pp = Var q /\ ptr_covers bg2 bt2 q back_s 32)` by
          (qpat_assum `!root span. not_fresh_at owner root /\ ptr_covers kg kt root u span ==> _` mp_tac >>
           qpat_assum `window_array_root ctx func owner _ _ _ _ _ _ _ _ _ _ _ _ hu` mp_tac >>
           qpat_assum `window_array_cursor T owner ip _ _ _ _ _ _ _ hu` mp_tac >>
           qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ hu` mp_tac >>
           rpt (qpat_x_assum `ptr_covers kg kt _ u _` mp_tac) >>
           rpt (qpat_x_assum `src = Var _` mp_tac) >>
           rpt (qpat_x_assum `dst = Var _` mp_tac) >>
           rpt (qpat_x_assum `ip = Var _` mp_tac) >>
           rpt (qpat_x_assum `pp = Var _` mp_tac) >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           simp_tac bool_ss [window_array_root_def, window_array_cursor_def] >>
           rpt strip_tac >> metis_tac[]) >>
     `st.cs_next_var <= owner.cs_next_var` by
       (qpat_assum `loop_st.cs_next_var = st.cs_next_var+2` mp_tac >>
        qpat_assum `owner.cs_next_var = loop_st.cs_next_var+(if T then 3 else 1)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [] >> decide_tac) >>
        `!x. not_fresh_at st x ==>
          FLOOKUP bg2 x = FLOOKUP G x /\ op_taint bt2 (Var x) = op_taint tn (Var x)` by
          (gen_tac >> strip_tac >>
           qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP bg2 x = FLOOKUP kg x /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `!x. not_fresh_at st x ==> FLOOKUP kg x = _ /\ _`
             (qspec_then `x` mp_tac) >>
           qpat_assum `not_fresh_at st x` mp_tac >>
           qpat_assum `st.cs_next_var <= owner.cs_next_var` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[not_fresh_at_mono]) >>
        `bt2.t_stor = tn.t_stor /\ bt2.t_trans = tn.t_trans /\ bt2.t_imm = tn.t_imm` by
          (qpat_assum `bt2.t_stor = bodytn.t_stor` mp_tac >>
           qpat_assum `bt2.t_trans = bodytn.t_trans` mp_tac >>
           qpat_assum `bt2.t_imm = bodytn.t_imm` mp_tac >>
           qpat_assum `bodytn.t_stor = at7.t_stor` mp_tac >>
           qpat_assum `bodytn.t_trans = at7.t_trans` mp_tac >>
           qpat_assum `bodytn.t_imm = at7.t_imm` mp_tac >>
           qpat_assum `at7.t_stor = ht.t_stor` mp_tac >>
           qpat_assum `at7.t_trans = ht.t_trans` mp_tac >>
           qpat_assum `at7.t_imm = ht.t_imm` mp_tac >>
           qpat_assum `ht.t_stor = kt.t_stor` mp_tac >>
           qpat_assum `ht.t_trans = kt.t_trans` mp_tac >>
           qpat_assum `ht.t_imm = kt.t_imm` mp_tac >>
           qpat_assum `kt.t_stor = tn.t_stor` mp_tac >>
           qpat_assum `kt.t_trans = tn.t_trans` mp_tac >>
           qpat_assum `kt.t_imm = tn.t_imm` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>

     `(!i. b <= i /\ i < b+32 ==> i NOTIN bt2.t_mem) /\
      (!i. bi <= i /\ i < bi+32 ==> i NOTIN bt2.t_mem) /\
      (!i. bd <= i /\ i < bd+32 ==> i NOTIN bt2.t_mem)` by
       (qpat_assum `bt2.t_mem = bodytn.t_mem DIFF _` mp_tac >>
        qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN bodytn.t_mem` mp_tac >>
        qpat_assum `!i. bi <= i /\ i < bi+32 ==> i NOTIN bodytn.t_mem` mp_tac >>
        qpat_assum `!i. bd <= i /\ i < bd+32 ==> i NOTIN bodytn.t_mem` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF] >> metis_tac[]) >>
     `!i. d <= i /\ i < d+32+SUC k*abi_member_head_size ty ==> i NOTIN bt2.t_mem` by
       (qpat_assum `!i. d <= i /\ i < d+32+SUC k*abi_member_head_size ty ==> i NOTIN bodytn.t_mem` mp_tac >>
        qpat_assum `bt2.t_mem = bodytn.t_mem DIFF _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF] >> metis_tac[]) >>
     `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\
       i < d+32+LENGTH avs*abi_member_head_size ty+
         SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs)) ==> i NOTIN bt2.t_mem` by
       (qpat_assum `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\
          i < d+32+LENGTH avs*abi_member_head_size ty+
            SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs)) ==> i NOTIN bodytn.t_mem` mp_tac >>
        qpat_assum `bt2.t_mem = bodytn.t_mem DIFF _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF] >> metis_tac[]) >>
     `?q. dp = Var q /\ ptr_covers bg2 bt2 q back_s 32` by
       (qpat_assum `!root span. not_fresh_at owner root /\ ptr_covers kg kt root u span ==> _` mp_tac >>
        qpat_assum `T ==> (?q. dp = Var q /\ ptr_covers kg kt q u 32) /\ _` mp_tac >>
        qpat_assum `window_array_cursor T owner dp _ bd _ _ _ _ _ hu` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [window_array_cursor_def] >>
        rpt strip_tac >> metis_tac[]) >>
     qpat_assum `window_array_transition ctx func owner
       (window_alloca_sites func (frag_ids st en)) _ u back_s` mp_tac >>
     qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ back_s` mp_tac >>
     qpat_assum `abi_encode_exec_frame func s back_s` mp_tac >>
     qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ back_s` mp_tac >>
     qpat_assum `allocas_from lo back_s` mp_tac >>
     qpat_assum `lo <= back_s.vs_alloca_next` mp_tac >>
     qpat_assum `op_taint bt2 count_op = {}` mp_tac >>
     qpat_assum `op_prov bg2 count_op = NONE` mp_tac >>
     rpt (qpat_x_assum `ptr_covers bg2 bt2 _ back_s _` mp_tac) >>
     rpt (qpat_x_assum `src = Var _` mp_tac) >>
     rpt (qpat_x_assum `dst = Var _` mp_tac) >>
     rpt (qpat_x_assum `ip = Var _` mp_tac) >>
     rpt (qpat_x_assum `pp = Var _` mp_tac) >>
     rpt (qpat_x_assum `dp = Var _` mp_tac) >>
     qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN bt2.t_mem` mp_tac >>
     qpat_assum `!i. bi <= i /\ i < bi+32 ==> i NOTIN bt2.t_mem` mp_tac >>
     qpat_assum `!i. bd <= i /\ i < bd+32 ==> i NOTIN bt2.t_mem` mp_tac >>
     qpat_assum `!mem. mem_agree_outside bt2.t_mem back_s.vs_memory mem ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP bg2 x = FLOOKUP G x /\ _` mp_tac >>
     qpat_assum `!i. d <= i /\ i < d+32+SUC k*abi_member_head_size ty ==> i NOTIN bt2.t_mem` mp_tac >>
     qpat_assum `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\
       i < d+32+LENGTH avs*abi_member_head_size ty+
         SUM (MAP (abi_member_tail_size ty) (TAKE (SUC k) avs)) ==> i NOTIN bt2.t_mem` mp_tac >>
     qpat_assum `!i. _ ==> (i IN bt2.t_mem <=> i IN tn.t_mem)` mp_tac >>
     qpat_assum `bt2.t_stor = tn.t_stor` mp_tac >>
     qpat_assum `bt2.t_trans = tn.t_trans` mp_tac >>
     qpat_assum `bt2.t_imm = tn.t_imm` mp_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK back_s,bg2,bt2)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qexists_tac `back_s` >>
     asm_simp_tac (srw_ss()) [Excl "enc_def"] >>
     qexists_tac `bg2` >> qexists_tac `bt2` >> asm_rewrite_tac[] >>
     gvs[Excl "enc_def"] >> rpt strip_tac >> decide_tac) >>
  `?loop_s. window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))]
      (jump_to (FST labels) init_s) loop_s /\ P (LENGTH avs) loop_s` by
    (irule window_array_loop_run >>
     qexistsl_tac [`LENGTH (avs:abi_value list)`, `P`, `0`] >>
     simp_tac bool_ss [arithmeticTheory.ZERO_LESS_EQ] >>
     asm_rewrite_tac[] >>
     qx_gen_tac `last_s` >> strip_tac >> qexists_tac `last_s` >>
     asm_rewrite_tac[] >> irule window_array_transition_refl >>
     qpat_assum `P (LENGTH avs) last_s` mp_tac >>
     qpat_assum `Abbrev (P = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     full_simp_tac bool_ss [Abbr `P`] >>
     metis_tac[window_array_inv_resources, window_array_inv_control]) >>
  qpat_assum `P (LENGTH avs) loop_s` mp_tac >>
  simp_tac bool_ss [Abbr `P`] >> strip_tac >>
  rename1 `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK loop_s,loopG,looptn)` >>
  qabbrev_tac `exit_s = jump_to (SND (SND labels))
    (abi_encode_array_header_state
      (STRING #"%" (toString owner.cs_next_var))
      (STRING #"%" (toString (owner.cs_next_var+1)))
      (STRING #"%" (toString (owner.cs_next_var+2)))
      (LENGTH avs) (LENGTH avs) loop_s)` >>
  `?exitG exittn.
    (!x. not_fresh_at owner x ==>
      FLOOKUP exitG x = FLOOKUP loopG x /\
      op_taint exittn (Var x) = op_taint looptn (Var x)) /\
    exittn.t_mem = looptn.t_mem /\ exittn.t_stor = looptn.t_stor /\
    exittn.t_trans = looptn.t_trans /\ exittn.t_imm = looptn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (loop_s,loopG,looptn) [] (OK exit_s,exitG,exittn)` by
    (qpat_assum `!k u hg ht. _`
       (qspecl_then [`LENGTH (avs:abi_value list)`, `loop_s`, `loopG`, `looptn`] mp_tac) >>
     impl_tac
     >- (asm_rewrite_tac[] >> simp[]) >>
     simp_tac (srw_ss()) [Abbr `exit_s`, Excl "enc_def"]) >>
  `window_array_transition ctx func owner
      (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] loop_s exit_s` by
    (qpat_assum `!k u. k <= LENGTH avs /\ P k u ==> _`
       (qspecl_then [`LENGTH (avs:abi_value list)`, `loop_s`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> simp[]) >>
     simp_tac (srw_ss()) [Abbr `exit_s`, Excl "enc_def"]) >>
  `window_array_inv ctx func owner (window_alloca_sites func (frag_ids st en))
    ei asz msz active ty avs src dst ip loop_st.cs_next_id bi
    dp (if active then index_en.cs_next_id else 0) bd count_op
    (SND (SND labels)) sb cap d (LENGTH avs) exit_s` by
    (simp_tac bool_ss [Abbr `exit_s`] >> irule window_array_header_inv >>
     conj_tac
     >- (POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def] >>
         metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
     conj_tac
     >- (qexists_tac `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]` >>
         first_assum ACCEPT_TAC) >>
     qexists_tac `FST (labels:string#string#string)` >> first_assum ACCEPT_TAC) >>
  `exit_s.vs_memory = loop_s.vs_memory /\
   exit_s.vs_allocas = loop_s.vs_allocas /\
   exit_s.vs_alloca_next = loop_s.vs_alloca_next /\
   abi_encode_exec_frame func loop_s exit_s` by
    (qpat_assum `Abbrev (exit_s = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[Abbr `exit_s`, jump_to_def, abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
       update_var_def, abi_encode_exec_frame_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def]) >>
  `abi_encode_exec_frame func s exit_s` by
    (qpat_assum `abi_encode_exec_frame func s loop_s` mp_tac >>
     qpat_assum `abi_encode_exec_frame func loop_s exit_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_encode_exec_frame_trans]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK exit_s,exitG,exittn)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK loop_s,loopG,looptn)`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (loop_s,loopG,looptn) [] (OK exit_s,exitG,exittn)`
       (qspec_then `D` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `allocas_from lo exit_s /\ lo <= exit_s.vs_alloca_next` by
    (qpat_assum `allocas_from lo loop_s` mp_tac >>
     qpat_assum `lo <= loop_s.vs_alloca_next` mp_tac >>
     qpat_assum `exit_s.vs_allocas = loop_s.vs_allocas` mp_tac >>
     qpat_assum `exit_s.vs_alloca_next = loop_s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
  `!mem. mem_agree_outside exittn.t_mem exit_s.vs_memory mem ==>
    abi_encoder_window_input (AbiDynArray ei asz msz active)
      (Array NONE ty) (ListV avs) sb cap mem` by
    (qpat_assum `!mem. mem_agree_outside looptn.t_mem loop_s.vs_memory mem ==> _` mp_tac >>
     qpat_assum `exittn.t_mem = looptn.t_mem` mp_tac >>
     qpat_assum `exit_s.vs_memory = loop_s.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!root span. not_fresh_at owner root /\
    ptr_covers loopG looptn root loop_s span ==>
    ptr_covers exitG exittn root exit_s span` by
    (qx_genl_tac [`root`, `span`] >> strip_tac >>
     qpat_assum `!x. not_fresh_at owner x ==> FLOOKUP exitG x = _ /\ _` mp_tac >>
     qpat_assum `window_array_transition ctx func owner
       (window_alloca_sites func (frag_ids st en)) _ loop_s exit_s` mp_tac >>
     qpat_assum `not_fresh_at owner root` mp_tac >>
     qpat_assum `ptr_covers loopG looptn root loop_s span` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
     metis_tac[window_array_transition_vars]) >>
  `(?q. src = Var q /\ ptr_covers exitG exittn q exit_s cap) /\
   (?q. dst = Var q /\ ptr_covers exitG exittn q exit_s
      (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
   (?q. pp = Var q /\ ptr_covers exitG exittn q exit_s 32) /\
   (active ==> ?q. dp = Var q /\ ptr_covers exitG exittn q exit_s 32)` by
    (qpat_assum `!root span. not_fresh_at owner root /\
       ptr_covers loopG looptn root loop_s span ==> _` mp_tac >>
     qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ loop_s` mp_tac >>
     qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ loop_s` mp_tac >>
     rpt (qpat_x_assum `ptr_covers loopG looptn _ loop_s _` mp_tac) >>
     qpat_assum `active ==> (?q. dp = Var q /\ ptr_covers loopG looptn q loop_s 32) /\ _` mp_tac >>
     rpt (qpat_x_assum `src = Var _` mp_tac) >>
     rpt (qpat_x_assum `dst = Var _` mp_tac) >>
     rpt (qpat_x_assum `pp = Var _` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_inv_def, window_array_root_def, window_array_cursor_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `exit_st.cs_current_insts = [] /\
   exit_st.cs_current_bb = SND (SND labels) /\
   owner.cs_next_var <= exit_st.cs_next_var` by
    (qpat_assum `abi_encoder_array_loop_code func owner body_st body_end exit_st ip count_op labels` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encoder_array_loop_code_def] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_window_input (AbiDynArray ei asz msz active)
      (Array NONE ty) (ListV avs) sb cap exit_s.vs_memory /\
   abi_encoder_array_prefix ty avs (LENGTH avs) d exit_s.vs_memory /\
   eval_operand src exit_s = SOME (n2w sb) /\ sb < dimword (:256) /\
   alloca_inv exit_s /\ alloca_room ctx func exit_s /\ ~exit_s.vs_halted /\
   exit_s.vs_current_bb = exit_st.cs_current_bb /\
   exit_s.vs_inst_idx = LENGTH exit_st.cs_current_insts /\
   sb+32 <= exit_s.vs_alloca_next` by
    (qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ exit_s` mp_tac >>
     qpat_assum `exit_st.cs_current_insts = []` mp_tac >>
     qpat_assum `exit_st.cs_current_bb = SND (SND labels)` mp_tac >>
     qpat_assum `32 <= cap` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[window_array_inv_def, window_array_root_def] >>
     `exit_s.vs_alloca_next < dimword (:256)` by
       metis_tac[alloca_room_next_lt] >> decide_tac) >>
  `(active ==> eval_operand dp exit_s = SOME (n2w bd) /\
      bd < dimword (:256) /\ bd+32 <= exit_s.vs_alloca_next /\
      (!x. dp = Var x ==> not_fresh_at exit_st x) /\
      mload bd exit_s = n2w (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) avs)))` by
    (qpat_assum `window_array_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ exit_s` mp_tac >>
     qpat_assum `owner.cs_next_var <= exit_st.cs_next_var` mp_tac >>
     qpat_assum `alloca_inv exit_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> strip_tac >> strip_tac >>
     fs[window_array_inv_def, window_array_cursor_def,
       alloca_inv_def, alloca_next_valid_def, mload_def,
       valueEncodingDefsTheory.mem_word_at_def, Excl "enc_def"] >>
     metis_tac[not_fresh_at_mono]) >>
  `?scalar_raw. window_pure_seq exit_st loop_end exit_s scalar_raw /\
    eval_operand size_op scalar_raw =
      SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. size_op = Var x ==> not_fresh_at loop_end x) /\
    (!x. ~not_fresh_at loop_end x ==>
      lookup_var x scalar_raw = lookup_var x exit_s)` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ exit_s.vs_memory` mp_tac >>
     qpat_assum `(if active then abi_encode_array_dynamic_exit src dp exit_st
       else abi_encode_array_static_exit src asz exit_st) = (size_op,loop_end)` mp_tac >>
     qpat_assum `eval_operand src exit_s = SOME (n2w sb)` mp_tac >>
     qpat_assum `sb < dimword (:256)` mp_tac >>
     qpat_assum `active ==> eval_operand dp exit_s = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `(active ==> eval_operand dp exit_s = SOME (n2w bd) /\
       bd < dimword (:256) /\
       (!x. dp = Var x ==> not_fresh_at exit_st x) /\
       mload bd exit_s = n2w (LENGTH avs*abi_member_head_size ty+
         SUM (MAP (abi_member_tail_size ty) avs)))` by metis_tac[] >>
     drule_all abiEncoderWindowArrayExitTheory.window_array_scalar_exit_pure_observed >>
     strip_tac >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
  qabbrev_tac `scalar_s = scalar_raw with vs_inst_idx := LENGTH loop_end.cs_current_insts` >>
  `window_phase ctx func exit_st loop_end {} [] exit_s scalar_s` by
    (simp_tac bool_ss [Abbr `scalar_s`] >> irule window_pure_seq_phase >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `window_array_transition ctx func owner {} [] exit_s scalar_s` by
    (irule window_array_transition_owner_weaken >>
     qexists_tac `exit_st` >> conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >>
         qexists_tac `owner` >> asm_rewrite_tac[]) >>
     irule window_array_pure_phase_transition >>
     qexists_tac `loop_end` >> first_assum ACCEPT_TAC) >>
  `?exit_len exit_c1 exit_payload exit_c2.
    emit_op MLOAD [src] exit_st = (exit_len,exit_c1) /\
    (if active then emit_op MLOAD [dp] exit_c1
     else emit_op MUL [exit_len;Lit (n2w asz)] exit_c1) = (exit_payload,exit_c2) /\
    emit_op ADD [Lit 32w;exit_payload] exit_c2 = (size_op,loop_end)` by
    (qpat_assum `(if active then abi_encode_array_dynamic_exit src dp exit_st
       else abi_encode_array_static_exit src asz exit_st) = (size_op,loop_end)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >>
     simp_tac bool_ss [COND_CLAUSES, abi_encode_array_dynamic_exit_def,
       abi_encode_array_static_exit_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
  qabbrev_tac `ev0 = STRING #"%" (toString exit_st.cs_next_var)` >>
  qabbrev_tac `ev1 = STRING #"%" (toString exit_c1.cs_next_var)` >>
  qabbrev_tac `ev2 = STRING #"%" (toString exit_c2.cs_next_var)` >>
  `emit_op (if active then MLOAD else MUL)
      (if active then [dp] else [exit_len;Lit (n2w asz)]) exit_c1 =
    (exit_payload,exit_c2)` by
    (qpat_assum `(if active then emit_op MLOAD [dp] exit_c1 else _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >> simp[]) >>
  qpat_assum `emit_op MLOAD [src] exit_st = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op (if active then MLOAD else MUL) _ exit_c1 = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD [Lit 32w;exit_payload] exit_c2 = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `exit_len = Var ev0 /\ exit_payload = Var ev1 /\ size_op = Var ev2` by
    (qpat_assum `exit_len = Var _` mp_tac >>
     qpat_assum `exit_payload = Var _` mp_tac >>
     qpat_assum `size_op = Var _` mp_tac >>
     simp_tac bool_ss [Abbr `ev0`, Abbr `ev1`, Abbr `ev2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  qabbrev_tac `ex1 = mk_inst exit_st.cs_next_id MLOAD [src] [ev0]` >>
  qabbrev_tac `ex2 = mk_inst exit_c1.cs_next_id
    (if active then MLOAD else MUL)
    (if active then [dp] else [exit_len;Lit (n2w asz)]) [ev1]` >>
  qabbrev_tac `ex3 = mk_inst exit_c2.cs_next_id ADD [Lit 32w;exit_payload] [ev2]` >>
  `emitted_insts exit_st loop_end = [ex1;ex2;ex3]` by
    (qpat_assum `exit_c1.cs_current_insts = exit_st.cs_current_insts ++ _` mp_tac >>
     qpat_assum `exit_c2.cs_current_insts = exit_c1.cs_current_insts ++ _` mp_tac >>
     qpat_assum `loop_end.cs_current_insts = exit_c2.cs_current_insts ++ _` mp_tac >>
     simp_tac bool_ss [Abbr `ex1`, Abbr `ex2`, Abbr `ex3`,
       Abbr `ev0`, Abbr `ev1`, Abbr `ev2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  `?exit_load exit_mid.
    step_inst_base ex1 exit_s = OK exit_load /\
    step_inst_base ex2 exit_load = OK exit_mid /\
    step_inst_base ex3 exit_mid = OK scalar_raw` by
    (qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     qpat_assum `emitted_insts exit_st loop_end = [ex1;ex2;ex3]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowSequenceTheory.window_pure_seq_def,
       abiEncoderWindowSequenceTheory.window_seq_def, run_inst_seq_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `mem_word_at sb exit_s.vs_memory = n2w (LENGTH avs)` by
    (qpat_assum `abi_encoder_window_input _ _ _ _ _ exit_s.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_encoder_window_array_iff]) >>
  `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` by
    (qpat_assum `step_inst_base ex1 exit_s = OK exit_load` mp_tac >>
     qpat_assum `eval_operand src exit_s = SOME (n2w sb)` mp_tac >>
     qpat_assum `mem_word_at sb exit_s.vs_memory = n2w (LENGTH avs)` mp_tac >>
     qpat_assum `sb < dimword (:256)` mp_tac >>
     simp_tac bool_ss [Abbr `ex1`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, exec_read1_def,
       w2n_n2w, LESS_MOD, GSYM mem_word_at_eq_mload]) >>
  `!x. not_fresh_at exit_st x ==> x <> ev0 /\ x <> ev1 /\ x <> ev2` by
    (qpat_assum `exit_c1.cs_next_var = exit_st.cs_next_var+1` mp_tac >>
     qpat_assum `exit_c2.cs_next_var = exit_c1.cs_next_var+1` mp_tac >>
     simp_tac bool_ss [Abbr `ev0`, Abbr `ev1`, Abbr `ev2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[not_fresh_at_def] >> rpt strip_tac >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD, LESS_EQ_TRANS]) >>
  `ev0 <> ev1 /\ ev0 <> ev2 /\ ev1 <> ev2` by
    (qpat_assum `exit_c1.cs_next_var = exit_st.cs_next_var+1` mp_tac >>
     qpat_assum `exit_c2.cs_next_var = exit_c1.cs_next_var+1` mp_tac >>
     simp_tac bool_ss [Abbr `ev0`, Abbr `ev1`, Abbr `ev2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `exit_st.cs_next_var <> exit_c1.cs_next_var /\
      exit_st.cs_next_var <> exit_c2.cs_next_var /\
      exit_c1.cs_next_var <> exit_c2.cs_next_var` by decide_tac >>
     metis_tac[listTheory.CONS_11,
       REWRITE_RULE [FUN_EQ_THM, combinTheory.o_DEF, combinTheory.I_THM]
         ASCIInumbersTheory.num_dec_string]) >>
  `(active ==> eval_operand dp exit_load = SOME (n2w bd) /\
      mload bd exit_load = n2w (LENGTH avs*abi_member_head_size ty+
        SUM (MAP (abi_member_tail_size ty) avs))) /\
   eval_operand exit_len exit_load = SOME (n2w (LENGTH avs))` by
    (qpat_assum `active ==> eval_operand dp exit_s = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at exit_st x ==> x <> ev0 /\ _` mp_tac >>
     qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
     qpat_assum `exit_len = Var ev0` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `dp` >> gvs[eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, mload_def] >> metis_tac[]) >>
  qabbrev_tac `exit_off = if active then LENGTH avs*abi_member_head_size ty+
    SUM (MAP (abi_member_tail_size ty) avs) else LENGTH avs*asz` >>
  `exit_mid = update_var ev1 (n2w exit_off) exit_load` by
    (qpat_assum `step_inst_base ex2 exit_load = OK exit_mid` mp_tac >>
     qpat_assum `active ==> eval_operand dp exit_load = _ /\ _` mp_tac >>
     qpat_assum `active ==> eval_operand dp exit_s = _ /\ _` mp_tac >>
     qpat_assum `eval_operand exit_len exit_load = SOME (n2w (LENGTH avs))` mp_tac >>
     simp_tac bool_ss [Abbr `ex2`, Abbr `exit_off`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >>
     simp[step_inst_base_opcode_eqs, exec_read1_def, exec_pure2_def,
       eval_operand_def, w2n_n2w, LESS_MOD, word_mul_n2w]) >>
  `eval_operand exit_payload exit_mid = SOME (n2w exit_off)` by
    (qpat_assum `exit_mid = update_var ev1 (n2w exit_off) exit_load` mp_tac >>
     qpat_assum `exit_payload = Var ev1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `scalar_raw = update_var ev2 (n2w (32+exit_off)) exit_mid` by
    (qpat_assum `step_inst_base ex3 exit_mid = OK scalar_raw` mp_tac >>
     qpat_assum `eval_operand exit_payload exit_mid = SOME (n2w exit_off)` mp_tac >>
     simp_tac bool_ss [Abbr `ex3`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def, word_add_n2w]) >>
  `!i. sb <= i /\ i < sb+32 ==> i NOTIN exittn.t_mem` by
    (qpat_assum `!mem. mem_agree_outside exittn.t_mem exit_s.vs_memory mem ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     mp_tac (Q.SPECL [`exittn.t_mem`, `exit_s.vs_memory`, `sb`,
       `n2w (LENGTH (avs:abi_value list)):bytes32`] robust_mem_word_at_clean) >>
     impl_tac
     >- (rpt strip_tac >> first_x_assum drule >>
         simp_tac bool_ss [abi_encoder_window_array_iff] >>
         rpt strip_tac >> gvs[Excl "enc_def"]) >>
     simp[]) >>
  qabbrev_tac `eg1 = step_prov PG exitG ex1 exit_load` >>
  qabbrev_tac `et1 = step_taint ex1 exit_s exit_load exittn` >>
  qabbrev_tac `eg2 = step_prov PG eg1 ex2 exit_mid` >>
  qabbrev_tac `et2 = step_taint ex2 exit_load exit_mid et1` >>
  qabbrev_tac `eg3 = step_prov PG eg2 ex3 scalar_raw` >>
  qabbrev_tac `et3 = step_taint ex3 exit_mid scalar_raw et2` >>
  `op_taint et1 exit_len = {} /\ et1.t_mem = exittn.t_mem` by
    (qpat_assum `!i. sb <= i /\ i < sb+32 ==> i NOTIN exittn.t_mem` mp_tac >>
     qpat_assum `eval_operand src exit_s = SOME (n2w sb)` mp_tac >>
     qpat_assum `mem_word_at sb exit_s.vs_memory = n2w (LENGTH avs)` mp_tac >>
     qpat_assum `sb < dimword (:256)` mp_tac >>
     qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
     qpat_assum `exit_len = Var ev0` mp_tac >>
     simp_tac bool_ss [Abbr `et1`, Abbr `ex1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `eval_operand src exit_s = SOME (n2w sb)`
       (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
     simp_tac (srw_ss()) [w2n_n2w, LESS_MOD, GSYM mem_word_at_eq_mload] >>
     disch_then (qspecl_then [`exittn`, `exit_st.cs_next_id`, `ev0`] mp_tac) >> simp[]) >>
  `active ==> !i. bd <= i /\ i < bd+32 ==> i NOTIN et1.t_mem` by
    (qpat_assum `active ==> (?q. dp = Var q /\ ptr_covers loopG looptn q loop_s 32) /\ _` mp_tac >>
     qpat_assum `exittn.t_mem = looptn.t_mem` mp_tac >>
     qpat_assum `et1.t_mem = exittn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `op_taint et2 exit_payload = {} /\ et2.t_mem = et1.t_mem` by
    (Cases_on `active`
     >- (qpat_assum `T ==> eval_operand dp exit_load = _ /\ _` mp_tac >>
         qpat_assum `T ==> eval_operand dp exit_s = _ /\ _` mp_tac >>
         qpat_assum `T ==> !i. bd <= i /\ i < bd+32 ==> i NOTIN et1.t_mem` mp_tac >>
         qpat_assum `exit_mid = update_var ev1 (n2w exit_off) exit_load` mp_tac >>
         qpat_assum `exit_payload = Var ev1` mp_tac >>
         simp_tac bool_ss [Abbr `et2`, Abbr `ex2`, Abbr `exit_off`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >> rpt strip_tac >>
         qpat_assum `eval_operand dp exit_load = SOME (n2w bd)`
           (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
         simp_tac (srw_ss()) [w2n_n2w, LESS_MOD] >>
         disch_then (qspecl_then [`et1`, `exit_c1.cs_next_id`, `ev1`] mp_tac) >> simp[]) >>
     qpat_assum `op_taint et1 exit_len = {}` mp_tac >>
     qpat_assum `eval_operand exit_len exit_load = SOME (n2w (LENGTH avs))` mp_tac >>
     qpat_assum `exit_mid = update_var ev1 (n2w exit_off) exit_load` mp_tac >>
     qpat_assum `exit_payload = Var ev1` mp_tac >>
     simp_tac bool_ss [Abbr `et2`, Abbr `ex2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, new_site_bytes_def, update_var_def, step_writes_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
     Cases_on `exit_len` >> fs[op_taint_def, FLOOKUP_DEF]) >>
  `op_taint et3 size_op = {} /\ et3.t_mem = et2.t_mem` by
    (qpat_assum `op_taint et2 exit_payload = {}` mp_tac >>
     qpat_assum `eval_operand exit_payload exit_mid = SOME (n2w exit_off)` mp_tac >>
     qpat_assum `scalar_raw = update_var ev2 (n2w (32+exit_off)) exit_mid` mp_tac >>
     qpat_assum `size_op = Var ev2` mp_tac >>
     simp_tac bool_ss [Abbr `et3`, Abbr `ex3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, new_site_bytes_def, update_var_def, step_writes_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def, eval_operand_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]) >>
  `et3.t_mem = exittn.t_mem /\ et3.t_stor = exittn.t_stor /\
   et3.t_trans = exittn.t_trans /\ et3.t_imm = exittn.t_imm` by
    (qpat_assum `et3.t_mem = et2.t_mem` mp_tac >>
     qpat_assum `et2.t_mem = et1.t_mem` mp_tac >>
     qpat_assum `et1.t_mem = exittn.t_mem` mp_tac >>
     simp_tac bool_ss [Abbr `et3`, Abbr `et2`, Abbr `et1`,
       Abbr `ex1`, Abbr `ex2`, Abbr `ex3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >>
     simp[step_taint_nonmemory_frame, mk_inst_def]) >>
  `!x. not_fresh_at exit_st x ==>
    FLOOKUP eg3 x = FLOOKUP exitG x /\
    op_taint et3 (Var x) = op_taint exittn (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at exit_st x ==> x <> ev0 /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at exit_st x` mp_tac >>
     simp_tac bool_ss [Abbr `eg3`, Abbr `eg2`, Abbr `eg1`,
       Abbr `et3`, Abbr `et2`, Abbr `et1`, Abbr `ex1`, Abbr `ex2`, Abbr `ex3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     asm_simp_tac (srw_ss()) [step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  `?sq. src = Var sq /\ ptr_covers exitG exittn sq exit_s 32` by
    (qpat_assum `ptr_covers exitG exittn _ exit_s cap` mp_tac >>
     rpt (qpat_x_assum `src = Var _` mp_tac) >>
     qpat_assum `32 <= cap` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [ptr_covers_def] >> rpt strip_tac >>
     rename1 `lookup_var cq exit_s = SOME cw` >>
     rename1 `FLOOKUP exitG cq = SOME (cbase,ccap)` >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     qexistsl_tac [`cw`, `cbase`, `ccap`] >> asm_rewrite_tac[] >> decide_tac) >>
  `(active ==> ?dq. dp = Var dq /\ ptr_covers eg1 et1 dq exit_load 32)` by
    (strip_tac >>
     qpat_assum `active ==> ?q. dp = Var q /\ ptr_covers exitG exittn q exit_s 32` mp_tac >>
     qpat_assum `active ==> eval_operand dp exit_s = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at exit_st x ==> x <> ev0 /\ _` mp_tac >>
     qpat_assum `active` mp_tac >>
     qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
     qpat_assum `mem_word_at sb exit_s.vs_memory = n2w (LENGTH avs)` mp_tac >>
     qpat_assum `sb < dimword (:256)` mp_tac >>
     simp_tac bool_ss [Abbr `eg1`, Abbr `et1`, Abbr `ex1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     rename1 `dp = Var exit_dpq` >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >>
     mp_tac (Q.SPECL [`PG`, `exitG`, `exittn`, `exit_s`, `exit_st.cs_next_id`,
       `src`, `ev0`, `exit_dpq`, `n2w sb:bytes32`, `32`]
       (Q.INST_TYPE [`:'a` |-> `:256`] wordLoadStorePtrTheory.mload_preserves_ptr_covers)) >>
     asm_simp_tac (srw_ss()) [w2n_n2w, LESS_MOD, GSYM mem_word_at_eq_mload] >>
     metis_tac[]) >>
  `!j. step_inst_base ex1 (exit_s with vs_inst_idx := j) =
      OK (exit_load with vs_inst_idx := j) /\
    step_inst_base ex2 (exit_load with vs_inst_idx := j) =
      OK (exit_mid with vs_inst_idx := j) /\
    step_inst_base ex3 (exit_mid with vs_inst_idx := j) =
      OK (scalar_raw with vs_inst_idx := j)` by
    (qpat_assum `step_inst_base ex1 exit_s = OK exit_load` mp_tac >>
     qpat_assum `step_inst_base ex2 exit_load = OK exit_mid` mp_tac >>
     qpat_assum `step_inst_base ex3 exit_mid = OK scalar_raw` mp_tac >>
     simp_tac bool_ss [Abbr `ex1`, Abbr `ex2`, Abbr `ex3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> Cases_on `active` >>
     asm_simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  `!D j. ptr_inst_ok D lo 0 ctx func exitG exittn ex1
    (exit_s with vs_inst_idx := j)` by
    (rpt gen_tac >>
     qpat_assum `src = Var sq` mp_tac >>
     qpat_assum `ptr_covers exitG exittn sq exit_s 32` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `allocas_from lo exit_s` mp_tac >>
     simp_tac bool_ss [Abbr `ex1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
     irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     qexists_tac `0` >> asm_simp_tac (srw_ss()) [allocas_from_def] >>
     irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[]) >>
  `!D j. ptr_inst_ok D lo 0 ctx func eg1 et1 ex2
    (exit_load with vs_inst_idx := j)` by
    (rpt gen_tac >> Cases_on `active`
     >- (qpat_assum `T ==> ?dq. dp = Var dq /\ ptr_covers eg1 et1 dq exit_load 32` mp_tac >>
         qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
         qpat_assum `allocas_from lo exit_s` mp_tac >>
         qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
         simp_tac bool_ss [Abbr `ex2`] >> POP_ASSUM_LIST (K ALL_TAC) >>
         rpt strip_tac >> gvs[] >>
         irule ptr_inst_ok_lower_bound_transport >>
         conj_tac >- (fs[allocas_from_def, update_var_def] >> first_assum ACCEPT_TAC) >>
         qexists_tac `0` >> asm_simp_tac (srw_ss()) [allocas_from_def] >>
         irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[]) >>
     qpat_assum `op_taint et1 exit_len = {}` mp_tac >>
     qpat_assum `allocas_from lo exit_s` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `!j. step_inst_base ex1 _ = _ /\ _` mp_tac >>
     qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
     qpat_assum `exit_mid = update_var ev1 (n2w exit_off) exit_load` mp_tac >>
     qpat_assum `Abbrev (ex2 = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `step_inst 0 ctx ex2 (exit_load with vs_inst_idx := j) =
       OK (exit_mid with vs_inst_idx := j)` by
       (asm_simp_tac (srw_ss()) [step_inst_non_invoke, Abbr `ex2`, mk_inst_def]) >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `ex2`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
     conj_tac
     >- (gen_tac >> Cases_on `op = exit_len` >> fs[op_taint_def] >>
         Cases_on `op = Lit (n2w asz)` >> fs[op_taint_def]) >>
     fs[allocas_from_def, update_var_def] >> first_assum ACCEPT_TAC) >>
  `!D j. ptr_inst_ok D lo 0 ctx func eg2 et2 ex3
    (exit_mid with vs_inst_idx := j)` by
    (rpt gen_tac >>
     qpat_assum `op_taint et2 exit_payload = {}` mp_tac >>
     qpat_assum `allocas_from lo exit_s` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `!j. step_inst_base ex1 _ = _ /\ _` mp_tac >>
     qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
     qpat_assum `exit_mid = update_var ev1 (n2w exit_off) exit_load` mp_tac >>
     qpat_assum `scalar_raw = update_var ev2 (n2w (32+exit_off)) exit_mid` mp_tac >>
     qpat_assum `Abbrev (ex3 = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `step_inst 0 ctx ex3 (exit_mid with vs_inst_idx := j) =
       OK (scalar_raw with vs_inst_idx := j)` by
       (asm_simp_tac (srw_ss()) [step_inst_non_invoke, Abbr `ex3`, mk_inst_def]) >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `ex3`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, op_taint_def] >>
     conj_tac
     >- (gen_tac >> Cases_on `op = exit_payload` >> fs[op_taint_def] >>
         Cases_on `op = Lit 32w` >> fs[op_taint_def]) >>
     fs[allocas_from_def, update_var_def] >> first_assum ACCEPT_TAC) >>
  `run_inst_seq_mem_ok [ex1;ex2;ex3] exit_s` by
    (qpat_assum `step_inst_base ex1 exit_s = OK exit_load` mp_tac >>
     qpat_assum `step_inst_base ex2 exit_load = OK exit_mid` mp_tac >>
     qpat_assum `step_inst_base ex3 exit_mid = OK scalar_raw` mp_tac >>
     qpat_assum `eval_operand src exit_s = SOME (n2w sb)` mp_tac >>
     qpat_assum `sb < dimword (:256)` mp_tac >>
     qpat_assum `sb+32 <= exit_s.vs_alloca_next` mp_tac >>
     qpat_assum `active ==> eval_operand dp exit_load = _ /\ _` mp_tac >>
     qpat_assum `active ==> eval_operand dp exit_s = _ /\ _` mp_tac >>
     qpat_assum `exit_load = update_var ev0 (n2w (LENGTH avs)) exit_s` mp_tac >>
     qpat_assum `Abbrev (ex1 = _)` mp_tac >>
     qpat_assum `Abbrev (ex2 = _)` mp_tac >>
     qpat_assum `Abbrev (ex3 = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
       [`step_inst_base ex1 exit_s = OK exit_load`,
        `step_inst_base ex2 exit_load = OK exit_mid`,
        `step_inst_base ex3 exit_mid = OK scalar_raw`] >>
     simp[NoAsms] >> Cases_on `active` >>
     gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def, Abbr `ex1`, Abbr `ex2`, Abbr `ex3`,
       mk_inst_def, contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       update_var_def, w2n_n2w, LESS_MOD]) >>
  `!D. inst_seq_ptr D lo ctx func PG exitG exittn
    [ex1;ex2;ex3] exit_s eg3 et3` by
    (gen_tac >>
     qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func exitG exittn ex1 _` mp_tac >>
     qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func eg1 et1 ex2 _` mp_tac >>
     qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func eg2 et2 ex3 _` mp_tac >>
     qpat_assum `step_inst_base ex1 exit_s = OK exit_load` mp_tac >>
     qpat_assum `!j. step_inst_base ex1 _ = _ /\ _` mp_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`Abbrev (eg1 = _)`, `Abbrev (et1 = _)`,
        `Abbrev (eg2 = _)`, `Abbrev (et2 = _)`,
        `Abbrev (eg3 = _)`, `Abbrev (et3 = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     pure_rewrite_tac[inst_seq_ptr_def] >>
     qpat_assum `step_inst_base ex1 exit_s = OK exit_load`
       (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (eg1 = _)`, `Abbrev (et1 = _)`] >>
     qpat_assum `!j. step_inst_base ex1 _ = _ /\ _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (eg2 = _)`, `Abbrev (et2 = _)`] >>
     qpat_assum `!j. step_inst_base ex1 _ = _ /\ _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (eg3 = _)`, `Abbrev (et3 = _)`] >>
     simp[NoAsms] >> conj_tac
     >- (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func exitG exittn ex1 _`
           (qspecl_then [`D`, `exit_s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
     conj_tac
     >- (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func eg1 et1 ex2 _`
           (qspecl_then [`D`, `SUC exit_s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
     qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func eg2 et2 ex3 _`
       (qspecl_then [`D`, `SUC (SUC exit_s.vs_inst_idx)`] mp_tac) >> simp[NoAsms]) >>
  `loop_end.cs_current_insts = exit_st.cs_current_insts ++ [ex1;ex2;ex3] /\
   loop_end.cs_current_bb = exit_st.cs_current_bb` by
    (qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     qpat_assum `emitted_insts exit_st loop_end = [ex1;ex2;ex3]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abiEncoderWindowSequenceTheory.window_pure_seq_def,
       abiEncoderWindowSequenceTheory.window_seq_def, emitted_insts_def, inst_extends_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `?exit_bb. lookup_block exit_s.vs_current_bb func.fn_blocks = SOME exit_bb /\
    isPREFIX [ex1;ex2;ex3] (DROP exit_s.vs_inst_idx exit_bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code exit_st loop_end func`, `loop_end.cs_current_insts = _`,
        `loop_end.cs_current_bb = _`, `exit_s.vs_current_bb = exit_st.cs_current_bb`,
        `exit_s.vs_inst_idx = LENGTH exit_st.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (exit_s,exitG,exittn) [] (OK scalar_s,eg3,et3)` by
    (gen_tac >>
     qpat_assum `lookup_block exit_s.vs_current_bb func.fn_blocks = SOME exit_bb` mp_tac >>
     qpat_assum `isPREFIX [ex1;ex2;ex3] _` mp_tac >>
     qpat_assum `~exit_s.vs_halted` mp_tac >>
     qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     qpat_assum `emitted_insts exit_st loop_end = [ex1;ex2;ex3]` mp_tac >>
     qpat_assum `run_inst_seq_mem_ok [ex1;ex2;ex3] exit_s` mp_tac >>
     qpat_assum `!D. inst_seq_ptr D lo ctx func PG exitG exittn _ _ eg3 et3` mp_tac >>
     qpat_assum `exit_s.vs_inst_idx = LENGTH exit_st.cs_current_insts` mp_tac >>
     qpat_assum `loop_end.cs_current_insts = exit_st.cs_current_insts ++ [ex1;ex2;ex3]` mp_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`Abbrev (ex1 = _)`, `Abbrev (ex2 = _)`, `Abbrev (ex3 = _)`,
        `Abbrev (scalar_s = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `run_inst_seq [ex1;ex2;ex3] exit_s = OK scalar_raw` by
       (fs[abiEncoderWindowSequenceTheory.window_pure_seq_def,
         abiEncoderWindowSequenceTheory.window_seq_def] >> metis_tac[]) >>
     `inst_seq_ptr D lo ctx func PG exitG exittn [ex1;ex2;ex3] exit_s eg3 et3` by
       metis_tac[] >>
     mp_tac (Q.SPECL [`[ex1;ex2;ex3]`, `exit_s`, `scalar_raw`,
       `exitG`, `exittn`, `eg3`, `et3`, `ctx`, `func`, `exit_bb`]
       run_inst_seq_gas_origin_ptr_path) >>
     Cases_on `active` >>
     fs[Abbr `ex1`, Abbr `ex2`, Abbr `ex3`, Abbr `scalar_s`,
       mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) exit_s` by
    (qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ loop_s` mp_tac >>
     qpat_assum `window_array_transition ctx func owner
       (window_alloca_sites func (frag_ids st en)) _ loop_s exit_s` mp_tac >>
     qpat_assum `exit_s.vs_memory = loop_s.vs_memory` mp_tac >>
     qpat_assum `exit_s.vs_allocas = loop_s.vs_allocas` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[window_array_cursor_def, Excl "enc_def"] >>
     irule window_array_transition_eval >> goal_assum (drule_at Any) >>
     qexistsl_tac [`ctx`, `func`, `window_alloca_sites func (frag_ids st en)`,
       `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`, `owner`] >>
     asm_rewrite_tac[]) >>
  `window_array_cursor T owner pp st.cs_next_id b 0 sb cap d
    (LENGTH (enc (Array NONE ty) (ListV avs))) scalar_s` by
    (irule window_array_cursor_frame >>
     qexistsl_tac [`{}`, `ctx`, `func`, `[]`, `exit_s`] >>
     asm_rewrite_tac[] >> simp[]) >>
  `alloca_inv scalar_s /\ alloca_room ctx func scalar_s /\ ~scalar_s.vs_halted /\
   scalar_s.vs_current_bb = loop_end.cs_current_bb /\
   scalar_s.vs_inst_idx = LENGTH loop_end.cs_current_insts` by
    (qpat_assum `window_phase ctx func exit_st loop_end {} [] exit_s scalar_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[window_phase_control, window_phase_resources]) >>
  `eval_operand pp scalar_s = SOME (n2w b) /\ b < dimword (:256) /\
   mload b scalar_s = 0w /\ FLOOKUP scalar_s.vs_allocas st.cs_next_id = SOME (b,32) /\
   (!x. pp = Var x \/ size_op = Var x ==> not_fresh_at loop_end x) /\
   eval_operand size_op scalar_s = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs))))` by
    (qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ scalar_s` mp_tac >>
     qpat_assum `eval_operand size_op scalar_raw = SOME _` mp_tac >>
     qpat_assum `!x. size_op = Var x ==> not_fresh_at loop_end x` mp_tac >>
     qpat_assum `owner.cs_next_var <= exit_st.cs_next_var` mp_tac >>
     qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     simp_tac bool_ss [Abbr `scalar_s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_cursor_def,
       abiEncoderWindowSequenceTheory.window_pure_seq_def,
       abiEncoderWindowSequenceTheory.window_seq_def,
       GSYM mem_word_at_eq_mload] >> rpt strip_tac >>
     asm_simp_tac (srw_ss()) [] >> metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `?finish_raw finish_mid finish_before finish_after.
    window_seq loop_end en scalar_s finish_raw /\
    window_pure_seq loop_end finish_before scalar_s finish_mid /\
    window_pure_seq finish_after en
      (mstore b (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) finish_mid) finish_raw /\
    eval_operand out finish_raw = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    (!x. out = Var x ==> not_fresh_at en x)` by
    (qpat_assum `abi_encode_array_finish pp size_op loop_end = (out,en)` mp_tac >>
     qpat_assum `eval_operand pp scalar_s = SOME (n2w b)` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     qpat_assum `mload b scalar_s = 0w` mp_tac >>
     qpat_assum `eval_operand size_op scalar_s = SOME _` mp_tac >>
     qpat_assum `!x. pp = Var x \/ size_op = Var x ==> not_fresh_at loop_end x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_all window_array_parent_finish_seq >> strip_tac >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  `?parent_old parent_c1 parent_next parent_c2 parent_c3.
    emit_op MLOAD [pp] loop_end = (parent_old,parent_c1) /\
    emit_op ADD [parent_old;size_op] parent_c1 = (parent_next,parent_c2) /\
    emit_void MSTORE [pp;parent_next] parent_c2 = ((),parent_c3) /\
    emit_op MLOAD [pp] parent_c3 = (out,en)` by
    (qpat_assum `abi_encode_array_finish pp size_op loop_end = (out,en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_encode_array_finish_def, comp_bind_def,
       comp_ignore_bind_def, LET_THM] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
     rename1 `emit_void MSTORE _ _ = (parent_ignored,_)` >>
     Cases_on `parent_ignored:unit` >> metis_tac[]) >>
  qpat_assum `emit_op MLOAD [pp] loop_end = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD [parent_old;size_op] parent_c1 = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_void MSTORE [pp;parent_next] parent_c2 = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
  qpat_assum `emit_op MLOAD [pp] parent_c3 = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qabbrev_tac `pv0 = STRING #"%" (toString loop_end.cs_next_var)` >>
  qabbrev_tac `pv1 = STRING #"%" (toString parent_c1.cs_next_var)` >>
  qabbrev_tac `pv2 = STRING #"%" (toString parent_c3.cs_next_var)` >>
  `parent_old = Var pv0 /\ parent_next = Var pv1 /\ out = Var pv2` by
    (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `pf1 = mk_inst loop_end.cs_next_id MLOAD [pp] [pv0]` >>
  qabbrev_tac `pf2 = mk_inst parent_c1.cs_next_id ADD [parent_old;size_op] [pv1]` >>
  qabbrev_tac `pf3 = mk_inst parent_c2.cs_next_id MSTORE [pp;parent_next] []` >>
  qabbrev_tac `pf4 = mk_inst parent_c3.cs_next_id MLOAD [pp] [pv2]` >>
  `emitted_insts loop_end en = [pf1;pf2;pf3;pf4]` by
    (qpat_assum `parent_c1.cs_current_insts = loop_end.cs_current_insts ++ _` mp_tac >>
     qpat_assum `parent_c2.cs_current_insts = parent_c1.cs_current_insts ++ _` mp_tac >>
     qpat_assum `parent_c3.cs_current_insts = parent_c2.cs_current_insts ++ _` mp_tac >>
     qpat_assum `en.cs_current_insts = parent_c3.cs_current_insts ++ _` mp_tac >>
     simp_tac bool_ss [Abbr `pf1`, Abbr `pf2`, Abbr `pf3`, Abbr `pf4`,
       Abbr `pv0`, Abbr `pv1`, Abbr `pv2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  `?parent_load parent_add parent_store.
    step_inst_base pf1 scalar_s = OK parent_load /\
    step_inst_base pf2 parent_load = OK parent_add /\
    step_inst_base pf3 parent_add = OK parent_store /\
    step_inst_base pf4 parent_store = OK finish_raw` by
    (qpat_assum `window_seq loop_end en scalar_s finish_raw` mp_tac >>
     qpat_assum `emitted_insts loop_end en = [pf1;pf2;pf3;pf4]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowSequenceTheory.window_seq_def, run_inst_seq_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `parent_load = update_var pv0 0w scalar_s` by
    (qpat_assum `step_inst_base pf1 scalar_s = OK parent_load` mp_tac >>
     qpat_assum `eval_operand pp scalar_s = SOME (n2w b)` mp_tac >>
     qpat_assum `mload b scalar_s = 0w` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     simp_tac bool_ss [Abbr `pf1`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, exec_read1_def, w2n_n2w, LESS_MOD]) >>
  `!x. not_fresh_at loop_end x ==> x <> pv0 /\ x <> pv1 /\ x <> pv2` by
    (qpat_assum `parent_c1.cs_next_var = loop_end.cs_next_var+1` mp_tac >>
     qpat_assum `parent_c2.cs_next_var = parent_c1.cs_next_var+1` mp_tac >>
     qpat_assum `parent_c3.cs_next_var = parent_c2.cs_next_var` mp_tac >>
     simp_tac bool_ss [Abbr `pv0`, Abbr `pv1`, Abbr `pv2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[not_fresh_at_def] >> rpt strip_tac >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_ADD, LESS_EQ_TRANS]) >>
  `eval_operand parent_old parent_load = SOME (0w:bytes32) /\
   eval_operand size_op parent_load =
     SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs))))` by
    (qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_old = Var pv0` mp_tac >>
     qpat_assum `!x. not_fresh_at loop_end x ==> x <> pv0 /\ _` mp_tac >>
     qpat_assum `!x. pp = Var x \/ size_op = Var x ==> not_fresh_at loop_end x` mp_tac >>
     qpat_assum `eval_operand size_op scalar_s = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `size_op` >> gvs[eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `parent_add = update_var pv1
    (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) parent_load` by
    (qpat_assum `step_inst_base pf2 parent_load = OK parent_add` mp_tac >>
     qpat_assum `eval_operand parent_old parent_load = SOME 0w` mp_tac >>
     qpat_assum `eval_operand size_op parent_load = SOME _` mp_tac >>
     simp_tac bool_ss [Abbr `pf2`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, exec_pure2_def, WORD_ADD_0, Excl "enc_def"]) >>
  `eval_operand pp parent_add = SOME (n2w b) /\
   eval_operand parent_next parent_add =
     SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs))))` by
    (qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_next = Var pv1` mp_tac >>
     qpat_assum `!x. not_fresh_at loop_end x ==> x <> pv0 /\ _` mp_tac >>
     qpat_assum `!x. pp = Var x \/ size_op = Var x ==> not_fresh_at loop_end x` mp_tac >>
     qpat_assum `eval_operand pp scalar_s = SOME (n2w b)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `pp` >> gvs[eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `parent_store = mstore b
    (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) parent_add` by
    (qpat_assum `step_inst_base pf3 parent_add = OK parent_store` mp_tac >>
     qpat_assum `eval_operand pp parent_add = SOME (n2w b)` mp_tac >>
     qpat_assum `eval_operand parent_next parent_add = SOME _` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     simp_tac bool_ss [Abbr `pf3`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, exec_write2_def, w2n_n2w, LESS_MOD]) >>
  `eval_operand pp parent_store = SOME (n2w b) /\
   mload b parent_store = n2w (LENGTH (enc (Array NONE ty) (ListV avs)))` by
    (qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
     qpat_assum `eval_operand pp parent_add = SOME (n2w b)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[venomMemPropsTheory.mload_mstore_same] >>
     Cases_on `pp` >> gvs[eval_operand_def, lookup_var_def,
       mstore_def, write_memory_with_expansion_def]) >>
  `finish_raw = update_var pv2
    (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) parent_store` by
    (qpat_assum `step_inst_base pf4 parent_store = OK finish_raw` mp_tac >>
     qpat_assum `eval_operand pp parent_store = SOME (n2w b)` mp_tac >>
     qpat_assum `mload b parent_store = _` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     simp_tac bool_ss [Abbr `pf4`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[step_inst_base_opcode_eqs, exec_read1_def, w2n_n2w, LESS_MOD]) >>
  qabbrev_tac `pfg1 = step_prov PG eg3 pf1 parent_load` >>
  qabbrev_tac `pft1 = step_taint pf1 scalar_s parent_load et3` >>
  qabbrev_tac `pfg2 = step_prov PG pfg1 pf2 parent_add` >>
  qabbrev_tac `pft2 = step_taint pf2 parent_load parent_add pft1` >>
  qabbrev_tac `pfg3 = step_prov PG pfg2 pf3 parent_store` >>
  qabbrev_tac `pft3 = step_taint pf3 parent_add parent_store pft2` >>
  qabbrev_tac `pfg4 = step_prov PG pfg3 pf4 finish_raw` >>
  qabbrev_tac `pft4 = step_taint pf4 parent_store finish_raw pft3` >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN et3.t_mem` by
    (qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN looptn.t_mem` mp_tac >>
     qpat_assum `et3.t_mem = exittn.t_mem` mp_tac >>
     qpat_assum `exittn.t_mem = looptn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `op_taint pft1 parent_old = {} /\ pft1.t_mem = et3.t_mem` by
    (qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN et3.t_mem` mp_tac >>
     qpat_assum `eval_operand pp scalar_s = SOME (n2w b)` mp_tac >>
     qpat_assum `mload b scalar_s = 0w` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_old = Var pv0` mp_tac >>
     simp_tac bool_ss [Abbr `pft1`, Abbr `pf1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `eval_operand pp scalar_s = SOME (n2w b)`
       (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
     simp_tac (srw_ss()) [w2n_n2w, LESS_MOD] >>
     disch_then (qspecl_then [`et3`, `loop_end.cs_next_id`, `pv0`] mp_tac) >> simp[]) >>
  `op_taint pft1 size_op = {}` by
    (qpat_assum `op_taint et3 size_op = {}` mp_tac >>
     qpat_assum `size_op = Var ev2` mp_tac >>
     qpat_assum `!x. not_fresh_at loop_end x ==> x <> pv0 /\ _` mp_tac >>
     qpat_assum `!x. pp = Var x \/ size_op = Var x ==> not_fresh_at loop_end x` mp_tac >>
     simp_tac bool_ss [Abbr `pft1`, Abbr `pf1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[] >> `ev2 <> pv0` by metis_tac[] >>
     asm_simp_tac (srw_ss()) [step_taint_other_output, mk_inst_def]) >>
  `op_taint pft2 parent_next = {} /\ pft2.t_mem = pft1.t_mem` by
    (qpat_assum `op_taint pft1 parent_old = {}` mp_tac >>
     qpat_assum `op_taint pft1 size_op = {}` mp_tac >>
     qpat_assum `eval_operand parent_old parent_load = SOME 0w` mp_tac >>
     qpat_assum `eval_operand size_op parent_load = SOME _` mp_tac >>
     qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `parent_next = Var pv1` mp_tac >>
     simp_tac bool_ss [Abbr `pft2`, Abbr `pf2`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[step_taint_def, set_var_taint_def, out_taint_def,
       mem_taint_def, new_site_bytes_def, update_var_def, step_writes_def,
       mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, range_bytes_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]) >>
  `pfg3 = pfg2 /\ pft3.t_var = pft2.t_var /\
   pft3.t_mem = pft2.t_mem DIFF {i | b <= i /\ i < b+32}` by
    (qpat_assum `pp = Var _` mp_tac >>
     qpat_assum `eval_operand pp parent_add = SOME (n2w b)` mp_tac >>
     qpat_assum `eval_operand parent_next parent_add = SOME _` mp_tac >>
     qpat_assum `op_taint pft2 parent_next = {}` mp_tac >>
     qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     simp_tac bool_ss [Abbr `pfg3`, Abbr `pft3`, Abbr `pf3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
     fs[eval_operand_def] >>
     drule_all wordLoadStorePtrTheory.mstore_ghost_frame >>
     asm_simp_tac (srw_ss()) [w2n_n2w, LESS_MOD, Excl "enc_def"] >> metis_tac[]) >>
  `!i. b <= i /\ i < b+32 ==> i NOTIN pft3.t_mem` by
    (qpat_assum `pft3.t_mem = pft2.t_mem DIFF _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[IN_DIFF, GSPECIFICATION]) >>
  `op_taint pft4 out = {} /\ pft4.t_mem = pft3.t_mem` by
    (qpat_assum `!i. b <= i /\ i < b+32 ==> i NOTIN pft3.t_mem` mp_tac >>
     qpat_assum `eval_operand pp parent_store = SOME (n2w b)` mp_tac >>
     qpat_assum `mload b parent_store = _` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     qpat_assum `finish_raw = update_var pv2 _ parent_store` mp_tac >>
     qpat_assum `out = Var pv2` mp_tac >>
     simp_tac bool_ss [Abbr `pft4`, Abbr `pf4`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `eval_operand pp parent_store = SOME (n2w b)`
       (mp_then Any mp_tac wordLoadStorePtrTheory.mload_ghost_clean) >>
     simp_tac (srw_ss()) [w2n_n2w, LESS_MOD] >>
     disch_then (qspecl_then [`pft3`, `parent_c3.cs_next_id`, `pv2`] mp_tac) >> simp[]) >>
  `pft4.t_mem = et3.t_mem DIFF {i | b <= i /\ i < b+32} /\
   pft4.t_stor = et3.t_stor /\ pft4.t_trans = et3.t_trans /\
   pft4.t_imm = et3.t_imm` by
    (qpat_assum `pft4.t_mem = pft3.t_mem` mp_tac >>
     qpat_assum `pft3.t_mem = pft2.t_mem DIFF _` mp_tac >>
     qpat_assum `pft2.t_mem = pft1.t_mem` mp_tac >>
     qpat_assum `pft1.t_mem = et3.t_mem` mp_tac >>
     simp_tac bool_ss [Abbr `pft4`, Abbr `pft3`, Abbr `pft2`, Abbr `pft1`,
       Abbr `pf1`, Abbr `pf2`, Abbr `pf3`, Abbr `pf4`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[step_taint_nonmemory_frame, mk_inst_def]) >>
  `!x. not_fresh_at loop_end x ==>
    FLOOKUP pfg4 x = FLOOKUP eg3 x /\
    op_taint pft4 (Var x) = op_taint et3 (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at loop_end x ==> x <> pv0 /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at loop_end x` mp_tac >>
     simp_tac bool_ss [Abbr `pfg4`, Abbr `pfg3`, Abbr `pfg2`, Abbr `pfg1`,
       Abbr `pft4`, Abbr `pft3`, Abbr `pft2`, Abbr `pft1`,
       Abbr `pf1`, Abbr `pf2`, Abbr `pf3`, Abbr `pf4`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     asm_simp_tac (srw_ss()) [step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  `allocas_from lo scalar_s /\ lo <= scalar_s.vs_alloca_next` by
    (qpat_assum `allocas_from lo exit_s` mp_tac >>
     qpat_assum `lo <= exit_s.vs_alloca_next` mp_tac >>
     qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     simp_tac bool_ss [Abbr `scalar_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowSequenceTheory.window_pure_seq_def, allocas_from_def]) >>
  `!root span. not_fresh_at exit_st root /\
    ptr_covers exitG exittn root exit_s span ==>
    ptr_covers eg3 et3 root scalar_s span` by
    (qx_genl_tac [`root`, `span`] >> strip_tac >>
     qpat_assum `!x. not_fresh_at exit_st x ==> FLOOKUP eg3 x = _ /\ _` mp_tac >>
     qpat_assum `window_phase ctx func exit_st loop_end {} [] exit_s scalar_s` mp_tac >>
     qpat_assum `not_fresh_at exit_st root` mp_tac >>
     qpat_assum `ptr_covers exitG exittn root exit_s span` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [ptr_covers_def] >>
     metis_tac[window_phase_vars]) >>
  `?ppq. pp = Var ppq /\ ptr_covers eg3 et3 ppq scalar_s 32` by
    (qpat_assum `!root span. not_fresh_at exit_st root /\
       ptr_covers exitG exittn root exit_s span ==> _` mp_tac >>
     qpat_assum `window_array_cursor T owner pp _ _ _ _ _ _ _ exit_s` mp_tac >>
     qpat_assum `owner.cs_next_var <= exit_st.cs_next_var` mp_tac >>
     rpt (qpat_x_assum `ptr_covers exitG exittn _ exit_s 32` mp_tac) >>
     rpt (qpat_x_assum `pp = Var _` mp_tac) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [window_array_cursor_def] >> rpt strip_tac >>
     metis_tac[not_fresh_at_mono]) >>
  `b+32 <= scalar_s.vs_alloca_next` by
    (qpat_assum `alloca_inv scalar_s` mp_tac >>
     qpat_assum `FLOOKUP scalar_s.vs_allocas st.cs_next_id = SOME (b,32)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `!j. step_inst_base pf1 (scalar_s with vs_inst_idx := j) =
      OK (parent_load with vs_inst_idx := j) /\
    step_inst_base pf2 (parent_load with vs_inst_idx := j) =
      OK (parent_add with vs_inst_idx := j) /\
    step_inst_base pf3 (parent_add with vs_inst_idx := j) =
      OK (parent_store with vs_inst_idx := j) /\
    step_inst_base pf4 (parent_store with vs_inst_idx := j) =
      OK (finish_raw with vs_inst_idx := j)` by
    (qpat_assum `step_inst_base pf1 scalar_s = OK parent_load` mp_tac >>
     qpat_assum `step_inst_base pf2 parent_load = OK parent_add` mp_tac >>
     qpat_assum `step_inst_base pf3 parent_add = OK parent_store` mp_tac >>
     qpat_assum `step_inst_base pf4 parent_store = OK finish_raw` mp_tac >>
     simp_tac bool_ss [Abbr `pf1`, Abbr `pf2`, Abbr `pf3`, Abbr `pf4`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     asm_simp_tac (srw_ss()) [instIdxIndepTheory.step_inst_inst_idx_indep,
       instIdxIndepTheory.exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  `!x span. not_fresh_at loop_end x /\ ptr_covers eg3 et3 x scalar_s span ==>
    ptr_covers pfg1 pft1 x parent_load span /\
    ptr_covers pfg2 pft2 x parent_add span /\
    ptr_covers pfg3 pft3 x parent_store span` by
    (qx_genl_tac [`x`, `span`] >> strip_tac >>
     qpat_assum `!x. not_fresh_at loop_end x ==> x <> pv0 /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `not_fresh_at loop_end x` mp_tac >>
     qpat_assum `ptr_covers eg3 et3 x scalar_s span` mp_tac >>
     qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
     simp_tac bool_ss [Abbr `pfg3`, Abbr `pfg2`, Abbr `pfg1`,
       Abbr `pft3`, Abbr `pft2`, Abbr `pft1`, Abbr `pf1`, Abbr `pf2`, Abbr `pf3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[ptr_covers_def, step_prov_other_output,
       step_taint_other_output, mk_inst_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, mstore_def, write_memory_with_expansion_def]) >>
  `ptr_covers pfg1 pft1 ppq parent_load 32 /\
   ptr_covers pfg2 pft2 ppq parent_add 32 /\
   ptr_covers pfg3 pft3 ppq parent_store 32` by
    (qpat_assum `!x span. not_fresh_at loop_end x /\ ptr_covers eg3 et3 x scalar_s span ==> _`
       (qspecl_then [`ppq`, `32`] mp_tac) >>
     qpat_assum `ptr_covers eg3 et3 ppq scalar_s 32` mp_tac >>
     qpat_assum `pp = Var ppq` mp_tac >>
     qpat_assum `!x. pp = Var x \/ size_op = Var x ==> not_fresh_at loop_end x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `allocas_from lo parent_load /\ allocas_from lo parent_add /\
   allocas_from lo parent_store` by
    (qpat_assum `allocas_from lo scalar_s` mp_tac >>
     qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[allocas_from_def, update_var_def, mstore_def,
       write_memory_with_expansion_def] >> first_assum ACCEPT_TAC) >>
  `!D j. ptr_inst_ok D lo 0 ctx func eg3 et3 pf1
    (scalar_s with vs_inst_idx := j)` by
    (rpt gen_tac >>
     qpat_assum `pp = Var ppq` mp_tac >>
     qpat_assum `ptr_covers eg3 et3 ppq scalar_s 32` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `allocas_from lo scalar_s` mp_tac >>
     simp_tac bool_ss [Abbr `pf1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
     irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     qexists_tac `0` >> asm_simp_tac (srw_ss()) [allocas_from_def] >>
     irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[]) >>
  `!D j. ptr_inst_ok D lo 0 ctx func pfg2 pft2 pf3
    (parent_add with vs_inst_idx := j)` by
    (rpt gen_tac >>
     qpat_assum `pp = Var ppq` mp_tac >>
     qpat_assum `ptr_covers pfg2 pft2 ppq parent_add 32` mp_tac >>
     qpat_assum `op_taint pft2 parent_next = {}` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `allocas_from lo parent_add` mp_tac >>
     simp_tac bool_ss [Abbr `pf3`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
     irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     qexists_tac `0` >> asm_simp_tac (srw_ss()) [allocas_from_def] >>
     irule ptr_inst_ok_mstore >> simp[]) >>
  `!D j. ptr_inst_ok D lo 0 ctx func pfg3 pft3 pf4
    (parent_store with vs_inst_idx := j)` by
    (rpt gen_tac >>
     qpat_assum `pp = Var ppq` mp_tac >>
     qpat_assum `ptr_covers pfg3 pft3 ppq parent_store 32` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `allocas_from lo parent_store` mp_tac >>
     simp_tac bool_ss [Abbr `pf4`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
     irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
     qexists_tac `0` >> asm_simp_tac (srw_ss()) [allocas_from_def] >>
     irule wordLoadStorePtrTheory.ptr_inst_ok_mload >> simp[]) >>
  `!D j. ptr_inst_ok D lo 0 ctx func pfg1 pft1 pf2
    (parent_load with vs_inst_idx := j)` by
    (rpt gen_tac >>
     qpat_assum `op_taint pft1 parent_old = {}` mp_tac >>
     qpat_assum `op_taint pft1 size_op = {}` mp_tac >>
     qpat_assum `allocas_from lo parent_add` mp_tac >>
     qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `~ctx_has_dalloca ctx` mp_tac >>
     qpat_assum `!j. step_inst_base pf1 _ = _ /\ _` mp_tac >>
     qpat_assum `Abbrev (pf2 = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `step_inst 0 ctx pf2 (parent_load with vs_inst_idx := j) =
       OK (parent_add with vs_inst_idx := j)` by
       (asm_simp_tac (srw_ss()) [step_inst_non_invoke, Abbr `pf2`, mk_inst_def]) >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, access_ok_def, taint_ok_def,
       Abbr `pf2`, mk_inst_def, codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def] >>
     conj_tac
     >- (gen_tac >> Cases_on `op = parent_old` >> fs[] >>
         Cases_on `op = size_op` >> fs[]) >>
     gvs[allocas_from_def, update_var_def, Excl "enc_def"] >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `finish_s = finish_raw with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `finish_raw.vs_allocas = scalar_s.vs_allocas /\
   finish_raw.vs_alloca_next = scalar_s.vs_alloca_next /\
   finish_raw.vs_halted = scalar_s.vs_halted /\
   finish_raw.vs_current_bb = scalar_s.vs_current_bb` by
    (qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
     qpat_assum `finish_raw = update_var pv2 _ parent_store` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] scalar_s finish_raw` by
    (`abi_encoder_registered_effect {st.cs_next_id} [] scalar_s finish_mid` by
       (irule abiEncoderWindowSequenceTheory.window_pure_seq_registered_effect >>
        goal_assum (drule_at Any)) >>
     `abi_encoder_registered_effect {st.cs_next_id} [] finish_mid
       (mstore b (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) finish_mid)` by
       (irule abiEncoderPrimitiveEffectTheory.abi_encoder_registered_slot_store >>
        qpat_assum `window_pure_seq loop_end finish_before scalar_s finish_mid` mp_tac >>
        qpat_assum `FLOOKUP scalar_s.vs_allocas st.cs_next_id = SOME (b,32)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[abiEncoderWindowSequenceTheory.window_pure_seq_def]) >>
     `abi_encoder_registered_effect {st.cs_next_id} []
       (mstore b (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) finish_mid) finish_raw` by
       (irule abiEncoderWindowSequenceTheory.window_pure_seq_registered_effect >>
        goal_assum (drule_at Any)) >>
     qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] scalar_s finish_mid` mp_tac >>
     qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] finish_mid _` mp_tac >>
     qpat_assum `abi_encoder_registered_effect {st.cs_next_id} [] _ finish_raw` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[abi_encoder_registered_effect_trans]) >>
  `window_alloca_growth scalar_s finish_raw` by
    (irule window_alloca_growth_fields >> asm_rewrite_tac[]) >>
  `alloca_inv finish_raw /\ alloca_room ctx func finish_raw` by
    (qpat_assum `alloca_inv scalar_s` mp_tac >>
     qpat_assum `alloca_room ctx func scalar_s` mp_tac >>
     qpat_assum `finish_raw.vs_allocas = scalar_s.vs_allocas` mp_tac >>
     qpat_assum `finish_raw.vs_alloca_next = scalar_s.vs_alloca_next` mp_tac >>
     qpat_assum `parent_load = update_var pv0 0w scalar_s` mp_tac >>
     qpat_assum `parent_add = update_var pv1 _ parent_load` mp_tac >>
     qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
     qpat_assum `finish_raw = update_var pv2 _ parent_store` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[alloca_inv_def, alloca_next_valid_def, allocas_non_overlapping_def,
       alloca_room_def, pending_alloca_size_def, update_var_def, mstore_def,
       write_memory_with_expansion_def, Excl "enc_def"] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `window_phase ctx func loop_end en {st.cs_next_id} [] scalar_s finish_s` by
    (simp_tac bool_ss [Abbr `finish_s`] >> irule window_seq_phase >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `run_inst_seq_mem_ok [pf1;pf2;pf3;pf4] scalar_s` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`step_inst_base pf1 scalar_s = OK parent_load`,
        `step_inst_base pf2 parent_load = OK parent_add`,
        `step_inst_base pf3 parent_add = OK parent_store`,
        `step_inst_base pf4 parent_store = OK finish_raw`,
        `eval_operand pp scalar_s = SOME (n2w b)`,
        `eval_operand pp parent_add = SOME (n2w b)`,
        `eval_operand pp parent_store = SOME (n2w b)`,
        `eval_operand parent_next parent_add = SOME _`,
        `b < dimword (:256)`, `b+32 <= scalar_s.vs_alloca_next`,
        `parent_load = update_var pv0 0w scalar_s`,
        `parent_add = update_var pv1 _ parent_load`,
        `parent_store = mstore b _ parent_add`,
        `Abbrev (pf1 = _)`, `Abbrev (pf2 = _)`,
        `Abbrev (pf3 = _)`, `Abbrev (pf4 = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     pure_rewrite_tac[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
     map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
       [`step_inst_base pf1 scalar_s = OK parent_load`,
        `step_inst_base pf2 parent_load = OK parent_add`,
        `step_inst_base pf3 parent_add = OK parent_store`,
        `step_inst_base pf4 parent_store = OK finish_raw`] >>
     simp[NoAsms] >>
     gvs[unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       Abbr `pf1`, Abbr `pf2`, Abbr `pf3`, Abbr `pf4`, mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       update_var_def, mstore_def, write_memory_with_expansion_def,
       w2n_n2w, LESS_MOD]) >>
  `!D. inst_seq_ptr D lo ctx func PG eg3 et3
    [pf1;pf2;pf3;pf4] scalar_s pfg4 pft4` by
    (gen_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`!D j. ptr_inst_ok D lo 0 ctx func eg3 et3 pf1 _`,
        `!D j. ptr_inst_ok D lo 0 ctx func pfg1 pft1 pf2 _`,
        `!D j. ptr_inst_ok D lo 0 ctx func pfg2 pft2 pf3 _`,
        `!D j. ptr_inst_ok D lo 0 ctx func pfg3 pft3 pf4 _`,
        `step_inst_base pf1 scalar_s = OK parent_load`,
        `!j. step_inst_base pf1 _ = _ /\ _`,
        `Abbrev (pfg1 = _)`, `Abbrev (pft1 = _)`,
        `Abbrev (pfg2 = _)`, `Abbrev (pft2 = _)`,
        `Abbrev (pfg3 = _)`, `Abbrev (pft3 = _)`,
        `Abbrev (pfg4 = _)`, `Abbrev (pft4 = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     pure_rewrite_tac[inst_seq_ptr_def] >>
     qpat_assum `step_inst_base pf1 scalar_s = OK parent_load`
       (fn th => pure_rewrite_tac[th]) >> simp[NoAsms] >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (pfg1 = _)`, `Abbrev (pft1 = _)`] >>
     qpat_assum `!j. step_inst_base pf1 _ = _ /\ _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (pfg2 = _)`, `Abbrev (pft2 = _)`] >>
     qpat_assum `!j. step_inst_base pf1 _ = _ /\ _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (pfg3 = _)`, `Abbrev (pft3 = _)`] >>
     qpat_assum `!j. step_inst_base pf1 _ = _ /\ _`
       (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, step_prov_inst_idx, step_taint_inst_idx_left,
       step_taint_inst_idx_right] >>
     map_every (fn q => qpat_assum q (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]))
       [`Abbrev (pfg4 = _)`, `Abbrev (pft4 = _)`] >>
     simp[NoAsms] >> conj_tac
     >- (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func eg3 et3 pf1 _`
           (qspecl_then [`D`, `scalar_s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
     conj_tac
     >- (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func pfg1 pft1 pf2 _`
           (qspecl_then [`D`, `SUC scalar_s.vs_inst_idx`] mp_tac) >> simp[NoAsms]) >>
     conj_tac
     >- (qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func pfg2 pft2 pf3 _`
           (qspecl_then [`D`, `SUC (SUC scalar_s.vs_inst_idx)`] mp_tac) >> simp[NoAsms]) >>
     qpat_assum `!D j. ptr_inst_ok D lo 0 ctx func pfg3 pft3 pf4 _`
       (qspecl_then [`D`, `SUC (SUC (SUC scalar_s.vs_inst_idx))`] mp_tac) >> simp[NoAsms]) >>
  `en.cs_current_insts = loop_end.cs_current_insts ++ [pf1;pf2;pf3;pf4] /\
   en.cs_current_bb = loop_end.cs_current_bb` by
    (qpat_assum `window_seq loop_end en scalar_s finish_raw` mp_tac >>
     qpat_assum `emitted_insts loop_end en = [pf1;pf2;pf3;pf4]` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abiEncoderWindowSequenceTheory.window_seq_def,
       emitted_insts_def, inst_extends_def] >> rpt strip_tac >> metis_tac[]) >>
  `?parent_bb. lookup_block scalar_s.vs_current_bb func.fn_blocks = SOME parent_bb /\
    isPREFIX [pf1;pf2;pf3;pf4]
      (DROP scalar_s.vs_inst_idx parent_bb.bb_instructions)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code loop_end en func`, `en.cs_current_insts = _`,
        `en.cs_current_bb = _`, `scalar_s.vs_current_bb = loop_end.cs_current_bb`,
        `scalar_s.vs_inst_idx = LENGTH loop_end.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND] >>
     qexists_tac `bb` >> qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
     asm_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (scalar_s,eg3,et3) [] (OK finish_s,pfg4,pft4)` by
    (gen_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`lookup_block scalar_s.vs_current_bb func.fn_blocks = SOME parent_bb`,
        `isPREFIX [pf1;pf2;pf3;pf4] _`, `~scalar_s.vs_halted`,
        `window_seq loop_end en scalar_s finish_raw`,
        `emitted_insts loop_end en = [pf1;pf2;pf3;pf4]`,
        `run_inst_seq_mem_ok [pf1;pf2;pf3;pf4] scalar_s`,
        `!D. inst_seq_ptr D lo ctx func PG eg3 et3 _ _ pfg4 pft4`,
        `scalar_s.vs_inst_idx = LENGTH loop_end.cs_current_insts`,
        `en.cs_current_insts = loop_end.cs_current_insts ++ [pf1;pf2;pf3;pf4]`,
        `Abbrev (pf1 = _)`, `Abbrev (pf2 = _)`,
        `Abbrev (pf3 = _)`, `Abbrev (pf4 = _)`, `Abbrev (finish_s = _)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `run_inst_seq [pf1;pf2;pf3;pf4] scalar_s = OK finish_raw` by
       (fs[abiEncoderWindowSequenceTheory.window_seq_def] >> metis_tac[]) >>
     `inst_seq_ptr D lo ctx func PG eg3 et3 [pf1;pf2;pf3;pf4] scalar_s pfg4 pft4` by
       metis_tac[] >>
     mp_tac (Q.SPECL [`[pf1;pf2;pf3;pf4]`, `scalar_s`, `finish_raw`,
       `eg3`, `et3`, `pfg4`, `pft4`, `ctx`, `func`, `parent_bb`]
       run_inst_seq_gas_origin_ptr_path) >>
     fs[Abbr `pf1`, Abbr `pf2`, Abbr `pf3`, Abbr `pf4`, Abbr `finish_s`,
       mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK finish_s,pfg4,pft4)` by
    (gen_tac >>
     map_every (fn q => qpat_assum q (qspec_then `D` mp_tac))
       [`!D. gas_origin_ptr_path _ (s,G,tn) [] (OK exit_s,exitG,exittn)`,
        `!D. gas_origin_ptr_path _ (exit_s,exitG,exittn) [] (OK scalar_s,eg3,et3)`,
        `!D. gas_origin_ptr_path _ (scalar_s,eg3,et3) [] (OK finish_s,pfg4,pft4)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `scalar_s.vs_memory = exit_s.vs_memory /\
   scalar_s.vs_allocas = exit_s.vs_allocas /\
   scalar_s.vs_alloca_next = exit_s.vs_alloca_next` by
    (qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     simp_tac bool_ss [Abbr `scalar_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[abiEncoderWindowSequenceTheory.window_pure_seq_def]) >>
  `abi_encode_exec_frame func exit_s finish_s` by
    (`abi_encode_exec_frame func parent_add parent_store` by
       (qpat_assum `parent_store = mstore b _ parent_add` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[abi_encode_exec_frame_mstore]) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`abi_encode_exec_frame func parent_add parent_store`,
        `exit_load = update_var ev0 _ exit_s`,
        `exit_mid = update_var ev1 _ exit_load`,
        `scalar_raw = update_var ev2 _ exit_mid`,
        `parent_load = update_var pv0 0w scalar_s`,
        `parent_add = update_var pv1 _ parent_load`,
        `finish_raw = update_var pv2 _ parent_store`] >>
     simp_tac bool_ss [Abbr `scalar_s`, Abbr `finish_s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[abi_encode_exec_frame_def, update_var_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_def]) >>
  `abi_encode_exec_frame func s finish_s` by
    (qpat_assum `abi_encode_exec_frame func s exit_s` mp_tac >>
     qpat_assum `abi_encode_exec_frame func exit_s finish_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_encode_exec_frame_trans]) >>
  `finish_s.vs_allocas = loop_s.vs_allocas /\
   FLOOKUP finish_s.vs_allocas st.cs_next_id = SOME (b,32)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`finish_raw.vs_allocas = scalar_s.vs_allocas`,
        `scalar_s.vs_allocas = exit_s.vs_allocas`,
        `exit_s.vs_allocas = loop_s.vs_allocas`,
        `FLOOKUP scalar_s.vs_allocas st.cs_next_id = SOME (b,32)`] >>
     simp_tac bool_ss [Abbr `finish_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[]) >>
  `st.cs_next_var <= owner.cs_next_var` by
    (qpat_assum `loop_st.cs_next_var = st.cs_next_var+2` mp_tac >>
     qpat_assum `owner.cs_next_var = loop_st.cs_next_var+(if active then 3 else 1)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >> simp[]) >>
  `!x. not_fresh_at st x ==>
    FLOOKUP pfg4 x = FLOOKUP G x /\
    op_taint pft4 (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     map_every (fn q => qpat_assum q mp_tac)
       [`!x. not_fresh_at st x ==> FLOOKUP loopG x = _ /\ _`,
        `!x. not_fresh_at owner x ==> FLOOKUP exitG x = _ /\ _`,
        `!x. not_fresh_at exit_st x ==> FLOOKUP eg3 x = _ /\ _`,
        `!x. not_fresh_at loop_end x ==> FLOOKUP pfg4 x = _ /\ _`,
        `not_fresh_at st x`, `owner.cs_next_var <= exit_st.cs_next_var`,
        `window_pure_seq exit_st loop_end exit_s scalar_raw`,
        `abi_encode_array_prefix src dst st = ((pp,count_op),loop_st)`,
        `abi_decode_index_init loop_st = (ip,index_en)`] >>
     qpat_assum `st.cs_next_var <= owner.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[abiEncoderWindowSequenceTheory.window_pure_seq_def,
       abiEncoderWindowSequenceTheory.window_seq_def, inst_extends_def] >>
     metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `pft4.t_stor = tn.t_stor /\ pft4.t_trans = tn.t_trans /\
   pft4.t_imm = tn.t_imm` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`pft4.t_stor = et3.t_stor`, `pft4.t_trans = et3.t_trans`,
        `pft4.t_imm = et3.t_imm`, `et3.t_stor = exittn.t_stor`,
        `et3.t_trans = exittn.t_trans`, `et3.t_imm = exittn.t_imm`,
        `exittn.t_stor = looptn.t_stor`, `exittn.t_trans = looptn.t_trans`,
        `exittn.t_imm = looptn.t_imm`, `looptn.t_stor = tn.t_stor`,
        `looptn.t_trans = tn.t_trans`, `looptn.t_imm = tn.t_imm`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `LENGTH (enc (Array NONE ty) (ListV avs)) =
    32+LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) avs)` by
    (irule window_array_layout >> goal_assum (drule_at Any)) >>
  `!i. d <= i /\ i < d+LENGTH (enc (Array NONE ty) (ListV avs)) ==>
    i NOTIN pft4.t_mem` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`!i. d <= i /\ i < d+32+LENGTH avs*abi_member_head_size ty ==> i NOTIN looptn.t_mem`,
        `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\ _ ==> i NOTIN looptn.t_mem`,
        `LENGTH (enc (Array NONE ty) (ListV avs)) = _`,
        `pft4.t_mem = et3.t_mem DIFF _`, `et3.t_mem = exittn.t_mem`,
        `exittn.t_mem = looptn.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `i NOTIN looptn.t_mem` by
       (Cases_on `i < d+32+LENGTH avs*abi_member_head_size ty`
        >- (qpat_assum `!i. d <= i /\ _ ==> i NOTIN looptn.t_mem` irule >>
            decide_tac) >>
        qpat_assum `!i. d+32+LENGTH avs*abi_member_head_size ty <= i /\ _ ==> _` irule >>
        fs[TAKE_LENGTH_ID, Excl "enc_def"] >> decide_tac) >>
     gvs[IN_DIFF, Excl "enc_def"]) >>
  `!i. (i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i) /\
    (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
      FLOOKUP finish_s.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
    (i IN pft4.t_mem <=> i IN tn.t_mem)` by
    (qx_gen_tac `i` >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`!i. _ ==> (i IN looptn.t_mem <=> i IN tn.t_mem)`,
        `pft4.t_mem = et3.t_mem DIFF _`, `et3.t_mem = exittn.t_mem`,
        `exittn.t_mem = looptn.t_mem`, `finish_s.vs_allocas = loop_s.vs_allocas`,
        `FLOOKUP finish_s.vs_allocas st.cs_next_id = SOME (b,32)`,
        `st.cs_next_id IN window_alloca_sites func (frag_ids st en)`,
        `!id b sz. _ ==> i < b \/ b+sz <= i`,
        `i < d \/ d+LENGTH (enc (Array NONE ty) (ListV avs)) <= i`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `i < b \/ b+32 <= i` by metis_tac[] >>
     `~(b <= i /\ i < b+32)` by decide_tac >>
     asm_simp_tac (srw_ss()) [IN_DIFF, GSPECIFICATION] >> metis_tac[]) >>
  `window_array_transition ctx func loop_end {st.cs_next_id} [] scalar_s finish_s` by
    (qpat_assum `window_phase ctx func loop_end en {st.cs_next_id} [] scalar_s finish_s`
       (mp_then Any irule window_array_phase_transition) >>
     qpat_assum `finish_raw.vs_allocas = scalar_s.vs_allocas` mp_tac >>
     simp_tac bool_ss [Abbr `finish_s`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[window_sizes32_def]) >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) exit_s.vs_memory =
    enc (Array NONE ty) (ListV avs)` by
    (irule window_array_prefix_complete >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) finish_s.vs_memory =
    enc (Array NONE ty) (ListV avs)` by
    (`mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) finish_s.vs_memory =
      mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) scalar_s.vs_memory` by
       (`abi_encoder_registered_effect {st.cs_next_id} [] scalar_s finish_s` by
           (qpat_assum `window_array_transition ctx func loop_end {st.cs_next_id} [] scalar_s finish_s`
              (mp_then Any ACCEPT_TAC window_array_transition_effect)) >>
        `regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,32)` by
          (qpat_assum `window_array_cursor T owner pp st.cs_next_id b _ _ _ _ _ scalar_s` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> simp[window_array_cursor_def]) >>
        map_every (fn q => qpat_assum q mp_tac)
          [`abi_encoder_registered_effect {st.cs_next_id} [] scalar_s finish_s`,
           `FLOOKUP finish_s.vs_allocas st.cs_next_id = SOME (b,32)`,
           `regions_disjoint (d,LENGTH (enc (Array NONE ty) (ListV avs))) (b,32)`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        mp_tac (Q.INST [`ids` |-> `{st.cs_next_id}`, `outs` |-> `([]:(num # num) list)`,
          `s` |-> `scalar_s`, `t` |-> `finish_s`, `p` |-> `d`,
          `n` |-> `LENGTH (enc (Array NONE ty) (ListV avs))`]
          (SPEC_ALL abi_encoder_window_effect_bytes)) >>
        impl_tac
        >- (asm_rewrite_tac[] >> simp[EVERY_DEF, IN_SING, Excl "enc_def"] >>
            rpt strip_tac >> gvs[Excl "enc_def"]) >> simp[]) >>
     qpat_assum `mem_bytes_at d _ exit_s.vs_memory = _` mp_tac >>
     qpat_assum `scalar_s.vs_memory = exit_s.vs_memory` mp_tac >>
     qpat_assum `mem_bytes_at d _ finish_s.vs_memory = mem_bytes_at d _ scalar_s.vs_memory` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `!later narrow outs u v.
    window_array_transition ctx func later narrow outs u v /\
    st.cs_next_var <= later.cs_next_var /\
    narrow SUBSET window_alloca_sites func (frag_ids st en) /\
    EVERY (\(base,len). d <= base /\ base+len <= d+LENGTH (enc (Array NONE ty) (ListV avs))) outs ==>
    window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] u v` by
    (rpt strip_tac >> irule window_array_transition_owner_weaken >>
     qexists_tac `later` >> conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >>
         qexists_tac `st` >> asm_rewrite_tac[]) >>
     irule window_array_transition_region >>
     goal_assum (drule_at Any) >> qexists_tac `narrow` >> asm_rewrite_tac[]) >>
  `st.cs_next_var <= loop_st.cs_next_var /\
   st.cs_next_var <= index_en.cs_next_var /\
   st.cs_next_var <= loop_end.cs_next_var` by
    (qpat_assum `loop_st.cs_next_var = st.cs_next_var+2` mp_tac >>
     qpat_assum `index_en.cs_next_var = loop_st.cs_next_var+1` mp_tac >>
     qpat_assum `st.cs_next_var <= owner.cs_next_var` mp_tac >>
     qpat_assum `owner.cs_next_var <= exit_st.cs_next_var` mp_tac >>
     qpat_assum `window_pure_seq exit_st loop_end exit_s scalar_raw` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abiEncoderWindowSequenceTheory.window_pure_seq_def,
       abiEncoderWindowSequenceTheory.window_seq_def, inst_extends_def] >>
     rpt strip_tac >> decide_tac) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s prefix_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`st`, `{st.cs_next_id}`, `[(d,32)]`] >>
     asm_rewrite_tac[] >>
     qpat_assum `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[SUBSET_DEF]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] prefix_s index_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`loop_st`, `{loop_st.cs_next_id}`, `[]`] >>
     asm_rewrite_tac[] >>
     qpat_assum `loop_st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[SUBSET_DEF]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] index_s init_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`index_en`, `if active then {index_en.cs_next_id} else {}`, `[]`] >>
     asm_rewrite_tac[] >>
     qpat_assum `active ==> index_en.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     qpat_assum `index_en.cs_next_id = loop_st.cs_next_id+2` mp_tac >>
     qpat_assum `loop_st.cs_next_id = st.cs_next_id+4` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `active` >> rpt strip_tac >> gvs[SUBSET_DEF]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))]
    init_s (jump_to (FST labels) init_s)` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`owner`, `{}`, `[]`] >> asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))]
    (jump_to (FST labels) init_s) loop_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`owner`, `window_alloca_sites func (frag_ids st en)`,
       `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`] >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] loop_s exit_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`owner`, `window_alloca_sites func (frag_ids st en)`,
       `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`] >>
     asm_rewrite_tac[] >> POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] exit_s scalar_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`owner`, `{}`, `[]`] >> asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] scalar_s finish_s` by
    (qpat_assum `!later narrow outs u v. _` irule >>
     qexistsl_tac [`loop_end`, `{st.cs_next_id}`, `[]`] >>
     asm_rewrite_tac[] >>
     qpat_assum `st.cs_next_id IN window_alloca_sites func (frag_ids st en)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[SUBSET_DEF]) >>
  `window_array_transition ctx func st (window_alloca_sites func (frag_ids st en))
    [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s finish_s` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`window_array_transition ctx func st _ _ s prefix_s`,
        `window_array_transition ctx func st _ _ prefix_s index_s`,
        `window_array_transition ctx func st _ _ index_s init_s`,
        `window_array_transition ctx func st _ _ init_s (jump_to (FST labels) init_s)`,
        `window_array_transition ctx func st _ _ (jump_to (FST labels) init_s) loop_s`,
        `window_array_transition ctx func st _ _ loop_s exit_s`,
        `window_array_transition ctx func st _ _ exit_s scalar_s`,
        `window_array_transition ctx func st _ _ scalar_s finish_s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule window_array_transition_trans >> qexists_tac `prefix_s` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `index_s` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `init_s` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `jump_to (FST labels) init_s` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `loop_s` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `exit_s` >> asm_rewrite_tac[] >>
     irule window_array_transition_trans >> qexists_tac `scalar_s` >> asm_rewrite_tac[]) >>
  `window_sizes32 (window_alloca_sites func (frag_ids st en)) finish_s` by
    (irule window_array_transition_sizes >> goal_assum (drule_at Any) >>
     qpat_assum `window_array_root ctx func st _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[window_array_root_def]) >>
  `window_strong_result ctx func st en out (Array NONE ty) (ListV avs) d s finish_s` by
    (`eval_operand out finish_s = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs))))` by
       (qpat_assum `eval_operand out finish_raw = SOME _` mp_tac >>
        simp_tac bool_ss [Abbr `finish_s`, eval_operand_inst_idx]) >>
     `abi_encoder_registered_effect (frag_ids st en)
       [(d,LENGTH (enc (Array NONE ty) (ListV avs)))] s finish_s` by
       (qpat_assum `window_array_transition ctx func st _ _ s finish_s` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
        irule abi_encoder_registered_effect_enlarge >>
        qexistsl_tac [`window_alloca_sites func (frag_ids st en)`,
          `[(d,LENGTH (enc (Array NONE ty) (ListV avs)))]`] >>
        simp[window_alloca_sites_subset, Excl "enc_def"] >>
        irule window_array_transition_effect >>
        qexistsl_tac [`ctx`, `func`, `st`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `window_array_transition ctx func st _ _ s finish_s` mp_tac >>
     qpat_assum `window_sizes32 _ finish_s` mp_tac >>
     qpat_assum `window_phase ctx func loop_end en _ _ scalar_s finish_s` mp_tac >>
     qpat_assum `eval_operand out finish_s = SOME _` mp_tac >>
     qpat_assum `mem_bytes_at d _ finish_s.vs_memory = _` mp_tac >>
     qpat_assum `abi_encoder_registered_effect (frag_ids st en) _ s finish_s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     qpat_assum `window_array_transition ctx func st _ _ s finish_s`
       (strip_assume_tac o PURE_REWRITE_RULE [window_array_transition_def]) >>
     qpat_assum `window_phase ctx func loop_end en _ _ scalar_s finish_s`
       (strip_assume_tac o PURE_REWRITE_RULE [window_phase_def]) >>
     qpat_assum `window_sizes32 _ finish_s`
       (assume_tac o PURE_REWRITE_RULE [window_sizes32_def]) >>
     pure_rewrite_tac[window_strong_result_def, abi_encoder_window_result_def] >>
     asm_rewrite_tac[] >>
     metis_tac[abiEncoderExtendSimTheory.abi_encoder_extend_sim_sim]) >>
  qexistsl_tac [`finish_s`, `pfg4`, `pft4`] >> asm_rewrite_tac[]
QED
