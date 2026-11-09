(* Universal owned execution, assembled over coherence rather than source types. *)
Theory calldataRecursiveExecution
Ancestors
  valueEncodingDefs calldataRecursiveProducers calldataFiniteTyped calldataAggregateTyped
  abiDecoderCoherence compileEnv abiDecoderAppend fragExec
  abiDecoderMemberInfos valueEncodingProofs list rich_list

Theorem calldata_recursive_member_appends[local]:
  cs_appends
    (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
        dp <- emit_op ADD [dst; Lit (n2w vo)];
        compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od)
Proof
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_abi_member_pointer] >> gen_tac >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_emit_helpers] >>
  simp[cj 1 cs_appends_abi_decode_mutual]
QED

Theorem calldata_recursive_nonbulk_owned[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) st = ((),final) /\
  fn_has_code st final fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= base_addr+cap /\
  d+type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  (!middle last cdst csrc.
    compile_abi_decode_to_buf cdst csrc CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),last) /\
    fn_has_code middle last fn /\
    st.cs_next_id <= middle.cs_next_id /\ last.cs_next_id <= final.cs_next_id /\
    abi_decoder_operand_live middle.cs_next_var csrc /\
    abi_decoder_operand_live middle.cs_next_var cdst /\
    (last.cs_current_insts = [] ==>
      !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) ==>
    !u w e.
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand csrc u = SOME w /\ eval_operand cdst u = SOME (n2w e) /\
    alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
    (!id q k. middle.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP u.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+cap /\
    e+type_memory_size tv < dimword (:256) ==>
    (?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
    ?v x scratch. ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
      v.vs_inst_idx = LENGTH last.cs_current_insts /\
      value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x e v.vs_memory /\
      (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn u = r /\
          (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
      v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
      alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
      (!id q k. middle.cs_next_id <= id /\ id < last.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        FLOOKUP v.vs_allocas id = SOME (q,k)) /\
      (!id. id < middle.cs_next_id \/ last.cs_next_id <= id ==>
        FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op v = eval_operand op u) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::scratch) u v /\
      (!q k. MEM (q,k) scratch ==> ?id. middle.cs_next_id <= id /\ id < last.cs_next_id /\
        FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\
    value_has_type (ArrayTV tv (Dynamic maxn)) x /\ val_wf (ArrayTV tv (Dynamic maxn)) x /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size (ArrayTV tv (Dynamic maxn)))::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_coherent_array_iff] >> strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  qpat_x_assum `compile_abi_decode_to_buf dst src _ (Lit 0w) _ _ st = _`
    (assume_tac o PURE_REWRITE_RULE [exprLoweringTheory.type_to_abi_dec_info_def]) >>
  qpat_assum `type_memory_bytes ce ty = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  drule_all calldata_nonbulk_parent_shell_conditional >> strip_tac >>
  `!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_x_assum `!id q k. st.cs_next_id <= id /\ _ ==> _` drule >>
     asm_rewrite_tac[] >> simp[]) >>
  `header_st.cs_next_id < final.cs_next_id` by decide_tac >>
  drule_all (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `sz` |-> `type_memory_size (ArrayTV tv (Dynamic maxn))`]
    calldata_owned_counter_address) >>
  disch_then (qx_choose_then `counter` (map_every assume_tac o CONJUNCTS)) >>
  `d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= initial.vs_alloca_next` by
    (irule abiCallerAllocationTheory.abi_caller_allocation_end >>
     qpat_assum `FLOOKUP initial.vs_allocas oid = _` (irule_at Any) >>
     asm_rewrite_tac[]) >>
  `st.cs_next_id <= middle.cs_next_id` by decide_tac >>
  `st1.cs_current_insts = [] ==>
    !bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (strip_tac >>
     qpat_assum `FST ops = _`
       (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
     qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     qpat_assum `fn_has_code st1 final fn` mp_tac >>
     qpat_assum `st1.cs_current_insts = []` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all calldata_loop_child_continuation_phi >> simp[]) >>
  irule calldata_coherent_nonbulk_array_owned_run >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `abi_decoder_coherent _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `FLOOKUP initial.vs_allocas oid = _` (irule_at Any) >>
  qpat_assum `abi_decode_index_init _ = _` (irule_at Any) >>
  qpat_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand src initial = _` (irule_at Any) >>
  qpat_assum `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>` (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := abi_decode_header_insts _ _ _ _ _ _ _ _ _ _|>`)) >>
  qpat_assum `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ abi_decode_backedge_insts _ _ _ _ _|>` (irule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _ ++ abi_decode_backedge_insts _ _ _ _ _|>`)) >>
  qpat_assum `lookup_block (FST (SND _)) _ = _` (irule_at Any) >>
  qpat_assum `lookup_block (SND (SND _)) _ = _` (irule_at Any) >>
  qexists_tac `counter` >>
  rpt (conj_tac >- (FIRST [first_assum ACCEPT_TAC, REFL_TAC])) >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `!middle last cdst csrc. _` drule_all >>
      disch_then ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[pairTheory.PAIR]
QED

Theorem calldata_recursive_list_el[local]:
  !R xs ys i. LIST_REL R xs ys ==> i < LENGTH xs ==>
    R (EL i xs) (EL i ys)
Proof
  simp[LIST_REL_EL_EQN]
QED

Theorem calldata_coherent_owned_run:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !dst src st final fn initial p d ctx site oid base_addr cap.
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),final) /\
  fn_has_code st final fn /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  (final.cs_current_insts = [] ==>
    !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  (?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
    mem_safe_run fuel ctx fn initial) \/
  ?v x sc. ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
    v.vs_inst_idx = LENGTH final.cs_current_insts /\ value_has_type tv x /\
    val_wf tv x /\ val_in_memory tv x d v.vs_memory /\
    (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn initial)) /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k))
Proof
  ho_match_mp_tac calldata_coherent_induction >>
  conj_tac >- suspend "base" >>
  conj_tac >- suspend "flag" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "tuple" >>
  suspend "struct"
QED

Resume calldata_coherent_owned_run[base]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (BaseT bt) (BaseTV bt)` by
    (irule (cj 1 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  Cases_on `is_word_type (BaseT bt)`
  >- (drule_all calldata_coherent_word_owned_run >>
      disch_then ACCEPT_TAC) >>
  Cases_on `bt` >>
  qpat_x_assum `~is_word_type _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [is_word_type_def]) >>
  FIRST [
    (rename1 `StringT maxn` >>
     `BaseT (StringT maxn) = BaseT (StringT maxn)` by simp[] >>
     drule_all calldata_coherent_string_owned_run >> disch_then ACCEPT_TAC),
    (rename1 `BytesT bound` >> Cases_on `bound`
     >- (qpat_x_assum `abi_decoder_scalar_valid _` mp_tac >>
         simp_tac (srw_ss()) [abi_decoder_scalar_valid_def] >>
         disch_tac >> qpat_x_assum `~is_word_type _` mp_tac >>
         simp[is_word_type_def]) >>
     qpat_x_assum `~is_word_type _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [is_word_type_def]) >>
     rename1 `Dynamic maxn` >>
     `BaseT (BytesT (Dynamic maxn)) = BaseT (BytesT (Dynamic maxn))` by simp[] >>
     drule_all calldata_coherent_bytes_owned_run >> disch_then ACCEPT_TAC)]
QED
Resume calldata_coherent_owned_run[flag]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (FlagT nsid) (FlagTV n)` by
    (irule (cj 2 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  `is_word_type (FlagT nsid)` by simp[is_word_type_def] >>
  drule_all calldata_coherent_word_owned_run >> disch_then ACCEPT_TAC
QED
Resume calldata_coherent_owned_run[array]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (ArrayT ty bound) (ArrayTV tv bound)` by
    (irule (cj 3 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  Cases_on `bound`
  >- (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)
        calldata_coherent_fixed_array_owned_run_tail >>
      disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
      disch_then irule >>
      conj_tac
      >- metis_tac[calldata_recursive_member_appends, cs_appends_def] >>
      conj_tac
      >- metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      reverse conj_tac
      >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
            (qexists `p` >> first_assum ACCEPT_TAC)]) >>
      qexists `abi_decoder_member_infos sf ce (REPLICATE n ty)` >>
      conj_tac >- suspend "fixed_callback" >>
      simp[]) >>
  suspend "dynamic"
QED
Resume calldata_coherent_owned_run[fixed_callback]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_member_address_static_live >> strip_tac >>
  `ei = type_to_abi_dec_info sf ce ty` by
    (qpat_x_assum `EL i _ = (ei,az,mz)` mp_tac >>
     qpat_x_assum `i < LENGTH _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decoder_member_infos_def, EL_MAP, EL_REPLICATE]) >>
  `b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (drule calldata_member_tail_empty_exit_phi >>
     disch_then (qspec_then `fn` mp_tac) >> asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `w` >> first_assum ACCEPT_TAC),
    (qpat_x_assum `ci_mono st a` mp_tac >>
     qpat_x_assum `ci_mono b final` mp_tac >>
     qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `a.cs_next_id <= mid.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)]
QED
Resume calldata_coherent_owned_run[dynamic]:
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "nonbulk" >>
  `~is_abi_dynamic ce.ce_struct_fields ty /\
    ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)` by
    (qpat_x_assum `~(_ \/ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `ArrayT ty (Dynamic n) = ArrayT ty (Dynamic n)` by simp[] >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic n)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) F n` by
    (qpat_x_assum `~is_abi_dynamic _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringTheory.type_to_abi_dec_info_def]) >>
  drule_all calldata_coherent_bulk_array_owned_run >> disch_then ACCEPT_TAC
QED
Resume calldata_coherent_owned_run[nonbulk]:
  `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))` by
    (irule (cj 3 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)
    calldata_recursive_nonbulk_owned >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  conj_tac >- suspend "nonbulk_callback" >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `p` >> first_assum ACCEPT_TAC),
    (qexists `env` >> first_assum ACCEPT_TAC)]
QED
Resume calldata_coherent_owned_run[nonbulk_callback]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `w` >> first_assum ACCEPT_TAC), decide_tac]
QED
Resume calldata_coherent_owned_run[tuple]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by
    (qpat_assum `LIST_REL _ tys tvs` mp_tac >>
     ho_match_mp_tac listTheory.LIST_REL_mono >>
     rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  `abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs)` by
    (irule (cj 4 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  qpat_x_assum `LIST_REL (\ty tv. _ /\ _) tys tvs` mp_tac >>
  qmatch_goalsub_abbrev_tac `LIST_REL ih tys tvs` >> disch_tac >>
  drule calldata_tuple_member_metadata >> strip_tac >>
  qpat_x_assum `TupleTV _ = TupleTV _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `tvs = _` SUBST_ALL_TAC >>
  drule calldata_member_indexed_metadata >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (assume_tac o REWRITE_RULE [abi_decoder_tuple_infos]) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)
    calldata_complex_tuple_owned_run_tail >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  conj_tac
  >- metis_tac[calldata_recursive_member_appends, cs_appends_def] >>
  conj_tac
  >- metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def] >>
  conj_tac >- suspend "tuple_callback" >>
  suspend "tuple_layout"
QED
Resume calldata_coherent_owned_run[tuple_layout]:
  qpat_x_assum `Abbrev (ih = _)` kall_tac >>
  qpat_x_assum `!i. SUM (MAP _ (TAKE i _)) = SUM (MAP type_memory_size _)`
    (qspec_then `LENGTH (abi_decoder_member_infos sf ce tys)` mp_tac) >>
  qpat_assum `LENGTH (abi_decoder_member_infos sf ce tys) = _`
    (fn th => pure_rewrite_tac[th, TAKE_LENGTH_ID]) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> `i < LENGTH tys` by decide_tac >>
      qpat_x_assum `!i. i < LENGTH tys ==> _` drule >>
      strip_tac >> asm_rewrite_tac[] >> simp_tac std_ss []) >>
  qpat_assum `type_memory_size (TupleTV _) = _` (fn th =>
    (qpat_x_assum `d + type_memory_size _ < _`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
     qpat_x_assum `d + type_memory_size _ <= _`
      (assume_tac o PURE_REWRITE_RULE [th]))) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `p` >> first_assum ACCEPT_TAC),
    (asm_rewrite_tac[] >> NO_TAC)]
QED
Resume calldata_coherent_owned_run[tuple_callback]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH tys` by decide_tac >>
  `ih (EL i tys) (EL i tvs')` by
    (qpat_assum `LIST_REL ih _ _`
       (mp_then Any (qspec_then `i` mp_tac) calldata_recursive_list_el) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `Abbrev (ih = _)`
    (fn th => qpat_x_assum `ih _ _`
      (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [PURE_REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
  drule calldata_member_address_static_live >> strip_tac >>
  `ei = type_to_abi_dec_info sf ce (EL i tys)` by
    (qpat_x_assum `!i. i < LENGTH tys ==> _` drule >>
     strip_tac >> qpat_x_assum `EL i _ = (ei,az,mz)` mp_tac >>
     asm_rewrite_tac[] >> simp_tac std_ss []) >>
  `b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (drule calldata_member_tail_empty_exit_phi >>
     disch_then (qspec_then `fn` mp_tac) >> asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `w` >> first_assum ACCEPT_TAC),
    (qpat_x_assum `ci_mono st a` mp_tac >>
     qpat_x_assum `ci_mono b final` mp_tac >>
     qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `a.cs_next_id <= mid.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)]
QED
Resume calldata_coherent_owned_run[struct]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (abi_decoder_coherent ce (env \\ nsid) (sf \\ nsid_to_string nsid))
    (MAP SND args) tvs` by
    (qpat_assum `LIST_REL _ (MAP SND args) tvs` mp_tac >>
     ho_match_mp_tac listTheory.LIST_REL_mono >>
     rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `LIST_REL (\ty tv. _ /\ _) _ tvs` mp_tac >>
  qmatch_goalsub_abbrev_tac `LIST_REL ih (MAP SND args) tvs` >> disch_tac >>
  `abi_decoder_coherent ce env sf (StructT nsid) (StructTV (ZIP (MAP FST args,tvs)))` by
    (qpat_x_assum `Abbrev (ih = _)` kall_tac >>
     irule (cj 5 abi_decoder_coherent_rules) >> asm_rewrite_tac[] >>
     qexists `fields` >> asm_rewrite_tac[]) >>
  `MAP (FST o SND) fields = MAP SND args` by
    (qpat_x_assum `MAP _ fields = args` (SUBST1_TAC o SYM) >>
     simp[MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD]) >>
  drule abi_decoder_struct_infos >> disch_then (qspec_then `ce` mp_tac) >>
  disch_then (fn th => qpat_assum `MAP (FST o SND) fields = _`
    (fn eq => assume_tac (PURE_REWRITE_RULE [eq] th))) >>
  drule calldata_member_indexed_metadata >> strip_tac >>
  `MAP SND (ZIP (MAP FST args,tvs)) = tvs` by
    (drule LIST_REL_LENGTH >> simp[LENGTH_MAP] >> strip_tac >> simp[MAP_ZIP]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (fn th => qpat_assum `type_to_abi_dec_info sf ce (StructT nsid) = _`
      (fn eq => assume_tac (PURE_REWRITE_RULE [eq] th))) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)
    calldata_complex_struct_owned_run_tail >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  conj_tac
  >- metis_tac[calldata_recursive_member_appends, cs_appends_def] >>
  conj_tac
  >- metis_tac[cj 2 cs_appends_abi_decode_mutual, cs_appends_def] >>
  conj_tac >- suspend "struct_callback" >>
  suspend "struct_layout"
QED
Resume calldata_coherent_owned_run[struct_layout]:
  qpat_x_assum `Abbrev (ih = _)` kall_tac >>
  `type_memory_size (StructTV (ZIP (MAP FST args,tvs))) = SUM (MAP type_memory_size tvs)` by
    (simp_tac std_ss [valueEncodingTheory.type_memory_size_def, type_memory_size_fields_sum, GSYM MAP_MAP_o] >>
     qpat_assum `MAP SND (ZIP _) = tvs` (fn th => rewrite_tac[th])) >>
  qpat_x_assum `!i. SUM (MAP _ (TAKE i _)) = SUM (MAP type_memory_size _)`
    (qspec_then `LENGTH (abi_decoder_member_infos (sf \\ nsid_to_string nsid) ce (MAP SND args))` mp_tac) >>
  qpat_assum `LENGTH (abi_decoder_member_infos _ _ _) = _`
    (fn th => pure_rewrite_tac[th, TAKE_LENGTH_ID]) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `i < LENGTH (MAP SND args)` by
        (drule LIST_REL_LENGTH >> strip_tac >> decide_tac) >>
      qpat_x_assum `!i. i < LENGTH (MAP SND args) ==> _` drule >>
      strip_tac >> asm_rewrite_tac[] >> simp_tac std_ss []) >>
  qpat_assum `type_memory_size (StructTV _) = _` (fn th =>
    (qpat_x_assum `d + type_memory_size _ < _`
      (assume_tac o PURE_REWRITE_RULE [th]) >>
     qpat_x_assum `d + type_memory_size _ <= _`
      (assume_tac o PURE_REWRITE_RULE [th]))) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `p` >> first_assum ACCEPT_TAC),
    (asm_rewrite_tac[] >> NO_TAC)]
QED
Resume calldata_coherent_owned_run[struct_callback]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH (MAP SND args)` by
    (drule LIST_REL_LENGTH >> strip_tac >> decide_tac) >>
  `ih (EL i (MAP SND args)) (EL i tvs)` by
    (qpat_assum `LIST_REL ih _ _`
       (mp_then Any (qspec_then `i` mp_tac) calldata_recursive_list_el) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `Abbrev (ih = _)`
    (fn th => qpat_x_assum `ih _ _`
      (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [PURE_REWRITE_RULE [markerTheory.Abbrev_def] th])) >>
  drule calldata_member_address_static_live >> strip_tac >>
  `ei = type_to_abi_dec_info (sf \\ nsid_to_string nsid) ce (EL i (MAP SND args))` by
    (qpat_x_assum `!i. i < LENGTH (MAP SND args) ==> _` drule >>
     strip_tac >> qpat_x_assum `EL i _ = (ei,az,mz)` mp_tac >>
     asm_rewrite_tac[] >> simp_tac std_ss []) >>
  `b.cs_current_insts = [] ==>
    !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (drule calldata_member_tail_empty_exit_phi >>
     disch_then (qspec_then `fn` mp_tac) >> asm_rewrite_tac[] >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_assum `MAP SND (ZIP _) = tvs`
    (fn th => pure_rewrite_tac[th] >>
      rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then irule >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qexists `w` >> first_assum ACCEPT_TAC),
    (qpat_x_assum `ci_mono st a` mp_tac >>
     qpat_x_assum `ci_mono b final` mp_tac >>
     qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `a.cs_next_id <= mid.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)]
QED
Finalise calldata_coherent_owned_run
