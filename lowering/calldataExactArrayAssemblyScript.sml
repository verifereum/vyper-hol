Theory calldataExactArrayAssembly
Ancestors
  calldataExactMembers calldataExactDyn calldataRecursiveProducers
  calldataSourceCorrespondence calldataSourceDecisions abiDecoderCoherence
  abiDecoderAppend abiDecoderMemberInfos calldataAggregateTyped
  abiCallerAllocation exprLowering valueEncodingDefs vyperCalldata
  arithmetic list rich_list words compileEnv abiEncoder

Theorem calldata_exact_array_case:
  let R = \ty tv.
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
    (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = NONE /\
      ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
        mem_safe_run fuel ctx fn initial) \/
    ?v x sc. cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) = SOME x /\
      ~v.vs_halted /\ v.vs_current_bb = final.cs_current_bb /\
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
  in
  (!dst src xs st final fn initial srcword d ctx site oid base_addr cap TV ts member_ptrs build.
    compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) xs 0 0 st = ((),final) /\
    fn_has_code st final fn /\ ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts /\
    eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\
    alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
    (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
      FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
    (oid < st.cs_next_id \/ final.cs_next_id <= oid) /\ base_addr <= d /\
    d+type_memory_size TV <= base_addr+cap /\ d+type_memory_size TV < dimword (:256) /\
    LENGTH ts = LENGTH xs /\
    (!i. i < LENGTH xs ==> type_memory_size (EL i ts) = (\(ei,az,mz). mz) (EL i xs)) /\
    (!i ei az mz. i < LENGTH xs /\ EL i xs = (ei,az,mz) ==>
      dec_info_needs_offset ei = tv_abi_dynamic (EL i ts) /\
      member_ptrs i = cd_member_ptr F initial.vs_call_ctx.cc_calldata (EL i ts)
        (w2n srcword) (SUM (MAP (\(ei,az,mz). az) (TAKE i xs)))) /\
    exact_aggregate_pack TV ts member_ptrs initial.vs_call_ctx.cc_calldata (w2n srcword) build /\
    (!ys ao vo a b.
      compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w) ys ao vo a = ((),b) ==>
      cs_extends a b) /\
    (!ei ao vo a b.
      (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei) ao CALLDATALOAD (Lit 0w) (Lit 0w);
          dp <- emit_op ADD [dst; Lit (n2w vo)];
          compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei od) a = ((),b) ==>
      cs_extends a b) /\
    (!i a mid b ep dp ei az mz.
      i < LENGTH xs /\ EL i xs = (ei,az,mz) /\
      (do ep <- compile_getelemptr_abi src (dec_info_needs_offset ei)
            (SUM (MAP (\(ei,az,mz). az) (TAKE i xs))) CALLDATALOAD (Lit 0w) (Lit 0w);
          dp <- emit_op ADD [dst; Lit (n2w (SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))))];
          return (ep,dp) od) a = ((ep,dp),mid) /\
      compile_abi_decode_to_buf dp ep CALLDATALOAD (Lit 0w) (Lit 0w) ei mid = ((),b) /\
      cs_extends st a /\ cs_extends b final /\ fn_has_code mid b fn /\
      ci_mono st a /\ ci_mono b final /\
      compile_abi_decode_complex_elems dst src CALLDATALOAD (Lit 0w) (Lit 0w)
        (DROP (SUC i) xs)
        (az + SUM (MAP (\(ei,az,mz). az) (TAKE i xs)))
        (mz + SUM (MAP (\(ei,az,mz). mz) (TAKE i xs))) b = ((),final) /\
      fn_has_code b final fn ==>
      !u w e. ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
        u.vs_inst_idx = LENGTH mid.cs_current_insts /\
        eval_operand ep u = SOME w /\ eval_operand dp u = SOME (n2w e) /\
        u.vs_call_ctx.cc_calldata = initial.vs_call_ctx.cc_calldata /\ w2n w = member_ptrs i /\
        alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
        (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
          FLOOKUP u.vs_allocas id = SOME (q,k) ==>
          k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
          ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
            ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
        FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
        base_addr <= e /\ e+type_memory_size (EL i ts) <= base_addr+cap /\
        e+type_memory_size (EL i ts) < dimword (:256) ==>
        (cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = NONE /\
          ?fuel z. run_from fuel ctx fn u = Abort Revert_abort z /\ mem_safe_run fuel ctx fn u) \/
        ?v x sc. ~v.vs_halted /\ v.vs_current_bb = b.cs_current_bb /\
          v.vs_inst_idx = LENGTH b.cs_current_insts /\
          (cd_decode F initial.vs_call_ctx.cc_calldata (EL i ts) (member_ptrs i) = SOME x /\
            value_has_type (EL i ts) x) /\ val_wf (EL i ts) x /\
          val_in_memory (EL i ts) x e v.vs_memory /\
          (!fuel r. run_from fuel ctx fn v = r /\ (!err. r <> Error err) ==>
            ?fuel'. run_from fuel' ctx fn u = r /\
              (mem_safe_run fuel ctx fn v ==> mem_safe_run fuel' ctx fn u)) /\
          v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
          alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
          (!id q k. mid.cs_next_id <= id /\ id < b.cs_next_id /\
            FLOOKUP v.vs_allocas id = SOME (q,k) ==>
            k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
            ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
              ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
          u.vs_alloca_next <= v.vs_alloca_next /\
          (!id q k. FLOOKUP u.vs_allocas id = SOME (q,k) ==>
            FLOOKUP v.vs_allocas id = SOME (q,k)) /\
          (!id. id < mid.cs_next_id \/ b.cs_next_id <= id ==>
            FLOOKUP v.vs_allocas id = FLOOKUP u.vs_allocas id) /\
          (!op. abi_decoder_operand_live mid.cs_next_var op ==>
            eval_operand op v = eval_operand op u) /\
          abi_decode_footprint_frame ((e,type_memory_size (EL i ts))::sc) u v /\
          (!q k. MEM (q,k) sc ==> ?id. mid.cs_next_id <= id /\ id < b.cs_next_id /\
            FLOOKUP v.vs_allocas id = SOME (q,k))) ==>
    (cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = NONE /\
      ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\ mem_safe_run fuel ctx fn initial) \/
    ?t vs scratch. ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
      t.vs_inst_idx = LENGTH final.cs_current_insts /\
      cd_decode F initial.vs_call_ctx.cc_calldata TV (w2n srcword) = SOME (build vs) /\
      value_has_type TV (build vs) /\ val_wf TV (build vs) /\
      val_in_memory TV (build vs) d t.vs_memory /\
      (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
        ?fuel'. run_from fuel' ctx fn initial = r /\
          (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn initial)) /\
      t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
      (!id q k. st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= t.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP t.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      abi_decode_footprint_frame ((d,type_memory_size TV)::scratch) initial t /\
      (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < final.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (q,k))) ==>
  (!n. ~is_abi_dynamic ce.ce_struct_fields ty /\
    ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
    abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n)) ==>
    R (ArrayT ty (Dynamic n)) (ArrayTV tv (Dynamic n))) ==>
  abi_decoder_coherent ce env sf ty tv /\ R ty tv /\
  abi_decoder_header ce env (ArrayT ty bound) (ArrayTV tv bound) ==>
  R (ArrayT ty bound) (ArrayTV tv bound)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> disch_then (mk_asm "linked") >> strip_tac >> strip_tac >>
  `abi_decoder_coherent ce env sf (ArrayT ty bound) (ArrayTV tv bound)` by
    (irule (cj 3 abi_decoder_coherent_rules) >> asm_rewrite_tac[]) >>
  Cases_on `bound`
  >- suspend "fixed" >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- suspend "nonbulk" >>
  asm_x "linked" kall_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED
Resume calldata_exact_array_case[fixed]:
  BETA_TAC >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_fixed_member_metadata >> strip_tac >>
  qpat_x_assum `ArrayTV _ _ = ArrayTV _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  drule calldata_member_indexed_metadata >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  simp_tac (srw_ss()) [Once compile_abi_decode_to_buf_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >> strip_tac >>
  `exact_aggregate_pack (ArrayTV tv (Fixed n)) (REPLICATE n tv)
    (\i. cd_member_ptr F initial.vs_call_ctx.cc_calldata tv (w2n p) (i * tv_abi_size tv))
    initial.vs_call_ctx.cc_calldata (w2n p)
    (\vs. ArrayV (make_array_value tv (Fixed n) vs))` by
      simp[exact_aggregate_pack_fixed] >>
  asm "linked" (drule_at (Pat `exact_aggregate_pack _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src initial = SOME _`)) >>
  disch_then (drule_at (Pat `eval_operand dst initial = SOME _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>

  (impl_tac >- suspend "fixed_premises") >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `fixed_end` (qx_choose_then `fixed_values`
      (qx_choose_then `fixed_scratch` assume_tac))))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`fixed_end`,
    `ArrayV (make_array_value tv (Fixed n) fixed_values)`, `fixed_scratch`] >>
  pop_assum (fn th => POP_ASSUM_LIST (K all_tac) >>
    map_every assume_tac (CONJUNCTS (BETA_RULE th))) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac[]
QED
Resume calldata_exact_array_case[fixed_premises]:
  asm_x "linked" kall_tac >>
  asm_rewrite_tac [] >>
  conj_tac >- suspend "fixed_sizes" >>
  conj_tac >- suspend "fixed_pointers" >>
  conj_tac >- suspend "fixed_extends" >>
  conj_tac >- suspend "fixed_element_extends" >>
  suspend "fixed_child"
QED
Resume calldata_exact_array_case[fixed_sizes]:
  rpt strip_tac >>
  qpat_x_assum `!i. i < LENGTH (REPLICATE n ty) ==> _`
    (qspec_then `i` mp_tac) >>
  qpat_x_assum `i < LENGTH _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[LENGTH_REPLICATE] >> rpt strip_tac >> asm_rewrite_tac []
QED
Resume calldata_exact_array_case[fixed_pointers]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH (REPLICATE n ty) ==> _`
    (qspec_then `i` mp_tac) >>
  qpat_x_assum `EL i (abi_decoder_member_infos _ _ _) = (ei,az,mz)` mp_tac >>
  qpat_x_assum `i < LENGTH _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[LENGTH_REPLICATE] >> ntac 3 strip_tac >>
  gvs[EL_REPLICATE] >>
  conj_tac
  >- (drule calldata_coherent_offset >>
      drule calldata_coherent_dynamic >> simp[]) >>
  drule abi_decoder_coherent_header >>
  drule calldataSourceSizeTheory.calldata_coherent_embedded_size >>
  qpat_x_assum `i < n` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  rewrite_tac[REPLICATE_GENLIST, TAKE_GENLIST, MAP_GENLIST] >>
  simp[abi_decoder_header_def, combinTheory.o_DEF, MIN_DEF] >>
  `(\x:num. abi_member_head_size (vyper_to_abi_type env ty)) =
    K (abi_member_head_size (vyper_to_abi_type env ty))` by simp[FUN_EQ_THM] >>
  asm_rewrite_tac[GSYM REPLICATE_GENLIST, SUM_REPLICATE]
QED
Resume calldata_exact_array_case[fixed_extends]:
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[abiDecoderMemberConsTheory.abi_decoder_members_extends]
QED
Resume calldata_exact_array_case[fixed_element_extends]:
  POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >>
  qspecl_then [`dst`,`src`,`CALLDATALOAD`,`Lit 0w`,`Lit 0w`,
    `[(ei,0,0)]`,`ao`,`vo`,`a`,`b`] mp_tac
    (Q.GENL [`dst`,`src`,`opc`,`base_op`,`hi`,`elems`,`ao`,`vo`,`st`,`final`]
      abiDecoderMemberConsTheory.abi_decoder_members_extends) >>
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> metis_tac[]
QED
Resume calldata_exact_array_case[fixed_child]:
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
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`w`,`ctx`,`site`] mp_tac) >>
  (impl_tac >- suspend "fixed_child_pre") >>
  suspend "fixed_child_post"
QED
Resume calldata_exact_array_case[fixed_child_pre]:
  qpat_x_assum `tv = tv'` SUBST_ALL_TAC >>
  `i < n` by metis_tac[LENGTH_REPLICATE] >>
  qpat_assum `i < n` (fn th =>
    qpat_x_assum `e + type_memory_size (EL i _) <= _`
      (assume_tac o SIMP_RULE (srw_ss()) [EL_REPLICATE, th]) >>
    qpat_x_assum `e + type_memory_size (EL i _) < _`
      (assume_tac o SIMP_RULE (srw_ss()) [EL_REPLICATE, th]) >>
    simp_tac (srw_ss()) [EL_REPLICATE, th]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `ci_mono st a` mp_tac >>
     qpat_x_assum `ci_mono b final` mp_tac >>
     qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `a.cs_next_id <= mid.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac)]
QED
Resume calldata_exact_array_case[fixed_child_post]:
  qpat_x_assum `tv = tv'` SUBST_ALL_TAC >>
  `i < n` by metis_tac[LENGTH_REPLICATE] >>
  qpat_assum `i < n` (fn th => simp_tac (srw_ss()) [EL_REPLICATE, th]) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac
    (qx_choose_then `child_end` (qx_choose_then `child_value`
      (qx_choose_then `child_scratch` assume_tac))))
  >- (disj1_tac >> conj_tac
      >- (qpat_x_assum `exact_aggregate_pack _ _ _ _ _ _` mp_tac >>
          qpat_x_assum `cd_decode F u.vs_call_ctx.cc_calldata _ _ = NONE` mp_tac >>
          qpat_x_assum `u.vs_call_ctx.cc_calldata = _` mp_tac >>
          qpat_x_assum `w2n w = _` mp_tac >>
          qpat_x_assum `i < n` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
          simp[exact_aggregate_pack_def, LENGTH_REPLICATE] >>
          rpt strip_tac >> first_x_assum irule >> qexists `i` >>
          simp[EL_REPLICATE]) >> metis_tac[]) >>
  disj2_tac >> qexistsl [`child_end`,`child_value`,`child_scratch`] >>
  qpat_x_assum `u.vs_call_ctx.cc_calldata = _` mp_tac >>
  qpat_x_assum `w2n w = _` mp_tac >>
  pop_assum (fn th => POP_ASSUM_LIST (K all_tac) >>
    map_every assume_tac (CONJUNCTS th)) >>
  ntac 2 strip_tac >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `cd_decode F u.vs_call_ctx.cc_calldata _ _ = SOME _` mp_tac >>
     asm_rewrite_tac[])]
QED
Resume calldata_exact_array_case[nonbulk]:
  asm_x "linked" kall_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
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
    `sz` |-> `type_memory_size (ArrayTV tv (Dynamic n))`]
    calldata_owned_counter_address) >>
  disch_then (qx_choose_then `counter` (map_every assume_tac o CONJUNCTS)) >>
  `d+type_memory_size (ArrayTV tv (Dynamic n)) <= initial.vs_alloca_next` by
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
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = tv_abi_dynamic tv /\
   abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv /\
   (tv_abi_dynamic tv \/ tv_needs_clamp tv)` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `is_abi_dynamic _ _ \/ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule calldata_coherent_offset >>
     drule calldata_coherent_dynamic >>
     drule calldata_coherent_clamp >>
     drule calldataSourceSizeTheory.calldata_coherent_embedded_size >>
     simp[]) >>
  irule calldata_exact_nonbulk_array_owned_run >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic n)) _` (irule_at Any) >>
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
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC,
    (disj1_tac >> first_assum ACCEPT_TAC),
    (disj2_tac >> first_assum ACCEPT_TAC),
    (pure_rewrite_tac[pairTheory.PAIR] >> first_assum ACCEPT_TAC),
    suspend "nonbulk_child"]
QED
Resume calldata_exact_array_case[nonbulk_child]:
  markerLib.RESUME_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rule_assum_tac BETA_RULE >>
  qpat_x_assum `!dst src st final fn initial p d ctx site oid base_addr cap. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME (n2w _)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`w`,`ctx`,`site`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `oid < _ \/ _ <= oid` mp_tac >>
     qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
     qpat_x_assum `st1.cs_next_id <= final.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac)])) >>
  disch_then ACCEPT_TAC
QED
Finalise calldata_exact_array_case
