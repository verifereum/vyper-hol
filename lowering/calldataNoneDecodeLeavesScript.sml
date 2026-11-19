(* One-sided source correlation for straight-line calldata decoders. *)
Theory calldataNoneDecodeLeaves
Ancestors
  calldataExactScalarAccepted calldataExactScalarRejected calldataExactBytesJoint
  calldataSourceWord calldataBulkSourceOutcome calldataBulkUniformPtr
  calldataBulkOperationalCertificate abiDecoderWordTyped abiDecoderFrameCompose
  abiCallerAllocation calldataDynOwned instIdxIndep option
  abiDecoderCoherence compileEnv vyperCalldata calldataSourceCorrespondence
  ptrDiscipline calldataBulkLive calldataFiniteTransport
  calldataStaticSourceExact calldataBulkSourceExact abiDecoderBulk
  abiDecoderDynarrayPrefix abiDecoderGuards abiEncoder abiDecoderContract
  venomMemDefs venomState words arithmetic emitHelperProps abiDecoderArrayHeader fragExec
  calldataCountGuardRejectOrigin

Theorem none_decode_leaf_paths:
  !ce env sf ty tv st last limit ctx fn site src child initial p d oid base_addr cap G tn lower PG.
  abi_decoder_coherent ce env sf ty tv /\
  ((?cl. type_to_abi_dec_info sf ce ty = DecPrimWord cl) \/
   is_bytestring_type ty \/
   (?ety maxn ei abi_sz mem_sz.
      ty = ArrayT ety (Dynamic maxn) /\
      type_to_abi_dec_info sf ce ty = DecDynArray ei abi_sz mem_sz F maxn /\
      ~dec_info_needs_clamp ei)) /\
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME p /\
  eval_operand (Var child) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+type_memory_size tv <= base_addr+cap /\
  d+type_memory_size tv < dimword (:256) /\
  ptr_covers G tn child initial (type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lower initial /\
  lower <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (?z H u. z.vs_returndata = [] /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (Abort Revert_abort z,H,u))) \/
  ?v sc H u.
    IS_SOME (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p)) /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    v.vs_call_ctx = initial.vs_call_ctx /\
    v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,type_memory_size tv)::sc) initial v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v (type_memory_size tv) /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      op_taint u (Var name) = op_taint tn (Var name)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
      (initial,G,tn) [] (OK v,H,u))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?cl. _) \/ _` strip_assume_tac
  >- suspend "word"
  >- suspend "bytes"
  >> suspend "bulk"
QED

Resume none_decode_leaf_paths[word]:
  `type_memory_size tv = 32 /\ is_word_type ty /\
    cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p) =
      cd_word_value tv (abi_decode_load CALLDATALOAD p initial)` by
    (qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
     qpat_assum `type_to_abi_dec_info _ _ _ = DecPrimWord _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abi_decoder_coherent_header >>
     simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
     drule_all abi_decoder_primitive_cases >> strip_tac >>
     gvs[is_word_type_def, cd_decode_def, calldata_decode_load_word] >>
     Cases_on `bt` >> gvs[is_word_type_def, cd_decode_def] >>
     Cases_on `b` >> gvs[is_word_type_def, cd_decode_def]) >>
  qpat_x_assum `type_memory_size tv = 32` SUBST_ALL_TAC >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info _ _ _ = DecPrimWord _`
    (fn th => pure_rewrite_tac [th]) >> disch_tac >>
  Cases_on `abi_clamp_ok cl (abi_decode_load CALLDATALOAD p initial)`
  >- (drule_all calldata_coherent_word_rejects >>
      disch_then (qspec_then `abi_decode_load CALLDATALOAD p initial` assume_tac) >>
      drule_all calldata_word_accepted_resource_joint >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      disj2_tac >> qexistsl [`v`,`[]`,`H`,`u`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qpat_x_assum `(cd_word_value _ _ = NONE) = _` mp_tac >>
          Cases_on `cd_word_value tv (abi_decode_load CALLDATALOAD p initial)` >>
          asm_simp_tac std_ss [IS_SOME_DEF])
      >- simp_tac (srw_ss()) [] >>
      qx_gen_tac `name` >> disch_tac >>
      qpat_assum `!name. not_fresh_at st name ==> FLOOKUP H name = _ /\ _`
        (qspec_then `name` mp_tac) >>
      asm_simp_tac bool_ss [op_taint_def, venomStateTheory.operand_case_def]) >>
  drule_all calldata_word_rejected_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]
QED

Resume none_decode_leaf_paths[bytes]:
  drule_all calldata_exact_bytes_joint_limit >>
  disch_then (qspec_then `PG` strip_assume_tac)
  >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> simp[]) >>
  disj2_tac >> qexistsl [`v`,`sc`,`H`,`u`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `cd_decode _ _ _ _ = SOME _` SUBST1_TAC >>
      simp_tac std_ss [IS_SOME_DEF]) >>
  qx_gen_tac `name` >> disch_tac >>
  qpat_assum `!name. not_fresh_at st name ==> FLOOKUP H name = _ /\ _`
    (qspec_then `name` mp_tac) >>
  asm_simp_tac bool_ss [op_taint_def, venomStateTheory.operand_case_def]
QED

Resume none_decode_leaf_paths[bulk]:
  qpat_x_assum `ty = ArrayT _ _` SUBST_ALL_TAC >>
  drule_all calldata_bulk_descriptor_layout >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info _ _ _ = DecDynArray _ _ _ F _`
    (fn th => pure_rewrite_tac [th]) >> disch_tac >>
  qabbrev_tac `n = w2n (abi_decode_load CALLDATALOAD p initial)` >>
  qabbrev_tac `lim = maxn MOD dimword (:256)` >>
  `lim < dimword (:256) /\ lim <= maxn` by simp[Abbr `lim`, MOD_LESS_EQ] >>
  Cases_on `n <= lim` >- suspend "bulk_ok" >> suspend "bulk_abort"
QED

Resume none_decode_leaf_paths[bulk_ok]:
  `n <= maxn` by decide_tac >>
  `n * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >>
  `lim * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >>
  `base_addr+cap <= initial.vs_alloca_next` by
    (qpat_assum `alloca_inv initial` mp_tac >>
     simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp_tac bool_ss []) >>
  `d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
   32+n*mem_sz <= type_memory_size tv /\
   d+32+n*mem_sz <= initial.vs_alloca_next /\
   d+(32+lim*mem_sz) < dimword (:256) /\
   d+(32+lim*mem_sz) <= initial.vs_alloca_next` by
    (qpat_assum `type_memory_size tv = _` SUBST1_TAC >> decide_tac) >>
  `w2n (abi_decode_load CALLDATALOAD p initial) * mem_sz < dimword (:256) /\
   w2n (abi_decode_load CALLDATALOAD p initial) <= maxn MOD dimword (:256)` by
    (unabbrev_all_tac >> asm_rewrite_tac[]) >>
  drule_all calldata_bulk_accepted_live_mod >> strip_tac >>
  `compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w)
     (DecDynArray ei abi_sz mem_sz F lim) st = ((),last)` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ (DecDynArray _ _ _ F maxn) _ = _` mp_tac >>
     `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
     qpat_assum `abi_decode_source_opcode CALLDATALOAD`
       (fn th => pure_rewrite_tac [MATCH_MP abi_decode_bulk_phases
         (CONJ th (ASSUME ``~dec_info_needs_clamp ei``))]) >>
     simp_tac std_ss [abi_decode_dynarray_position_prefix_unbounded, Abbr `lim`,
       compile_abi_dec_addr_def, comp_bind_def, comp_return_def,
       calldata_count_guard_mod_limit]) >>
  drule_all (Q.INST [`maxn` |-> `lim`] calldata_bulk_accepted_operational) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lookup_var child initial = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var child) initial = _` mp_tac >> simp_tac bool_ss [eval_operand_def]) >>
  `not_fresh_at st child /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (rpt conj_tac >> rpt strip_tac >> metis_tac[calldata_operand_live_not_fresh]) >>
  `abi_decode_load CALLDATALOAD p initial = n2w n` by simp[Abbr `n`] >>
  drule_all (Q.INST [`maxn` |-> `maxn`] calldata_bulk_decoder_endpoint_ptr_uniform_origin) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `?values. cd_decode_elems T initial.vs_call_ctx.cc_calldata etv
       (w2n (p+32w)) 0 n = SOME values` by
    (qpat_x_assum `mem_bytes_at _ _ t.vs_memory = _` mp_tac >>
     asm_simp_tac bool_ss [Abbr `n`] >> disch_tac >>
     drule_all calldata_static_elems_source_exact >> metis_tac[]) >>
  `IS_SOME (cd_decode F initial.vs_call_ctx.cc_calldata tv (w2n p))` by
    (qpat_assum `tv = ArrayTV _ _` SUBST1_TAC >>
     drule_all calldata_bulk_source_decode >> disch_then (pure_rewrite_tac o single) >>
     `w2n (cd_word initial.vs_call_ctx.cc_calldata (w2n p)) = n` by
        simp[Abbr `n`, calldata_decode_load_word] >>
     `~(maxn < n)` by decide_tac >> asm_simp_tac std_ss [IS_SOME_DEF]) >>
  qabbrev_tac `v = t with vs_inst_idx := LENGTH last.cs_current_insts` >>
  `v.vs_allocas = initial.vs_allocas /\ v.vs_alloca_next = initial.vs_alloca_next` by
    asm_simp_tac (srw_ss()) [Abbr `v`] >>
  drule_all calldata_alloca_inv_fields >> disch_tac >>
  drule_all calldata_alloca_frontier_inv_fields >> disch_tac >>
  `abi_decode_frame d (32+n*mem_sz) initial v` by
    (qpat_assum `abi_decode_frame d _ initial t` mp_tac >>
     simp_tac (srw_ss()) [abi_decode_frame_def, Abbr `v`, Abbr `n`] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_frame d (type_memory_size tv) initial v` by
    (irule abi_decode_frame_widen >> qexistsl [`d`,`32+n*mem_sz`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disj2_tac >> qexistsl [`v`,`[]`,`H`,`u`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- asm_simp_tac (srw_ss()) [Abbr `v`]
  >- asm_simp_tac (srw_ss()) [Abbr `v`]
  >- asm_rewrite_tac[]
  >- asm_rewrite_tac[LESS_EQ_REFL]
  >- asm_rewrite_tac[]
  >- asm_rewrite_tac[]
  >- asm_simp_tac (srw_ss()) [Abbr `v`, eval_op_inst_idx]
  >- asm_simp_tac (srw_ss()) [GSYM abi_decode_frame_footprint]
  >- simp_tac (srw_ss()) []
  >- (qpat_assum `ptr_covers H u child t _` mp_tac >>
      simp_tac (srw_ss()) [Abbr `v`, ghostPcTransportPtrTheory.ptr_covers_inst_idx])
  >- (qx_gen_tac `name` >> disch_tac >>
      qpat_assum `!x. not_fresh_at st x ==> lookup_var _ _ = _ /\ _`
        (qspec_then `name` (fn th =>
          qpat_assum `not_fresh_at st name` (strip_assume_tac o MATCH_MP th))) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `d + 32 + n * mem_sz <= _ ==> _` (fn th =>
    qpat_assum `d + 32 + n * mem_sz <= initial.vs_alloca_next` (ACCEPT_TAC o MATCH_MP th))
QED

Resume none_decode_leaf_paths[bulk_abort]:
  `maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p initial)` by
    (unabbrev_all_tac >> decide_tac) >>
  disj1_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  Cases_on `abi_decode_count_guard CALLDATALOAD src maxn st` >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (cnt,guard)` >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_assum `abi_decode_source_opcode CALLDATALOAD` (fn opc =>
    qpat_assum `~dec_info_needs_clamp ei` (fn unclamped =>
      qpat_assum `abi_decode_count_guard CALLDATALOAD src maxn st = (cnt,guard)`
        (fn guard_code => simp_tac std_ss
          [MATCH_MP abi_decode_bulk_phases (CONJ opc unclamped),
           abi_decode_dynarray_position_prefix_unbounded, compile_abi_dec_addr_def,
           comp_bind_def, comp_return_def, LET_THM, guard_code]))) >>
  disch_tac >>
  `cs_extends st guard` by
    (drule_all abi_decode_count_guard_fragment_shape >> strip_tac >>
     irule cs_extends_same_block >>
     fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends guard last` by
    (qpat_assum `abi_decode_bulk_body _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decode_bulk_body_def, abi_decode_bulk_payload_def,
       abi_decode_array_header_def, compile_abi_dec_addr_def, comp_return_def,
       comp_bind_def, comp_ignore_bind_def, emitHelperTheory.emit_op_def,
       emitHelperTheory.emit_void_def, compileEnvTheory.emit_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       cs_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     disch_then (SUBST1_TAC o SYM) >> qexists_tac `[]` >>
     simp[GSYM listTheory.APPEND_ASSOC]) >>
  `fn_has_code st guard fn` by metis_tac[fn_has_code_split] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp initial` by simp[] >>
  drule_all calldata_count_guard_rejected_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]
QED

Finalise none_decode_leaf_paths
