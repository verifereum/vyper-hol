(* Source-exact initialized array loop with a synchronized owned child callback. *)
Theory sourceOwnedArrayLoopPtr
Ancestors
  decoderLoopHeaderCorePtr decoderLoopBackedgeCorePtr decoderArraySetupPtr
  calldataDynOwned sourceRecursiveComplexPtr sourceEncodingWindows sourceEncodingLayout
  actualAllocaReplayPtr actualAllocSitesCredit abiDecoderCoherence abiDecoderContract
  abiDecoderExecution abiDecoderFrame abiDecoderReentry abiDecoderLoop
  abiDecoderDynamicLoopSetup abiDecoderArraySetupCode abiDecoderArraySlice
  abiDecoderValidArrayMemory abiDecoderValidArrayBackedge
  abiEncoder abiEncoderSourceTransport abiCanonicalHeadSize abiCanonicalWindows abiDecodeRanges
  bodyPtrDefs ptrSafeRun ptrDiscipline compileEnv emitHelperProps fragExec
  venomState venomExecSemantics venomInst venomMemDefs allocaFrontierBound
  exprLowering exprLoweringProps
  vyperABI vyperValue valueEncoding valueEncodingProps valueTypingMemoryProps
  finite_map words list rich_list arithmetic pred_set contractABI byte
  canonicalMemberTraversalPtr abiDecoderOffset

Theorem source_owned_array_loop_ptr:
  (!i r G tn child childsrc e srcpos.
    i < LENGTH xs /\
    compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decoder_coherent ce env sf ty tv /\ value_has_type tv (EL i xs) /\
    vyper_to_abi env ty (EL i xs) = SOME (EL i avs) /\
    mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)))
      r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) (EL i avs) /\
    srcpos + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) < dimword (:256) /\
    eval_operand childsrc r = SOME (n2w srcpos) /\
    lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
    abi_decoder_operand_live middle.cs_next_var childsrc /\
    abi_decoder_operand_live middle.cs_next_var (Var child) /\
    abi_decoder_operand_live middle.cs_next_var (Var root) /\
    ptr_covers G tn child r (type_memory_size tv) /\
    ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
    alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
    unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
    base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
    e + type_memory_size tv < dimword (:256) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
    (middle.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
    allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
    r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
    ?t H u fp.
      abi_decode_sim ctx fn r t /\
      ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
      t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
      val_in_memory tv (EL i xs) e t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv (EL i xs) e mem) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::fp) r t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
      r.vs_alloca_next <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
        FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
      (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,k) ==>
        k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p k. MEM (p,k) fp ==> ?id. middle.cs_next_id <= id /\
        id < end_st.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op t = eval_operand op r) /\
      (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)) ==>
  !n j s G tn.
    LENGTH xs - j = n /\ j <= LENGTH xs /\ LENGTH xs <= maxn /\
    maxn < dimword (:256) /\ outsz = 32 + maxn * type_memory_size tv /\
    abi_decoder_coherent ce env sf ty tv /\ 0 < type_slot_size tv /\
    EVERY (value_has_type tv) xs /\
    vyper_to_abi_same env ty xs = SOME avs /\
    LIST_REL (\aty av. ~is_dynamic aty ==>
      LENGTH (enc aty av) = abi_member_head_size aty)
      (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs /\
    mem_bytes_at cdsbase (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
      s.vs_call_ctx.cc_calldata = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
    cdsbase + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
    abi_decode_load CALLDATALOAD (n2w cdsbase : bytes32) s = n2w (LENGTH xs) /\
    abi_decode_array_element_setup (Var q) src (Var root) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_size tv) body_st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    fn_has_code body_st end_st fn /\ fn_inst_ids_distinct fn /\
    (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid (Var q) src CALLDATALOAD iv cv cmp done /\
    body_st.cs_current_bb = body_lbl /\ body_st.cs_current_insts = [] /\
    lookup_block end_st.cs_current_bb fn.fn_blocks = SOME back_bb /\
    FST ops = Var elem_idx /\
    back_bb.bb_instructions = end_st.cs_current_insts ++
      abi_decode_backedge_insts end_st.cs_next_id elem_idx nv (Var q) hdr /\
    lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
    iv = STRING #"%" (toString first_var) /\
    cv = STRING #"%" (toString (first_var+1)) /\
    cmp = STRING #"%" (toString (first_var+2)) /\
    done = STRING #"%" (toString (first_var+3)) /\
    nv = STRING #"%" (toString end_st.cs_next_var) /\
    first_var + 4 <= body_st.cs_next_var /\ end_st.cs_next_var < limit.cs_next_var /\
    abi_decoder_operand_live first_var src /\
    abi_decoder_operand_live first_var (Var root) /\ abi_decoder_operand_live first_var (Var q) /\
    eval_operand src s = SOME (n2w cdsbase) /\ lookup_var root s = SOME (n2w d) /\
    lookup_var q s = SOME (n2w slot) /\ mload slot s = n2w j /\
    mem_word_at d s.vs_memory = n2w (LENGTH xs) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      mem_word_at d mem = n2w (LENGTH xs)) /\
    (!i. i < j ==> val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) s.vs_memory /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
        val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
    base_addr <= d /\ d+outsz <= base_addr+owner_cap /\ d+outsz < dimword (:256) /\
    FLOOKUP s.vs_allocas index_id = SOME (slot,32) /\ index_id < middle.cs_next_id /\
    slot+32 < dimword (:256) /\
    (slot+32 <= base_addr \/ base_addr+owner_cap <= slot) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers G tn root s outsz /\ ptr_covers G tn q s 32 /\
    DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    fresh_vars_wrt limit s /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
    ?t H u fp.
      abi_decode_sim ctx fn s t /\
      ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d mem) /\
      abi_decode_footprint_frame ((d,outsz)::(slot,32)::fp) s t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
      s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt limit t /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      FLOOKUP t.vs_allocas index_id = SOME (slot,32) /\
      (!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) ==> FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
      (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,k) ==>
        k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p k. MEM (p,k) fp ==> ?id. middle.cs_next_id <= id /\
        id < end_st.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      ptr_covers H u root t outsz /\ ptr_covers H u q t 32 /\
      (!op. abi_decoder_operand_live first_var op ==> eval_operand op t = eval_operand op s) /\
      (!x. not_fresh_at body_st x /\ ~MEM x [iv;cv;cmp;done] ==>
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_tac >> Induct_on `n`
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `j = LENGTH xs` by decide_tac >>
      qpat_x_assum `!i r G tn child childsrc e srcpos. _` kall_tac >>
      `src <> Var iv /\ ALL_DISTINCT [q;iv;cv;cmp;done]` by
        (map_every (fn pat => qpat_x_assum pat mp_tac)
           [`iv = _`,`cv = _`,`cmp = _`,`done = _`,
            `abi_decoder_operand_live first_var src`,
            `abi_decoder_operand_live first_var (Var q)`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> Cases_on `src` >>
         fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
         metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
      qpat_assum `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`
        (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_loop_cfg_def]) >>
      qpat_x_assum `?bb. lookup_block body_lbl _ = _ /\ _` strip_assume_tac >>
      qpat_x_assum `?bb. lookup_block exit_lbl _ = _ /\ _` strip_assume_tac >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME hdr_bb /\
        hdr_bb.bb_instructions =
          abi_decode_header_insts hid (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl` by
        (map_every (fn pat => qpat_x_assum pat mp_tac)
          [`lookup_block hdr fn.fn_blocks = SOME hdr_bb`,
           `lookup_block hdr fn.fn_blocks = SOME _`, `s.vs_current_bb = hdr`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         gvs[]) >>
      `abi_decode_load CALLDATALOAD (n2w cdsbase : bytes32) s = n2w j /\
        j < dimword (:256)` by metis_tac[LESS_EQ_LESS_TRANS] >>
      `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by metis_tac[] >>
      `j <= j /\ LENGTH xs < dimword (:256)` by decide_tac >>
      drule_all decoder_index_header_ptr_core_uniform >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      `abi_decode_sim ctx fn s t` by
        (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
         irule abi_decode_ready_header_sim >>
         simp_tac bool_ss [abi_decode_loop_ready_def] >>
         conj_tac >- (qpat_x_assum `ALL_DISTINCT [q;iv;cv;cmp;done]` mp_tac >>
                      simp_tac list_ss []) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`hid`,`Var q`,`CALLDATALOAD`,`n2w slot`,`src`,`n2w cdsbase`] >>
         pure_rewrite_tac [abi_decode_source_opcode_def, eval_operand_def] >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`slot + 32 < dimword (:256)`, `mload slot s = n2w j`,
            `abi_decode_load CALLDATALOAD (n2w cdsbase : bytes32) s = n2w j`,
            `lookup_var q s = SOME _`, `eval_operand src s = SOME _`,
            `s.vs_inst_idx = 0`, `~s.vs_halted`, `s.vs_current_bb = hdr`,
            `src <> Var iv`, `abi_decode_loop_cfg fn hdr _ _ _ _ _ _ _ _ _ _`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         `slot < dimword (:256)` by decide_tac >>
         simp[wordsTheory.w2n_n2w]) >>
      `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d s.vs_memory /\
       (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d mem)` by
        (map_every (fn pat => qpat_assum pat mp_tac)
          [`mem_word_at d s.vs_memory = _`, `!mem. mem_agree_outside _ _ _ ==> _`,
           `!i. i < j ==> _`, `j = LENGTH xs`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         simp[val_in_memory_def] >>
         irule calldata_elems_memory_from_index >> metis_tac[]) >>
      drule calldata_header_owned_state >>
      disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
      `~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0` by
        (qpat_assum `t = jump_to _ _` mp_tac >>
         qpat_assum `~s.vs_halted` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
         simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
      `fresh_vars_wrt limit t` by
        (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
         simp_tac bool_ss [abiDecoderLoopRegistersTheory.abi_decoder_fresh_jump] >>
         pure_asm_rewrite_tac [] >>
         irule (cj 1 abiDecoderLoopRegistersTheory.abi_decoder_header_registers) >>
         conj_tac >-
           (drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
            strip_tac >>
            mp_tac (cj 1 abiDecoderCountersTheory.abi_decoder_vars_mono_mutual) >>
            simp_tac bool_ss [abiDecoderCountersTheory.abi_decoder_vars_mono_def] >>
            disch_then (qspecl_then
              [`SND (SND ops)`,`FST (SND ops)`,`CALLDATALOAD`,`Lit 0w`,
               `type_to_abi_dec_info sf ce ty`,`middle`] mp_tac) >>
            pure_asm_rewrite_tac [pairTheory.SND] >> strip_tac >> decide_tac) >>
         first_assum ACCEPT_TAC) >>
      qpat_x_assum `t = jump_to _ _` kall_tac >>
      qexistsl_tac [`t`,`H`,`u`,`[]`] >>
      pure_asm_rewrite_tac [] >>
      simp_tac bool_ss [abi_footprint_disjoint_def, listTheory.MEM, SUBSET_REFL,
        LESS_EQ_REFL] >>
      conj_tac >-
        (simp_tac bool_ss [abi_decode_footprint_frame_def] >>
         pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
      conj_tac >-
        (qpat_assum `allocas_from lower s` mp_tac >>
         qpat_assum `t.vs_allocas = s.vs_allocas` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> simp[allocas_from_def]) >>
      conj_tac >-
        (`~MEM root [iv;cv;cmp;done]` by
           (map_every (fn pat => qpat_assum pat mp_tac)
             [`abi_decoder_operand_live first_var (Var root)`,
              `iv = _`,`cv = _`,`cmp = _`,`done = _`] >>
            POP_ASSUM_LIST (K ALL_TAC) >>
            simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
            metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
         qpat_x_assum `!x. ~MEM x [iv;cv;cmp;done] ==> _` drule >>
         strip_tac >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`lookup_var root t = _`, `FLOOKUP H root = _`,
            `op_taint u (Var root) = _`, `ptr_covers G tn root s outsz`,
            `outsz = _`] >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[decoderGhostFramePtrTheory.ptr_covers_frame]) >>
      conj_tac >-
        (qpat_assum `!op. op <> Var iv /\ _ ==> _` mp_tac >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`iv = _`,`cv = _`,`cmp = _`,`done = _`] >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         first_x_assum irule >>
         Cases_on `op` >>
         gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
         metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
      qpat_assum `!x. ~MEM x [iv;cv;cmp;done] ==> _` mp_tac >>
      map_every (fn pat => qpat_assum pat mp_tac)
        [`iv = _`,`cv = _`,`cmp = _`,`done = _`] >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp_tac list_ss [] >> metis_tac[])
  >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `j < LENGTH xs /\ LENGTH xs < dimword (:256)` by decide_tac >>
  `src <> Var iv /\ ALL_DISTINCT [q;iv;cv;cmp;done]` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`iv = _`,`cv = _`,`cmp = _`,`done = _`,
        `abi_decoder_operand_live first_var src`,
        `abi_decoder_operand_live first_var (Var q)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> Cases_on `src` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
  qpat_assum `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_loop_cfg_def]) >>
  qpat_x_assum `?bb. lookup_block body_lbl _ = _ /\ _` strip_assume_tac >>
  qpat_x_assum `?bb. lookup_block exit_lbl _ = _ /\ _` strip_assume_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME hdr_bb /\
    hdr_bb.bb_instructions =
      abi_decode_header_insts hid (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
      [`lookup_block hdr fn.fn_blocks = SOME hdr_bb`,
       `lookup_block hdr fn.fn_blocks = SOME _`, `s.vs_current_bb = hdr`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by metis_tac[] >>
  drule_all decoder_index_header_ptr_core_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule abi_encoder_same_conversion >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `32 + abi_tuple_child_offset
      (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j +
      LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) <=
      LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) /\
    mem_bytes_at (cdsbase + 32 + abi_tuple_child_offset
      (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j)
      (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs))) s.vs_call_ctx.cc_calldata =
      enc (vyper_to_abi_type env ty) (EL j avs)` by
    (drule_all structural_array_indexed_source >> simp_tac bool_ss [optionTheory.NOT_SOME_NONE,
       optionTheory.SOME_11]) >>
  drule calldata_header_owned_state >>
  disch_then (qspecl_then [`site`,`fn`,`ctx`] strip_assume_tac) >>
  `~t.vs_halted /\ t.vs_current_bb = body_lbl /\ t.vs_inst_idx = 0` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`t = jump_to _ _`,`~s.vs_halted`,`j < LENGTH xs`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  `!op. abi_decoder_operand_live first_var op ==> eval_operand op t = eval_operand op s` by
    (qpat_assum `!op. op <> Var iv /\ _ ==> _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`iv = _`,`cv = _`,`cmp = _`,`done = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     first_x_assum irule >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
  `eval_operand (Var q) t = SOME (n2w slot) /\
    eval_operand src t = SOME (n2w cdsbase) /\
    eval_operand (Var root) t = SOME (n2w d)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live first_var op ==> _`,
       `abi_decoder_operand_live first_var (Var q)`,
       `abi_decoder_operand_live first_var src`,
       `abi_decoder_operand_live first_var (Var root)`,
       `lookup_var q s = _`,`lookup_var root s = _`,`eval_operand src s = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[eval_operand_def]) >>
  `abi_decoder_operand_live body_st.cs_next_var src /\
    abi_decoder_operand_live body_st.cs_next_var (Var root)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`first_var+4 <= body_st.cs_next_var`,
       `abi_decoder_operand_live first_var src`,
       `abi_decoder_operand_live first_var (Var root)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[abi_decoder_operand_live_mono, DECIDE ``a+4 <= b ==> a <= b``]) >>
  `mload (w2n (n2w slot : bytes32)) t = n2w j` by
    (qpat_assum `mload slot t = _` mp_tac >>
     qpat_assum `slot+32 < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `slot < dimword (:256)` by decide_tac >> simp[]) >>
  drule_all calldata_element_setup_repeat >> strip_tac >>
  `32 + j * type_memory_size tv + type_memory_size tv <= outsz /\
    d + 32 + j * type_memory_size tv < dimword (:256) /\
    type_memory_size tv < dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`j < LENGTH xs`,`LENGTH xs <= maxn`,`outsz = _`,
       `d+outsz < dimword (:256)`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `j+1 <= maxn /\ 1 <= maxn` by decide_tac >>
     `((j+1) * type_memory_size tv <= maxn * type_memory_size tv) /\
       (1 * type_memory_size tv <= maxn * type_memory_size tv)` by
       metis_tac[LESS_MONO_MULT] >>
     rule_assum_tac (PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_LEFT_1, MULT_RIGHT_1]) >>
     decide_tac) >>
  `!x. abi_decoder_operand_live first_var (Var x) ==>
       ~MEM x [iv;cv;cmp;done]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`iv = _`,`cv = _`,`cmp = _`,`done = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[LESS_EQ_REFL, DECIDE ``n <= n+1 /\ n <= n+2 /\ n <= n+3``]) >>
  `ptr_covers H u root t outsz` by
    (`~MEM root [iv;cv;cmp;done]` by
       (qpat_assum `!x. abi_decoder_operand_live first_var (Var x) ==> _` mp_tac >>
        qpat_assum `abi_decoder_operand_live first_var (Var root)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_assum `!x. ~MEM x [iv;cv;cmp;done] ==> _` drule >> strip_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var root t = _`,`FLOOKUP H root = _`,
        `op_taint u (Var root) = _`,`ptr_covers G tn root s outsz`,`outsz = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[decoderGhostFramePtrTheory.ptr_covers_frame]) >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!x. abi_decoder_operand_live first_var (Var x) ==> _`,
       `!x. ~MEM x [iv;cv;cmp;done] ==> _`,
       `abi_decoder_operand_live first_var src`,`op_taint tn src = {}`,
       `op_prov G src = NONE`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `src` >>
     simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `lookup_var q t = SOME (n2w slot) /\ lookup_var root t = SOME (n2w d)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`eval_operand (Var q) t = _`,`eval_operand (Var root) t = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[eval_operand_def]) >>
  `not_fresh_at body_st q /\ not_fresh_at body_st root /\
    (!x. src = Var x ==> not_fresh_at body_st x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decoder_operand_live first_var (Var q)`,
       `abi_decoder_operand_live body_st.cs_next_var (Var root)`,
       `abi_decoder_operand_live body_st.cs_next_var src`,
       `first_var+4 <= body_st.cs_next_var`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[calldata_operand_live_not_fresh, abi_decoder_operand_live_mono,
       DECIDE ``a+4 <= b ==> a <= b``]) >>
  `j < dimword (:256) /\
    (!a. slot <= a /\ a < slot+32 ==> a NOTIN u.t_mem)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`j < LENGTH xs`,`LENGTH xs < dimword (:256)`,
       `DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem`,`u.t_mem = tn.t_mem`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[DISJOINT_DEF, EXTENSION] >> metis_tac[LESS_TRANS]) >>
  drule_all calldata_array_element_setup_endpoint_ptr_core >>
  disch_then (qspecl_then [`ARB`,`ctx`,`PG`,`\g r. F`] strip_assume_tac) >>
  rename1 `SND (SND ops) = Var child` >>
  rename1 `op_taint u' (FST ops) = {}` >>
  qabbrev_tac `r = t' with vs_inst_idx := LENGTH middle.cs_current_insts` >>
  `LENGTH (emitted_insts body_st middle) + t.vs_inst_idx =
     LENGTH middle.cs_current_insts` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`inst_extends body_st middle`,`body_st.cs_current_insts = []`,`t.vs_inst_idx = 0`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[emitted_insts_def, inst_extends_def]) >>
  `ptr_covers H' u' child r (type_memory_size tv)` by
    (unabbrev_all_tac >>
     qpat_assum `ptr_covers H' u' child _ _` mp_tac >>
     qpat_assum `LENGTH (emitted_insts body_st middle) + _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `cs_extends middle end_st` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[abiDecoderAppendTheory.cs_extends_abi_decode]) >>
  `cs_extends body_st middle` by
    (qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_shape >>
     simp[abi_decode_source_opcode_def] >> strip_tac >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code body_st middle fn /\ fn_has_code middle end_st fn` by
    (drule_all fn_has_code_split >> simp_tac bool_ss []) >>
  `abi_decode_sim ctx fn t r /\ ~r.vs_halted /\
    r.vs_current_bb = middle.cs_current_bb /\
    r.vs_inst_idx = LENGTH middle.cs_current_insts` by
    (qpat_assum `frag_exec_ptr _ _ _ body_st middle _ _ _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_has_code body_st middle fn`,`~ctx_has_dalloca ctx`,
        `~t.vs_halted`,`t.vs_current_bb = body_lbl`,
        `body_st.cs_current_bb = body_lbl`,`t.vs_inst_idx = 0`,
        `body_st.cs_current_insts = []`,
        `LENGTH (emitted_insts body_st middle) + _ = _`] >>
     simp_tac bool_ss [Abbr `r`] >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> fs[frag_exec_ptr_def] >>
     first_x_assum (qspec_then `fn` mp_tac) >>
     simp[] >> strip_tac >> gvs[abi_decode_sim_def] >> metis_tac[]) >>
  `r.vs_memory = t.vs_memory /\ r.vs_call_ctx = t.vs_call_ctx /\
    r.vs_data_section = t.vs_data_section /\ r.vs_allocas = t.vs_allocas /\
    r.vs_alloca_next = t.vs_alloca_next /\
    alloca_inv r /\ alloca_frontier_inv ctx fn site r` by
    (simp_tac bool_ss [Abbr `r`] >>
     qpat_assum `abi_decoder_address_frame body_st.cs_next_var t t'` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`alloca_inv t <=> _`,`alloca_inv s`,
        `alloca_frontier_inv ctx fn site t <=> _`,`alloca_frontier_inv ctx fn site s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `alloca_inv t /\ alloca_frontier_inv ctx fn site t` by metis_tac[] >>
     gvs[abi_decoder_address_frame_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, allocaBudgetPropsTheory.remaining_alloca_budget_def] >>
     metis_tac[]) >>
  `middle.cs_next_var <= end_st.cs_next_var` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     mp_tac (cj 1 abiDecoderCountersTheory.abi_decoder_vars_mono_mutual) >>
     simp_tac bool_ss [abiDecoderCountersTheory.abi_decoder_vars_mono_def] >>
     disch_then (qspecl_then
       [`SND (SND ops)`,`FST (SND ops)`,`CALLDATALOAD`,`Lit 0w`,
        `type_to_abi_dec_info sf ce ty`,`middle`] mp_tac) >>
     pure_asm_rewrite_tac [pairTheory.SND] >> simp[]) >>
  `fresh_vars_wrt limit t` by
    (qpat_assum `t = jump_to _ _` mp_tac >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`fresh_vars_wrt limit s`,`iv = _`,`cv = _`,`cmp = _`,`done = _`,
        `first_var+4 <= body_st.cs_next_var`,`end_st.cs_next_var < limit.cs_next_var`,
        `middle.cs_next_var <= end_st.cs_next_var`] >>
     qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >> irule (cj 1 decoder_index_header_replay_frame) >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     gvs[] >> decide_tac) >>
  `fresh_vars_wrt limit r` by
    (`middle.cs_next_var <= limit.cs_next_var` by decide_tac >>
     drule_all calldataDynStepTheory.calldata_element_setup_reentry >> strip_tac >>
     `t'' = t'` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`run_inst_seq (emitted_insts body_st middle) t = OK t'`,
          `run_inst_seq (emitted_insts body_st middle) t = OK t''`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
     simp_tac bool_ss [Abbr `r`] >>
     qpat_assum `fresh_vars_wrt limit t''` mp_tac >>
     qpat_assum `t'' = t'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[fresh_vars_wrt_def]) >>
  `ptr_covers H' u' root r outsz` by
    (simp_tac bool_ss [Abbr `r`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers H u root t outsz`,`not_fresh_at body_st root`,
        `!x. not_fresh_at body_st x ==> lookup_var x t' = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     goal_assum (drule_at Any) >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) =
     32 + LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs))` by
    (pure_rewrite_tac[canonical_array_tuple] >>
     simp_tac (srw_ss()) [LENGTH_APPEND, enc_number_def, LENGTH_word_to_bytes]) >>
  `mem_bytes_at (cdsbase+32)
      (LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs)))
      t.vs_call_ctx.cc_calldata =
      enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs) /\
    cdsbase+32 + LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs)) < dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`mem_bytes_at cdsbase _ s.vs_call_ctx.cc_calldata = _`,
       `cdsbase + LENGTH _ < dimword (:256)`,
       `LENGTH (enc (Array NONE _) _) = _`, `t.vs_call_ctx = s.vs_call_ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 strip_tac >>
     conj_tac >- (irule EQ_TRANS >>
       qexists_tac `TAKE (LENGTH (enc (Tuple (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty))) (ListV avs)))
         (DROP 32 (mem_bytes_at cdsbase (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) s.vs_call_ctx.cc_calldata))` >>
       conj_tac >- (sym_tac >> simp[mem_bytes_at_window]) >>
       asm_rewrite_tac[] >>
       pure_rewrite_tac[canonical_array_tuple] >>
       simp_tac (srw_ss()) [enc_number_def, LENGTH_word_to_bytes, DROP_APPEND,
         DROP_LENGTH_TOO_LONG, TAKE_LENGTH_ID, Excl "enc_def"]) >>
     decide_tac) >>
  `SUM (MAP abi_member_head_size
       (TAKE j (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)))) =
      j * abi_embedded_static_size ce.ce_struct_fields ty` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `j < LENGTH avs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule abi_decoder_coherent_header >>
     strip_tac >> fs[abi_decoder_header_def] >>
     `TAKE j (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) =
        REPLICATE j (vyper_to_abi_type env ty)` by
       simp[REPLICATE_GENLIST, TAKE_GENLIST, MIN_DEF] >>
     simp[SUM_REPLICATE]) >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    abi_decode_load CALLDATALOAD
      (n2w (cdsbase+32+j * abi_embedded_static_size ce.ce_struct_fields ty) : bytes32) t =
      n2w (abi_tuple_child_offset
        (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j)` by
    (strip_tac >>
     qpat_assum `SUM (MAP abi_member_head_size _) = _`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     irule structural_tuple_indexed_offset_load >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`j < LENGTH avs`, `is_dynamic (vyper_to_abi_type env ty)`,
        `cdsbase+32 + LENGTH _ < dimword (:256)`,
        `mem_bytes_at (cdsbase+32) _ t.vs_call_ctx.cc_calldata = _`,
        `LIST_REL _ (REPLICATE (LENGTH avs) _) avs`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[abi_decode_source_def, EL_REPLICATE, Excl "enc_def"]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
     is_dynamic (vyper_to_abi_type env ty)` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv` mp_tac >>
     qpat_assum `0 < type_slot_size tv` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[abi_decoder_positive_offset]) >>
  `eval_operand (FST (SND ops)) r = SOME (n2w (cdsbase+32+
      abi_tuple_child_offset (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j))` by
    (simp_tac bool_ss [Abbr `r`, eval_operand_def, lookup_var_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand (FST (SND ops)) t' = _`,
        `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = _`,
        `is_dynamic (vyper_to_abi_type env ty) ==> _`,
        `SUM (MAP abi_member_head_size _) = _`, `j < LENGTH avs`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     fs[abiDecoderMemberSliceTheory.abi_tuple_child_offset_def, EL_REPLICATE, eval_operand_def, lookup_var_def,
       GSYM word_add_n2w, Excl "enc_def"]) >>
  `lookup_var child r = SOME (n2w (d+32+j * type_memory_size tv))` by
    (simp_tac bool_ss [Abbr `r`, lookup_var_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operand (SND (SND ops)) t' = _`, `SND (SND ops) = Var child`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[eval_operand_def, lookup_var_def]) >>
  `mem_bytes_at (cdsbase+32+abi_tuple_child_offset
       (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j)
       (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs))) r.vs_call_ctx.cc_calldata =
       enc (vyper_to_abi_type env ty) (EL j avs) /\
    cdsbase+32+abi_tuple_child_offset
       (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j +
       LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) < dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`mem_bytes_at (cdsbase+32+_) _ s.vs_call_ctx.cc_calldata = _`,
        `32+abi_tuple_child_offset _ _ _ + _ <= _`,
        `cdsbase + LENGTH _ < dimword (:256)`,
        `r.vs_call_ctx = t.vs_call_ctx`, `t.vs_call_ctx = s.vs_call_ctx`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 5 strip_tac >>
     conj_tac >- metis_tac[] >> decide_tac) >>
  `lookup_var root r = SOME (n2w d)` by
    (simp_tac bool_ss [Abbr `r`, lookup_var_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var root t = _`, `not_fresh_at body_st root`,
        `!x. not_fresh_at body_st x ==> lookup_var x t' = _ /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `abi_decoder_operand_live middle.cs_next_var (Var root)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decoder_operand_live body_st.cs_next_var (Var root)`,
        `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `base_addr <= d+32+j * type_memory_size tv /\
    d+32+j * type_memory_size tv + type_memory_size tv <= base_addr+owner_cap /\
    d+32+j * type_memory_size tv + type_memory_size tv < dimword (:256)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`base_addr <= d`, `d+outsz <= base_addr+owner_cap`,
        `d+outsz < dimword (:256)`,
        `32+j * type_memory_size tv + type_memory_size tv <= outsz`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lower r /\ lower <= r.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`r.vs_allocas = t.vs_allocas`, `r.vs_alloca_next = t.vs_alloca_next`,
        `t.vs_allocas = s.vs_allocas`, `t.vs_alloca_next = s.vs_alloca_next`,
        `allocas_from lower s`, `lower <= s.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 6 strip_tac >>
     fs[allocas_from_def] >> metis_tac[]) >>
  `value_has_type tv (EL j xs) /\
    vyper_to_abi env ty (EL j xs) = SOME (EL j avs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`EVERY (value_has_type tv) xs`, `j < LENGTH xs`,
        `!i. i < LENGTH xs ==> vyper_to_abi env ty (EL i xs) = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[EVERY_EL] >> metis_tac[]) >>
  `FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`r.vs_allocas = s.vs_allocas`, `FLOOKUP s.vs_allocas oid = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
  `!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`r.vs_allocas = s.vs_allocas`, `r.vs_alloca_next = s.vs_alloca_next`,
        `!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\ FLOOKUP s.vs_allocas id = _ ==> _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `compile_abi_decode_to_buf (Var child) (FST (SND ops)) CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decoder_operand_live middle.cs_next_var (Var child)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`compile_abi_decode_to_buf _ _ _ _ _ middle = _`,
        `SND (SND ops) = Var child`,
        `abi_decoder_operand_live middle.cs_next_var (SND (SND ops))`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[]) >>
  `end_st.cs_next_var <= limit.cs_next_var` by decide_tac >>
  qpat_assum `!i r G tn child childsrc e srcpos. _`
    (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ child _ _`)) >>
  disch_then (qspecl_then
    [`j`, `d + 32 + j * type_memory_size tv`,
     `cdsbase + 32 + abi_tuple_child_offset
       (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs j`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST
    [first_assum ACCEPT_TAC, disj2_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (qx_choose_then `child_end`
    (qx_choose_then `childG` (qx_choose_then `childtn`
      (qx_choose_then `childfp` strip_assume_tac)))) >>
  `abi_footprint_disjoint d 32
    ((d + 32 + j * type_memory_size tv,type_memory_size tv)::childfp)` by
    (qpat_assum `abi_footprint_disjoint base_addr owner_cap childfp` mp_tac >>
     qpat_assum `base_addr <= d` mp_tac >>
     qpat_assum `d + outsz <= base_addr + owner_cap` mp_tac >>
     qpat_assum `outsz = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_footprint_disjoint_def] >> rpt strip_tac >> simp[] >>
     first_x_assum drule >> decide_tac) >>
  `mem_bytes_at d 32 child_end.vs_memory = mem_bytes_at d 32 r.vs_memory` by
    (irule abi_decode_footprint_frame_slice >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `mem_word_at d child_end.vs_memory = n2w (LENGTH xs)` by
    (qpat_assum `mem_bytes_at d 32 child_end.vs_memory = _` mp_tac >>
     qpat_assum `r.vs_memory = _` mp_tac >>
     qpat_assum `t.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `mem_word_at d s.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[mem_word_at_def, mem_bytes_at_def]) >>
  `!a. d <= a /\ a < d+32 ==> a NOTIN childtn.t_mem` by
    (qpat_assum `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> _` mp_tac >>
     qpat_assum `childtn.t_mem SUBSET u'.t_mem` mp_tac >>
     qpat_assum `u'.t_mem = u.t_mem` mp_tac >>
     qpat_assum `u.t_mem = tn.t_mem` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule representationCleanPtrTheory.robust_mem_word_at_clean >>
     gvs[SUBSET_DEF] >> metis_tac[]) >>
  `!mem. mem_agree_outside childtn.t_mem child_end.vs_memory mem ==>
    mem_word_at d mem = n2w (LENGTH xs)` by
    (qpat_assum `!a. d <= a /\ a < d+32 ==> _` mp_tac >>
     qpat_assum `mem_word_at d child_end.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `mem_bytes_at d 32 mem = mem_bytes_at d 32 child_end.vs_memory` by
       (irule LIST_EQ >> simp[valueEncodingProofsTheory.EL_mem_bytes_at] >> rpt strip_tac >>
        `d + x NOTIN childtn.t_mem` by (first_x_assum irule >> decide_tac) >>
        qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >>
        disch_then (qspec_then `d+x` mp_tac) >>
        simp[LIST_EQ_REWRITE, valueEncodingProofsTheory.EL_mem_bytes_at]) >>
     qpat_assum `mem_word_at d child_end.vs_memory = _` mp_tac >>
     qpat_assum `mem_bytes_at d 32 mem = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[mem_word_at_def, mem_bytes_at_def]) >>
  `!i. i < j ==> abi_footprint_disjoint
    (d+32+i*type_memory_size tv) (type_memory_size tv)
    ((d+32+j*type_memory_size tv,type_memory_size tv)::childfp)` by
    (qpat_assum `abi_footprint_disjoint base_addr owner_cap childfp` mp_tac >>
     qpat_assum `base_addr <= d` mp_tac >>
     qpat_assum `d + outsz <= base_addr + owner_cap` mp_tac >>
     qpat_assum `outsz = _` mp_tac >>
     qpat_assum `j < LENGTH xs` mp_tac >>
     qpat_assum `LENGTH xs <= maxn` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `i+1 <= j` by decide_tac >>
     `(i+1)*type_memory_size tv <= j*type_memory_size tv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     `i*type_memory_size tv + type_memory_size tv <= j*type_memory_size tv` by
       (qpat_x_assum `(i+1)*_ <= _` mp_tac >>
        simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
     `j*type_memory_size tv <= maxn*type_memory_size tv` by
       (irule LESS_MONO_MULT >> decide_tac) >>
     simp[abi_footprint_disjoint_def] >> rpt strip_tac >> simp[] >>
     qpat_x_assum `abi_footprint_disjoint _ _ childfp` mp_tac >>
     simp[abi_footprint_disjoint_def] >>
     disch_then (drule_at Any) >> decide_tac) >>
  `!i. i < j ==>
    val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) child_end.vs_memory /\
    !mem. mem_agree_outside childtn.t_mem child_end.vs_memory mem ==>
      val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem` by
    (gen_tac >> disch_tac >>
     `value_has_type tv (EL i xs)` by
       (qpat_assum `EVERY (value_has_type tv) xs` mp_tac >>
        qpat_assum `i < j` mp_tac >> qpat_assum `j < LENGTH xs` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[EVERY_EL] >> metis_tac[LESS_TRANS]) >>
     `val_wf tv (EL i xs) /\ val_footprint tv (EL i xs) <= type_memory_size tv` by
       ((qpat_assum `value_has_type tv (EL i xs)` mp_tac >>
        rpt (pop_assum kall_tac) >>
        metis_tac[value_has_type_memory_wf, exprSimTheory.val_footprint_le])) >>
     `!mem. mem_agree_outside u'.t_mem r.vs_memory mem ==>
       val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`!i. i < j ==> val_in_memory _ _ _ s.vs_memory /\ _`,
          `i < j`, `r.vs_memory = _`, `t.vs_memory = s.vs_memory`,
          `u'.t_mem = u.t_mem`, `u.t_mem = tn.t_mem`] >>
        rpt (pop_assum kall_tac) >> gvs[] >> metis_tac[]) >>
     `abi_footprint_disjoint (d+32+i*type_memory_size tv)
       (val_footprint tv (EL i xs))
       ((d+32+j*type_memory_size tv,type_memory_size tv)::childfp)` by
       (qpat_assum `!i. i < j ==> abi_footprint_disjoint _ _ _` mp_tac >>
        qpat_assum `val_footprint tv (EL i xs) <= _` mp_tac >>
        qpat_assum `i < j` mp_tac >> rpt (pop_assum kall_tac) >>
        rpt strip_tac >>
        irule abiEncoderArrayFrameTheory.abi_footprint_disjoint_subwindow >>
        qexistsl_tac [`d+32+i*type_memory_size tv`, `type_memory_size tv`] >> simp[]) >>
     irule robust_value_footprint_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl_tac [`r`, `u'`] >> simp[]) >>
  `FLOOKUP child_end.vs_allocas index_id = SOME (slot,32)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!id. id < middle.cs_next_id \/ _ ==> FLOOKUP child_end.vs_allocas id = _`,
       `index_id < middle.cs_next_id`, `r.vs_allocas = s.vs_allocas`,
       `FLOOKUP s.vs_allocas index_id = _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `abi_footprint_disjoint slot 32 childfp` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!p k. MEM (p,k) childfp ==> _`, `alloca_inv child_end`,
       `FLOOKUP child_end.vs_allocas index_id = _`, `index_id < middle.cs_next_id`] >>
     rpt (pop_assum kall_tac) >>
     simp[abi_footprint_disjoint_def, alloca_inv_def, allocas_non_overlapping_def] >>
     rpt strip_tac >>
     qpat_x_assum `!p k. MEM (p,k) childfp ==> _` drule >> strip_tac >>
     `index_id <> id` by decide_tac >> metis_tac[]) >>
  `abi_footprint_disjoint slot 32
    ((d+32+j*type_memory_size tv,type_memory_size tv)::childfp)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_footprint_disjoint slot 32 childfp`,
       `slot+32 <= base_addr \/ base_addr+owner_cap <= slot`,
       `base_addr <= d+32+j*type_memory_size tv`,
       `d+32+j*type_memory_size tv+type_memory_size tv <= base_addr+owner_cap`] >>
     rpt (pop_assum kall_tac) >> simp[abi_footprint_disjoint_def] >>
     rpt strip_tac >> simp[] >> first_x_assum drule >> decide_tac) >>
  `abi_decoder_operand_live middle.cs_next_var (Var q)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decoder_operand_live first_var (Var q)`,
       `first_var+4 <= body_st.cs_next_var`,
       `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >>
     metis_tac[abi_decoder_operand_live_mono, DECIDE ``a+4 <= b /\ b <= c ==> a <= c``]) >>
  `not_fresh_at middle q` by
    (qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var q)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[calldata_operand_live_not_fresh]) >>
  `lookup_var q child_end = lookup_var q r /\
    FLOOKUP childG q = FLOOKUP H' q /\
    op_taint childtn (Var q) = op_taint u' (Var q)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live middle.cs_next_var op ==>
          eval_operand op child_end = _`,
       `!x. not_fresh_at middle x ==> FLOOKUP childG x = _ /\ _`,
       `abi_decoder_operand_live middle.cs_next_var (Var q)`, `not_fresh_at middle q`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[eval_operand_def]) >>
  `ptr_covers H' u' q r 32` by
    (simp_tac bool_ss [Abbr `r`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers H u q t 32`,`not_fresh_at body_st q`,
        `!x. not_fresh_at body_st x ==> lookup_var x t' = _ /\ _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     goal_assum (drule_at Any) >> fs[lookup_var_def] >> metis_tac[]) >>
  `ptr_covers childG childtn q child_end 32` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`ptr_covers H' u' q r 32`, `lookup_var q child_end = _`,
       `FLOOKUP childG q = _`, `op_taint childtn (Var q) = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`H'`, `r`, `u'`] >> simp[]) >>
  `abi_decoder_operand_live middle.cs_next_var (Var elem_idx) /\
    not_fresh_at middle elem_idx` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _`,
       `FST ops = Var elem_idx`] >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  `eval_operand (Var elem_idx) child_end = eval_operand (Var elem_idx) r /\
    FLOOKUP childG elem_idx = FLOOKUP H' elem_idx /\
    op_taint childtn (Var elem_idx) = op_taint u' (Var elem_idx)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live middle.cs_next_var op ==>
          eval_operand op child_end = _`,
       `!x. not_fresh_at middle x ==> FLOOKUP childG x = _ /\ _`,
       `abi_decoder_operand_live middle.cs_next_var (Var elem_idx)`,
       `not_fresh_at middle elem_idx`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> metis_tac[]) >>
  `eval_operand (Var elem_idx) child_end = SOME (n2w j) /\
    op_taint childtn (Var elem_idx) = {} /\
    op_prov childG (Var elem_idx) = NONE` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`eval_operand (FST ops) t' = _`, `FST ops = Var elem_idx`,
       `op_taint u' (FST ops) = {}`, `op_prov H' (FST ops) = NONE`,
       `eval_operand (Var elem_idx) child_end = _`,
       `FLOOKUP childG elem_idx = _`, `op_taint childtn (Var elem_idx) = _`] >>
     simp_tac bool_ss [Abbr `r`] >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[op_prov_def, eval_operand_def, lookup_var_def]) >>
  `lookup_var q r = SOME (n2w slot)` by
    (simp_tac bool_ss [Abbr `r`, lookup_var_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`lookup_var q t = _`, `not_fresh_at body_st q`,
        `!x. not_fresh_at body_st x ==> lookup_var x t' = _ /\ _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[lookup_var_def] >> metis_tac[]) >>
  `lookup_var q child_end = SOME (n2w slot)` by
    (qpat_assum `lookup_var q child_end = _` mp_tac >>
     qpat_assum `lookup_var q r = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `middle.cs_next_var <= end_st.cs_next_var` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[abiDecoderCountersTheory.abi_decoder_variable_counter]) >>
  `q <> nv` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decoder_operand_live middle.cs_next_var (Var q)`,
       `middle.cs_next_var <= end_st.cs_next_var`,
       `nv = STRING #"%" (toString end_st.cs_next_var)`] >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decoder_operand_live_def] >> rpt strip_tac >>
     gvs[abi_decoder_older_vars_def] >> metis_tac[]) >>
  `lookup_block child_end.vs_current_bb fn.fn_blocks = SOME back_bb` by
    (qpat_assum `child_end.vs_current_bb = _` mp_tac >>
     qpat_assum `lookup_block end_st.cs_current_bb fn.fn_blocks = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp child_end` by simp[] >>
  `DISJOINT ({}:num set) childtn.t_mem` by simp[] >>
  drule_all decoder_index_backedge_ptr_core_uniform >>
  disch_then (qspec_then `PG`
    (qx_choose_then `backG` (qx_choose_then `backtn`
      (qx_choose_then `backstate` strip_assume_tac)))) >>
  `fresh_vars_wrt limit backstate /\
    backstate.vs_allocas = child_end.vs_allocas /\
    backstate.vs_alloca_next = child_end.vs_alloca_next /\
    backstate.vs_call_ctx = child_end.vs_call_ctx` by
    (drule_all decoder_index_backedge_replay_frame >> simp_tac bool_ss []) >>
  `~backstate.vs_halted /\ backstate.vs_current_bb = hdr /\ backstate.vs_inst_idx = 0` by
    (qpat_assum `backstate = _` mp_tac >>
     qpat_assum `~child_end.vs_halted` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def]) >>
  `eval_operand (Var q) child_end = SOME (n2w slot : bytes32) /\
    Var q <> Var nv` by
    (qpat_assum `lookup_var q child_end = SOME (n2w slot)` mp_tac >>
     qpat_assum `q <> nv` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[eval_operand_def]) >>
  `abi_decode_sim ctx fn child_end backstate` by
    (drule_all abi_decode_backedge_sim >>
     qpat_assum `backstate = _` mp_tac >>
     qpat_assum `slot+32 < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `slot < dimword (:256)` by decide_tac >>
     gvs[wordsTheory.w2n_n2w]) >>
  `alloca_inv backstate /\ alloca_frontier_inv ctx fn site backstate /\
    allocas_from lower backstate` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`alloca_inv child_end`, `alloca_frontier_inv ctx fn site child_end`,
       `allocas_from lower child_end`,
       `backstate.vs_allocas = child_end.vs_allocas`,
       `backstate.vs_alloca_next = child_end.vs_alloca_next`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_def, allocaBudgetPropsTheory.remaining_alloca_budget_def, allocas_from_def] >>
     metis_tac[]) >>
  `MEM (w2n (n2w slot : bytes32),32) [(slot,32)]` by
    (qpat_assum `slot+32 < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     `slot < dimword (:256)` by decide_tac >> simp[]) >>
  drule abi_decode_backedge_observations >>
  disch_then (qspecl_then [`n2w (SUC j) : bytes32`, `child_end`, `nv`, `hdr`] mp_tac) >>
  `slot < dimword (:256)` by
    (qpat_assum `slot+32 < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  simp_tac (srw_ss()) [wordsTheory.w2n_n2w] >> strip_tac >>
  `abi_decode_footprint_frame [(slot,32)] child_end backstate` by
    (qpat_assum `abi_decode_footprint_frame [(slot,32)] _ _` mp_tac >>
     qpat_assum `backstate = _` mp_tac >>
     qpat_assum `slot < dimword (:256)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `abi_footprint_disjoint d outsz [(slot,32)]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`slot+32 <= base_addr \/ base_addr+owner_cap <= slot`,
       `base_addr <= d`, `d+outsz <= base_addr+owner_cap`] >>
     rpt (pop_assum kall_tac) >> simp[abi_footprint_disjoint_def] >> decide_tac) >>
  `!i. i < SUC j ==>
    val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) backstate.vs_memory /\
    !mem. mem_agree_outside backtn.t_mem backstate.vs_memory mem ==>
      val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem` by
    (gen_tac >> disch_tac >>
     `i <= j` by decide_tac >>
     `value_has_type tv (EL i xs)` by
       (qpat_assum `EVERY (value_has_type tv) xs` mp_tac >>
        qpat_assum `i <= j` mp_tac >> qpat_assum `j < LENGTH xs` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[EVERY_EL] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
     `val_wf tv (EL i xs) /\ val_footprint tv (EL i xs) <= type_memory_size tv` by
       (qpat_assum `value_has_type tv (EL i xs)` mp_tac >>
        rpt (pop_assum kall_tac) >>
        metis_tac[value_has_type_memory_wf, exprSimTheory.val_footprint_le]) >>
     `!mem. mem_agree_outside childtn.t_mem child_end.vs_memory mem ==>
       val_in_memory tv (EL i xs) (d+32+i*type_memory_size tv) mem` by
       (Cases_on `i = j`
        >- (qpat_x_assum `i = j` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        `i < j` by decide_tac >>
        qpat_assum `!i. i < j ==> val_in_memory _ _ _ child_end.vs_memory /\ _` drule >>
        simp_tac bool_ss []) >>
     `abi_footprint_disjoint (d+32+i*type_memory_size tv)
       (val_footprint tv (EL i xs)) [(slot,32)]` by
       (map_every (fn pat => qpat_assum pat mp_tac)
         [`abi_footprint_disjoint d outsz [(slot,32)]`,
          `val_footprint tv (EL i xs) <= _`, `outsz = _`,
          `i <= j`, `j < LENGTH xs`, `LENGTH xs <= maxn`] >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        `i+1 <= maxn` by decide_tac >>
        `(i+1)*type_memory_size tv <= maxn*type_memory_size tv` by
          (irule LESS_MONO_MULT >> decide_tac) >>
        `i*type_memory_size tv + type_memory_size tv <= maxn*type_memory_size tv` by
          (qpat_assum `(i+1)*_ <= _` mp_tac >>
           simp_tac bool_ss [RIGHT_ADD_DISTRIB, MULT_LEFT_1]) >>
        irule abiEncoderArrayFrameTheory.abi_footprint_disjoint_subwindow >>
        qexistsl_tac [`d`, `outsz`] >>
        simp[]) >>
     irule robust_value_footprint_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl_tac [`child_end`, `childtn`] >> simp[]) >>
  `abi_footprint_disjoint d 32 [(slot,32)]` by
    (qpat_assum `abi_footprint_disjoint d outsz [(slot,32)]` mp_tac >>
     qpat_assum `outsz = _` mp_tac >> rpt (pop_assum kall_tac) >>
     simp[abi_footprint_disjoint_def] >> decide_tac) >>
  `mem_bytes_at d 32 backstate.vs_memory = mem_bytes_at d 32 child_end.vs_memory` by
    (irule abi_decode_footprint_frame_slice >> goal_assum (drule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `mem_word_at d backstate.vs_memory = n2w (LENGTH xs)` by
    (qpat_assum `mem_bytes_at d 32 backstate.vs_memory = _` mp_tac >>
     qpat_assum `mem_word_at d child_end.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[mem_word_at_def, mem_bytes_at_def]) >>
  `!mem. mem_agree_outside backtn.t_mem backstate.vs_memory mem ==>
    mem_word_at d mem = n2w (LENGTH xs)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!a. d <= a /\ a < d+32 ==> a NOTIN childtn.t_mem`,
       `backtn.t_mem SUBSET childtn.t_mem`, `mem_word_at d backstate.vs_memory = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `mem_bytes_at d 32 mem = mem_bytes_at d 32 backstate.vs_memory` by
       (irule LIST_EQ >> simp[valueEncodingProofsTheory.EL_mem_bytes_at] >> rpt strip_tac >>
        `d+x NOTIN backtn.t_mem` by
          (fs[SUBSET_DEF] >>
           `d <= d+x /\ d+x < d+32` by decide_tac >> metis_tac[]) >>
        qpat_x_assum `mem_agree_outside _ _ _` mp_tac >>
        simp[mem_agree_outside_def] >> disch_then (qspec_then `d+x` mp_tac) >>
        simp[LIST_EQ_REWRITE, valueEncodingProofsTheory.EL_mem_bytes_at]) >>
     qpat_assum `mem_word_at d backstate.vs_memory = _` mp_tac >>
     qpat_assum `mem_bytes_at d 32 mem = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[mem_word_at_def, mem_bytes_at_def]) >>
  `!op. abi_decoder_operand_live first_var op ==>
    eval_operand op r = eval_operand op t` by
    (simp_tac bool_ss [Abbr `r`] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!op. abi_decoder_operand_live body_st.cs_next_var op ==> eval_operand op t' = _`,
        `first_var+4 <= body_st.cs_next_var`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `abi_decoder_operand_live body_st.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `first_var` >> simp[]) >>
     qpat_x_assum `!op. abi_decoder_operand_live body_st.cs_next_var op ==> _` drule >>
     Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
  `!op. abi_decoder_operand_live first_var op ==>
    eval_operand op child_end = eval_operand op s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live first_var op ==> eval_operand op r = _`,
       `!op. abi_decoder_operand_live first_var op ==> eval_operand op t = _`,
       `!op. abi_decoder_operand_live middle.cs_next_var op ==> eval_operand op child_end = _`,
       `first_var+4 <= body_st.cs_next_var`,
       `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >>
     `abi_decoder_operand_live middle.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `first_var` >> simp[]) >>
     metis_tac[]) >>
  `!op. abi_decoder_operand_live first_var op ==> op <> Var nv` by
    (qpat_assum `nv = _` mp_tac >>
     qpat_assum `first_var+4 <= body_st.cs_next_var` mp_tac >>
     qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _` mp_tac >>
     qpat_assum `middle.cs_next_var <= end_st.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >> Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[DECIDE ``a+4<=b /\ b<=c /\ c<=d ==> a<=d``]) >>
  `!op. abi_decoder_operand_live first_var op ==>
    eval_operand op backstate = eval_operand op s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live first_var op ==> eval_operand op child_end = _`,
       `!op. abi_decoder_operand_live first_var op ==> op <> Var nv`,
       `backstate = _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_x_assum `!op. abi_decoder_operand_live first_var op ==> eval_operand op child_end = _` drule >>
     Cases_on `op` >> simp[eval_operand_def, lookup_var_def, jump_to_def,
       mstore_def, write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `root <> nv` by
    (qpat_assum `!op. abi_decoder_operand_live first_var op ==> op <> Var nv` mp_tac >>
     qpat_assum `abi_decoder_operand_live first_var (Var root)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `ptr_covers backG backtn root backstate outsz` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`ptr_covers childG childtn root child_end outsz`,
       `!x. x <> nv ==> lookup_var x backstate = _ /\ _`, `root <> nv`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl_tac [`childG`, `child_end`, `childtn`] >> metis_tac[]) >>
  `!x. not_fresh_at body_st x ==> not_fresh_at middle x` by
    (qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >>
     metis_tac[calldata_operand_live_not_fresh, abi_decoder_operand_live_mono]) >>
  `!x. not_fresh_at body_st x ==> x <> nv` by
    (qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _` mp_tac >>
     qpat_assum `middle.cs_next_var <= end_st.cs_next_var` mp_tac >>
     qpat_assum `nv = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands >>
     strip_tac >>
     fs[GSYM calldata_operand_live_not_fresh, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `!x. not_fresh_at body_st x ==> FLOOKUP backG x = FLOOKUP H x /\
    op_taint backtn (Var x) = op_taint u (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!x. not_fresh_at body_st x ==> not_fresh_at middle x`,
       `!x. not_fresh_at body_st x ==> x <> nv`,
       `!x. x <> nv ==> lookup_var x backstate = _ /\ _`,
       `!x. not_fresh_at middle x ==> FLOOKUP childG x = _ /\ _`,
       `!x. not_fresh_at body_st x ==> lookup_var x t' = _ /\ _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `op_taint backtn src = {} /\ op_prov backG src = NONE` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!x. not_fresh_at body_st x ==> FLOOKUP backG x = _ /\ _`,
       `!x. src = Var x ==> not_fresh_at body_st x`,
       `op_taint u src = {}`, `op_prov H src = NONE`] >>
     rpt (pop_assum kall_tac) >> Cases_on `src` >>
     simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `LENGTH xs - SUC j = n /\ SUC j <= LENGTH xs` by
    (qpat_assum `LENGTH xs - j = SUC n` mp_tac >>
     qpat_assum `j < LENGTH xs` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `backstate.vs_call_ctx = s.vs_call_ctx` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`backstate.vs_call_ctx = child_end.vs_call_ctx`,
       `abi_decode_footprint_frame ((d+32+j*type_memory_size tv,type_memory_size tv)::childfp) r child_end`,
       `r.vs_call_ctx = t.vs_call_ctx`, `t.vs_call_ctx = s.vs_call_ctx`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_footprint_frame_def]) >>
  `abi_decode_load CALLDATALOAD (n2w cdsbase : bytes32) backstate = n2w (LENGTH xs)` by
    (qpat_assum `abi_decode_load CALLDATALOAD (n2w cdsbase : bytes32) s = _` mp_tac >>
     qpat_assum `backstate.vs_call_ctx = s.vs_call_ctx` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_load_def, abi_decode_source_def]) >>
  `eval_operand src backstate = SOME (n2w cdsbase) /\
    lookup_var root backstate = SOME (n2w d) /\ lookup_var q backstate = SOME (n2w slot)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live first_var op ==> eval_operand op backstate = _`,
       `abi_decoder_operand_live first_var src`,
       `abi_decoder_operand_live first_var (Var root)`,
       `abi_decoder_operand_live first_var (Var q)`,
       `eval_operand src s = _`, `lookup_var root s = _`, `lookup_var q s = _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[eval_operand_def]) >>
  `FLOOKUP backstate.vs_allocas oid = SOME (base_addr,owner_cap) /\
    FLOOKUP backstate.vs_allocas index_id = SOME (slot,32)` by
    (qpat_assum `backstate.vs_allocas = child_end.vs_allocas` (fn th => rewrite_tac [th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP backstate.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= backstate.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (qpat_assum `backstate.vs_allocas = child_end.vs_allocas` (fn th => rewrite_tac [th]) >>
     qpat_assum `backstate.vs_alloca_next = child_end.vs_alloca_next` (fn th => rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  `lower <= backstate.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`lower <= s.vs_alloca_next`, `r.vs_alloca_next = s.vs_alloca_next`,
       `r.vs_alloca_next <= child_end.vs_alloca_next`,
       `backstate.vs_alloca_next = child_end.vs_alloca_next`] >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  qpat_x_assum `!j s G tn. _` (qspecl_then [`SUC j`, `backstate`, `backG`, `backtn`] mp_tac) >>
  (impl_tac
   >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
     (qpat_assum `backstate.vs_call_ctx = s.vs_call_ctx` (fn th => rewrite_tac [th]) >>
      first_assum ACCEPT_TAC)])) >>
  disch_then (qx_choose_then `final` (qx_choose_then `finalG`
    (qx_choose_then `finaltn` (qx_choose_then `finalfp` strip_assume_tac)))) >>
  `abi_decode_sim ctx fn s t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     irule abi_decode_ready_header_sim >>
     simp_tac bool_ss [abi_decode_loop_ready_def] >>
     conj_tac >- (qpat_x_assum `ALL_DISTINCT [q;iv;cv;cmp;done]` mp_tac >>
                  simp_tac list_ss []) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`hid`,`Var q`,`CALLDATALOAD`,`n2w slot`,`src`,`n2w cdsbase`] >>
     pure_rewrite_tac [abi_decode_source_opcode_def, eval_operand_def] >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`slot+32 < dimword (:256)`, `mload slot s = n2w j`,
        `abi_decode_load CALLDATALOAD (n2w cdsbase : bytes32) s = n2w (LENGTH xs)`,
        `lookup_var q s = SOME _`, `eval_operand src s = SOME _`,
        `s.vs_inst_idx = 0`, `~s.vs_halted`, `s.vs_current_bb = hdr`,
        `src <> Var iv`, `abi_decode_loop_cfg fn hdr _ _ _ _ _ _ _ _ _ _`,
        `j < LENGTH xs`, `LENGTH xs < dimword (:256)`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     `slot < dimword (:256)` by decide_tac >> simp[wordsTheory.w2n_n2w]) >>
  `abi_decode_sim ctx fn s final` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decode_sim ctx fn s t`, `abi_decode_sim ctx fn t r`,
       `abi_decode_sim ctx fn r child_end`, `abi_decode_sim ctx fn child_end backstate`,
       `abi_decode_sim ctx fn backstate final`] >>
     rpt (pop_assum kall_tac) >> metis_tac[abi_decode_sim_trans]) >>
  `abi_decode_footprint_frame ((d,outsz)::(slot,32)::(childfp ++ finalfp)) r child_end` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `(d+32+j*type_memory_size tv,type_memory_size tv)::childfp` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     simp_tac bool_ss [MEM, MEM_APPEND] >> rpt gen_tac >> strip_tac
     >- (qexistsl_tac [`d`,`outsz`] >>
         map_every (fn pat => qpat_assum pat mp_tac)
           [`j < LENGTH xs`, `LENGTH xs <= maxn`, `outsz = _`,
            `(d',sz) = (d+32+j*type_memory_size tv,type_memory_size tv)`] >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[] >>
         `j+1 <= maxn` by decide_tac >>
         `(j+1)*type_memory_size tv <= maxn*type_memory_size tv` by
           (irule LESS_MONO_MULT >> decide_tac) >>
         qpat_x_assum `(j+1)*type_memory_size tv <= _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         pure_rewrite_tac [RIGHT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac)
     >> qexistsl_tac [`d'`,`sz`] >>
     qpat_assum `MEM (d',sz) childfp` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `abi_decode_footprint_frame ((d,outsz)::(slot,32)::(childfp ++ finalfp)) child_end backstate` by
    (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(slot,32)]` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt (pop_assum kall_tac) >> simp[] >>
     qexistsl_tac [`slot`,`32`] >> simp[]) >>
  `abi_decode_footprint_frame ((d,outsz)::(slot,32)::(childfp ++ finalfp)) backstate final` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `(d,outsz)::(slot,32)::finalfp` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt (pop_assum kall_tac) >>
     rpt gen_tac >> strip_tac >> qexistsl_tac [`d'`,`sz`] >> gvs[]) >>
  `abi_decode_footprint_frame ((d,outsz)::(slot,32)::(childfp ++ finalfp)) s final` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decode_footprint_frame _ r child_end`,
       `abi_decode_footprint_frame _ child_end backstate`,
       `abi_decode_footprint_frame _ backstate final`,
       `r.vs_memory = t.vs_memory`, `t.vs_memory = s.vs_memory`,
       `r.vs_call_ctx = t.vs_call_ctx`, `t.vs_call_ctx = s.vs_call_ctx`,
       `r.vs_data_section = t.vs_data_section`, `t.vs_data_section = s.vs_data_section`] >>
     rpt (pop_assum kall_tac) >> simp[abi_decode_footprint_frame_def]) >>
  `abi_footprint_disjoint base_addr owner_cap (childfp ++ finalfp)` by
    (pure_rewrite_tac [abi_footprint_disjoint_append] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `s.vs_alloca_next <= final.vs_alloca_next` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`r.vs_alloca_next = s.vs_alloca_next`,
       `r.vs_alloca_next <= child_end.vs_alloca_next`,
       `backstate.vs_alloca_next = child_end.vs_alloca_next`,
       `backstate.vs_alloca_next <= final.vs_alloca_next`] >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) ==>
    FLOOKUP final.vs_allocas id = SOME (p,k)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`r.vs_allocas = s.vs_allocas`, `backstate.vs_allocas = child_end.vs_allocas`,
       `!id p k. FLOOKUP r.vs_allocas id = _ ==> FLOOKUP child_end.vs_allocas id = _`,
       `!id p k. FLOOKUP backstate.vs_allocas id = _ ==> FLOOKUP final.vs_allocas id = _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
    FLOOKUP final.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`r.vs_allocas = s.vs_allocas`, `backstate.vs_allocas = child_end.vs_allocas`,
       `!id. _ ==> FLOOKUP child_end.vs_allocas id = FLOOKUP r.vs_allocas id`,
       `!id. _ ==> FLOOKUP final.vs_allocas id = FLOOKUP backstate.vs_allocas id`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!p k. MEM (p,k) (childfp ++ finalfp) ==> ?id.
    middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP final.vs_allocas id = SOME (p,k)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!p k. MEM (p,k) childfp ==> _`, `!p k. MEM (p,k) finalfp ==> _`,
       `backstate.vs_allocas = child_end.vs_allocas`,
       `!id p k. FLOOKUP backstate.vs_allocas id = _ ==> FLOOKUP final.vs_allocas id = _`] >>
     rpt (pop_assum kall_tac) >> simp_tac bool_ss [MEM_APPEND] >> metis_tac[]) >>
  `!op. abi_decoder_operand_live first_var op ==>
    eval_operand op final = eval_operand op s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live first_var op ==> eval_operand op final = _`,
       `!op. abi_decoder_operand_live first_var op ==> eval_operand op backstate = _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `!x. not_fresh_at body_st x /\ ~MEM x [iv;cv;cmp;done] ==>
    FLOOKUP finalG x = FLOOKUP G x /\ op_taint finaltn (Var x) = op_taint tn (Var x)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!x. not_fresh_at body_st x /\ ~MEM x [iv;cv;cmp;done] ==> FLOOKUP finalG x = _ /\ _`,
       `!x. not_fresh_at body_st x ==> FLOOKUP backG x = _ /\ _`,
       `!x. ~MEM x [iv;cv;cmp;done] ==> lookup_var x t = _ /\ _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  qpat_x_assum `!x. not_fresh_at body_st x /\ ~MEM x [iv;cv;cmp;done] ==> FLOOKUP finalG x = _ /\ _`
    (assume_tac o SIMP_RULE list_ss []) >>
  `finaltn.t_mem SUBSET tn.t_mem /\ finaltn.t_stor = tn.t_stor /\
    finaltn.t_trans = tn.t_trans /\ finaltn.t_imm = tn.t_imm` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`finaltn.t_mem SUBSET backtn.t_mem`, `backtn.t_mem SUBSET childtn.t_mem`,
       `childtn.t_mem SUBSET u'.t_mem`, `u'.t_mem = u.t_mem`, `u.t_mem = tn.t_mem`,
       `finaltn.t_stor = _`, `backtn.t_stor = _`, `childtn.t_stor = _`, `u'.t_stor = _`, `u.t_stor = _`,
       `finaltn.t_trans = _`, `backtn.t_trans = _`, `childtn.t_trans = _`, `u'.t_trans = _`, `u.t_trans = _`,
       `finaltn.t_imm = _`, `backtn.t_imm = _`, `childtn.t_imm = _`, `u'.t_imm = _`, `u.t_imm = _`] >>
     rpt (pop_assum kall_tac) >> metis_tac[SUBSET_TRANS]) >>
  `allocas_from lower t` by
    (qpat_assum `t.vs_allocas = s.vs_allocas` mp_tac >>
     qpat_assum `allocas_from lower s` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[allocas_from_def] >> metis_tac[]) >>
  `!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H' u' r) ==>
    !fuel. ptr_safe_run D lower fuel ctx fn PG H u t` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!D lower ctx' func. _`, `fn_has_code body_st middle fn`,
       `allocas_from lower t`, `~ctx_has_dalloca ctx`,
       `t.vs_current_bb = body_lbl`, `body_st.cs_current_bb = body_lbl`,
       `t.vs_inst_idx = 0`, `body_st.cs_current_insts = []`] >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG finalG finaltn final) ==>
    !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!D. _ ==> !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s`,
       `!D. _ ==> !fuel. ptr_safe_run D lower fuel ctx fn PG H u t`,
       `!D. _ ==> !fuel. ptr_safe_run D lower fuel ctx fn PG H' u' r`,
       `!D. _ ==> !fuel. ptr_safe_run D lower fuel ctx fn PG childG childtn child_end`,
       `!D. _ ==> !fuel. ptr_safe_run D lower fuel ctx fn PG backG backtn backstate`] >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  qexistsl_tac [`final`, `finalG`, `finaltn`, `childfp ++ finalfp`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
