Theory calldataScratchLoopPtr
Ancestors
  calldataScratchArrayPtr decoderScratchLoopPtr decoderScratchLoopCorePtr
  decoderGhostFramePtr robustCopyTransportPtr valueEncodingTyping abiScratchDecoderArrayIteration
  abiScratchDecoderLoopFinite abiScratchDecoderLoopContext abiDecoderRecursiveLoopContext
  abiScratchDecoderLoopInvariant abiScratchDecoderContract abiScratchEncoderContract
  abiDecoderContract abiDecoderAllocation abiDecoderReentry abiDecoderExecution
  abiDecoderLoop abiDecoderProtectedScratch abiDecoderValidArrayMemory
  abiDecoderFrame abiScratchEffect abiScratchFootprint
  compileEnv ptrDiscipline venomState words list arithmetic

Theorem calldata_scratch_loop_iteration_prefix_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var q) src (Var root)
    CALLDATALOAD (Lit 0w) hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs CALLDATALOAD (Lit 0w)
    (Var q) src (Var root) sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s /\
  fn_inst_ids_distinct func /\ j < LENGTH vs /\ n <= j /\
  (!k. k < n ==> !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) mem) /\
  ptr_covers G tn root s (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ptr_covers G tn q s 32 /\ DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?t H u.
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
      first last lo hi next limit_st b cap initial hdr (SUC j) t /\
    abi_decode_sim ctx func s t /\
    ptr_covers H u root t (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    ptr_covers H u q t 32 /\ mload slot t = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\ DISJOINT P u.t_mem /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\ allocas_from lower t /\
    (!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!k a. k IN abi_decoder_ids first last /\ ~(k IN abi_decoder_ids lo hi) /\
      FLOOKUP s.vs_allocas k = SOME (a,32) ==>
      FLOOKUP t.vs_allocas k = SOME (a,32) /\ mload a t = mload a s) /\
    (!k. k < n \/ k = j ==> !mem.
      mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) mem) /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) mem) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_loop_data_facts >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
  qhdtm_assum `abi_decoder_recursive_loop_compiled`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qhdtm_assum `abi_scratch_decoder_loop_data`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_data_def]) >>
  `abi_decoder_budget first last b cap s /\ FLOOKUP s.vs_allocas site = SOME (slot,32)` by
    fs[abi_scratch_decoder_loop_inv_def, abi_scratch_effect_def, Excl "enc_def"] >>
  `site IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot + 32 < dimword (:256)` by
    (qpat_assum `abi_decoder_budget first last b cap s` mp_tac >>
     simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> decide_tac) >>
  `sb + LENGTH bs < dimword (:256) /\ eval_operand src initial = SOME (n2w sb)` by
    fs[abi_scratch_decoder_ranges_def] >>
  drule_at (Pat `abi_decode_loop_cfg _ _ _ _ _ _ _ _ _ _ _ _`) decoder_scratch_header_ptr_core >>
  disch_then (drule_at (Pat `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (qspecl_then [`header_var`,`ctx`,`PG`,`D`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  strip_tac >>
  rename1 `abi_decode_sim ctx func s h` >>
  `h.vs_memory = s.vs_memory` by
    (qpat_assum `h = _` (fn th => pure_rewrite_tac [th]) >>
     simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  `~MEM root [STRING #"%" (toString header_var); STRING #"%" (toString (header_var+1));
      STRING #"%" (toString (header_var+2)); STRING #"%" (toString (header_var+3))] /\
   (!x. src = Var x ==> ~MEM x [STRING #"%" (toString header_var);
      STRING #"%" (toString (header_var+1)); STRING #"%" (toString (header_var+2));
      STRING #"%" (toString (header_var+3))])` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> rpt strip_tac >>
     fs[] >> metis_tac[DECIDE ``next <= header_var ==> next <= header_var + (n:num)``]) >>
  `ptr_covers H u root h (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[] >> metis_tac[]) >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> fs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `allocas_from lower h /\ DISJOINT P u.t_mem` by
    (fs[allocas_from_def] >> metis_tac[]) >>
  `abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
     d (32 + maxn * type_memory_bytes ce ty) first last b cap initial` by
    gvs[] >>
  drule_at (Pat `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h`)
    abi_scratch_decoder_body_inputs >>
  disch_then (drule_at (Pat `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`Var q`,`st.cs_next_var`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  `abi_scratch_decoder_ranges CALLDATALOAD (Lit 0w) src (Var root) sb (LENGTH bs)
     d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) first last b cap h` by gvs[] >>
  `mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD h) = bs` by
    fs[abi_decoder_valid_array_memory_def] >>
  `lookup_var q h = SOME (n2w slot) /\ j < dimword (:256) /\
   first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
   site NOTIN abi_decoder_ids middle.cs_next_id end_st.cs_next_id` by
    (fs[eval_operand_def, abi_decoder_ids_def] >> decide_tac) >>
  `DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\
   h.vs_inst_idx = LENGTH st.cs_current_insts /\
   FLOOKUP h.vs_allocas site = SOME (slot,32)` by simp[] >>
  drule calldata_scratch_array_body_ptr >>
  disch_then (drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ h`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ root h _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ q h _`)) >>
  disch_then (drule_at (Pat `allocas_from _ h`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_var q h = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP h.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ h`)) >>
  disch_then (drule_at (Pat `mload slot h = _`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
  disch_then (qspecl_then [`PG`,`P`,`D`] mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  qpat_x_assum `!start end_st func ctx src root bs v sb d first last b cap limit_st initial G tn lower P D PG. _` kall_tac >>
  `d + 32 + j * type_memory_size tv + type_memory_size tv <=
     d + (32 + maxn * type_memory_bytes ce ty)` by
    (`(j+1) * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by
       (irule LESS_MONO_MULT2 >> decide_tac) >>
     pop_assum mp_tac >>
     pure_rewrite_tac [LEFT_ADD_DISTRIB, MULT_CLAUSES] >>
     qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac [th]) >>
     decide_tac) >>
  qpat_assum `type_memory_size tv = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  `!k. k < n ==> !mem.
     mem_agree_outside u'.t_mem actual.vs_memory mem ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) mem` by
    suspend "prefix_child" >>
  drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_scratch_decoder_child_advance >>
  disch_then (drule_at (Pat `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >>
    qpat_assum `type_memory_size tv = type_memory_bytes ce ty`
      (fn th => pure_rewrite_tac [GSYM th]) >> decide_tac)) >> strip_tac >>
  `abi_decoder_budget first last b cap actual` by
    fs[abi_scratch_effect_def, Excl "enc_def"] >>
  drule abi_scratch_decoder_loop_slot_separation >>
  disch_then (qspec_then `site` mp_tac) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`lo`,`limit_st`,`hi`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> gvs[])) >> disch_then assume_tac >>
  qpat_assum `(_ \/ _) /\ (_ ==> _)` (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\ _`
    strip_assume_tac >>
  `lookup_block actual.vs_current_bb func.fn_blocks = SOME bb'` by metis_tac[] >>
  `eval_operand (Var (STRING #"%" (toString st.cs_next_var))) actual = SOME (n2w j) /\
   op_taint u' (Var (STRING #"%" (toString st.cs_next_var))) = {} /\
   op_prov H' (Var (STRING #"%" (toString st.cs_next_var))) = NONE /\
   eval_operand (Var q) actual = SOME (n2w slot)` by
    (qpat_assum `FST ops = _` (fn th =>
       map_every (fn pat => qpat_assum pat
         (assume_tac o PURE_REWRITE_RULE [th]))
         [`eval_operand (FST ops) actual = _`, `op_taint u' (FST ops) = _`,
          `op_prov H' (FST ops) = _`]) >>
     asm_simp_tac bool_ss [eval_operand_def]) >>
  drule_at (Pat `abi_decoder_valid_array_memory _ _ _ _ _ _ _ _`) decoder_scratch_backedge_ptr_core >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_block actual.vs_current_bb _ = _`)) >>
  disch_then (drule_at (Pat `_.bb_instructions = _ ++ abi_decode_backedge_insts _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) actual = SOME (n2w j)`)) >>
  disch_then (drule_at (Pat `lookup_block hdr _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP actual.vs_allocas _ = _`)) >>
  disch_then (qspec_then `end_st.cs_next_var` mp_tac) >>
  disch_then (qspecl_then [`ctx`,`PG`,`P`,`D`] mp_tac) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >> strip_tac >>
  `root <> STRING #"%" (toString end_st.cs_next_var)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> metis_tac[]) >>
  `ptr_covers H'' u'' root h' (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))` by
    (irule ptr_covers_frame >> qexistsl_tac [`H'`,`actual`,`u'`] >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  `abi_decode_sim ctx func s h'` by
    (irule abi_decode_sim_trans >> qexists_tac `h` >>
     conj_tac >- asm_simp_tac bool_ss [] >>
     irule abi_decode_sim_trans >> qexists_tac `actual` >> asm_simp_tac bool_ss []) >>
  `allocas_from lower h'` by
    (qpat_assum `h'.vs_allocas = actual.vs_allocas` (fn th =>
       pure_rewrite_tac [allocas_from_def, th]) >>
     qpat_assum `allocas_from lower actual` (fn th =>
       ACCEPT_TAC (PURE_REWRITE_RULE [allocas_from_def] th))) >>
  qexistsl_tac [`h'`,`H''`,`u''`] >>
  qpat_assum `type_memory_size tv = type_memory_bytes ce ty`
    (fn th => pure_rewrite_tac [GSYM th]) >>
  asm_simp_tac bool_ss [IgnAsm `h' = _`,
    IgnAsm `type_memory_size tv = _`, IgnAsm `type_memory_bytes ce _ = _`] >>
  conj_tac >- suspend "taint_subset" >>
  conj_tac >- suspend "old_vars" >>
  conj_tac >- suspend "protected_scratch" >>
  suspend "element_memory"
QED

Resume calldata_scratch_loop_iteration_prefix_ptr[taint_subset]:
  qpat_assum `u''.t_mem SUBSET u'.t_mem` mp_tac >>
  qpat_assum `u'.t_mem SUBSET u.t_mem` mp_tac >>
  qpat_assum `u.t_mem = tn.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Resume calldata_scratch_loop_iteration_prefix_ptr[old_vars]:
  qpat_assum `!x. ~MEM x _ ==> lookup_var x h = _ /\ _` mp_tac >>
  qpat_assum `!x. not_fresh_at st x ==> _` mp_tac >>
  qpat_assum `!x. x <> _ ==> lookup_var x h' = _ /\ _` mp_tac >>
  qpat_assum `next <= header_var` mp_tac >>
  qpat_assum `next <= st.cs_next_var` mp_tac >>
  qpat_assum `next <= end_st.cs_next_var` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [abi_decoder_older_vars_def, not_fresh_at_def] >>
  simp_tac bool_ss [pred_setTheory.GSPECIFICATION, MEM] >>
  rpt strip_tac >>
  qpat_x_assum `GSPEC _ x` (assume_tac o SIMP_RULE std_ss [pred_setTheory.GSPECIFICATION] o
     ONCE_REWRITE_RULE [GSYM pred_setTheory.SPECIFICATION]) >>
  `x <> STRING #"%" (toString end_st.cs_next_var) /\
   (!n. st.cs_next_var <= n ==> x <> STRING #"%" (toString n)) /\
   ~MEM x [STRING #"%" (toString header_var);
     STRING #"%" (toString (header_var+1));
     STRING #"%" (toString (header_var+2));
     STRING #"%" (toString (header_var+3))]` by
    (simp[MEM] >> metis_tac[LESS_EQ_TRANS,
       DECIDE ``h <= h + (n:num)``]) >>
  qpat_x_assum `!x. x <> _ ==> lookup_var x h' = _ /\ _`
    (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. (!n. _ ==> _) ==> _` (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. _ /\ _ ==> lookup_var x h = _ /\ _`
    (qspec_then `x` mp_tac) >>
  fs[MEM]
QED

Resume calldata_scratch_loop_iteration_prefix_ptr[protected_scratch]:
  qpat_assum `!site slot. site IN _ /\ _ /\ FLOOKUP h.vs_allocas _ = _ ==> _` mp_tac >>
  qpat_assum `abi_decoder_budget first last b cap actual` mp_tac >>
  qpat_assum `FLOOKUP actual.vs_allocas site = SOME (slot,32)` mp_tac >>
  qpat_assum `site IN abi_decoder_ids first last` mp_tac >>
  qpat_assum `lo <= site` mp_tac >> qpat_assum `site < hi` mp_tac >>
  qpat_assum `lo <= st.cs_next_id` mp_tac >>
  qpat_assum `end_st.cs_next_id <= hi` mp_tac >>
  qpat_assum `h.vs_allocas = s.vs_allocas` mp_tac >>
  qpat_assum `h.vs_memory = s.vs_memory` mp_tac >>
  qpat_assum `h' = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  rpt gen_tac >> strip_tac >>
  `k <> site /\ k NOTIN abi_decoder_ids st.cs_next_id end_st.cs_next_id` by
    (fs[abi_decoder_ids_def] >> decide_tac) >>
  `FLOOKUP actual.vs_allocas k = SOME (a,32) /\ mload a actual = mload a h` by
    (first_x_assum irule >> simp[]) >>
  `a + 32 <= slot \/ slot + 32 <= a` by
    (drule_all abi_decoder_budget_sites_disjoint >> simp[]) >>
  asm_simp_tac bool_ss [IgnAsm `h' = _`] >>
  `mload a h = mload a s` by simp[mload_def] >>
  `abi_decode_footprint_frame [(slot,32)] actual h'` by
    (qpat_assum `h' = _` SUBST1_TAC >>
     simp[abi_decode_footprint_frame_def, jump_to_def] >>
     rpt strip_tac >> irule EQ_TRANS >>
     irule_at Any valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     simp[update_var_def] >> fs[abi_footprint_disjoint_def]) >>
  `mload a h' = mload a actual` by
    (irule abi_decode_footprint_frame_mload >> qexists_tac `[(slot,32)]` >>
     simp[abi_footprint_disjoint_def]) >>
  qpat_x_assum `h' = _` kall_tac >> metis_tac[]
QED

Resume calldata_scratch_loop_iteration_prefix_ptr[element_memory]:
  `(!k. k < n \/ k = j ==> !mem.
     mem_agree_outside u''.t_mem h'.vs_memory mem ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) mem)` suffices_by
    (disch_tac >>
     qpat_assum `!k. k < n \/ k = j ==> _` mp_tac >>
     qpat_assum `h' = _` mp_tac >>
     qpat_assum `type_memory_size tv = type_memory_bytes ce ty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> fs[] >>
     metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  gen_tac >> disch_tac >>
  `k < LENGTH vs /\
   (!mem. mem_agree_outside u'.t_mem actual.vs_memory mem ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) mem)` by
    (Cases_on `k = j` >- metis_tac[] >>
     `k < n /\ k < LENGTH vs` by decide_tac >> metis_tac[]) >>
  qpat_assum `!mem. mem_agree_outside u'.t_mem actual.vs_memory mem ==>
    val_in_memory tv (EL k vs) _ mem` mp_tac >>
  qpat_assum `u''.t_mem SUBSET u'.t_mem` mp_tac >>
  qpat_assum `all_have_type tv vs` mp_tac >>
  qpat_assum `k < LENGTH vs` mp_tac >>
  qpat_assum `h' = _` mp_tac >>
  qpat_assum `slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  `val_wf tv (EL k vs)` by
    (irule (cj 1 value_has_type_val_wf) >>
     fs[vyperTypingTheory.all_have_type_EVERY, EVERY_EL]) >>
  `val_footprint tv (EL k vs) <= type_memory_size tv` by
    metis_tac[exprSimTheory.val_footprint_le] >>
  `(k+1) * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
    (irule LESS_MONO_MULT2 >> decide_tac) >>
  `abi_decode_footprint_frame [(slot,32)] actual h'` by
    (qpat_assum `h' = _` SUBST1_TAC >>
     simp[abi_decode_footprint_frame_def, jump_to_def] >>
     rpt strip_tac >> irule EQ_TRANS >>
     irule_at Any valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >>
     simp[update_var_def] >> fs[abi_footprint_disjoint_def]) >>
  qpat_x_assum `h' = _` kall_tac >>
  `!mem. mem_agree_outside u'.t_mem h'.vs_memory mem ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- asm_simp_tac bool_ss [] >>
     qexistsl_tac [`actual.vs_memory`,`h'.vs_memory`,`u'.t_mem`,`u'.t_mem`,
       `{a | slot <= a /\ a < slot+32}`] >>
     asm_simp_tac bool_ss [] >>
     conj_tac
     >- (qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
         simp_tac bool_ss [abi_decode_footprint_frame_def, abi_footprint_disjoint_def,
           MEM, pairTheory.FST, pairTheory.SND] >>
         rpt strip_tac >> first_x_assum irule >>
         fs[pred_setTheory.IN_GSPEC_IFF] >> decide_tac) >>
     simp[pred_setTheory.IN_GSPEC_IFF] >> rpt strip_tac >>
     fs[LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >>
  fs[bodyPtrDefsTheory.mem_agree_outside_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Resume calldata_scratch_loop_iteration_prefix_ptr[prefix_child]:
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ h actual`
    (mp_then Any mp_tac abi_scratch_effect_frame) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> disch_tac >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ h` mp_tac >>
  qpat_assum `!k. k < n ==> _` mp_tac >>
  qpat_assum `h.vs_memory = s.vs_memory` mp_tac >>
  qpat_assum `u.t_mem = tn.t_mem` mp_tac >>
  qpat_assum `u'.t_mem SUBSET u.t_mem` mp_tac >>
  qpat_assum `all_have_type tv vs` mp_tac >>
  qpat_assum `j < LENGTH vs` mp_tac >>
  qpat_assum `n <= j` mp_tac >>
  qpat_assum `LENGTH vs <= maxn` mp_tac >>
  qpat_assum `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = _` mp_tac >>
  qpat_assum `abi_decode_footprint_frame _ h actual` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  gen_tac >> disch_tac >>
  `val_wf tv (EL k vs)` by
    (irule (cj 1 value_has_type_val_wf) >>
     fs[vyperTypingTheory.all_have_type_EVERY, EVERY_EL] >>
     `k < LENGTH vs` by decide_tac >> metis_tac[]) >>
  `val_footprint tv (EL k vs) <= type_memory_size tv` by
    metis_tac[exprSimTheory.val_footprint_le] >>
  `(k+1)*type_memory_size tv <= j*type_memory_size tv /\
   j*type_memory_size tv <= maxn*type_memory_size tv` by
    (conj_tac >> irule LESS_MONO_MULT2 >> decide_tac) >>
  `mem_bytes_at (d+32+k*type_memory_size tv) (val_footprint tv (EL k vs))
     actual.vs_memory =
   mem_bytes_at (d+32+k*type_memory_size tv) (val_footprint tv (EL k vs))
     h.vs_memory` by
    (irule abi_decode_footprint_frame_slice >> goal_assum (drule_at Any) >>
     simp_tac bool_ss [abi_scratch_disjoint_cons] >>
     conj_tac >- (disj1_tac >>
       qpat_assum `(k+1)*type_memory_size tv <= j*type_memory_size tv` mp_tac >>
       pure_rewrite_tac [LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
     qpat_x_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ h` mp_tac >>
     simp_tac bool_ss [abi_scratch_decoder_ranges_def, abi_footprint_disjoint_def] >>
     rpt strip_tac >> first_x_assum drule >>
     qpat_assum `(k+1)*type_memory_size tv <= j*type_memory_size tv` mp_tac >>
     qpat_assum `j*type_memory_size tv <= maxn*type_memory_size tv` mp_tac >>
     qpat_assum `type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = _`
       (fn th => pure_rewrite_tac [th]) >>
     pure_rewrite_tac [LEFT_ADD_DISTRIB, MULT_CLAUSES] >> decide_tac) >>
  match_mp_tac (Q.INST [`oldmem` |-> `h.vs_memory`,
    `oldtaint` |-> `u.t_mem`] calldata_member_robust_window_frame) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Finalise calldata_scratch_loop_iteration_prefix_ptr


Theorem calldata_scratch_loop_iteration_ptr:
  (!start end_st func ctx src root bs v sb d first last b cap limit_st initial
      G tn lower P D PG.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
    fn_has_code start end_st func /\ fn_inst_ids_distinct func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_decoder_input ce env sf ty tv bs v start src (Var root)
      CALLDATALOAD (Lit 0w) sb d first last b cap initial /\
    abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
    fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
    initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts /\
    ptr_covers G tn root initial (type_memory_bytes ce ty) /\
    op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower initial /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
    ?actual H u.
      val_in_memory tv v d actual.vs_memory /\
      (!mem. mem_agree_outside u.t_mem actual.vs_memory mem ==>
        val_in_memory tv v d mem) /\
      abi_scratch_effect first last start.cs_next_id end_st.cs_next_id
        start.cs_next_var limit_st d (type_memory_bytes ce ty) b cap initial actual /\
      actual.vs_current_bb = end_st.cs_current_bb /\
      actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
      abi_decode_sim ctx func initial actual /\
      ptr_covers H u root actual (type_memory_bytes ce ty) /\
      u.t_mem SUBSET tn.t_mem /\ DISJOINT P u.t_mem /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial /\
        FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
      allocas_from lower actual /\
      (!site slot. site IN abi_decoder_ids first last /\
        ~(site IN abi_decoder_ids start.cs_next_id end_st.cs_next_id) /\
        FLOOKUP initial.vs_allocas site = SOME (slot,32) ==>
        FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
        mload slot actual = mload slot initial) /\
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u actual) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn initial)) /\
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var q) src (Var root)
    CALLDATALOAD (Lit 0w) hdr exit_lbl hid header_var first last lo hi next limit_st site /\
  abi_scratch_decoder_loop_data ce env sf ty tv maxn bs vs CALLDATALOAD (Lit 0w)
    (Var q) src (Var root) sb d slot first last b cap next initial /\
  abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial hdr j s /\
  fn_inst_ids_distinct func /\ j < LENGTH vs /\
  ptr_covers G tn root s (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ptr_covers G tn q s 32 /\ DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower s /\ ~ctx_has_dalloca ctx /\ DISJOINT P tn.t_mem ==>
  ?t H u.
    abi_scratch_decoder_loop_inv CALLDATALOAD bs tv vs sb d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
      first last lo hi next limit_st b cap initial hdr (SUC j) t /\
    abi_decode_sim ctx func s t /\
    ptr_covers H u root t (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
    ptr_covers H u q t 32 /\ mload slot t = n2w (SUC j) /\
    DISJOINT {a | slot <= a /\ a < slot+32} u.t_mem /\ DISJOINT P u.t_mem /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\ allocas_from lower t /\
    (!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!k a. k IN abi_decoder_ids first last /\ ~(k IN abi_decoder_ids lo hi) /\
      FLOOKUP s.vs_allocas k = SOME (a,32) ==>
      FLOOKUP t.vs_allocas k = SOME (a,32) /\ mload a t = mload a s) /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) mem) /\
    ((!fuel. ptr_safe_run D lower fuel ctx func PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)
Proof
  strip_tac >>
  mp_tac (Q.INST [`n` |-> `0`] calldata_scratch_loop_iteration_prefix_ptr) >>
  (impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >>
    asm_simp_tac bool_ss [DECIDE ``0 <= (j:num) /\ ~(k < 0)``])) >>
  strip_tac >> qexistsl_tac [`t`,`H`,`u`] >> asm_simp_tac bool_ss [] >>
  qpat_assum `!k a. _` mp_tac >> POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
