Theory abiEncodeValuesDynamicPrefix
Ancestors
  abiEncodeValuesPrefix abiDecodeRanges abiEncoderProps
  abiEncodeValuesSource abiEncoderWindow abiEncoderAdmissible
  abiEncodeValuesDynamic abiEncodeValuesRun abiEncodeValuesMetadata
  abiEncodeValuesPhases abiEncodeValuesLayout abiEncoderWindowContract abiEncoderWindowPhase
  exprSimAbiEncodeExecFrame exprLoweringProps allocaSiteResource
  fragGasOriginPtr fragExec compileEnv ptrDiscipline valueEncodingDefs
  vyperABI vyperValue vyperTyping contractABI venomState venomInst venomMemDefs
  finite_map pred_set arithmetic list words pair

(* The recursive encoder fills the new tail. Its suffix publishes the
   corresponding offset and advances the cursor by the encoded length. *)
Theorem abi_encode_values_dynamic_prefix_input_side:
  abi_encode_values_source_side Child lo explicit ctx func PG /\
  abi_encode_values_suffix_join Child Row func /\
  abi_encode_values_prefix_at ats avs hl d (Var cursor_var) loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ is_dynamic at /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  compile_abi_encode_to_buf (Var dest) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor_var) offset len mid = (len,en) /\
  ci_mono st en /\ abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  bs = enc at av /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dest) s = SOME (n2w (d+off)) /\
  eval_operand (Var head) s = SOME (n2w (d+h)) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn (Var dest) = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn dest s (LENGTH bs) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d+off,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  FLOOKUP s.vs_allocas owner = SOME (b,capacity) /\ owner < st.cs_next_id /\ owner <> loc /\
  b <= d /\ d+off+LENGTH bs <= b+capacity /\
  (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (p,sz)) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH bs) (p,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    abi_encode_values_prefix_at ats avs hl d (Var cursor_var) loc slot (SUC i) en t G' tn' /\
    window_phase ctx func st en (loc INSERT window_alloca_sites func (frag_ids st mid))
      [(d+h,32);(d+off,LENGTH bs)] s t /\
    abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d+h \/ d+h+32 <= i) /\
      (i < d+off \/ d+off+LENGTH bs <= i) /\
      (!id p sz. id IN (loc INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (p,sz) ==> i < p \/ p+sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    Row st en s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_values_prefix_at_def]) >>
  `abi_member_head_size at = 32 /\ abi_member_tail_size at av = LENGTH bs` by
    simp[abi_member_head_size_def, abi_member_tail_size_def] >>
  `b+capacity <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `32+h <= off` by decide_tac >>
  `d+h+32 <= s.vs_alloca_next /\ d+off+LENGTH bs <= s.vs_alloca_next` by decide_tac >>
  `venomMemDefs$regions_disjoint (b,capacity) (slot,32)` by
    metis_tac[alloca_site_registered_disjoint] >>
  `venomMemDefs$regions_disjoint (d+h,32) (slot,32) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH bs) (slot,32) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH bs) (d+h,32)` by
    (qpat_assum `venomMemDefs$regions_disjoint (b,capacity) (slot,32)` mp_tac >>
     simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def, FST, SND] >>
     decide_tac) >>
  `!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       Var cursor_var = Var x \/ offset = Var x ==> not_fresh_at st x` by
    (gen_tac >> disch_then STRIP_ASSUME_TAC >>
     TRY (qpat_assum `Var cursor_var = Var x`
       (SUBST1_TAC o SYM o SIMP_RULE bool_ss [operand_11]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       offset = Var x ==> not_fresh_at st x` (qspec_then `x` irule) >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`head_addr` |-> `d+h`,`tail` |-> `d+off`,`site` |-> `loc`,
    `cursor` |-> `cursor_var`]
    abi_encode_values_dynamic_body_input_side) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac) >>
  `owner NOTIN loc INSERT window_alloca_sites func (frag_ids st mid)` by
    (simp_tac (srw_ss()) [IN_INSERT, window_alloca_sites_def, frag_ids_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     disj1_tac >> disj1_tac >> decide_tac) >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`cursor` |-> `Var cursor_var`,`hs` |-> `32`,`ts` |-> `LENGTH (bs:word8 list)`,
    `cap` |-> `capacity`,`ids` |-> `loc INSERT window_alloca_sites func (frag_ids st mid)`,
    `outs` |-> `[(d+h,32);(d+off,LENGTH (bs:word8 list))]`] abi_encode_values_prefix_next) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (sym_tac >> first_assum ACCEPT_TAC) >>
    TRY (asm_rewrite_tac [EVERY_DEF, FORALL_PROD] >> NO_TAC) >>
    TRY (decide_tac >> NO_TAC)
    >- (simp_tac (srw_ss()) [EVERY_DEF, FORALL_PROD] >> qx_gen_tac `j` >>
        disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
        qpat_assum `!i. _ /\ _ /\ _ ==> (i IN tn'.t_mem <=> i IN tn.t_mem)`
          (qspec_then `j` mp_tac) >>
        impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          PURE_REWRITE_TAC [IN_INSERT] >> first_assum ACCEPT_TAC) >>
        disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
    qx_gen_tac `j` >> disch_tac >>
    qpat_assum `!i. (d+h <= i /\ _) \/ _ ==> i NOTIN tn'.t_mem`
      (qspec_then `j` irule) >> asm_rewrite_tac[]) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_values_dynamic_prefix_input:
  abi_encode_values_prefix_at ats avs hl d (Var cursor_var) loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ is_dynamic at /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  compile_abi_encode_to_buf (Var dest) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor_var) offset len mid = (len,en) /\
  ci_mono st en /\ abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  bs = enc at av /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dest) s = SOME (n2w (d+off)) /\
  eval_operand (Var head) s = SOME (n2w (d+h)) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn (Var dest) = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn dest s (LENGTH bs) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d+off,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  FLOOKUP s.vs_allocas owner = SOME (b,capacity) /\ owner < st.cs_next_id /\ owner <> loc /\
  b <= d /\ d+off+LENGTH bs <= b+capacity /\
  (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (p,sz)) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH bs) (p,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    abi_encode_values_prefix_at ats avs hl d (Var cursor_var) loc slot (SUC i) en t G' tn' /\
    window_phase ctx func st en (loc INSERT window_alloca_sites func (frag_ids st mid))
      [(d+h,32);(d+off,LENGTH bs)] s t /\
    abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d+h \/ d+h+32 <= i) /\
      (i < d+off \/ d+off+LENGTH bs <= i) /\
      (!id p sz. id IN (loc INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (p,sz) ==> i < p \/ p+sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  mp_tac (PURE_REWRITE_RULE
    [abi_encode_values_source_side_trivial, abi_encode_values_suffix_join_trivial,
     AND_CLAUSES]
    (CONV_RULE (DEPTH_CONV BETA_CONV)
      (Q.INST [`Child` |-> `\a b s t. T`, `Row` |-> `\a b s t. T`]
        abi_encode_values_dynamic_prefix_input_side))) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_values_dynamic_prefix:
  abi_encode_values_prefix_at ats avs hl d (Var cursor_var) loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type env ty /\ is_dynamic at /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\
  compile_abi_encode_to_buf (Var dest) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var head) (Var cursor_var) offset len mid = (len,en) /\
  ci_mono st en /\ abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v sb mem) /\
  bs = enc at av /\ cap = val_footprint tv v /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var dest) s = SOME (n2w (d+off)) /\
  eval_operand (Var head) s = SOME (n2w (d+h)) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn (Var dest) = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var dest = Var x \/ Var head = Var x \/
       offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn dest s (LENGTH bs) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d+off,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  FLOOKUP s.vs_allocas owner = SOME (b,capacity) /\ owner < st.cs_next_id /\ owner <> loc /\
  b <= d /\ d+off+LENGTH bs <= b+capacity /\
  (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (p,sz)) /\
    venomMemDefs$regions_disjoint (d+off,LENGTH bs) (p,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    abi_encode_values_prefix_at ats avs hl d (Var cursor_var) loc slot (SUC i) en t G' tn' /\
    window_phase ctx func st en (loc INSERT window_alloca_sites func (frag_ids st mid))
      [(d+h,32);(d+off,LENGTH bs)] s t /\
    abi_encode_exec_frame func s t /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d+h \/ d+h+32 <= i) /\
      (i < d+off \/ d+off+LENGTH bs <= i) /\
      (!id p sz. id IN (loc INSERT window_alloca_sites func (frag_ids st mid)) /\
        FLOOKUP t.vs_allocas id = SOME (p,sz) ==> i < p \/ p+sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_values_plan_window_input >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  mp_tac abi_encode_values_dynamic_prefix_input >>
  impl_tac >-
    (qpat_x_assum `bs = _` SUBST_ALL_TAC >>
     qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     qpat_x_assum `at = vyper_to_abi_type env ty` SUBST_ALL_TAC >>
     asm_rewrite_tac[]) >>
  disch_then ACCEPT_TAC
QED
