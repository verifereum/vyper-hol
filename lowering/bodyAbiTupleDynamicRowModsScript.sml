(* The dynamic branch of a reached ABI tuple row. *)
Theory bodyAbiTupleDynamicRowMods
Ancestors
  bodyAbiTupleBufferStateMods bodyAbiTupleBufferResourcesMods bodyAbiTupleBufferPhaseMods
  abiEncodeValuesRun abiEncodeValuesDynamicPrefix abiEncodeValuesPrefixFrame abiEncodeValuesMetadata
  abiEncoderWindowJointPhases abiEncoderWindowPhase abiEncoderAdmissible
  abiEncoderWindowContract abiEncoderProps abiDecodeRanges abiEncoderWindowChild
  freshWrites emitHelperProps
  exprSimAbiEncodeSiteResources exprSimAbiEncodePlanMetadata reasonCopySourcePtr
  allocaSiteResource fragGasOriginPtrLoop fragExec exprLoweringProps
  bodyPtrDefs loweringStateRelDefs loweringPosts compileEnv
  vyperABI vyperValue vyperTyping vyperContext contractABI
  venomMemDefs venomState venomInst finite_map pred_set list arithmetic words pair

Theorem dynamic_row_addresses[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
    shared pbase capacity root dst dst_offset prefix st s G tn /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot i st s G tn /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  ho + 32 <= off /\ off <= capacity-dst_offset /\
  abi_encode_child_prefix (Var dst) ho (Var dp) st = ((head_op,offset,tail_op),en) /\
  fn_has_code st en func /\ ci_mono st en ==>
  ?t G' tn' hp tp.
    head_op = Var hp /\ tail_op = Var tp /\
    window_phase ctx func st en {} [] s t /\ abi_encode_exec_frame func s t /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot i en t G' tn' /\
    eval_operand (Var hp) t = SOME (n2w (pbase+dst_offset+ho)) /\
    eval_operand (Var tp) t = SOME (n2w (pbase+dst_offset+off)) /\
    eval_operand offset t = SOME (n2w off) /\ op_taint tn' offset = {} /\
    ptr_covers G' tn' hp t 32 /\ ptr_covers G' tn' tp t (capacity-dst_offset-off) /\
    (!x. Var hp = Var x \/ offset = Var x \/ Var tp = Var x ==> not_fresh_at en x) /\
    (!x. not_fresh_at st x ==> FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac abi_tuple_buffer_resources_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  qhdtm_assum `abi_encode_values_prefix_at`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_values_prefix_at_def]) >>
  `pbase+capacity <= s.vs_alloca_next` by
    (irule alloca_site_registered_below >> asm_rewrite_tac[] >> qexists `shared` >> asm_rewrite_tac[]) >>
  `pbase+dst_offset + (capacity-dst_offset) <= s.vs_alloca_next` by decide_tac >>
  `ho+32 <= capacity-dst_offset` by decide_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s)` by (strip_tac >> first_x_assum drule >> simp[]) >>
  `mem_word_at slot s.vs_memory = n2w off` by asm_rewrite_tac[] >>
  mp_tac (Q.INST [`ops` |-> `(head_op,offset,tail_op)`, `d` |-> `pbase+dst_offset`,
                  `bound` |-> `capacity-dst_offset`] window_child_prefix_joint) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`,`hp`,`tp`]
    (strip_assume_tac o PURE_REWRITE_RULE [FST,SND])) >>
  qexistsl [`t`,`G'`,`tn'`,`hp`,`tp`] >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot i en t G' tn'` by
    (irule abi_encode_values_prefix_arith >>
     qhdtm_assum `abi_encode_values_prefix_at` (irule_at Any) >>
     qhdtm_assum `window_phase` (irule_at Any) >> asm_rewrite_tac[]) >>
  qpat_x_assum `head_op = Var hp` SUBST_ALL_TAC >>
  qpat_x_assum `tail_op = Var tp` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED

(* The tail encoder's scratch sites are strictly in its compiler interval. *)
Theorem dynamic_row_scratch[local]:
  compile_abi_encode_to_buf (Var tp) src ei st = (len,mid) /\
  fn_has_code st mid func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  aid IN window_alloca_sites func (frag_ids st mid) ==>
  st.cs_next_id <= aid /\ aid < mid.cs_next_id /\
  ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce scopes x
Proof
  simp_tac (srw_ss()) [window_alloca_sites_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `st.cs_next_id <= aid /\ aid < mid.cs_next_id` by
    (fs[frag_ids_def] >> decide_tac) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `?inst. MEM inst _ /\ _` (qx_choose_then `scratch` strip_assume_tac) >>
  `scratch.inst_id IN frag_ids st mid` by asm_rewrite_tac[] >>
  `?q. scratch.inst_operands = [Lit 32w] /\ scratch.inst_outputs = [q] /\
       not_local_ptr ce scopes q` by
    (mp_tac (Q.INST [`earlier` |-> `st`, `ready` |-> `st`, `body_end` |-> `mid`,
                      `obs` |-> `func`, `i` |-> `scratch`, `dst` |-> `Var tp`,
                      `out` |-> `len`] (SPEC_ALL abi_encode_compiled_scratch_site)) >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  rename1 `scratch.inst_outputs = [scratch_var]` >>
  qexistsl [`scratch`,`scratch_var`] >> asm_rewrite_tac[]
QED

Theorem dynamic_row_tail_phase[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
    shared b capacity root dst dst_offset prefix st s G tn /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s0) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner_inst (fn_insts func) /\ owner_inst.inst_opcode = ALLOCA /\
  owner_inst.inst_id = shared /\ owner_inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_opcode = ALLOCA /\
  cursor_inst.inst_id = loc /\ cursor_inst.inst_outputs = [dp] /\ not_local_ptr ce ee.scopes dp /\
  shared < loc /\
  abi_encode_values_prefix_at ats avs hl (b+dst_offset) (Var dp) loc slot i st s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ is_dynamic at /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off + LENGTH (enc at av) <= capacity-dst_offset /\
  compile_abi_encode_to_buf (Var tp) src ei st = (len,mid) /\
  abi_encode_child_suffix (Var hp) (Var dp) offset len mid = (len,en) /\
  ci_mono st mid /\ ci_mono mid en /\
  fn_has_code st mid func /\ fn_has_code mid en func /\ abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = enc at av /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> abi_encoder_window_input ei ct rv sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand (Var tp) s = SOME (n2w (b+dst_offset+off)) /\
  eval_operand (Var hp) s = SOME (n2w (b+dst_offset+h)) /\ eval_operand offset s = SOME (n2w off) /\
  op_taint tn src = {} /\ op_taint tn offset = {} /\
  (!x. src = Var x \/ Var tp = Var x \/ Var hp = Var x \/ offset = Var x ==> not_fresh_at st x) /\
  ptr_covers G tn hp s 32 /\ ptr_covers G tn tp s (LENGTH (enc at av)) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (b+dst_offset+off,LENGTH (enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (p,sz)) /\
    venomMemDefs$regions_disjoint (b+dst_offset+off,LENGTH (enc at av)) (p,sz)) ==>
  ?t G' tn'.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
      shared b capacity root dst dst_offset prefix en t G' tn' /\
    abi_tuple_row_effects_mods ce ee func shared b capacity dst_offset loc st s G tn en t G' tn' /\
    abi_encode_values_prefix_at ats avs hl (b+dst_offset) (Var dp) loc slot (SUC i) en t G' tn' /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac abi_tuple_buffer_resources_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `op_taint tn (Var tp) = {}` by
    (qpat_assum `ptr_covers G tn tp s _` mp_tac >> simp[NoAsms, ptr_covers_def]) >>
  `ci_mono st en` by metis_tac[ci_mono_trans] >>
  `shared <> loc /\ b <= b+dst_offset /\ b+dst_offset+off+LENGTH (enc at av) <= b+capacity` by decide_tac >>
  mp_tac (Q.INST [`d` |-> `b+dst_offset`, `dest` |-> `tp`, `head` |-> `hp`,
    `cursor_var` |-> `dp`, `owner` |-> `shared`, `bs` |-> `enc at av`]
    abi_encode_values_dynamic_prefix_input) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] strip_assume_tac) >>
  qexistsl [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  suspend "tail_frame"
QED

Resume dynamic_row_tail_phase[tail_frame]:
  qpat_assum `ci_mono st mid` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_assum `ci_mono mid en` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `local_ptrs_reserved ce st` by metis_tac[local_ptrs_reserved_next_var] >>
  `!aid. aid IN window_alloca_sites func (frag_ids st mid) ==>
     st.cs_next_id <= aid /\ aid < mid.cs_next_id /\
     ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (rpt strip_tac >> drule_all dynamic_row_scratch >> simp[]) >>
  qhdtm_assum `abi_encode_values_prefix_at`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_values_prefix_at_def]) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ (SUC i) _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_encode_values_prefix_at_def]) >>
  `abi_member_head_size at = 32` by asm_rewrite_tac[abi_member_head_size_def] >>
  qpat_x_assum `h = _` SUBST_ALL_TAC >>
  qpat_x_assum `off = _` SUBST_ALL_TAC >>
  qpat_x_assum `at = _` SUBST_ALL_TAC >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  irule abi_tuple_buffer_phase_mods >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
  qexistsl [`explicit`,`PG`] >>
  asm_rewrite_tac[EVERY_DEF,IN_INSERT] >>
  suspend "tail_sites"
QED

Resume dynamic_row_tail_phase[tail_sites]:
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
  qexists `hz` >>
  simp_tac bool_ss [pairTheory.UNCURRY, optionTheory.SOME_11, EXISTS_REFL] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (qx_gen_tac `j` >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_assum `!j. _ /\ _ /\ _ ==> (j IN tn'.t_mem <=> j IN tn.t_mem)`
        (qspec_then `j` mp_tac) >>
      impl_tac >- asm_rewrite_tac[IN_INSERT] >>
      disch_then (irule o iffLR) >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  conj_tac >- (rpt strip_tac >> TRY (decide_tac >> NO_TAC) >> first_x_assum drule >> strip_tac >> decide_tac) >>
  conj_tac
  >- (gen_tac >> strip_tac
      >- (qexistsl [`owner_inst`,`root`] >> asm_rewrite_tac[])
      >- (qexistsl [`cursor_inst`,`dp`] >> asm_rewrite_tac[]) >>
      first_x_assum drule >> disch_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2)) >>
  conj_tac >- (strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  conj_tac >- (qexists `slot` >> REFL_TAC) >>
  decide_tac
QED

Finalise dynamic_row_tail_phase

Theorem dynamic_row_offset_var[local]:
  abi_encode_child_prefix (Var dst) h (Var dp) a = ((head,offset,tail),p) /\
  fn_has_code a p func ==>
  ?x. offset = Var x
Proof
  strip_tac >> drule_all window_child_prefix_context >>
  simp_tac (srw_ss()) [] >>
  disch_then (qx_choosel_then [`a1`,`a2`] strip_assume_tac) >>
  qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qexists `STRING #"%" (toString a1.cs_next_var)` >> asm_rewrite_tac[]
QED

Theorem dynamic_row_keep_pointer[local]:
  (!x. not_fresh_at a x ==>
    (!w. lookup_var x u = SOME w ==> lookup_var x z = SOME w) /\
    FLOOKUP Gz x = FLOOKUP Gu x /\ op_taint tz (Var x) = op_taint tu (Var x)) /\
  not_fresh_at a x /\ eval_operand (Var x) u = SOME w /\ ptr_covers Gu tu x u n ==>
  eval_operand (Var x) z = SOME w /\ ptr_covers Gz tz x z n
Proof
  simp_tac bool_ss [ptr_covers_def,eval_operand_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  first_x_assum drule >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  rpt strip_tac >> asm_rewrite_tac[] >> metis_tac[]
QED

(* Restore is requested only after the prefix has produced the actual tail
   operand; the physical input certificate is for that precise encoder cut. *)
Theorem abi_tuple_dynamic_row_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s0) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM owner_inst (fn_insts func) /\ owner_inst.inst_opcode = ALLOCA /\
  owner_inst.inst_id = shared /\ owner_inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_opcode = ALLOCA /\
  cursor_inst.inst_id = loc /\ cursor_inst.inst_outputs = [dp] /\ not_local_ptr ce ee.scopes dp /\
  shared < loc /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot i a u Gu tu /\
  compile_abi_encode_value_rows ce (Var dst) (Var dp) h [(saved,ty)] a = ((),en) /\
  fn_has_code a en func /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ is_dynamic at /\
  at = vyper_to_abi_type (get_tenv cx) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off + LENGTH (enc at av) <= capacity-dst_offset /\
  (!prep ready mid q Gq tq tp src len.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
      shared pbase capacity root dst dst_offset prefix prep q Gq tq /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot i prep q Gq tq /\
    eval_operand (Var tp) q = SOME (n2w (pbase+dst_offset+off)) /\
    ptr_covers Gq tq tp q (capacity-dst_offset-off) /\ not_fresh_at prep tp /\
    unwrap_value ce saved prep = (src,ready) /\
    compile_abi_encode_to_buf (Var tp) src (type_to_abi_enc_info ce.ce_struct_fields ce ty) ready = (len,mid) /\
    ci_mono prep ready /\ ci_mono ready mid /\ fn_has_code prep ready func /\ fn_has_code ready mid func ==>
    ?s G tn sb.
      abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
        shared pbase capacity root dst dst_offset prefix ready s G tn /\
      abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc prep q Gq tq ready s G tn /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot i ready s G tn /\
      eval_operand src s = SOME (n2w sb) /\ op_taint tn src = {} /\
      (!x. src = Var x ==> not_fresh_at ready x) /\
      (?ct rv. enc ct rv = enc at av /\
        !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
            ct rv sb (val_footprint tv v) mem) /\
      (0 < val_footprint tv v ==> sb + val_footprint tv v <= s.vs_alloca_next /\
        venomMemDefs$regions_disjoint (sb,val_footprint tv v) (pbase+dst_offset+off,LENGTH (enc at av)) /\
        ?p. src = Var p /\ ptr_covers G tn p s (val_footprint tv v)) /\
      (!inst p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id IN frag_ids ready mid /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (p,sz) ==>
        sz = 32 /\ (0 < val_footprint tv v ==> venomMemDefs$regions_disjoint (sb,val_footprint tv v) (p,sz)) /\
        venomMemDefs$regions_disjoint (pbase+dst_offset+off,LENGTH (enc at av)) (p,sz)) /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gq,tq) [] (OK s,G,tn)) ==>
  ?z Gz tz.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc a u Gu tu en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var dp) loc slot (SUC i) en z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `is_abi_dynamic ce.ce_struct_fields ty` by
    (drule_all abi_encode_translated_dynamic >> disch_then SUBST1_TAC >>
     qpat_assum `at = vyper_to_abi_type _ _` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
  `abi_member_head_size at = 32` by asm_rewrite_tac[abi_member_head_size_def] >>
  `h + 32 <= off /\ off <= capacity-dst_offset` by decide_tac >>
  drule_all abi_encode_values_dynamic_cuts >>
  disch_then (qx_choosel_then [`head_op`,`offset`,`tail_op`,`prep`,`src`,`st`,`len`,`mid`] strip_assume_tac) >>
  mp_tac (Q.INST [`st` |-> `a`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`,
                  `en` |-> `prep`,`ho` |-> `h`] dynamic_row_addresses) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`,`hp`,`tp`] strip_assume_tac) >>
  qpat_x_assum `head_op = Var hp` SUBST_ALL_TAC >>
  qpat_x_assum `tail_op = Var tp` SUBST_ALL_TAC >>
  `not_fresh_at prep hp /\ not_fresh_at prep tp /\
    (!x. offset = Var x ==> not_fresh_at prep x)` by
    (qpat_assum `!x. Var hp = Var x \/ offset = Var x \/ Var tp = Var x ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule_all_then strip_assume_tac dynamic_row_offset_var >>
  rename1 `offset = Var ofs` >>
  suspend "address_frame"
QED

Resume abi_tuple_dynamic_row_mods[address_frame]:
  `abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d0 se s0 G0 tn0
      shared pbase capacity root dst dst_offset prefix prep q Gq tq /\
   abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset loc a u Gu tu prep q Gq tq` by
    (irule abi_tuple_buffer_phase_mods >>
     qpat_assum `window_phase ctx func a prep {} [] u q` (irule_at Any) >>
     qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a u Gu tu`
       (irule_at Any) >>
     qexistsl [`explicit`,`PG`] >>
     asm_rewrite_tac[EVERY_DEF,IN_INSERT,NOT_IN_EMPTY] >>
     qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
       (qx_choose_then `hz` assume_tac) >>
     qexists `hz` >> asm_rewrite_tac[] >>
     gen_tac >> disch_tac >> qexistsl [`owner_inst`,`root`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!prep ready mid q Gq tq tp src len. _`
    (qspecl_then [`prep`,`st`,`mid`,`q`,`Gq`,`tq`,`tp`,`src`,`len`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`s`,`G`,`tn`,`sb`] strip_assume_tac) >>
  suspend "keep_operands"
QED

Resume abi_tuple_dynamic_row_mods[keep_operands]:
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ prep q Gq tq st s G tn`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  `eval_operand (Var hp) s = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers G tn hp s 32` by
    (irule dynamic_row_keep_pointer >> qexistsl [`Gq`,`prep`,`tq`,`q`] >> asm_rewrite_tac[]) >>
  `eval_operand (Var tp) s = SOME (n2w (pbase+dst_offset+off)) /\ ptr_covers G tn tp s (capacity-dst_offset-off)` by
    (irule dynamic_row_keep_pointer >> qexistsl [`Gq`,`prep`,`tq`,`q`] >> asm_rewrite_tac[]) >>
  `LENGTH (enc at av) <= capacity-dst_offset-off` by decide_tac >>
  `ptr_covers G tn tp s (LENGTH (enc at av))` by
    (irule ptr_covers_mono >> qexists `capacity-dst_offset-off` >> asm_rewrite_tac[]) >>
  `eval_operand offset s = SOME (n2w off) /\ op_taint tn offset = {}` by
    (qpat_x_assum `offset = Var ofs` SUBST_ALL_TAC >>
     `not_fresh_at prep ofs` by
       (qpat_assum `!x. Var ofs = Var x ==> _` (qspec_then `ofs` mp_tac) >> simp[NoAsms]) >>
     qpat_assum `!x. not_fresh_at prep x ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `eval_operand (Var ofs) q = _` (assume_tac o REWRITE_RULE [eval_operand_def]) >>
     qpat_assum `!w. lookup_var ofs q = _ ==> _` (drule_then assume_tac) >>
     asm_rewrite_tac[eval_operand_def]) >>
  `!x. src = Var x \/ Var tp = Var x \/ Var hp = Var x \/ offset = Var x ==> not_fresh_at st x` by
    (gen_tac >> disch_then (DISJ_CASES_THEN2 assume_tac mp_tac)
     >- (qpat_assum `!x. src = Var x ==> _` (drule_then ACCEPT_TAC)) >>
     disch_tac >> irule not_fresh_at_mono >> qexists `prep` >>
     qpat_assum `ci_mono prep st` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     asm_rewrite_tac[] >> metis_tac[operand_11]) >>
  suspend "tail"
QED

Resume abi_tuple_dynamic_row_mods[tail]:
  qpat_x_assum `at = vyper_to_abi_type _ _` kall_tac >>
  mp_tac (Q.INST [`b` |-> `pbase`,
                  `ei` |-> `type_to_abi_enc_info ce.ce_struct_fields ce ty`,
                  `cap` |-> `val_footprint tv v`] dynamic_row_tail_phase) >>
  impl_tac
  >- (asm_rewrite_tac[abi_encoder_translation_admissible] >>
      qexistsl [`ct`,`rv`] >> asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  qexistsl [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (irule abi_tuple_row_effects_trans_mods >>
      qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ st s G tn en z Gz tz` (irule_at Any) >>
      irule abi_tuple_row_effects_trans_mods >>
      qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ prep q Gq tq st s G tn` (irule_at Any) >>
      asm_rewrite_tac[]) >>
  qx_gen_tac `D` >> irule gas_origin_ptr_path_trans >> qexistsl [`Gq`,`q`,`tq`] >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tu) [] _` (qspec_then `D` ACCEPT_TAC)) >>
  irule gas_origin_ptr_path_trans >> qexistsl [`G`,`s`,`tn`] >>
  conj_tac
  >- (qpat_assum `!D. gas_origin_ptr_path _ (q,Gq,tq) [] _` (qspec_then `D` ACCEPT_TAC)) >>
  qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _` (qspec_then `D` ACCEPT_TAC)
QED

Finalise abi_tuple_dynamic_row_mods
