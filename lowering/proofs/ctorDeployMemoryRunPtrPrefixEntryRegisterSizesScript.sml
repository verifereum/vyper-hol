(* Same-witness registration decoder with literal allocation sizes. *)
Theory ctorDeployMemoryRunPtrPrefixEntryRegisterSizes
Ancestors
 ctorDeployMemoryRunPtrPrefixEntryLiteralSizes
 ctorDeployLoweringEntryRegisterSizes ctorDeployMemoryRunPtrPrefixEntryRegisterOne
 ctorDeployMemoryRunPtrPrefixEntryRegisterAlloc
 ctorDeployMemoryRunPtrPrefixRegisterOne ctorDeployMemoryRunPtrPrefixRegisterAlloc
 ctorDeployMemoryRunPtrPrefixEntryRegisterDecode
 ctorDeployMemoryRunPtrPrefixCompleteCoherent
 ctorDeployMemoryRunPtrPrefixEntryRegisterAddress
 ctorRegisterArgs abiDecoderCode abiDecoderContract abiEncoderRegisteredEffect
 abiDecoderCoherence abiDecoderCounters ctorAbiActualFrame abiDecoderLoop
 abiEncoderProps emitHelperProps fragExec compileEnv
 localPtrsProps entryArgPtrs loweringHalt moduleLowering context venomInst venomExecSemantics
 allocaFrontierBound allocaBudgetProps venomMemDefs ctorAbiActualSites ctorDeployMemoryFrontier
 ptrSafeRun ptrDiscipline venomState finite_map words arithmetic pred_set list rich_list

Theorem prefix_entry_register_decode_sizes:
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 fresh_vars_wrt st initial /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next /\ lo <= d /\
 (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
 ?actual H qt B.
 (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st last) 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt last actual /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = last.cs_current_bb /\
 actual.vs_inst_idx = LENGTH last.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all prefix_entry_register_decode_paired >>
 disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
 disch_then (qx_choose_then `actual` (qx_choose_then `H` (qx_choose_then `qt`
   (qx_choose_then `B` (map_every assume_tac o CONJUNCTS))))) >>
 qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[] >>
 drule (SRULE [ctor_actual_scratch_sites] prefix_entry_decoder_literal_sizes) >>
 disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
 disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
 simp[] >> disch_tac >> rpt gen_tac >> strip_tac >>
 first_x_assum irule >> asm_rewrite_tac[] >>
 qexistsl [`b'`,`inst`] >> asm_rewrite_tac[]
QED

Theorem prefix_entry_register_address_decode_sizes:
 !ptr. i < LENGTH atys /\ LENGTH avs = LENGTH atys /\
 EL i atys = vyper_to_abi_type env ty /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 LENGTH encoded < dimword (:256) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) v /\
 FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
   DLOAD (Lit 0w) 0 st = ((),last) /\
 fresh_vars_wrt st initial /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 FLOOKUP G ptr = SOME (b,sz) /\ b <= d /\ d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn (Var ptr) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next /\ lo <= d /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
 ?actual H qt B.
 (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st last) 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt last actual /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = last.cs_current_bb /\
 actual.vs_inst_idx = LENGTH last.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
 actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all prefix_entry_register_canonical_address_paired >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
 disch_then (qx_choose_then `src` (qx_choose_then `middle`
   (qx_choose_then `prepared` (qx_choose_then `sb` (qx_choose_then `AG`
     (qx_choose_then `atn` (map_every assume_tac o CONJUNCTS))))))) >>
 `middle.cs_current_bb = st.cs_current_bb` by
   (qpat_x_assum `cs_extends st middle` mp_tac >> simp[cs_extends_def]) >>
 `alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared` by
   (asm_rewrite_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def] >>
    metis_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def]) >>
 `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
   (rpt strip_tac >> simp[] >> first_x_assum irule >> decide_tac) >>
 `FLOOKUP AG ptr' = SOME (b,sz) /\ op_taint atn (Var ptr') = {}` by metis_tac[] >>
 `d + type_memory_bytes ce ty <= prepared.vs_alloca_next /\
  lo <= prepared.vs_alloca_next` by simp[] >>
 `!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP prepared.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by
   (asm_rewrite_tac[]) >>
 drule_all prefix_entry_register_decode_sizes >>
 disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
 disch_then (qx_choose_then `actual` (qx_choose_then `H` (qx_choose_then `qt`
   (qx_choose_then `B` (map_every assume_tac o CONJUNCTS))))) >>
 `!x. not_fresh_at st x ==> not_fresh_at middle x` by
   (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[] >>
 conj_tac >- suspend "effect" >>
 conj_tac >- suspend "scratch" >>
 metis_tac[abi_decode_sim_trans]
QED

Resume prefix_entry_register_address_decode_sizes[effect]:
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle last))
   [(d,type_memory_bytes ce ty)] initial prepared` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}`,`[]`] >> simp[]) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle last))
   [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> simp[]) >>
 irule abi_encoder_registered_effect_enlarge >>
 goal_assum (drule_at Any) >> simp[ctor_actual_sites_def, SUBSET_DEF] >> metis_tac[SUBSET_DEF]
QED

Resume prefix_entry_register_address_decode_sizes[scratch]:
 `ctor_actual_scratch func (frag_ids middle last) 0 initial.vs_alloca_next actual` by
   metis_tac[] >>
 simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >> strip_tac >>
 Cases_on `inst.inst_id IN frag_ids middle last`
 >- (qpat_x_assum `ctor_actual_scratch func (frag_ids middle last) 0 initial.vs_alloca_next actual`
       (mp_tac o REWRITE_RULE [ctor_actual_scratch_def]) >>
     disch_then (qspecl_then [`inst`,`b'`,`sz'`] mp_tac) >> asm_rewrite_tac[]) >>
 `inst.inst_id NOTIN ctor_actual_sites func (frag_ids middle last)` by
   simp[ctor_actual_sites_def] >>
 `FLOOKUP prepared.vs_allocas inst.inst_id = NONE` by
   (simp[] >> first_x_assum irule >> fs[frag_ids_def]) >>
 fs[abi_encoder_registered_effect_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Finalise prefix_entry_register_address_decode_sizes

Theorem prefix_entry_register_one_slot_sizes:
  i < LENGTH atys /\ LENGTH avs = LENGTH atys /\
  EL i atys = vyper_to_abi_type env ty /\ has_types atys avs /\
  encoded = enc (Tuple atys) (ListV avs) /\
  off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
  LENGTH encoded < dimword (:256) /\
  mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
  FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
  lookup_scopes name [scope] = SOME entry /\ val_wf entry.type entry.value /\
  type_memory_size entry.type <= type_memory_bytes ce ty /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty entry.type /\
  abi_decoder_metadata ce env ty entry.type
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) entry.value /\
  type_memory_bytes ce ty < dimword (:256) /\
  compile_alloc_buffer (type_memory_bytes ce ty) st = (buf,sa) /\
  ce' = (ce with ce_vars := ce.ce_vars |+
    (name,PtrVar buf.buf_operand (type_memory_bytes ce ty))) /\
  compile_decode_args ce' [build_positional_arg ce (name,ty)] off
    DLOAD (Lit 0w) 0 sa = ((),last) /\
  local_ptrs_rel func ce [scope] initial /\ fresh_vars_wrt st initial /\
  fn_has_code st sa func /\ fn_has_code sa last func /\ fn_inst_ids_distinct func /\
  (sa.cs_blocks = last.cs_blocks \/ !bb.
    lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  ?actual H qt B.
    (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\
      FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
    (FLOOKUP actual.vs_allocas st.cs_next_id =
       SOME (initial.vs_alloca_next,type_memory_bytes ce ty) /\
     (?p. buf.buf_operand = Var p /\ not_fresh_at last p /\
       lookup_var p actual = SOME (n2w initial.vs_alloca_next)) /\
     local_region ce' [scope] actual name initial.vs_alloca_next
       (type_memory_bytes ce ty)) /\
    local_ptrs_rel func ce' [scope] actual /\
    abi_encoder_registered_effect (frag_ids st last) [] initial actual /\
    allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
    alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
    fresh_vars_wrt last actual /\
    (!aid. last.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
    actual.vs_data_section = initial.vs_data_section /\
    actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
    (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
    ~actual.vs_halted /\ actual.vs_current_bb = last.cs_current_bb /\
    actual.vs_inst_idx = LENGTH last.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    initial.vs_alloca_next <= actual.vs_alloca_next /\
    actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
    actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
    actual.vs_gas_readings = initial.vs_gas_readings /\
    (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
    FINITE B /\ B SUBSET range_bytes [(initial.vs_alloca_next,type_memory_bytes ce ty)] /\
    DISJOINT B qt.t_mem /\
    (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory entry.type entry.value initial.vs_alloca_next mem) /\
    (!j. j IN B ==> j < actual.vs_alloca_next) /\
    qt.t_mem SUBSET (tn.t_mem UNION
      {j | initial.vs_alloca_next <= j /\ j < actual.vs_alloca_next}) /\
    (!j. j < initial.vs_alloca_next /\ j IN qt.t_mem ==> j IN tn.t_mem) /\
    (!C. (!j. j IN C ==> j < initial.vs_alloca_next) /\ DISJOINT C tn.t_mem ==>
      DISJOINT C qt.t_mem) /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt actual) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >>
  drule_all prefix_entry_register_alloc_actual >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
  disch_then (qx_choose_then `a` (qx_choose_then `AG` (qx_choose_then `atn`
    (map_every assume_tac o CONJUNCTS)))) >>
  `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
  drule_all prefix_register_alloc_semantic_frame >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!inst base sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP a.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n` by
    (`a.vs_allocas = initial.vs_allocas |+
       (st.cs_next_id,(initial.vs_alloca_next,type_memory_bytes ce ty))` by
       simp[update_var_def] >>
     drule deploy_ctor_register_alloc_literal_sizes >>
     disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
     disch_then (drule_at (Pat `_ .vs_allocas = _`)) >>
     simp[] >> disch_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum irule >> asm_rewrite_tac[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_decoder_coherent ce' env ce'.ce_struct_fields ty entry.type /\
   abi_decoder_metadata ce' env ty entry.type
     (type_to_abi_dec_info ce'.ce_struct_fields ce' ty) (EL i avs) entry.value /\
   type_memory_bytes ce' ty = type_memory_bytes ce ty` by simp[] >>
  `compile_decode_args ce' [build_positional_arg ce' (name,ty)] off
     DLOAD (Lit 0w) 0 sa = ((),last)` by gvs[] >>
  `FLOOKUP ce'.ce_vars name = SOME (PtrVar
     (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce' ty))` by
    simp[FLOOKUP_UPDATE] >>
  `lookup_var (STRING #"%" (toString st.cs_next_var)) a =
     SOME (n2w initial.vs_alloca_next) /\
   mem_bytes_at 0 (LENGTH encoded) a.vs_data_section = encoded` by
    (simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE, Excl "enc_def"] >>
     gvs[Excl "enc_def"]) >>
  `FLOOKUP AG (STRING #"%" (toString st.cs_next_var)) =
     SOME (initial.vs_alloca_next,type_memory_bytes ce ty) /\
   op_taint atn (Var (STRING #"%" (toString st.cs_next_var))) = {}` by
    simp[op_taint_def, FLOOKUP_UPDATE] >>
  `EL i atys = vyper_to_abi_type env ty /\
   initial.vs_alloca_next + type_memory_bytes ce' ty <= a.vs_alloca_next /\
   initial.vs_alloca_next + type_memory_bytes ce ty <= a.vs_alloca_next` by simp[] >>
  drule_at (Pat `abi_decoder_coherent _ _ _ _ _`) prefix_entry_register_address_decode_sizes >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `lookup_var _ a = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP AG _ = _`)) >>
  disch_then (drule_at (Pat `mem_bytes_at _ _ a.vs_data_section = _`)) >>
  qpat_assum `type_memory_bytes ce' ty = _`
    (fn th => simp_tac bool_ss [th,LESS_EQ_REFL]) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
  disch_then (qx_choose_then `actual` (qx_choose_then `H` (qx_choose_then `qt`
    (qx_choose_then `B` (map_every assume_tac o CONJUNCTS))))) >>
  suspend "finish"
QED

Resume prefix_entry_register_one_slot_sizes[finish]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  `st.cs_next_id <= sa.cs_next_id /\ st.cs_next_var <= sa.cs_next_var` by decide_tac >>
  `sa.cs_next_id <= last.cs_next_id` by
    (qpat_assum `compile_decode_args ce' [build_positional_arg ce' _] _ _ _ _ _ = _` mp_tac >>
     metis_tac[ctor_decode_args_next_id, pairTheory.SND]) >>
  `!x. not_fresh_at st x ==> not_fresh_at sa x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `initial.vs_alloca_next <= a.vs_alloca_next` by simp[] >>
  `atn.t_mem = tn.t_mem UNION {j | initial.vs_alloca_next <= j /\ j < a.vs_alloca_next}` by simp[] >>
  drule_all prefix_register_taint_compose >> strip_tac >>
  qexistsl [`actual`,`H`,`qt`,`B`] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- suspend "slot" >> asm_rewrite_tac[] >>
  conj_tac >- suspend "locals" >>
  conj_tac >- suspend "effect" >>
  conj_tac >- suspend "sites" >>
  simp_tac (srw_ss()) [update_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  conj_tac >- decide_tac >>
  conj_tac >- (rpt strip_tac >> simp[] >> metis_tac[]) >>
  conj_tac >- suspend "support" >>
  conj_tac >- suspend "ghost" >>
  metis_tac[]
QED

Resume prefix_entry_register_one_slot_sizes[locals]:
  qpat_assum `ce' = _` (fn th => pure_once_rewrite_tac[th]) >>
  asm_rewrite_tac[] >> irule ctor_scratch_decode_bind_ptr >>
  conj_tac >- simp[] >>
  qexistsl [`initial.vs_alloca_next`,`entry`,`frag_ids sa last`,`a`,`sa`,
    `n2w initial.vs_alloca_next : bytes32`] >>
  asm_rewrite_tac[] >> simp[w2n_n2w] >> gvs[]
QED

Resume prefix_entry_register_one_slot_sizes[effect]:
  irule ctor_registered_alloc_decode_effect >>
  qexistsl [`a`,`st.cs_next_id`,`frag_ids st sa`,`initial.vs_alloca_next`,
    `ctor_actual_sites func (frag_ids sa last)`,`type_memory_bytes ce ty`] >>
  asm_rewrite_tac[] >>
  simp[frag_ids_def, ctor_actual_sites_def, SUBSET_DEF, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> decide_tac
QED

Resume prefix_entry_register_one_slot_sizes[sites]:
  rpt strip_tac >>
  `aid NOTIN ctor_actual_sites func (frag_ids sa last)` by
    (simp[ctor_actual_sites_def, frag_ids_def] >> decide_tac) >>
  qpat_x_assum `abi_encoder_registered_effect _ _ a actual` mp_tac >>
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
  `FLOOKUP actual.vs_allocas aid = FLOOKUP a.vs_allocas aid` by metis_tac[] >>
  simp[] >> first_x_assum irule >> decide_tac
QED

Resume prefix_entry_register_one_slot_sizes[support]:
  qpat_assum `B SUBSET _` mp_tac >>
  simp_tac (srw_ss()) [SUBSET_DEF, range_bytes_def] >>
  disch_tac >> gen_tac >> disch_tac >>
  qpat_x_assum `!x. x IN B ==> _` drule >> strip_tac >> decide_tac
QED

Resume prefix_entry_register_one_slot_sizes[ghost]:
  rpt strip_tac >>
  `not_fresh_at sa x` by metis_tac[] >>
  `x <> STRING #"%" (toString st.cs_next_var)` by metis_tac[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> FLOOKUP H x = _ /\ _` drule >>
  simp[op_taint_def, FLOOKUP_UPDATE]
QED

Resume prefix_entry_register_one_slot_sizes[slot]:
  `st.cs_next_id NOTIN ctor_actual_sites func (frag_ids sa last)` by
    (simp[ctor_actual_sites_def, frag_ids_def] >> decide_tac) >>
  `FLOOKUP a.vs_allocas st.cs_next_id =
     SOME (initial.vs_alloca_next,type_memory_bytes ce ty)` by
    simp[update_var_def, FLOOKUP_UPDATE] >>
  `FLOOKUP actual.vs_allocas st.cs_next_id =
     SOME (initial.vs_alloca_next,type_memory_bytes ce ty)` by
    (irule abi_encoder_registered_effect_allocated >>
     qexistsl [`ctor_actual_sites func (frag_ids sa last)`,
       `[(initial.vs_alloca_next,type_memory_bytes ce ty)]`,`a`] >> asm_rewrite_tac[]) >>
  `not_fresh_at sa (STRING #"%" (toString st.cs_next_var))` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `sa.cs_next_var <= last.cs_next_var` by
    metis_tac[ctor_decode_args_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND] >>
  `not_fresh_at last (STRING #"%" (toString st.cs_next_var))` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `lookup_var (STRING #"%" (toString st.cs_next_var)) actual =
     SOME (n2w initial.vs_alloca_next)` by metis_tac[] >>
  conj_tac >- simp[FLOOKUP_UPDATE] >>
  conj_tac >- (qexists `STRING #"%" (toString st.cs_next_var)` >> simp[]) >>
  simp[local_region_def, FLOOKUP_UPDATE, w2n_n2w] >> metis_tac[]
QED

Finalise prefix_entry_register_one_slot_sizes
