(* Shifted same-witness array traversal boundaries. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteArrayRun
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteArrayIteration
  ctorDeployMemoryRunPtrPrefixLoopHeader ctorDeployLoweringEntryCompleteArrayRun
  abiDecoderLoop abiDecoderExecution abiDecoderContract abiDecoderReentry
  abiDecoderArrayBackedge ctorDeployLoweringEntryArrayOps
  abiDecoderRecursiveLoopContext abiDecoderTypedContract abiCanonicalHeadSize
  ctorDeployLoweringEntryArrayFrame relation
  ctorDeployMemoryRunPtrPrefixLoopElement ctorDeployMemoryRunPtrPrefixLoopClose
  abiDecoderVarSequence venomInst abiDecoderArraySetupCode
  abiDecoderPrimitiveLoopEntry ctorDeployMemoryRunPtrPrefixLoopSetup
  abiDecoderDynamicLoopSetup ctorAbiActualAlloc ctorAbiActualArrayInvariant
  ctorDeployLoweringEntryRegistration ctorDeployLoweringEntryCompleteScalar
  compileEnv venomState venomExecSemantics venomMemDefs valueEncoding valueEncodingProps
  ptrSafeRun ptrDiscipline words arithmetic list finite_map pred_set

val Ok = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem prefix_complete_array_header_pair:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid (Var slot_var) src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next (Var slot_var) /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand (Var slot_var) s = SOME (n2w slot) /\
  eval_operand src s = SOME srcaddr /\
  abi_decode_load DLOAD srcaddr s = n2w (LENGTH vs) /\
  LENGTH vs < dimword(:256) /\ FLOOKUP G slot_var = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\ ~ctx_has_dalloca ctx /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn src = {} /\
  (!a. a<32 ==> slot+a NOTIN tn.t_mem) ==>
  let t = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)
  in ?H qt.
    (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j t /\
    abi_decode_sim ctx func s t /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. abi_decoder_older_vars next x ==> FLOOKUP H x = FLOOKUP G x) /\
    (!opr. abi_decoder_operand_live next opr ==>
      eval_operand opr t = eval_operand opr s /\ op_taint qt opr = op_taint tn opr) /\
    op_taint qt (Var (STRING #"%" (toString first))) = {} /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `iv = STRING #"%" (toString first)` >>
  qabbrev_tac `cv = STRING #"%" (toString (first+1))` >>
  qabbrev_tac `cmp = STRING #"%" (toString (first+2))` >>
  qabbrev_tac `done = STRING #"%" (toString (first+3))` >>
  `ALL_DISTINCT [iv;cv;cmp;done]` by
    simp[Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
  `!opr x. abi_decoder_operand_live next opr /\ MEM x [iv;cv;cmp;done] ==>
    opr <> Var x` by
    (pure_rewrite_tac[MEM] >> rpt gen_tac >> strip_tac >>
     gvs[Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
     irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  `~MEM slot_var [iv;cv;cmp;done] /\
   (!x. MEM x [iv;cv;cmp;done] ==> src <> Var x)` by metis_tac[] >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by fs[] >>
  `eval_operand src s = SOME (n2w (w2n srcaddr)) /\
   abi_decode_load DLOAD (n2w (w2n srcaddr):bytes32) s = n2w (LENGTH vs)` by simp[n2w_w2n] >>
  `lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr;bb_instructions := abi_decode_header_insts hid
      (Var slot_var) src DLOAD iv cv cmp done body_lbl exit_lbl|> /\
   (!lbl. MEM lbl [body_lbl;exit_lbl] ==> ?bb.
     lookup_block lbl func.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0)` by
    (gvs[abi_decode_loop_cfg_def,Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >> metis_tac[]) >>
  drule_all prefix_loop_header_operand_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all deploy_ctor_array_header_observation >>
  disch_then (qspec_then `if j < LENGTH vs then body_lbl else exit_lbl` assume_tac) >>
  rule_assum_tac BETA_RULE >>
  qexistsl [`H`,`qt`] >>
  asm_simp_tac bool_ss [Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >>
  conj_tac >- (rpt strip_tac >>
    `abi_decoder_operand_live next (Var x)` by
      simp[abi_decoder_operand_live_def,IN_DEF] >>
    `~MEM x [STRING #"%" (toString first); STRING #"%" (toString (first+1));
       STRING #"%" (toString (first+2)); STRING #"%" (toString (first+3))]` by
      (strip_tac >> qpat_x_assum `!opr x. _` (qspecl_then [`Var x`,`x`] mp_tac) >> simp[]) >>
    qpat_x_assum `!x. ~MEM x _ ==> _` drule >> simp[]) >>
  conj_tac >-
    (gen_tac >> strip_tac >> namedCases_on `opr` ["w","x","lab"]
     >- simp[eval_operand_def,op_taint_def]
     >- (`~MEM x [STRING #"%" (toString first); STRING #"%" (toString (first+1));
          STRING #"%" (toString (first+2)); STRING #"%" (toString (first+3))]` by
          (strip_tac >> qpat_x_assum `!opr x. _` (qspecl_then [`Var x`,`x`] mp_tac) >> simp[]) >>
         qpat_x_assum `!x. ~MEM x _ ==> _` drule >> simp[]) >>
     simp[eval_operand_def,op_taint_def,jump_to_def,abi_decode_header_state_def,update_var_def]) >>
  simp[jump_to_def,abi_decode_header_state_def,update_var_def]
QED

Theorem prefix_complete_array_header_reach_pair:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src dst
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src dst
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  FLOOKUP G slot_var = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\ ~ctx_has_dalloca ctx /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn src = {} /\
  (!a. a < 32 ==> slot+a NOTIN tn.t_mem) ==>
  ?t H qt.
    (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j t /\
    abi_decode_sim ctx func s t /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!x. abi_decoder_older_vars next x ==> FLOOKUP H x = FLOOKUP G x) /\
    (!opr. abi_decoder_operand_live next opr ==>
      eval_operand opr t = eval_operand opr s /\ op_taint qt opr = op_taint tn opr) /\
    t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand (Var slot_var) s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (`!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
        eval_operand op s = SOME w` by
       (rpt strip_tac >> drule_all deploy_ctor_array_observation_operand >> simp[]) >>
     fs[abi_decoder_ranges_def, Excl "enc_def"] >> conj_tac >> first_x_assum irule >> simp[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword(:256)` by
    fs[abi_decoder_ranges_def,Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb:bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all prefix_complete_array_header_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  goal_assum (drule_at Any) >> fs[]
QED

(* The persistent relation carries operational and ambient frames together. *)
val Frame = ``\(s,G,tn,B) (t,H,qt,A).
  abi_decode_sim ctx func s t /\ qt.t_mem SUBSET tn.t_mem /\
  qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
  (!x. abi_decoder_older_vars next x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x) /\
    lookup_var x t = lookup_var x s) /\
  B SUBSET A /\
  (!a. a IN B ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  (!a. a < lo ==> read_byte a t.vs_memory = read_byte a s.vs_memory) /\
  t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\
  ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
    !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)``;

Theorem prefix_complete_array_frame_transitive:
  transitive (^Frame)
Proof
  simp_tac bool_ss [transitive_def] >>
  rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >> PairCases_on `z` >>
  simp_tac std_ss [] >> strip_tac >> rpt conj_tac >>
  metis_tac[abi_decode_sim_trans,SUBSET_TRANS,SUBSET_DEF]
QED

val Pk = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src (Var dst_var)
    sb d slot slot 32 next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  fn_inst_ids_distinct func /\ k + unit_alloca_budget ctx < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  lo <= slot /\ lo <= d /\ D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  slot_id IN ctor_actual_sites func ids /\ frag_ids st end_st SUBSET ids /\
  slot_id NOTIN frag_ids middle end_st /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+cap``;

val LoopAt = ``\label index j (s,G,tn,B).
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = index /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  FLOOKUP G slot_var = SOME (slot,32) /\ FLOOKUP G dst_var = SOME (b,cap) /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn (Var dst_var) = {} /\ op_taint tn src = {} /\
  DISJOINT tn.t_mem {a | slot <= a /\ a < slot+32} /\
  FINITE B /\ B SUBSET range_bytes [(d,32+j*type_memory_size tv)] /\ DISJOINT B tn.t_mem /\
  (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 s.vs_memory) ==>
    mload d (s with vs_memory := mem) = n2w (LENGTH vs) /\
    elems_in_memory (TAKE j vs) (d+32) tv mem)``;

Theorem prefix_complete_array_header_frame_pair:
  (^Pk) /\ (^LoopAt) hdr 0 j X ==>
  ?Y. (^LoopAt) (if j < LENGTH vs then st.cs_current_bb else exit_lbl) 0 j Y /\
    (^Frame) X Y
Proof
  PairCases_on `X` >> simp_tac std_ss [] >> strip_tac >>
  `slot+32 <= X0.vs_alloca_next /\ X0.vs_alloca_next < dimword(:256)` by
    (fs[alloca_inv_def,alloca_next_valid_def] >>
     metis_tac[deploy_ctor_shifted_frontier_bound]) >>
  `!a. a < 32 ==> slot+a NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+a` mp_tac) >> simp[]) >>
  drule_all (BETA_RULE prefix_complete_array_header_reach_pair) >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >> strip_tac >>
  qexists_tac `(t,H,qt,X3)` >> simp_tac std_ss [] >>
  `abi_decoder_operand_live next (Var slot_var) /\
   abi_decoder_operand_live next (Var dst_var) /\ abi_decoder_operand_live next src` by
    fs[abi_decoder_recursive_loop_data_def] >>
  `!x. abi_decoder_older_vars next x ==> abi_decoder_operand_live next (Var x)` by
    simp[abi_decoder_operand_live_def,IN_DEF] >>
  `abi_decoder_older_vars next slot_var /\ abi_decoder_older_vars next dst_var` by
    fs[abi_decoder_operand_live_def,IN_DEF] >>
  `!mem. mload d (t with vs_memory := mem) = mload d (X0 with vs_memory := mem)` by
    simp[mload_def] >>
  simp[SUBSET_REFL] >> rpt conj_tac >> metis_tac[eval_operand_def]
QED

Theorem prefix_complete_array_terminal_pair:
  (^Pk) /\ (^LoopAt) hdr 0 (LENGTH vs) X ==>
  ?Y. (^LoopAt) exit_lbl 0 (LENGTH vs) Y /\ (^Frame) X Y
Proof
  strip_tac >> drule_all prefix_complete_array_header_frame_pair >> simp[]
QED

Theorem prefix_complete_array_setup_ambient:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) di asz msz st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t ==>
  t.vs_code = s.vs_code /\ t.vs_gas_readings = s.vs_gas_readings /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st middle)` by
    (drule prefix_loop_element_setup_code >> simp[LET_THM] >>
     strip_tac >> Cases_on `dec_info_needs_offset di` >>
     gvs[abi_decoder_reentry_opcode_def,mk_inst_def]) >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_ambient >> simp[]
QED

Theorem prefix_complete_array_setup_vars:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) di asz msz st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  abi_decoder_older_vars next x /\ next <= st.cs_next_var ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> drule ctor_actual_sequence_var_frame >>
  disch_then irule >>
  drule prefix_loop_element_setup_code >> simp[LET_THM] >> strip_tac >>
  `!n. x <> STRING #"%" (toString (st.cs_next_var+n))` by
    (fs[abi_decoder_older_vars_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `st.cs_next_var+n` mp_tac) >> simp[]) >>
  Cases_on `dec_info_needs_offset di` >>
  gvs[mk_inst_def,is_terminator_def] >>
  metis_tac[ADD_COMM,ADD_0]
QED

Theorem prefix_complete_array_body_pair:
  (^Pk) /\ j < LENGTH vs /\
  (^LoopAt) st.cs_current_bb (LENGTH st.cs_current_insts) j X ==>
  ?prepared H qt.
    (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial j j prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
    eval_operand (FST ops) prepared = SOME (n2w j) /\
    eval_operand (FST (SND ops)) prepared = SOME (n2w (sb +
      abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)) /\
    eval_operand (SND (SND ops)) prepared = SOME (n2w (d+32+j*type_memory_bytes ce ty)) /\
    abi_decoder_operand_live middle.cs_next_var (FST ops) /\
    abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
    op_taint qt (FST ops) = {} /\ op_taint qt (FST (SND ops)) = {} /\
    op_taint qt (SND (SND ops)) = {} /\
    op_prov H (SND (SND ops)) = SOME (b,cap) /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
    prepared.vs_memory = (FST X).vs_memory /\
    (^Frame) X (prepared,H,qt,SND (SND (SND X)))
Proof
  PairCases_on `X` >> simp_tac std_ss [] >> strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  PairCases_on `ops` >> gvs[Excl "enc_def"] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_array_body_code >> simp_tac std_ss [] >>
  disch_then drule_all >> strip_tac >>
  `elems_in_memory (TAKE j vs) (d+32) tv X0.vs_memory` by
    (qpat_x_assum `!mem. _` (qspec_then `X0.vs_memory` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live next (Lit (0w:bytes32))` by
    simp[abi_decoder_operand_live_def] >>
  `abi_decoder_ranges DLOAD (Lit 0w) src (Var dst_var) sb
     (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot 32 X0` by
    (fs[abi_decoder_ranges_def,Excl "enc_def"] >>
     Cases_on `src` >>
     fs[eval_operand_def,abi_decoder_operand_live_def,IN_DEF] >> metis_tac[]) >>
  `eval_operand (Var slot_var) X0 = SOME (n2w slot)` by
    (fs[eval_operand_def,abi_decoder_operand_live_def,IN_DEF] >> metis_tac[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     X0.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    simp[Excl "enc_def"] >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst_var)` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `slot < dimword(:256)` by
    (fs[alloca_inv_def,alloca_next_valid_def] >>
     metis_tac[deploy_ctor_shifted_frontier_bound]) >>
  `!a. a < 32 ==> slot+a NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+a` mp_tac) >> simp[]) >>
  drule_all prefix_loop_element_setup_at_index_pair >>
  disch_then (qspecl_then [`func`,`PG`,`Ddead`] strip_assume_tac) >>
  `X0.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all prefix_loop_setup_execution_pair >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func X0 prepared` >>
  drule_all prefix_complete_array_setup_ambient >> strip_tac >>
  `(^Ok) k ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
     tv vs slot_id slot initial j j t` by
    (BETA_TAC >> irule (BETA_RULE deploy_ctor_array_observation_address) >>
     simp[Excl "enc_def"] >>
     qexistsl [`st.cs_next_var`,`X0`] >> simp[Excl "enc_def"]) >>
  `(^Ok) k ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
     tv vs slot_id slot initial j j prepared` by
    (unabbrev_all_tac >>
     pure_rewrite_tac[deploy_ctor_array_observation_inst_idx] >> asm_rewrite_tac[]) >>
  qexistsl [`prepared`,`H`,`qt`] >>
  `!x. abi_decoder_older_vars next x ==> not_fresh_at st x` by
    (fs[abi_decoder_older_vars_def,not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x X0` by
    (rpt strip_tac >> drule_all prefix_complete_array_setup_vars >> simp[]) >>
  `t.vs_memory = X0.vs_memory` by fs[abi_decoder_address_frame_def] >>
  unabbrev_all_tac >>
  pure_rewrite_tac[deploy_ctor_array_observation_inst_idx] >>
  rule_assum_tac BETA_RULE >>
  gvs[SUBSET_REFL,lookup_var_def,op_prov_def,allocas_from_def,Excl "enc_def"] >>
  metis_tac[]
QED

Theorem prefix_complete_array_header_support:
  (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 s.vs_memory) ==>
    mload d (s with vs_memory := mem) = n2w n /\
    elems_in_memory xs p tv mem) ==>
  !mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 s.vs_memory) ==>
    mem_bytes_at d 32 mem = mem_bytes_at d 32 s.vs_memory /\
    elems_in_memory xs p tv mem
Proof
  strip_tac >>
  `mload d s = n2w n` by
    (first_x_assum (qspec_then `s.vs_memory` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
  `mload d (s with vs_memory := mem) = mload d s` by simp[] >>
  drule mload_eq_mem_bytes_at_eq >> simp[]
QED

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_complete_array_body_iteration_pair:
  (^CshiftCode) ty tv ==>
  (^Pk) /\ j < LENGTH vs /\
  (^LoopAt) st.cs_current_bb (LENGTH st.cs_current_insts) j X ==>
  ?Y. (^LoopAt) hdr 0 (SUC j) Y /\ (^Frame) X Y
Proof
  disch_then (mk_asm "child") >> strip_tac >>
  drule_all prefix_complete_array_body_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  PairCases_on `X` >> fs[Excl "enc_def"] >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  PairCases_on `ops` >> gvs[Excl "enc_def"] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_array_body_code >> simp_tac std_ss [] >>
  disch_then drule_all >> strip_tac >>
  `prepared.vs_data_section = initial.vs_data_section` by fs[] >>
  drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)
    (SIMP_RULE std_ss [Once type_memory_bytes_def,Once ADD_COMM] (Q.INST [`hi` |-> `Lit (0w:bytes32)`]
      ctor_actual_array_child_inputs_at_index)) >>
  disch_then (drule_at (Pat `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sf`,`prepared`,`j`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  Cases_on `ops2` >> gvs[op_prov_def] >> rename1 `FLOOKUP H child_dst = SOME (b,cap)` >>
  `abi_decoder_older_vars next slot_var /\ abi_decoder_older_vars next dst_var` by
    fs[abi_decoder_operand_live_def,IN_DEF] >>
  `FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst_var = SOME (b,cap) /\
   op_taint qt (Var slot_var) = {} /\ op_taint qt (Var dst_var) = {} /\
   eval_operand (Var slot_var) prepared = SOME (n2w slot)` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  `!x. ops1 = Var x \/ Var child_dst = Var x \/ Lit (0w:bytes32) = Var x ==>
    not_fresh_at middle x` by
    (gen_tac >> strip_tac
     >- (qpat_x_assum `ops1 = Var x` SUBST_ALL_TAC >>
         qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var x)` mp_tac >>
         simp_tac (srw_ss()) [abi_decoder_operand_live_def,IN_DEF,
           abi_decoder_older_vars_def,not_fresh_at_def])
     >- (gvs[operand_11] >>
         qpat_assum `abi_decoder_operand_live middle.cs_next_var (Var _)` mp_tac >>
         simp_tac (srw_ss()) [abi_decoder_operand_live_def,IN_DEF,
           abi_decoder_older_vars_def,not_fresh_at_def]) >>
     fs[]) >>
  `!x. abi_decoder_older_vars next x ==> not_fresh_at middle x` by
    (fs[abi_decoder_older_vars_def,not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `not_fresh_at middle (STRING #"%" (toString st.cs_next_var))` by
    (fs[abi_decoder_operand_live_def,IN_DEF,abi_decoder_older_vars_def,
      not_fresh_at_def] >> metis_tac[]) >>
  `!mem. (!a. a IN X3 ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 prepared.vs_memory) ==>
    mem_bytes_at d 32 mem = mem_bytes_at d 32 prepared.vs_memory /\
    elems_in_memory (TAKE j vs) (d+32) tv mem` by
    (drule prefix_complete_array_header_support >> simp[]) >>
  `?hdr_bb. lookup_block hdr func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (fs[abi_decode_loop_cfg_def,abi_decode_header_insts_def,
      phi_prefix_length_def,mk_inst_def]) >>
  `?t H' qt' A.
    (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func prepared t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    FLOOKUP H' slot_var = SOME (slot,32) /\ FLOOKUP H' dst_var = SOME (b,cap) /\
    op_taint qt' (Var slot_var) = {} /\ op_taint qt' (Var dst_var) = {} /\
    qt'.t_mem SUBSET qt.t_mem /\ DISJOINT qt'.t_mem {a | slot <= a /\ a < slot+32} /\
    qt'.t_stor = qt.t_stor /\ qt'.t_trans = qt.t_trans /\ qt'.t_imm = qt.t_imm /\
    (!x. abi_decoder_older_vars next x ==> FLOOKUP H' x = FLOOKUP H x /\
      op_taint qt' (Var x) = op_taint qt (Var x)) /\
    FINITE A /\ A SUBSET range_bytes [(d,32+SUC j*type_memory_size tv)] /\
    DISJOINT A qt'.t_mem /\ X3 SUBSET A /\
    (!a. a IN X3 ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 prepared.vs_memory) /\
    (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 t.vs_memory) ==>
      mem_bytes_at d 32 mem = mem_bytes_at d 32 prepared.vs_memory /\
      elems_in_memory (TAKE (SUC j) vs) (d+32) tv mem) /\
    t.vs_code = prepared.vs_code /\ t.vs_gas_readings = prepared.vs_gas_readings /\
    t.vs_outcomes = prepared.vs_outcomes /\ t.vs_tx_ctx = prepared.vs_tx_ctx /\
    t.vs_block_ctx = prepared.vs_block_ctx /\
    (!x. abi_decoder_older_vars next x ==> lookup_var x t = lookup_var x prepared) /\
    (!a. a < lo ==> read_byte a t.vs_memory = read_byte a prepared.vs_memory) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H' qt' t) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared)` by
    (asm_x "child" (irule o MATCH_MP prefix_complete_child_iteration) >>
     rpt conj_tac >> asm_rewrite_tac[]
     >- decide_tac
     >- decide_tac
     >- (simp[Once ADD_COMM] >> irule LESS_MONO_MULT2 >> simp[])
     >- (`SUC j * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by
           (irule LESS_MONO_MULT2 >> simp[]) >> decide_tac)
     >- (qexists_tac `hdr_bb` >> simp[])
     >- (irule DISJOINT_SUBSET >> qexists_tac `X2.t_mem` >> simp[DISJOINT_SYM])
     >- simp[Once ADD_COMM]
     >- (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _` (irule_at Any) >>
         qpat_assum `abi_decoder_metadata ce env ty tv _ _ _` (irule_at Any) >>
         qpat_assum `bb.bb_instructions = _` (irule_at Any) >>
         simp_tac std_ss [] >> rpt conj_tac >> asm_rewrite_tac[] >>
         qexists_tac `sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j` >>
         simp_tac std_ss [AC ADD_ASSOC ADD_COMM] >> rpt conj_tac >> asm_rewrite_tac[]
         >- (qpat_assum `sb + (LENGTH _ + _) < _` mp_tac >> simp_tac std_ss [AC ADD_ASSOC ADD_COMM])
         >- decide_tac
         >- decide_tac
         >- decide_tac
         >- (irule SUBSET_TRANS >> qexists_tac `frag_ids st end_st` >>
             simp[abiEncoderPropsTheory.frag_ids_def,SUBSET_DEF] >> decide_tac)
         >> metis_tac[]) >>
     simp_tac std_ss [] >> rpt conj_tac >> asm_rewrite_tac[]
     >- decide_tac
     >- decide_tac
     >- (qpat_x_assum `!mem. (!a. a IN X3 ==> _) ==> mload _ _ = _ /\ _`
           (qspec_then `X0.vs_memory` mp_tac) >> simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H x = _ /\ _` drule >>
     strip_tac >> metis_tac[]) >>
  suspend "compose"
QED

Resume prefix_complete_array_body_iteration_pair[compose]:
  asm_x "child" kall_tac >>
  pop_assum strip_assume_tac >>
  qexists_tac `(t,H',qt',A)` >>
  rule_assum_tac BETA_RULE >>
  rpt (first_x_assum (CONJUNCTS_THEN assume_tac)) >>
  simp_tac std_ss [] >>
  rpt conj_tac >> asm_rewrite_tac[]
  >- (qpat_assum `abi_encoder_registered_effect _ [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] initial t` mp_tac >>
      simp_tac std_ss [Once type_memory_bytes_def,ADD_COMM])
  >- (namedCases_on `src` ["w","sx","lab"]
      >- simp[op_taint_def]
      >- (`abi_decoder_older_vars next sx` by
            (qpat_assum `abi_decoder_operand_live next (Var sx)` mp_tac >>
             simp_tac (srw_ss()) [abi_decoder_operand_live_def,IN_DEF]) >>
          qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H' x = _ /\ _`
            (qspec_then `sx` mp_tac) >>
          qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H x = _ /\ _`
            (qspec_then `sx` mp_tac) >> simp[]) >>
      simp[op_taint_def])
  >- (qpat_assum `A SUBSET range_bytes _` mp_tac >>
      qpat_assum `type_memory_size tv = _` (fn th => rewrite_tac[th]) >>
      simp_tac std_ss [ADD_COMM])
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!mem. (!a. a IN A ==> _) ==> _` drule >> strip_tac >>
      conj_tac >-
        (qpat_assum `mload d prepared = _` mp_tac >>
         pure_rewrite_tac[mload_def,LET_THM,GSYM mem_bytes_at_def] >>
         simp_tac (srw_ss()) [] >>
         qpat_assum `mem_bytes_at d 32 mem = _` (fn th => rewrite_tac[th])) >>
      asm_rewrite_tac[])
  >- (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_rewrite_tac[])
  >- (irule SUBSET_TRANS >> qexists_tac `qt.t_mem` >> asm_rewrite_tac[])
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H' x = _ /\ _` drule >>
      qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H x = _ /\ _` drule >>
      qpat_x_assum `!x. abi_decoder_older_vars next x ==> lookup_var x t = _` drule >>
      simp_tac std_ss [] >> metis_tac[])
  >- (qpat_assum `!a. a IN X3 ==> mem_bytes_at a 1 t.vs_memory = _` mp_tac >>
      qpat_assum `prepared.vs_memory = X0.vs_memory` (fn th => rewrite_tac[th]))
  >- (qpat_assum `!a. a < lo ==> read_byte a t.vs_memory = _` mp_tac >>
      qpat_assum `prepared.vs_memory = X0.vs_memory` (fn th => rewrite_tac[th])) >>
  disch_tac >>
  qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ H qt prepared) ==> _` irule >>
  qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ H' qt' t) ==> _` irule >>
  asm_rewrite_tac[]
QED

Finalise prefix_complete_array_body_iteration_pair

Theorem prefix_complete_array_successor_pair:
  (^CshiftCode) ty tv ==> 
  (^Pk) /\ j < LENGTH vs /\ (^LoopAt) hdr 0 j X ==>
  ?Y. (^LoopAt) hdr 0 (SUC j) Y /\ (^Frame) X Y
Proof
  disch_then (mk_asm "child") >> strip_tac >>
  drule_all prefix_complete_array_header_frame_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `st.cs_current_insts = []` by fs[abi_decoder_recursive_loop_compiled_def] >>
  `?Z. (^LoopAt) hdr 0 (SUC j) Z /\ (^Frame) Y Z` by
    (asm_x "child" (irule o MATCH_MP prefix_complete_array_body_iteration_pair) >>
     asm_rewrite_tac[LENGTH] >> conj_tac
     >- (qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (irule_at Any) >> asm_rewrite_tac[]) >>
     qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >> asm_rewrite_tac[LENGTH]) >>
  qexists_tac `Z` >> asm_rewrite_tac[] >>
  mp_tac prefix_complete_array_frame_transitive >>
  simp_tac std_ss [transitive_def] >> metis_tac[]
QED

Theorem prefix_complete_array_finite_pair:
  (^CshiftCode) ty tv ==> (^Pk) ==>
  !n j X. LENGTH vs = j+n /\ (^LoopAt) hdr 0 j X ==>
    ?Y. (^LoopAt) exit_lbl 0 (LENGTH vs) Y /\ (^Frame) X Y
Proof
  disch_tac >> strip_tac >> Induct
  >- (rpt gen_tac >> pure_rewrite_tac[ADD_0] >> strip_tac >>
      qpat_x_assum `LENGTH vs = j` (SUBST_ALL_TAC o SYM) >>
      irule prefix_complete_array_terminal_pair >> asm_rewrite_tac[] >>
      qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> asm_rewrite_tac[] >>
      qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j < LENGTH vs` by decide_tac >>
  drule_all prefix_complete_array_successor_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >> strip_tac >>
  qpat_x_assum `!j X. _` (qspecl_then [`SUC j`,`Y`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> decide_tac) >>
  strip_tac >> qexists_tac `Y'` >> asm_rewrite_tac[] >>
  mp_tac prefix_complete_array_frame_transitive >>
  pure_rewrite_tac[transitive_def] >> disch_then irule >>
  qexists_tac `Y` >> asm_rewrite_tac[]
QED

Theorem prefix_complete_array_prepared_pair:
  (^CshiftCode) ty tv ==> (^Pk) /\
  (^LoopAt) prepared.vs_current_bb (LENGTH prefix) 0 (prepared,G,tn,B) /\
  lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  ?actual H qt A.
    (^LoopAt) exit_lbl 0 (LENGTH vs) (actual,H,qt,A) /\
    (^Frame) (prepared,G,tn,B) (actual,H,qt,A) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem)
Proof
  disch_then (mk_asm "child") >> strip_tac >>
  `(^LoopAt) hdr 0 0 (jump_to hdr prepared,G,tn,B) /\
   (^Frame) (prepared,G,tn,B) (jump_to hdr prepared,G,tn,B)` by
    (qpat_x_assum `(^LoopAt) _ _ _ _` mp_tac >>
     simp_tac std_ss [] >> strip_tac >>
     `(^Ok) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial 0 0 (jump_to hdr prepared)` by
       (irule deploy_ctor_array_observation_jump >> simp_tac std_ss [] >> asm_rewrite_tac[]) >>
     drule_all abi_decoder_loop_entry_sim >>
     disch_then (qspec_then `ctx` assume_tac) >>
     `get_instruction bb prepared.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] [])` by
       simp[get_instruction_def,EL_APPEND_EQN] >>
     `(!fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn (jump_to hdr prepared)) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn prepared` by
       (match_mp_tac (Q.INST [`iid` |-> `id`] prefix_loop_entry_jump_run) >>
        asm_rewrite_tac[]) >>
     qpat_x_assum `(^Ok) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (jump_to hdr prepared)`
       (strip_assume_tac o BETA_RULE) >>
     asm_rewrite_tac[] >>
     fs[jump_to_def,allocas_from_def,mload_def,lookup_var_def] >>
     metis_tac[]) >>
  asm "child" (mp_tac o MATCH_MP prefix_complete_array_finite_pair) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qspecl_then [`LENGTH vs`,`0`,`(jump_to hdr prepared,G,tn,B)`] mp_tac) >>
  asm_rewrite_tac[ADD] >> strip_tac >> PairCases_on `Y` >>
  qexistsl [`Y0`,`Y1`,`Y2`,`Y3`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (mp_tac prefix_complete_array_frame_transitive >>
      pure_rewrite_tac[transitive_def] >> disch_then irule >>
      qexists_tac `(jump_to hdr prepared,G,tn,B)` >> asm_rewrite_tac[]) >>
  qpat_x_assum `(^LoopAt) exit_lbl _ _ _` mp_tac >>
  simp_tac std_ss [TAKE_LENGTH_ID] >> strip_tac >>
  simp[val_in_memory_dynarray] >>
  fs[mload_def,mem_word_at_def] >> metis_tac[]
QED

val _ = export_theory();
