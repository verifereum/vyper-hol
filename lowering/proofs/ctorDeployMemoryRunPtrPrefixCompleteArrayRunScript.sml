(* Shifted same-witness array traversal boundaries. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteArrayRun
Ancestors
  loweringStateRelDefs valueEncodingDefs
  compileEnv valueEncoding entrySinkExtraction fragGasPathMem
  ctorDeployMemoryRunPtrPrefixCompleteArrayIteration
  ctorDeployMemoryRunPtrPrefixLoopHeader ctorDeployLoweringEntryCompleteArrayRun
  abiDecoderLoop abiDecoderExecution abiDecoderContract abiDecoderReentry
  abiDecoderArrayBackedge ctorDeployLoweringEntryArrayOps
  abiDecoderRecursiveLoopContext abiDecoderTypedContract abiCanonicalHeadSize
  ctorDeployLoweringEntryArrayFrame relation
  ctorDeployMemoryRunPtrPrefixLoopElement ctorDeployMemoryRunPtrPrefixLoopClose
  ctorDeployMemoryRunMemEntryArrayBody ctorDeployMemoryRunMemEntryArraySteps
  ctorDeployMemoryRunMemEntryCompositeSetup ctorDeployMemoryRunMemEntryCompositeEdges rich_list
  abiDecoderArrayInvariant abiDecoderArraySetupInputs
  abiDecoderVarSequence venomInst abiDecoderArraySetupCode
  abiDecoderPrimitiveLoopEntry ctorDeployMemoryRunPtrPrefixLoopSetup
  abiDecoderDynamicLoopSetup ctorAbiActualAlloc ctorAbiActualArrayInvariant
  ctorDeployLoweringEntryRegistration ctorDeployLoweringEntryCompleteScalar
  venomState venomExecSemantics venomMemDefs valueEncodingProps
  ptrSafeRun ptrDiscipline words arithmetic list finite_map pred_set
  fragGasOriginPtr fragGasOriginPtrLoop

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

Theorem prefix_complete_array_header_pair_mode:
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
  (!a. a<32 ==> slot+a NOTIN tn.t_mem) /\
  (checked ==> alloca_history func s /\ w2n srcaddr + 32 <= LENGTH s.vs_data_section) ==>
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
    (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) [] (OK t, H, qt)) /\
    (checked ==> gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t) /\
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
  `checked ==> gas_path_mem ctx func s 0
     (OK (jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
       (abi_decode_header_state iv cv cmp done j (LENGTH vs) s))) /\
     alloca_history func (jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
       (abi_decode_header_state iv cv cmp done j (LENGTH vs) s))` by
    (strip_tac >>
     `alloca_history func s /\ w2n srcaddr + 32 <= LENGTH s.vs_data_section` by simp[] >>
     `w2n srcaddr < dimword(:256)` by simp[w2n_lt] >>
     `slot < dimword(:256)` by decide_tac >>
     `src <> Var iv /\ iv <> cv` by
       (conj_tac >- simp[] >> fs[ALL_DISTINCT]) >>
     `eval_operand src s = SOME (n2w (w2n srcaddr)) /\
      abi_decode_load DLOAD (n2w (w2n srcaddr):bytes32) s = n2w (LENGTH vs)` by simp[n2w_w2n] >>
     drule_all ctor_checked_header_path >>
     disch_then (qspec_then `ctx` strip_assume_tac) >> simp[]) >>
  `eval_operand src s = SOME (n2w (w2n srcaddr)) /\
   abi_decode_load DLOAD (n2w (w2n srcaddr):bytes32) s = n2w (LENGTH vs)` by simp[n2w_w2n] >>
  `lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr;bb_instructions := abi_decode_header_insts hid
      (Var slot_var) src DLOAD iv cv cmp done body_lbl exit_lbl|> /\
   (!lbl. MEM lbl [body_lbl;exit_lbl] ==> ?bb.
     lookup_block lbl func.fn_blocks = SOME bb /\ phi_prefix_length bb.bb_instructions = 0)` by
    (gvs[abi_decode_loop_cfg_def,Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`] >> metis_tac[]) >>
  `checked ==> run_inst_seq_mem_ok (TAKE 4 (abi_decode_header_insts hid
     (Var slot_var) src DLOAD iv cv cmp done body_lbl exit_lbl)) s` by
    (strip_tac >>
     `w2n srcaddr + 32 <= LENGTH s.vs_data_section` by simp[] >>
     `w2n srcaddr < dimword(:256)` by simp[w2n_lt] >>
     `slot < dimword(:256)` by decide_tac >>
     `src <> Var iv` by simp[] >>
     metis_tac[ctor_checked_header_prefix_mem_ok]) >>
  drule_all prefix_loop_header_operand_path >>
  disch_then (mp_tac o Q.INST [`D` |-> `Ddead`] o SPEC_ALL) >>
  strip_tac >>
  TRY (qpat_x_assum `t = jump_to _ _` SUBST_ALL_TAC) >>
  `checked ==> !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
       (abi_decode_header_state iv cv cmp done j (LENGTH vs) s)),H,qt)` by
    metis_tac[] >>
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


Theorem prefix_complete_array_header_reach_pair_mode:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src dst
    DLOAD (Lit 0w) (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Lit 0w) (Var slot_var) src dst
    0 sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  FLOOKUP G slot_var = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\ ~ctx_has_dalloca ctx /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn src = {} /\
  (!a. a < 32 ==> slot+a NOTIN tn.t_mem) /\
  (checked ==> alloca_history func s /\
    sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
      LENGTH initial.vs_data_section) ==>
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
    (checked ==> !D explicit. gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) [] (OK t, H, qt)) /\
    (checked ==> gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand (Var slot_var) s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (`!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
        eval_operand op s = SOME w` by
       (rpt strip_tac >> drule_all deploy_ctor_array_observation_operand >> simp[]) >>
     fs[abi_decoder_ranges_def, eval_operand_def, Excl "enc_def"] >> conj_tac >> first_x_assum irule >> simp[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword(:256)` by
    fs[abi_decoder_ranges_def, eval_operand_def,Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb:bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  `checked ==> alloca_history func s /\ w2n (n2w sb:bytes32) + 32 <= LENGTH s.vs_data_section` by
    (strip_tac >>
     `has_type (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
       fs[abi_decoder_metadata_def,vyperABITheory.vyper_to_abi_type_def,Excl "enc_def"] >>
     `32 <= LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))` by
       (irule canonical_dynamic_array_head_min >> simp[contractABITheory.is_dynamic_def]) >>
     `sb < dimword(:256)` by decide_tac >>
     fs[w2n_n2w,Excl "enc_def"] >> decide_tac) >>
  drule_all prefix_complete_array_header_pair_mode >>
  disch_then (mp_tac o SPEC_ALL) >>
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

val FrameMode = ``\X Y. (^Frame) X Y /\
  (checked ==> gas_path_mem ctx func (FST X) 0 (OK (FST Y)) /\
    alloca_history func (FST Y) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (FST X,FST (SND X),FST (SND (SND X))) []
      (OK (FST Y),FST (SND Y),FST (SND (SND Y))))``;

Theorem prefix_complete_array_frame_transitive_mode:
  transitive (^FrameMode)
Proof
  simp_tac bool_ss [transitive_def] >>
  map_every qx_gen_tac [`x`,`y`,`z`] >>
  PairCases_on `x` >> PairCases_on `y` >> PairCases_on `z` >>
  simp_tac std_ss [] >> strip_tac >> rpt conj_tac
  >~ [`checked ==> _`]
  >- (strip_tac >> fs[] >> rpt strip_tac >>
      metis_tac[gas_path_mem_then,ADD_0,gas_origin_ptr_path_trans]) >>
  metis_tac[abi_decode_sim_trans,SUBSET_TRANS,SUBSET_DEF]
QED


val Pk = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Lit 0w) (Var slot_var) src (Var dst_var)
    0 sb d slot slot 32 next initial /\
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

val PkMode = ``(^Pk) /\ (checked ==>
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
    LENGTH initial.vs_data_section)``;
val LoopAtMode = ``\label index j X. (^LoopAt) label index j X /\
  (checked ==> alloca_history func (FST X))``;

Theorem prefix_complete_array_header_frame_pair_mode:
  (^PkMode) /\ (^LoopAtMode) hdr 0 j X ==>
  ?Y. (^LoopAtMode) (if j < LENGTH vs then st.cs_current_bb else exit_lbl) 0 j Y /\
    (^FrameMode) X Y
Proof
  PairCases_on `X` >> simp_tac std_ss [] >> strip_tac >>
  `slot+32 <= X0.vs_alloca_next /\ X0.vs_alloca_next < dimword(:256)` by
    (fs[alloca_inv_def,alloca_next_valid_def] >>
     metis_tac[deploy_ctor_shifted_frontier_bound]) >>
  `!a. a < 32 ==> slot+a NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+a` mp_tac) >> simp[]) >>
  `(checked ==> alloca_history func X0 /\
    sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
      LENGTH initial.vs_data_section)` by simp[] >>
  drule_all (BETA_RULE prefix_complete_array_header_reach_pair_mode) >>
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

Theorem prefix_complete_array_header_frame_pair:
  (^Pk) /\ (^LoopAt) hdr 0 j X ==>
  ?Y. (^LoopAt) (if j < LENGTH vs then st.cs_current_bb else exit_lbl) 0 j Y /\
    (^Frame) X Y
Proof
  mp_tac (prefix_complete_array_header_frame_pair_mode |> Q.INST [`checked` |-> `F`]) >> simp[]
QED

Theorem prefix_complete_array_terminal_pair_mode:
  (^PkMode) /\ (^LoopAtMode) hdr 0 (LENGTH vs) X ==>
  ?Y. (^LoopAtMode) exit_lbl 0 (LENGTH vs) Y /\ (^FrameMode) X Y
Proof
  strip_tac >> drule_all prefix_complete_array_header_frame_pair_mode >> simp[]
QED

Theorem prefix_complete_array_terminal_pair:
  (^Pk) /\ (^LoopAt) hdr 0 (LENGTH vs) X ==>
  ?Y. (^LoopAt) exit_lbl 0 (LENGTH vs) Y /\ (^Frame) X Y
Proof
  strip_tac >> drule_all prefix_complete_array_header_frame_pair >> simp[]
QED

Theorem prefix_complete_array_setup_ambient:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) (Lit 0w) di asz msz st = (ops,middle) /\
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
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) (Lit 0w) di asz msz st = (ops,middle) /\
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

Theorem prefix_complete_array_body_pair_mode:
  (^Pk) /\ j < LENGTH vs /\
  (^LoopAt) st.cs_current_bb (LENGTH st.cs_current_insts) j X /\
  (checked ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
     LENGTH initial.vs_data_section /\ alloca_history func (FST X)) ==>
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
    (^Frame) X (prepared,H,qt,SND (SND (SND X))) /\
    (checked ==> gas_path_mem ctx func (FST X) 0 (OK prepared) /\
                 alloca_history func prepared /\
                 !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                   (FST X,FST (SND X),FST (SND (SND X))) [] (OK prepared,H,qt))
Proof
  PairCases_on `X` >> simp_tac std_ss [] >> strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  PairCases_on `ops` >> gvs[Excl "enc_def"] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_array_body_code >> simp_tac std_ss [] >>
  disch_then drule_all >> strip_tac >>
  `elems_in_memory (TAKE j vs) (d+32) tv X0.vs_memory` by
    (qpat_x_assum `!mem. _` (qspec_then `X0.vs_memory` mp_tac) >> simp[]) >>
  `abi_decoder_operand_live next (Lit (0w:bytes32))` by
    simp[abi_decoder_operand_live_def] >>
  `abi_decoder_ranges DLOAD (Lit 0w) (Lit 0w) src (Var dst_var) 0 sb
     (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot 32 X0` by
    (fs[abi_decoder_ranges_def, eval_operand_def,Excl "enc_def"] >>
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
  `(checked ==> gas_path_mem ctx func X0 0 (OK prepared) /\
                alloca_history func prepared /\
                !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
                  (X0,X1,X2) [] (OK prepared,H,qt))` by
    (strip_tac >> gvs[Excl "enc_def"] >>
     `run_inst_seq_mem_ok (emitted_insts st middle) X0` by
       (drule ctor_checked_array_setup_mem_ok_at_index >> disch_then irule >>
        goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
        conj_tac >- simp[abi_decoder_operand_live_def] >>
        conj_tac >- (qexists `limit_st` >> simp[]) >>
        goal_assum (drule_at Any) >>
        simp[Excl "enc_def"] >>
        goal_assum (drule_at Any) >>
        simp[Excl "enc_def"] >> goal_assum (drule_at Any) >>
        qexists `j` >> simp[Excl "enc_def"] >>
        fs[alloca_inv_def,alloca_next_valid_def] >> metis_tac[]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts st middle)` by
       (drule prefix_loop_element_setup_code >> simp[LET_THM] >>
        strip_tac >> Cases_on `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` >>
        gvs[mk_inst_def,is_terminator_def]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
        i.inst_opcode <> GAS) (emitted_insts st middle)` by
       (irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >> simp[]) >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts st middle)` by
       (irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >> simp[]) >>
     drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
     drule_all abi_decode_array_element_setup_shape >> strip_tac >>
     `X0.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
     drule_all ctor_checked_emitted_endpoint >>
     disch_then (qspec_then `ctx` strip_assume_tac) >>
     `X0 with vs_inst_idx := LENGTH st.cs_current_insts = X0` by
       simp[venom_state_component_equality] >>
     `!D'. inst_seq_ptr D' lo ctx func PG X1 X2 (emitted_insts st middle) X0 H qt` by
       (gen_tac >>
        qpat_assum `!D' k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspecl_then [`D'`,`LENGTH st.cs_current_insts`] mp_tac) >>
        pop_assum (fn th => rewrite_tac[th])) >>
     simp[Abbr `prepared`] >> rpt strip_tac >>
     irule emitted_origin_ptr_path >> qexists_tac `st` >> asm_rewrite_tac[]) >>
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


(* Share the precise child contract quotation with its natural producer. *)
val CshiftMode = ``\checked ty tv.
  ^(rand (rator (concl prefix_complete_child_iteration_mode)))``;

Theorem prefix_complete_array_body_iteration_pair_mode:
  (^CshiftMode) checked ty tv ==>
  (^PkMode) /\ j < LENGTH vs /\
  (^LoopAtMode) st.cs_current_bb (LENGTH st.cs_current_insts) j X ==>
  ?Y. (^LoopAtMode) hdr 0 (SUC j) Y /\ (^FrameMode) X Y
Proof
  disch_then (mk_asm "child") >> strip_tac >>
  mp_tac prefix_complete_array_body_pair_mode >>
  (impl_tac >- (PairCases_on `X` >> gvs[Excl "enc_def"])) >>
  strip_tac >> PairCases_on `X` >>
  fs[Excl "enc_def"] >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  PairCases_on `ops` >> gvs[Excl "enc_def"] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_array_body_code >> simp_tac std_ss [] >>
  disch_then drule_all >> strip_tac >>
  `prepared.vs_data_section = initial.vs_data_section` by fs[] >>
  drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)
    (SIMP_RULE std_ss [Once type_memory_bytes_def,Once ADD_COMM] (Q.INST [`hi` |-> `Lit (0w:bytes32)`]
      ctor_actual_array_child_inputs_at_index)) >>
  disch_then (drule_at (Pat `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
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
  `mem_bytes_at (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)
    (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs))) prepared.vs_data_section =
    enc (vyper_to_abi_type env ty) (EL j avs)` by simp[Excl "enc_def"] >>
  asm_x "child" (mp_tac o MATCH_MP (BETA_RULE prefix_complete_child_iteration_mode) o BETA_RULE) >>
  disch_then (fn th =>
    qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ middle = _`
      (mp_then Any mp_tac th)) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H child_dst = _`)) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  disch_then (drule_at (Pat `eval_operand ops1 prepared = _`)) >>
  disch_then (drule_at (Pat `op_taint qt ops1 = _`)) >>
  disch_then (mp_tac o REWRITE_RULE [GSYM CONJ_ASSOC]) >>
  disch_then (fn th => qpat_assum `alloca_frontier_inv_from _ _ _ _ prepared`
    (mp_then (Pat `alloca_frontier_inv_from _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ctor_actual_scratch _ _ _ _ prepared`
    (mp_then (Pat `ctor_actual_scratch _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `fresh_vars_wrt _ prepared`
    (mp_then (Pat `fresh_vars_wrt _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `FLOOKUP prepared.vs_allocas _ = _`
    (mp_then (Pat `FLOOKUP prepared.vs_allocas _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `FINITE X3`
    (mp_then (Pat `FINITE B`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `abi_encoder_registered_effect _ _ initial prepared`
    (mp_then (Pat `abi_encoder_registered_effect _ _ _ prepared`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_block hdr func.fn_blocks = SOME hdr_bb`
    (mp_then (Pat `lookup_block hdr _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `mem_bytes_at _ _ prepared.vs_data_section = enc _ _`
    (mp_then (Pat `mem_bytes_at _ _ prepared.vs_data_section = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `abi_decoder_operand_live next (Var slot_var)`
    (mp_then (Pat `abi_decoder_operand_live _ (Var slot_var)`) mp_tac th)) >>
  disch_then (qspecl_then [`mem_bytes_at d 32 prepared.vs_memory`,`Ddead`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt conj_tac
    >- (AP_TERM_TAC >> AP_TERM_TAC >> decide_tac)
    >- decide_tac
    >- decide_tac
    >- (disj2_tac >> simp_tac std_ss [] >> asm_rewrite_tac[])
    >- (irule SUBSET_TRANS >> qexists_tac `frag_ids st end_st` >>
        asm_rewrite_tac[] >> simp[abiEncoderPropsTheory.frag_ids_def,SUBSET_DEF] >> decide_tac)
    >- decide_tac
    >- (pure_rewrite_tac[MULT_CLAUSES] >> decide_tac)
    >- decide_tac
    >- decide_tac
    >- decide_tac
    >- (qpat_assum `!mem. _ ==> mload d (X0 with vs_memory := mem) = _ /\ _`
          (qspec_then `X0.vs_memory` mp_tac) >> simp[])
    >- (rpt strip_tac >>
        qpat_assum `!x w. _ ==> lookup_var x X0 = _` drule >>
        qpat_assum `!x. _ ==> _ /\ _ /\ lookup_var x prepared = _` drule >>
        simp_tac std_ss [] >> metis_tac[])
    >- (`LENGTH vs * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by
          (irule LESS_MONO_MULT >> asm_rewrite_tac[]) >> decide_tac)
    >- decide_tac
    >- decide_tac
    >- (first_x_assum irule >> asm_rewrite_tac[])
    >- (first_x_assum irule >> asm_rewrite_tac[])
    >- (`j * type_memory_bytes ce ty + 32 = 32 + j * type_memory_bytes ce ty` by decide_tac >>
        pop_assum (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC)
    >- (irule DISJOINT_SUBSET >> qexists_tac `X2.t_mem` >> asm_rewrite_tac[]) >>
    strip_tac >> reverse conj_tac >-
      (qpat_assum `checked ==> gas_path_mem _ _ _ _ _ /\ _` drule >> simp_tac std_ss []) >>
    irule ctor_checked_array_child_section_at_index >>
    qpat_assum `abi_decoder_metadata _ _ (ArrayT _ _) _ _ _ _` (irule_at Any) >>
    asm_simp_tac (srw_ss()) [contractABITheory.enc_def,LET_THM] >>
    qpat_assum `abi_decoder_ranges DLOAD _ _ _ _ _ _ _ _ _ _ initial` (irule_at Any) >>
    qexists_tac `sf` >> simp[Excl "enc_def"])) >>
  strip_tac >> suspend "compose"
QED

Resume prefix_complete_array_body_iteration_pair_mode[compose]:
  pop_assum strip_assume_tac >>
  qexists_tac `(t,H',qt',A)` >>
  rule_assum_tac BETA_RULE >>
  rpt (first_x_assum (CONJUNCTS_THEN assume_tac)) >>
  simp_tac std_ss [] >>
  rpt conj_tac >> asm_rewrite_tac[]
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
  >- (strip_tac >> qpat_assum `checked ==> gas_path_mem _ _ prepared _ _ /\ _` drule >> simp_tac std_ss [])
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
      qpat_assum `prepared.vs_memory = X0.vs_memory` (fn th => rewrite_tac[th]))
  >- (disch_tac >>
      qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ H qt prepared) ==> _` irule >>
      qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ H' qt' t) ==> _` irule >>
      asm_rewrite_tac[]) >>
  strip_tac >>
  qpat_assum `checked ==> gas_path_mem _ _ X0 _ _ /\ _` drule >> strip_tac >>
  qpat_assum `checked ==> gas_path_mem _ _ prepared _ _ /\ _` drule >> strip_tac >>
  qpat_assum `checked ==> !D explicit. gas_origin_ptr_path _ (prepared,_,_) _ _` drule >>
  strip_tac >> rpt conj_tac
  >- metis_tac[gas_path_mem_then,ADD_0]
  >- metis_tac[] >>
  metis_tac[gas_origin_ptr_path_trans]
QED

Finalise prefix_complete_array_body_iteration_pair_mode


Theorem prefix_complete_array_successor_pair_mode:
  (^CshiftMode) checked ty tv ==>
  (^PkMode) /\ j < LENGTH vs /\ (^LoopAtMode) hdr 0 j X ==>
  ?Y. (^LoopAtMode) hdr 0 (SUC j) Y /\ (^FrameMode) X Y
Proof
  disch_then (mk_asm "child") >> strip_tac >>
  drule_all prefix_complete_array_header_frame_pair_mode >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  `st.cs_current_insts = []` by fs[abi_decoder_recursive_loop_compiled_def] >>
  `?Z. (^LoopAtMode) hdr 0 (SUC j) Z /\ (^FrameMode) Y Z` by
    (asm_x "child" (irule o MATCH_MP prefix_complete_array_body_iteration_pair_mode) >>
     asm_rewrite_tac[LENGTH] >> conj_tac
     >- (qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (irule_at Any) >> asm_rewrite_tac[]) >>
     qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >> asm_rewrite_tac[LENGTH]) >>
  qexists_tac `Z` >> asm_rewrite_tac[] >>
  mp_tac prefix_complete_array_frame_transitive_mode >>
  pure_rewrite_tac[transitive_def] >> disch_then irule >>
  qexists_tac `Y` >> asm_rewrite_tac[]
QED


Theorem prefix_complete_array_finite_pair_mode:
  (^CshiftMode) checked ty tv ==> (^PkMode) ==>
  !n j X. LENGTH vs = j+n /\ (^LoopAtMode) hdr 0 j X ==>
    ?Y. (^LoopAtMode) exit_lbl 0 (LENGTH vs) Y /\ (^FrameMode) X Y
Proof
  disch_tac >> strip_tac >> Induct
  >- (rpt gen_tac >> pure_rewrite_tac[ADD_0] >> strip_tac >>
      qpat_x_assum `LENGTH vs = j` (SUBST_ALL_TAC o SYM) >>
      irule prefix_complete_array_terminal_pair_mode >> asm_rewrite_tac[] >>
      qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> asm_rewrite_tac[] >>
      qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j < LENGTH vs` by decide_tac >>
  drule_all prefix_complete_array_successor_pair_mode >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >> strip_tac >>
  qpat_x_assum `!j X. _` (qspecl_then [`SUC j`,`Y`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac[] >> decide_tac) >>
  strip_tac >> qexists_tac `Y'` >> asm_rewrite_tac[] >>
  mp_tac prefix_complete_array_frame_transitive_mode >>
  pure_rewrite_tac[transitive_def] >> disch_then irule >>
  qexists_tac `Y` >> asm_rewrite_tac[]
QED


Theorem prefix_complete_array_prepared_pair_mode:
  (^CshiftMode) checked ty tv ==> (^PkMode) /\
  (^LoopAtMode) prepared.vs_current_bb (LENGTH prefix) 0 (prepared,G,tn,B) /\
  lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  ?actual H qt A.
    (^LoopAtMode) exit_lbl 0 (LENGTH vs) (actual,H,qt,A) /\
    (^FrameMode) (prepared,G,tn,B) (actual,H,qt,A) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem)
Proof
  disch_then (mk_asm "child") >> strip_tac >>
  `(^LoopAtMode) hdr 0 0 (jump_to hdr prepared,G,tn,B) /\
   (^FrameMode) (prepared,G,tn,B) (jump_to hdr prepared,G,tn,B)` by
    (qpat_x_assum `(^LoopAtMode) _ _ _ _` mp_tac >>
     simp_tac std_ss [] >> strip_tac >>
     `(^Ok) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial 0 0 (jump_to hdr prepared)` by
       (irule deploy_ctor_array_observation_jump >> simp_tac std_ss [] >> asm_rewrite_tac[]) >>
     drule_all abi_decoder_loop_entry_sim >>
     disch_then (qspec_then `ctx` assume_tac) >>
     `get_instruction bb prepared.vs_inst_idx = SOME (mk_inst id JMP [Label hdr] [])` by
       simp[get_instruction_def,EL_APPEND_EQN] >>
     `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (prepared,G,tn) []
        (OK (jump_to hdr prepared),G,tn)` by
       (rpt gen_tac >> match_mp_tac (Q.INST [`iid` |-> `id`] jmp_origin_ptr_path) >>
        asm_rewrite_tac[]) >>
     `(checked ==> gas_path_mem ctx func prepared 0 (OK (jump_to hdr prepared)) /\
       alloca_history func (jump_to hdr prepared) /\
       !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (prepared,G,tn) []
         (OK (jump_to hdr prepared),G,tn))` by
       (strip_tac >> `alloca_history func prepared` by simp[] >>
        drule_all ctor_checked_jump_path >> simp[]) >>
     `(!fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn (jump_to hdr prepared)) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn prepared` by
       (match_mp_tac (Q.INST [`iid` |-> `id`] prefix_loop_entry_jump_run) >>
        asm_rewrite_tac[]) >>
     qpat_x_assum `(^Ok) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (jump_to hdr prepared)`
       (strip_assume_tac o BETA_RULE) >>
     asm_rewrite_tac[] >>
     fs[jump_to_def,allocas_from_def,mload_def,lookup_var_def] >>
     metis_tac[]) >>
  asm "child" (mp_tac o MATCH_MP prefix_complete_array_finite_pair_mode) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qspecl_then [`LENGTH vs`,`0`,`(jump_to hdr prepared,G,tn,B)`] mp_tac) >>
  asm_rewrite_tac[ADD] >> strip_tac >> PairCases_on `Y` >>
  qexistsl [`Y0`,`Y1`,`Y2`,`Y3`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (mp_tac prefix_complete_array_frame_transitive_mode >>
      pure_rewrite_tac[transitive_def] >> disch_then irule >>
      qexists_tac `(jump_to hdr prepared,G,tn,B)` >> asm_rewrite_tac[]) >>
  qpat_x_assum `(^LoopAtMode) exit_lbl _ _ _` mp_tac >>
  simp_tac std_ss [TAKE_LENGTH_ID] >> strip_tac >>
  simp[val_in_memory_dynarray] >>
  fs[mload_def,mem_word_at_def] >> metis_tac[]
QED


val _ = export_theory();
