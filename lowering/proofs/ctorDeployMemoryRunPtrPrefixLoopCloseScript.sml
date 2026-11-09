(* Finite paired loop iteration.  The invariant's carrier includes the runtime
   state, its ghosts and the finite semantic support; E composes their frames. *)
Theory ctorDeployMemoryRunPtrPrefixLoopClose
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployMemoryRunPtrPrefixLoopElement ctorDeployMemoryRunPtrPrefixLoopHeader
  ctorDeployMemoryRunPtrPrefixLoopIteration ctorAbiActualArrayFinite
  ctorAbiActualArrayRun ctorAbiActualArrayLayout ctorAbiActualArrayContext
  ctorDeployMemoryRunPtrPrefixLoopSetup abiDecoderCorrectPrimitiveArray exprLowering
  ctorAbiActualSites ctorDeployMemoryRunPtrPrefixCanonical valueEncoding abiDecoderArrayLoopInit
  abiDecoderLoopEmit abiDecoderRecursiveLoopEntry abiDecoderIndexInit
  pred_set relation arithmetic abiDecoderArraySetupInputs abiDecoderTypedContract
  abiDecoderArraySetupCode abiDecoderContract abiDecoderReentry
  compileEnv exprLoweringProps venomExecSemantics ptrSafeRun rich_list
  fragExec venomInst venomInstProps list abiDecoderExecution abiDecoderLoop
  abiDecoderRecursiveLoopContext ctorAbiActualArrayInvariant abiCanonicalHeadSize
  ctorAbiActualObservations abiDecoderDynamicLoopSetup venomMemDefs allocaFrontierBound
  ctorAbiActualArrayBody ptrDiscipline instIdxIndep abiDecoderCounters emitHelperProps
  ctorAbiActualArrayEntry venomState abiDecoderPrimitiveLoopEntry abiDecoderRecursiveLoopLayout

Theorem prefix_loop_finite_pair_bridge:
  transitive E /\
  (!j x. j < n /\ R j x ==> ?y. R (SUC j) y /\ E x y) /\
  (!x. R n x ==> ?y. Post y /\ E x y) ==>
  !i x. i <= n /\ R i x ==> ?y. Post y /\ E x y
Proof
  strip_tac >>
  completeInduct_on `n-i` >> rpt strip_tac >>
  Cases_on `i = n`
  >- metis_tac[] >>
  `i < n` by decide_tac >>
  `?u. R (SUC i) u /\ E x u` by metis_tac[] >>
  `n-SUC i < n-i /\ SUC i <= n` by decide_tac >>
  `?y. Post y /\ E u y` by metis_tac[] >>
  metis_tac[transitive_def]
QED

Theorem prefix_loop_setup_run_continuation:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) di asz msz st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  fn_has_code st middle fn /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!cursor fuel bb.
    (!k. k < LENGTH (emitted_insts st middle) ==>
      get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st middle))) ==>
    ptr_safe_block D lo fuel ctx fn PG H qt bb
      (t with vs_inst_idx := cursor+LENGTH (emitted_insts st middle)) ==>
    ptr_safe_block D lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor)) ==>
  ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
      (t with vs_inst_idx := LENGTH middle.cs_current_insts)) ==>
   !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `middle.cs_current_insts = st.cs_current_insts ++ emitted_insts st middle` by
    (fs[emitted_insts_def,IS_PREFIX_APPEND] >> simp[DROP_LENGTH_APPEND]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     isPREFIX middle.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `!k. k < LENGTH (emitted_insts st middle) ==>
    get_instruction bb (s.vs_inst_idx+k) = SOME (EL k (emitted_insts st middle))` by
    (fs[IS_PREFIX_APPEND] >> rpt strip_tac >>
     simp[get_instruction_def,EL_APPEND_EQN,LENGTH_APPEND]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
     qexists `emitted_insts st middle` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by fs[EVERY_MEM] >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     metis_tac[step_preserves_control_flow]) >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx fn PG H qt bb
    (t with vs_inst_idx := s.vs_inst_idx+LENGTH (emitted_insts st middle))` by
    (qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` (qspec_then `fuel` mp_tac) >>
     fs[ptr_safe_run_def]) >>
  `ptr_safe_block D lo fuel ctx fn PG G tn bb s` by
    (qpat_x_assum `!cursor fuel bb. _ ==> _ ==> _`
      (qspecl_then [`s.vs_inst_idx`,`fuel`,`bb`] mp_tac) >> simp[]) >>
  simp[ptr_safe_run_def]
QED

Theorem prefix_loop_setup_execution_pair:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) di asz msz st = (ops,middle) /\
  run_inst_seq (emitted_insts st middle) s = OK t /\
  fn_has_code st middle func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!cursor fuel bb.
    (!k. k < LENGTH (emitted_insts st middle) ==>
      get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st middle))) ==>
    ptr_safe_block D lo fuel ctx func PG H qt bb
      (t with vs_inst_idx := cursor+LENGTH (emitted_insts st middle)) ==>
    ptr_safe_block D lo fuel ctx func PG G tn bb (s with vs_inst_idx := cursor)) ==>
  let u = t with vs_inst_idx := LENGTH middle.cs_current_insts in
    ~u.vs_halted /\ u.vs_current_bb = middle.cs_current_bb /\
    u.vs_inst_idx = LENGTH middle.cs_current_insts /\ abi_decode_sim ctx func s u /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt u) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `frag_exec ctx st middle (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH middle.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  strip_tac >> drule_all prefix_loop_setup_run_continuation >> simp[]
QED

Theorem prefix_loop_header_reach_pair:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src dst
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src dst
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  FLOOKUP G slot_var = SOME (slot,32) /\
  slot+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= slot /\ ~ctx_has_dalloca ctx /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn src = {} /\
  (!k. k < 32 ==> slot+k NOTIN tn.t_mem) ==>
  ?t H qt.
    ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
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
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)
Proof
  strip_tac >> drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand (Var slot_var) s = SOME (n2w slot) /\
   eval_operand src s = SOME (n2w sb)` by
    (fs[abi_decoder_ranges_def,Excl "enc_def"] >>
     metis_tac[ctor_actual_array_observation_operand]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[ctor_actual_array_observation_def,abi_decode_source_def,Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword(:256)` by
    fs[abi_decoder_ranges_def,Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb:bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all prefix_loop_header_compiled_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Persistent frame over the runtime state, ghost map, taint and finite support.
   Equality of memory is deliberately not required across recursive children. *)
val loop_frame = ``\(s,G,tn,B) (t,H,qt,A).
  abi_decode_sim ctx func s t /\ qt.t_mem SUBSET tn.t_mem /\
  qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
  (!x. abi_decoder_older_vars next x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
  B SUBSET A /\
  (!a. a IN B ==> mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory) /\
  ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt t) ==>
    !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn s)``;

Theorem prefix_loop_frame_transitive:
  transitive (^loop_frame)
Proof
  simp_tac bool_ss [transitive_def] >>
  rpt gen_tac >> PairCases_on `x` >> PairCases_on `y` >> PairCases_on `z` >>
  simp_tac std_ss [] >> strip_tac >>
  rpt conj_tac >>
  metis_tac[abi_decode_sim_trans,SUBSET_TRANS,SUBSET_DEF]
QED

val loop_premises = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src (Var dst_var)
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  fn_inst_ids_distinct func /\ unit_alloca_budget ctx < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  lo <= slot /\ D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  slot_id IN ctor_actual_sites func ids /\ frag_ids st end_st SUBSET ids /\
  slot_id NOTIN frag_ids middle end_st /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+cap``;

(* The control location is a parameter only to share the body/header/exit interface. *)
val loop_at = ``\label index j (s,G,tn,B).
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = index /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  FLOOKUP G slot_var = SOME (slot,32) /\ FLOOKUP G dst_var = SOME (b,cap) /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn (Var dst_var) = {} /\ op_taint tn src = {} /\
  DISJOINT tn.t_mem {a | slot <= a /\ a < slot+32} /\
  FINITE B /\ B SUBSET range_bytes [(d,32+j*type_memory_size tv)] /\ DISJOINT B tn.t_mem /\
  (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 s.vs_memory) ==>
    mem_bytes_at d 32 mem = header /\ elems_in_memory (TAKE j vs) (d+32) tv mem)``;

Theorem prefix_loop_header_invariant_pair:
  (^loop_premises) /\ (^loop_at) hdr 0 j X ==>
  ?Y. (^loop_at) (if j < LENGTH vs then st.cs_current_bb else exit_lbl) 0 j Y /\
    (^loop_frame) X Y
Proof
  PairCases_on `X` >> simp_tac std_ss [] >> strip_tac >>
  `slot+32 <= X0.vs_alloca_next /\ X0.vs_alloca_next < dimword(:256)` by
    (fs[ctor_actual_array_observation_def,alloca_inv_def,alloca_next_valid_def] >>
     metis_tac[alloca_frontier_inv_bound]) >>
  `!k. k < 32 ==> slot+k NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+k` mp_tac) >> simp[]) >>
  drule_all prefix_loop_header_reach_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >> strip_tac >>
  qexists_tac `(t,H,qt,X3)` >> simp_tac std_ss [] >>
  `abi_decoder_operand_live next (Var slot_var) /\
   abi_decoder_operand_live next (Var dst_var) /\ abi_decoder_operand_live next src` by
    fs[abi_decoder_recursive_loop_data_def] >>
  `!x. abi_decoder_older_vars next x ==> abi_decoder_operand_live next (Var x)` by
    simp[abi_decoder_operand_live_def,IN_DEF] >>
  `abi_decoder_older_vars next slot_var /\ abi_decoder_older_vars next dst_var` by
    (fs[abi_decoder_operand_live_def,IN_DEF]) >>
  simp[SUBSET_REFL] >> rpt conj_tac >> metis_tac[]
QED

Theorem prefix_loop_terminal_pair:
  (^loop_premises) /\ (^loop_at) hdr 0 (LENGTH vs) X ==>
  ?Y. (^loop_at) exit_lbl 0 (LENGTH vs) Y /\ (^loop_frame) X Y
Proof
  strip_tac >> drule_all prefix_loop_header_invariant_pair >> simp[]
QED

val canonical_pair_floor = ``\ty tv.
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
    lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_loop_observation_at_cursor:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decoder_address_frame body_next s t /\ next <= body_next /\
  fresh_vars_wrt limit_st t /\ t.vs_labels = s.vs_labels /\
  abi_encoder_registered_effect {} [] s t ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j (t with vs_inst_idx := cursor)
Proof
  strip_tac >> simp[] >> irule ctor_actual_array_observation_address >>
  metis_tac[]
QED

Theorem prefix_loop_element_setup_at_index_pair:
  abi_decode_array_element_setup (Var ip) src dst DLOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = ((idx,child_src,child_dst),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  LENGTH avs = LENGTH vs /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    s.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand (Var ip) s = SOME (n2w slot) /\ mload slot s = n2w j /\
  slot < dimword(:256) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  FLOOKUP G ip = SOME (slot,32) /\
  op_taint tn (Var ip) = {} /\ (!k. k < 32 ==> slot+k NOTIN tn.t_mem) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?t H qt.
    run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand child_src t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) avs j)) /\
    eval_operand child_dst t = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    abi_decoder_operand_live st'.cs_next_var child_src /\
    abi_decoder_operand_live st'.cs_next_var child_dst /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    op_taint qt idx = {} /\ op_taint qt child_src = {} /\
    op_taint qt child_dst = {} /\ op_prov H child_dst = op_prov G dst /\
    qt.t_mem = tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_inst_idx = s.vs_inst_idx /\
    (!v. not_fresh_at st v ==>
      FLOOKUP H v = FLOOKUP G v /\ op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!cursor fuel bb.
      (!k. k < LENGTH (emitted_insts st st') ==>
        get_instruction bb (cursor+k) = SOME (EL k (emitted_insts st st'))) ==>
      ptr_safe_block Ddead lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := cursor+LENGTH (emitted_insts st st')) ==>
      ptr_safe_block Ddead lo fuel ctx fn PG G tn bb (s with vs_inst_idx := cursor))
Proof
  strip_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs /\
   TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (conj_tac
     >- (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
         asm_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]) >>
     mp_tac (Q.ISPEC `vs:value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]) >>
  `!k. k < 32 ==> k+slot NOTIN tn.t_mem` by metis_tac[ADD_COMM] >>
  qpat_assum `TAKE j avs ++ _ = avs` (fn av_eq =>
    qpat_assum `TAKE j vs ++ _ = vs` (fn v_eq =>
      drule (PURE_REWRITE_RULE [av_eq,v_eq] (Q.INST
        [`pre` |-> `TAKE j avs`, `av` |-> `EL j avs`, `post` |-> `DROP (SUC j) avs`,
         `vpre` |-> `TAKE j vs`, `v` |-> `EL j vs`, `vpost` |-> `DROP (SUC j) vs`]
        prefix_loop_element_setup_labels_pair)))) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var ip) s = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP G ip = _`)) >>
  disch_then (drule_at (Pat `op_taint tn src = _`)) >>
  disch_then (drule_at (Pat `allocas_from lo s`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt limit_st s`)) >>
  disch_then (drule_at (Pat `~ctx_has_dalloca ctx`)) >>
  disch_then (qspecl_then [`op_prov G dst`,`fn`,`PG`,`Ddead`] mp_tac) >>
  simp[LENGTH_TAKE,MIN_DEF,ADD_COMM,wordsTheory.w2n_n2w,Excl "enc_def"]
QED

Theorem prefix_loop_body_index_pair:
  (^canonical_pair_floor) ty tv ==>
  (^loop_premises) /\ j < LENGTH vs /\
  (^loop_at) st.cs_current_bb (LENGTH st.cs_current_insts) j X ==>
  ?Y. (^loop_at) hdr 0 (SUC j) Y /\ (^loop_frame) X Y
Proof
  disch_then (mk_asm "child") >> PairCases_on `X` >>
  simp_tac std_ss [] >> strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  PairCases_on `ops` >> gvs[Excl "enc_def"] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_array_body_code >> simp_tac std_ss [] >>
  disch_then drule_all >> strip_tac >>
  `abi_decoder_ranges DLOAD (Lit 0w) src (Var dst_var) sb
     (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap X0` by
    (irule ctor_actual_array_observation_ranges >> metis_tac[]) >>
  drule_all ctor_actual_array_observation_setup_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst_var)` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st X0` by fs[ctor_actual_array_observation_def] >>
  `!k. k < 32 ==> slot+k NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+k` mp_tac) >> simp[]) >>
  `mload slot X0 = n2w j` by
    (qpat_x_assum `mload _ X0 = _` mp_tac >> simp[]) >>
  drule_all prefix_loop_element_setup_at_index_pair >>
  disch_then (qspecl_then [`func`,`PG`,`Ddead`] strip_assume_tac) >>
  `X0.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all prefix_loop_setup_execution_pair >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func X0 prepared` >>
  `ctor_actual_array_observation ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
     tv vs slot_id slot initial j j prepared` by
    (simp[Abbr `prepared`] >> irule ctor_actual_array_observation_address >> metis_tac[]) >>
  suspend "child_inputs"
QED

Resume prefix_loop_body_index_pair[child_inputs]:
  `prepared.vs_data_section = X0.vs_data_section /\
   prepared.vs_memory = X0.vs_memory /\
   prepared.vs_allocas = X0.vs_allocas /\
   prepared.vs_alloca_next = X0.vs_alloca_next` by
    fs[Abbr `prepared`,abi_decoder_address_frame_def,Excl "enc_def"] >>
  `prepared.vs_data_section = initial.vs_data_section` by
    fs[ctor_actual_array_observation_def,Excl "enc_def"] >>
  drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)
    (SIMP_RULE std_ss [] (Q.INST [`hi` |-> `Lit (0w:bytes32)`]
      ctor_actual_array_child_inputs_at_index)) >>
  disch_then (drule_at (Pat `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sf`,`prepared`,`j`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  suspend "child_ghost"
QED

Resume prefix_loop_body_index_pair[child_ghost]:
  `?child_dst. ops2 = Var child_dst` by
    (Cases_on `ops2` >> fs[op_prov_def]) >>
  qpat_x_assum `ops2 = Var child_dst` SUBST_ALL_TAC >>
  `FLOOKUP H child_dst = SOME (b,cap)` by fs[op_prov_def] >>
  `eval_operand ops1 prepared = SOME (n2w
      (sb+abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)) /\
   eval_operand (Var child_dst) prepared = SOME (n2w
      (d+32+j*type_memory_size tv)) /\
   eval_operand (Var (STRING #"%" (toString st.cs_next_var))) prepared = SOME (n2w j)` by
    fs[Abbr `prepared`,eval_op_inst_idx] >>
  `allocas_from lo prepared /\ lo <= prepared.vs_alloca_next` by
    (asm_x "child" kall_tac >> conj_tac >- metis_tac[allocas_from_def] >> metis_tac[]) >>
  `not_fresh_at st slot_var /\ not_fresh_at st dst_var /\
   not_fresh_at middle slot_var /\ not_fresh_at middle dst_var /\
   not_fresh_at middle (STRING #"%" (toString st.cs_next_var)) /\
   (!x. ops1 = Var x \/ Var child_dst = Var x \/ Lit (0w:bytes32) = Var x ==>
        not_fresh_at middle x)` by
    (asm_x "child" kall_tac >> Cases_on `ops1` >>
     fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,IN_DEF,not_fresh_at_def] >>
     metis_tac[]) >>
  `FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst_var = SOME (b,cap) /\
   op_taint qt (Var slot_var) = {} /\ op_taint qt (Var dst_var) = {}` by
    (qpat_assum `!v. not_fresh_at st v ==> _` (qspec_then `slot_var` mp_tac) >>
     qpat_assum `!v. not_fresh_at st v ==> _` (qspec_then `dst_var` mp_tac) >> simp[]) >>
  suspend "child_call"
QED

Resume prefix_loop_body_index_pair[child_call]:
  `?hdr_bb. lookup_block hdr func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (fs[abi_decode_loop_cfg_def] >>
     simp[abi_decode_header_insts_def,phi_prefix_length_def]) >>
  `eval_operand (Var slot_var) prepared = SOME (n2w slot)` by
    (`abi_decoder_operand_live st.cs_next_var (Var slot_var)` by
       (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
     simp[Abbr `prepared`,eval_op_inst_idx] >>
     metis_tac[abi_decoder_address_frame_def]) >>
  asm "child" (fn th =>
    qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ = _`
      (mp_then Any mp_tac (MATCH_MP prefix_loop_child_iteration_floor th))) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H child_dst = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H slot_var = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H dst_var = _`)) >>
  disch_then (drule_at (Pat `op_taint qt ops1 = _`)) >>
  disch_then (drule_at (Pat `eval_operand ops1 prepared = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr _ = _`)) >>
  disch_then (drule_at (Pat `FINITE X3`)) >>
  disch_then (qspec_then `sb+abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j` mp_tac) >>
  disch_then (qspecl_then [`header`,`Ddead`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- (asm_x "child" kall_tac >>
    asm_simp_tac (srw_ss()) [ADD_COMM] >>
    `middle.cs_next_var <= end_st.cs_next_var` by
      metis_tac[abi_decoder_variable_counter] >>
    rpt conj_tac
    >- metis_tac[]
    >- metis_tac[]
    >- decide_tac
    >- (fs[abiEncoderPropsTheory.frag_ids_def,SUBSET_DEF] >> metis_tac[])
    >- decide_tac
    >- (`SUC j <= maxn` by decide_tac >>
        `SUC j * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by
          simp[] >> decide_tac)
    >- (fs[inst_extends_def] >> decide_tac)
    >> fs[inst_extends_def] >> decide_tac)) >>
  strip_tac >> suspend "compose" 
QED

Resume prefix_loop_body_index_pair[compose]:
  asm_x "child" kall_tac >>
  `!x. abi_decoder_older_vars next x ==> not_fresh_at st x` by
    (fs[abi_decoder_older_vars_def,not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. abi_decoder_older_vars next x ==>
     FLOOKUP H' x = FLOOKUP X1 x /\
     op_taint qt' (Var x) = op_taint X2 (Var x)` by metis_tac[] >>
  `op_taint qt' src = {}` by
    (`abi_decoder_operand_live next src` by
       fs[abi_decoder_recursive_loop_data_def] >>
     namedCases_on `src` ["lit","src_var","lab"]
     >- simp[op_taint_def]
     >- (`abi_decoder_older_vars next src_var` by
           (qpat_x_assum `abi_decoder_operand_live next (Var src_var)` mp_tac >>
            simp[abi_decoder_operand_live_def,IN_DEF]) >>
         qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H' x = FLOOKUP X1 x /\ _`
           (qspec_then `src_var` mp_tac) >> simp[]) >>
     simp[op_taint_def]) >>
  qexists_tac `(t',H',qt',A)` >>
  asm_simp_tac std_ss [ADD_COMM] >>
  rpt conj_tac
  >- (qpat_x_assum `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t'` mp_tac >>
      asm_simp_tac std_ss [])
  >- (qpat_x_assum `A SUBSET range_bytes _` mp_tac >> asm_simp_tac std_ss [ADD_COMM])
  >- (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[])
  >> metis_tac[SUBSET_TRANS]
QED

Finalise prefix_loop_body_index_pair

Theorem prefix_loop_successor_pair:
  (^canonical_pair_floor) ty tv ==>
  (^loop_premises) /\ j < LENGTH vs /\ (^loop_at) hdr 0 j X ==>
  ?Y. (^loop_at) hdr 0 (SUC j) Y /\ (^loop_frame) X Y
Proof
  strip_tac >> strip_tac >>
  `st.cs_current_insts = []` by fs[abi_decoder_recursive_loop_compiled_def] >>
  `?Z. (^loop_at) st.cs_current_bb 0 j Z /\ (^loop_frame) X Z` by
    (drule_all prefix_loop_header_invariant_pair >> simp[]) >>
  `(^loop_at) st.cs_current_bb (LENGTH st.cs_current_insts) j Z` by
    (PairCases_on `Z` >> fs[]) >>
  `?Y. (^loop_at) hdr 0 (SUC j) Y /\ (^loop_frame) Z Y` by
    (drule_all prefix_loop_body_index_pair >> simp[]) >>
  qexists_tac `Y` >> simp[] >>
  irule (REWRITE_RULE [transitive_def] prefix_loop_frame_transitive) >>
  qexists_tac `Z` >> asm_rewrite_tac []
QED

Theorem prefix_loop_finite_pair:
  (^canonical_pair_floor) ty tv ==>
  (^loop_premises) /\ i <= LENGTH vs /\ (^loop_at) hdr 0 i X ==>
  ?Y. (^loop_at) exit_lbl 0 (LENGTH vs) Y /\ (^loop_frame) X Y
Proof
  strip_tac >> strip_tac >>
  irule prefix_loop_finite_pair_bridge >>
  conj_tac >- ACCEPT_TAC prefix_loop_frame_transitive >>
  qexistsl_tac [`(^loop_at) hdr 0`,`i`,`LENGTH vs`] >>
  asm_rewrite_tac [prefix_loop_frame_transitive] >>
  conj_tac
  >- (rpt strip_tac >> drule_all prefix_loop_terminal_pair >> simp[]) >>
  rpt strip_tac >> drule_all prefix_loop_successor_pair >> simp[]
QED

(* Unlike loop_premises, the excluded semantic range is the index slot,
   not the allocation recorded for the destination operand. *)
val separated_loop_premises = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src (Var dst_var)
    sb d slot slot 32 next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  fn_inst_ids_distinct func /\ unit_alloca_budget ctx < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  lo <= slot /\ D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  slot_id IN ctor_actual_sites func ids /\ frag_ids st end_st SUBSET ids /\
  slot_id NOTIN frag_ids middle end_st /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+cap``;

Theorem prefix_loop_separated_header_pair:
  (^separated_loop_premises) /\ (^loop_at) hdr 0 j X ==>
  ?Y. (^loop_at) (if j < LENGTH vs then st.cs_current_bb else exit_lbl) 0 j Y /\
    (^loop_frame) X Y
Proof
  PairCases_on `X` >> simp_tac std_ss [] >> strip_tac >>
  `slot+32 <= X0.vs_alloca_next /\ X0.vs_alloca_next < dimword(:256)` by
    (fs[ctor_actual_array_observation_def,alloca_inv_def,alloca_next_valid_def] >>
     metis_tac[alloca_frontier_inv_bound]) >>
  `!k. k < 32 ==> slot+k NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+k` mp_tac) >> simp[]) >>
  drule_all prefix_loop_header_reach_pair >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >> strip_tac >>
  qexists_tac `(t,H,qt,X3)` >> simp_tac std_ss [] >>
  `abi_decoder_operand_live next (Var slot_var) /\
   abi_decoder_operand_live next (Var dst_var) /\ abi_decoder_operand_live next src` by
    fs[abi_decoder_recursive_loop_data_def] >>
  `!x. abi_decoder_older_vars next x ==> abi_decoder_operand_live next (Var x)` by
    simp[abi_decoder_operand_live_def,IN_DEF] >>
  `abi_decoder_older_vars next slot_var /\ abi_decoder_older_vars next dst_var` by
    (fs[abi_decoder_operand_live_def,IN_DEF]) >>
  simp[SUBSET_REFL] >> rpt conj_tac >> metis_tac[]
QED

Theorem prefix_loop_separated_terminal_pair:
  (^separated_loop_premises) /\ (^loop_at) hdr 0 (LENGTH vs) X ==>
  ?Y. (^loop_at) exit_lbl 0 (LENGTH vs) Y /\ (^loop_frame) X Y
Proof
  strip_tac >> drule_all prefix_loop_separated_header_pair >> simp[]
QED

Theorem prefix_loop_separated_body_pair:
  (^canonical_pair_floor) ty tv ==>
  (^separated_loop_premises) /\ j < LENGTH vs /\
  (^loop_at) st.cs_current_bb (LENGTH st.cs_current_insts) j X ==>
  ?Y. (^loop_at) hdr 0 (SUC j) Y /\ (^loop_frame) X Y
Proof
  disch_then (mk_asm "child") >> PairCases_on `X` >>
  simp_tac std_ss [] >> strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  PairCases_on `ops` >> gvs[Excl "enc_def"] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decoder_array_body_code >> simp_tac std_ss [] >>
  disch_then drule_all >> strip_tac >>
  `abi_decoder_ranges DLOAD (Lit 0w) src (Var dst_var) sb
     (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot 32 X0` by
    (irule ctor_actual_array_observation_ranges >> metis_tac[]) >>
  drule_all ctor_actual_array_observation_setup_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst_var)` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st X0` by fs[ctor_actual_array_observation_def] >>
  `!k. k < 32 ==> slot+k NOTIN X2.t_mem` by
    (qpat_x_assum `DISJOINT X2.t_mem _` mp_tac >>
     simp_tac std_ss [DISJOINT_DEF,EXTENSION,IN_INTER,NOT_IN_EMPTY,GSPECIFICATION] >>
     rpt strip_tac >> first_x_assum (qspec_then `slot+k` mp_tac) >> simp[]) >>
  `mload slot X0 = n2w j` by
    (qpat_x_assum `mload _ X0 = _` mp_tac >> simp[]) >>
  drule_all prefix_loop_element_setup_at_index_pair >>
  disch_then (qspecl_then [`func`,`PG`,`Ddead`] strip_assume_tac) >>
  `X0.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all prefix_loop_setup_execution_pair >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func X0 prepared` >>
  `ctor_actual_array_observation ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
     tv vs slot_id slot initial j j prepared` by
    (simp[Abbr `prepared`] >> irule ctor_actual_array_observation_address >> metis_tac[]) >>
  suspend "child_inputs"
QED

Resume prefix_loop_separated_body_pair[child_inputs]:
  `prepared.vs_data_section = X0.vs_data_section /\
   prepared.vs_memory = X0.vs_memory /\
   prepared.vs_allocas = X0.vs_allocas /\
   prepared.vs_alloca_next = X0.vs_alloca_next` by
    fs[Abbr `prepared`,abi_decoder_address_frame_def,Excl "enc_def"] >>
  `prepared.vs_data_section = initial.vs_data_section` by
    fs[ctor_actual_array_observation_def,Excl "enc_def"] >>
  drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)
    (SIMP_RULE std_ss [] (Q.INST [`hi` |-> `Lit (0w:bytes32)`]
      ctor_actual_array_child_inputs_at_index)) >>
  disch_then (drule_at (Pat `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sf`,`prepared`,`j`] mp_tac) >>
  simp_tac std_ss [LET_THM] >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  suspend "child_ghost"
QED

Resume prefix_loop_separated_body_pair[child_ghost]:
  `?child_dst. ops2 = Var child_dst` by
    (Cases_on `ops2` >> fs[op_prov_def]) >>
  qpat_x_assum `ops2 = Var child_dst` SUBST_ALL_TAC >>
  `FLOOKUP H child_dst = SOME (b,cap)` by fs[op_prov_def] >>
  `eval_operand ops1 prepared = SOME (n2w
      (sb+abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)) /\
   eval_operand (Var child_dst) prepared = SOME (n2w
      (d+32+j*type_memory_size tv)) /\
   eval_operand (Var (STRING #"%" (toString st.cs_next_var))) prepared = SOME (n2w j)` by
    fs[Abbr `prepared`,eval_op_inst_idx] >>
  `allocas_from lo prepared /\ lo <= prepared.vs_alloca_next` by
    (asm_x "child" kall_tac >> conj_tac >- metis_tac[allocas_from_def] >> metis_tac[]) >>
  `not_fresh_at st slot_var /\ not_fresh_at st dst_var /\
   not_fresh_at middle slot_var /\ not_fresh_at middle dst_var /\
   not_fresh_at middle (STRING #"%" (toString st.cs_next_var)) /\
   (!x. ops1 = Var x \/ Var child_dst = Var x \/ Lit (0w:bytes32) = Var x ==>
        not_fresh_at middle x)` by
    (asm_x "child" kall_tac >> Cases_on `ops1` >>
     fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,IN_DEF,not_fresh_at_def] >>
     metis_tac[]) >>
  `FLOOKUP H slot_var = SOME (slot,32) /\ FLOOKUP H dst_var = SOME (b,cap) /\
   op_taint qt (Var slot_var) = {} /\ op_taint qt (Var dst_var) = {}` by
    (qpat_assum `!v. not_fresh_at st v ==> _` (qspec_then `slot_var` mp_tac) >>
     qpat_assum `!v. not_fresh_at st v ==> _` (qspec_then `dst_var` mp_tac) >> simp[]) >>
  suspend "child_call"
QED

Resume prefix_loop_separated_body_pair[child_call]:
  `?hdr_bb. lookup_block hdr func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (fs[abi_decode_loop_cfg_def] >>
     simp[abi_decode_header_insts_def,phi_prefix_length_def]) >>
  `eval_operand (Var slot_var) prepared = SOME (n2w slot)` by
    (`abi_decoder_operand_live st.cs_next_var (Var slot_var)` by
       (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
     simp[Abbr `prepared`,eval_op_inst_idx] >>
     metis_tac[abi_decoder_address_frame_def]) >>
  asm "child" (fn th =>
    qpat_assum `compile_abi_decode_to_buf (Var child_dst) _ _ _ _ _ = _`
      (mp_then Any mp_tac (MATCH_MP prefix_loop_child_iteration_floor th))) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `bb.bb_instructions = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H child_dst = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H slot_var = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP H dst_var = _`)) >>
  disch_then (drule_at (Pat `op_taint qt ops1 = _`)) >>
  disch_then (drule_at (Pat `eval_operand ops1 prepared = _`)) >>
  disch_then (drule_at (Pat `lookup_block hdr _ = _`)) >>
  disch_then (drule_at (Pat `FINITE X3`)) >>
  disch_then (qspec_then `sb+abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j` mp_tac) >>
  disch_then (qspecl_then [`header`,`Ddead`,`lo`,`PG`] mp_tac) >>
  (impl_tac >- (asm_x "child" kall_tac >>
    asm_simp_tac (srw_ss()) [ADD_COMM] >>
    `middle.cs_next_var <= end_st.cs_next_var` by
      metis_tac[abi_decoder_variable_counter] >>
    rpt conj_tac
    >- metis_tac[]
    >- metis_tac[]
    >- decide_tac
    >- (fs[abiEncoderPropsTheory.frag_ids_def,SUBSET_DEF] >> metis_tac[])
    >- decide_tac
    >- (`SUC j <= maxn` by decide_tac >>
        `SUC j * type_memory_bytes ce ty <= maxn * type_memory_bytes ce ty` by
          simp[] >> decide_tac)
    >- (fs[inst_extends_def] >> decide_tac)
    >> fs[inst_extends_def] >> decide_tac)) >>
  strip_tac >> suspend "compose"
QED

Resume prefix_loop_separated_body_pair[compose]:
  asm_x "child" kall_tac >>
  `!x. abi_decoder_older_vars next x ==> not_fresh_at st x` by
    (fs[abi_decoder_older_vars_def,not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. abi_decoder_older_vars next x ==>
     FLOOKUP H' x = FLOOKUP X1 x /\
     op_taint qt' (Var x) = op_taint X2 (Var x)` by metis_tac[] >>
  `op_taint qt' src = {}` by
    (`abi_decoder_operand_live next src` by
       fs[abi_decoder_recursive_loop_data_def] >>
     namedCases_on `src` ["lit","src_var","lab"]
     >- simp[op_taint_def]
     >- (`abi_decoder_older_vars next src_var` by
           (qpat_x_assum `abi_decoder_operand_live next (Var src_var)` mp_tac >>
            simp[abi_decoder_operand_live_def,IN_DEF]) >>
         qpat_x_assum `!x. abi_decoder_older_vars next x ==> FLOOKUP H' x = FLOOKUP X1 x /\ _`
           (qspec_then `src_var` mp_tac) >> simp[]) >>
     simp[op_taint_def]) >>
  qexists_tac `(t',H',qt',A)` >>
  asm_simp_tac std_ss [ADD_COMM] >>
  rpt conj_tac
  >- (qpat_x_assum `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t'` mp_tac >>
      asm_simp_tac std_ss [])
  >- (qpat_x_assum `A SUBSET range_bytes _` mp_tac >> asm_simp_tac std_ss [ADD_COMM])
  >- (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[])
  >> metis_tac[SUBSET_TRANS]
QED

Finalise prefix_loop_separated_body_pair

Theorem prefix_loop_separated_successor_pair:
  (^canonical_pair_floor) ty tv ==>
  (^separated_loop_premises) /\ j < LENGTH vs /\ (^loop_at) hdr 0 j X ==>
  ?Y. (^loop_at) hdr 0 (SUC j) Y /\ (^loop_frame) X Y
Proof
  strip_tac >> strip_tac >>
  `st.cs_current_insts = []` by fs[abi_decoder_recursive_loop_compiled_def] >>
  `?Z. (^loop_at) st.cs_current_bb 0 j Z /\ (^loop_frame) X Z` by
    (drule_all prefix_loop_separated_header_pair >> simp[]) >>
  `(^loop_at) st.cs_current_bb (LENGTH st.cs_current_insts) j Z` by
    (PairCases_on `Z` >> fs[]) >>
  `?Y. (^loop_at) hdr 0 (SUC j) Y /\ (^loop_frame) Z Y` by
    (drule_all prefix_loop_separated_body_pair >> simp[]) >>
  qexists_tac `Y` >> simp[] >>
  irule (REWRITE_RULE [transitive_def] prefix_loop_frame_transitive) >>
  qexists_tac `Z` >> asm_rewrite_tac []
QED

Theorem prefix_loop_separated_finite_pair:
  (^canonical_pair_floor) ty tv ==>
  (^separated_loop_premises) /\ i <= LENGTH vs /\ (^loop_at) hdr 0 i X ==>
  ?Y. (^loop_at) exit_lbl 0 (LENGTH vs) Y /\ (^loop_frame) X Y
Proof
  strip_tac >> strip_tac >>
  irule prefix_loop_finite_pair_bridge >>
  conj_tac >- ACCEPT_TAC prefix_loop_frame_transitive >>
  qexistsl_tac [`(^loop_at) hdr 0`,`i`,`LENGTH vs`] >>
  asm_rewrite_tac [prefix_loop_frame_transitive] >>
  conj_tac
  >- (rpt strip_tac >> drule_all prefix_loop_separated_terminal_pair >> simp[]) >>
  rpt strip_tac >> drule_all prefix_loop_separated_successor_pair >> simp[]
QED

Theorem prefix_loop_zero_support:
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial 0 0 s /\
  ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = index /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  FLOOKUP G slot_var = SOME (slot,32) /\ FLOOKUP G dst_var = SOME (b,cap) /\
  op_taint tn (Var slot_var) = {} /\ op_taint tn (Var dst_var) = {} /\ op_taint tn src = {} /\
  DISJOINT tn.t_mem {a | slot <= a /\ a < slot+32} /\
  DISJOINT tn.t_mem {a | d <= a /\ a < d+32} /\
  mem_bytes_at d 32 s.vs_memory = header ==>
  (^loop_at) label index 0 (s,G,tn,range_bytes [(d,32)])
Proof
  simp_tac std_ss [] >> strip_tac >>
  `FINITE (range_bytes [(d,32)])` by
    (irule SUBSET_FINITE_I >> qexists_tac `count (d+32)` >>
     simp[range_bytes_def,SUBSET_DEF]) >>
  asm_simp_tac std_ss [SUBSET_REFL,DISJOINT_SYM] >>
  conj_tac >- fs[range_bytes_def,DISJOINT_SYM] >>
  rpt strip_tac >>
  `mem_bytes_at d 32 mem = mem_bytes_at d 32 s.vs_memory` by
    (irule prefix_canonical_support_window >>
     qexists_tac `range_bytes [(d,32)]` >> simp[range_bytes_def]) >>
  simp[val_in_memory_def]
QED

Theorem prefix_dynamic_array_setup_finite_pair_complete:
  (^canonical_pair_floor) ty tv /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
   G tn b sz Ddead lo PG.
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) st = ((),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av))
    initial.vs_data_section = enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av /\
  (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  D+N <= initial.vs_alloca_next /\
  frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
  ?avs vs guard_st header_st loop_st cnt labels body_st ops middle end_st prepared slot iv H qt Y.
    av = ListV avs /\ v = ArrayV (DynArrayV vs) /\
    abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn
      (abi_embedded_static_size ce.ce_struct_fields ty) st = ((),guard_st) /\
    abi_decode_array_header (Var dst) src DLOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (Var iv,loop_st) /\
    abi_decode_loop_prefix (Var iv) src DLOAD loop_st = (labels,body_st) /\
    abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var iv) src (Var dst)
      DLOAD (Lit 0w) (FST labels) (SND (SND labels)) (loop_st.cs_next_id+1)
      loop_st.cs_next_var st.cs_next_id st'.cs_next_id st.cs_next_id st'.cs_next_id
      loop_st.cs_next_var limit_st header_st.cs_next_id /\
    abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var iv) src (Var dst)
      sb d slot slot 32 loop_st.cs_next_var prepared /\
    ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) st.cs_next_var limit_st
      tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
      tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst) prepared = SOME (n2w d) /\
    eval_operand (Var iv) prepared = SOME (n2w slot) /\
    FLOOKUP H dst = SOME (b,sz) /\ FLOOKUP H iv = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst) = {} /\ op_taint qt (Var iv) = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
    qt.t_mem SUBSET tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial) /\
    ((\next slot_id slot_var dst_var cap initial header.
       (^loop_at) (SND (SND labels)) 0 (LENGTH vs) Y /\
       (^loop_frame) (jump_to (FST labels) prepared,H,qt,range_bytes [(d,32)]) Y)
      loop_st.cs_next_var header_st.cs_next_id iv dst sz prepared
      (mem_bytes_at d 32 prepared.vs_memory)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt (jump_to (FST labels) prepared)) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) /\
    abi_decode_sim ctx func prepared (jump_to (FST labels) prepared) /\
    SND (SND labels) = st'.cs_current_bb /\ st'.cs_current_insts = []
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
  BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
  `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
  `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
  drule_all ctor_actual_array_loop_layout >> strip_tac >>
  drule_all (SRULE [Excl "enc_def"]
    (Q.INST [`hi` |-> `Lit 0w`] ctor_actual_array_prefix_inputs)) >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var (Var dst)` by
    (Cases_on `src` >> fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,not_fresh_at_def]) >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by
    fs[abi_decoder_recursive_loop_compiled_def] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
    fs[Once type_memory_bytes_def] >>
  `d < dimword (:256)` by
    (drule_all alloca_frontier_inv_bound >> strip_tac >> decide_tac) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
    (irule ctor_actual_function_ids >> simp[]) >>
  `header_st.cs_next_id IN ctor_actual_sites func ids` by
    (qpat_assum `frag_ids st st' SUBSET ids`
       (mp_tac o MATCH_MP (Q.INST [`fn` |-> `func`] ctor_actual_sites_mono)) >>
     simp[SUBSET_DEF] >> disch_then irule >> simp[]) >>
  drule_all (Q.INST [`outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    prefix_loop_setup_pair) >>
  disch_then (qspecl_then [`tv`,`PG`,`Ddead`] strip_assume_tac) >>
  qpat_x_assum `ip = Var iv` SUBST_ALL_TAC >>
  `abi_decoder_operand_live st.cs_next_var (Lit (0w:bytes32))` by
    simp[abi_decoder_operand_live_def] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  `st.cs_next_var <= loop_st.cs_next_var` by
    (drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
     drule_all abi_decode_array_header_shape >> strip_tac >>
     drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  drule_all (SRULE [Excl "enc_def"]
    (Q.INST [`hi` |-> `Lit (0w:bytes32)`] ctor_actual_array_setup_context)) >>
  strip_tac >>
  `ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
    tv vs header_st.cs_next_id slot prepared 0 0 (jump_to (FST labels) prepared)` by
    (irule ctor_actual_array_observation_jump >> asm_rewrite_tac []) >>
  mp_tac (Q.INST [`initial` |-> `prepared`, `s` |-> `jump_to (FST (labels:string # string # string)) prepared`,
    `next` |-> `loop_st.cs_next_var`, `slot_id` |-> `header_st.cs_next_id`,
    `slot_var` |-> `iv`, `dst_var` |-> `dst`, `G` |-> `H`, `tn` |-> `qt`,
    `cap` |-> `sz`, `label` |-> `FST (labels:string # string # string)`, `index` |-> `0`,
    `header` |-> `mem_bytes_at d 32 prepared.vs_memory`] prefix_loop_zero_support) >>
  impl_tac >- (asm_rewrite_tac [] >> simp[jump_to_def,allocas_from_def] >>
    qpat_x_assum `allocas_from lo prepared` mp_tac >> simp[allocas_from_def]) >>
  disch_tac >>
  asm "child" mp_tac >>
  disch_then (mp_tac o GEN_ALL o MATCH_MP prefix_loop_separated_finite_pair) >>
  disch_then (drule_at (Pat `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then drule >>
  disch_then (drule_at (Pat `(^loop_at) _ _ _ _`)) >>
  disch_then (qspecl_then [`PG`,`Ddead`] mp_tac) >>
  impl_tac >- (asm_rewrite_tac [] >> simp[] >>
    irule SUBSET_TRANS >> qexists_tac `frag_ids st st'` >> asm_rewrite_tac []) >>
  disch_then (qx_choose_then `Y` assume_tac) >>
  drule_all abi_decoder_loop_phase_entry >> disch_tac >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
  `((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt
      (jump_to (FST labels) prepared)) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared)` by
    (match_mp_tac (Q.INST [`iid` |-> `loop_st.cs_next_id`,
       `hdr_bb` |-> `bb:basic_block`, `bb` |-> `<|bb_label := loop_st.cs_current_bb;
       bb_instructions := loop_st.cs_current_insts ++
         [mk_inst loop_st.cs_next_id JMP [Label (FST (labels:string # string # string))] []]|>`]
       prefix_loop_entry_jump_run) >>
     asm_simp_tac (srw_ss()) [get_instruction_def,EL_APPEND_EQN]) >>
  `abi_decode_sim ctx func prepared (jump_to (FST labels) prepared)` by
    (irule abi_decoder_loop_entry_sim >> simp[] >>
     qexists_tac `loop_st.cs_next_id` >> simp[]) >>
  `SND (SND labels) = st'.cs_current_bb /\ st'.cs_current_insts = []` by
    (drule abi_decoder_array_setup_head >> strip_tac >>
     qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac [] >>
     disch_then (mp_tac o MATCH_MP abi_decoder_loop_suffix_facts) >> simp[]) >>
  qexistsl_tac [`guard_st`,`header_st`,`loop_st`,`cnt`,`labels`,
    `body_st`,`ops`,`middle`,`end_st`,`prepared`,`slot`,`iv`,`H`,`qt`,`Y`] >>
  PairCases_on `Y` >> fs[]
QED

Theorem prefix_dynamic_array_setup_finite_pair:
  (^canonical_pair_floor) ty tv /\
  (is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
   G tn b sz Ddead lo PG.
  compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) st = ((),st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) root_di av v /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av))
    initial.vs_data_section = enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av /\
  (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  D+N <= initial.vs_alloca_next /\
  frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next ==>
  ?avs vs guard_st header_st loop_st cnt labels body_st ops middle end_st prepared slot iv H qt Y.
    av = ListV avs /\ v = ArrayV (DynArrayV vs) /\
    abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn
      (abi_embedded_static_size ce.ce_struct_fields ty) st = ((),guard_st) /\
    abi_decode_array_header (Var dst) src DLOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (Var iv,loop_st) /\
    abi_decode_loop_prefix (Var iv) src DLOAD loop_st = (labels,body_st) /\
    abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var iv) src (Var dst)
      DLOAD (Lit 0w) (FST labels) (SND (SND labels)) (loop_st.cs_next_id+1)
      loop_st.cs_next_var st.cs_next_id st'.cs_next_id st.cs_next_id st'.cs_next_id
      loop_st.cs_next_var limit_st header_st.cs_next_id /\
    abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var iv) src (Var dst)
      sb d slot slot 32 loop_st.cs_next_var prepared /\
    ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) st.cs_next_var limit_st
      tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
      tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst) prepared = SOME (n2w d) /\
    eval_operand (Var iv) prepared = SOME (n2w slot) /\
    FLOOKUP H dst = SOME (b,sz) /\ FLOOKUP H iv = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst) = {} /\ op_taint qt (Var iv) = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
    qt.t_mem SUBSET tn.t_mem /\ qt.t_stor = tn.t_stor /\
    qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial) /\
    ((\next slot_id slot_var dst_var cap initial header.
       (^loop_at) (SND (SND labels)) 0 (LENGTH vs) Y /\
       (^loop_frame) (jump_to (FST labels) prepared,H,qt,range_bytes [(d,32)]) Y)
      loop_st.cs_next_var header_st.cs_next_id iv dst sz prepared
      (mem_bytes_at d 32 prepared.vs_memory)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt (jump_to (FST labels) prepared)) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  drule prefix_dynamic_array_setup_finite_pair_complete >>
  disch_then drule >> disch_then (mk_asm "complete") >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_x "complete" drule_all >>
  disch_then (qspecl_then [`Ddead`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`avs`,`vs`,`guard_st`,`header_st`,`loop_st`,`cnt`,`labels`,
    `body_st`,`ops`,`middle`,`end_st`,`prepared`,`slot`,`iv`,`H`,`qt`,`Y`] >>
  asm_rewrite_tac []
QED

val _ = export_theory();
