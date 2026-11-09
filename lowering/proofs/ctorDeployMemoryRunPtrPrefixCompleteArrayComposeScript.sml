(* Setup and traversal share the prepared runtime witness. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteArrayCompose
Ancestors
  ctorDeployMemoryRunPtrPrefixCompleteArraySetup
  ctorDeployMemoryRunPtrPrefixCompleteArrayRun
  abiDecoderLoop abiDecoderExecution abiDecoderContract abiDecoderReentry
  abiDecoderRecursiveLoopContext abiDecoderTypedContract abiCanonicalHeadSize
  abiDecoderArraySetupCode abiDecoderDynamicLoopSetup ctorAbiActualArrayInvariant
  ctorDeployLoweringEntryRegistration ctorDeployLoweringEntryCompleteScalar
  compileEnv venomState venomExecSemantics venomMemDefs valueEncoding valueEncodingProps
  ptrSafeRun ptrDiscipline words arithmetic list finite_map pred_set
  abiDecoderArrayLoopInit abiDecoderIndexInit

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

val PreparedPk = ``
  abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi loop_st.cs_next_var limit_st header_st.cs_next_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) (Var slot_var) src (Var dst_var)
    sb d slot slot 32 loop_st.cs_next_var prepared /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  fn_inst_ids_distinct func /\ k + unit_alloca_budget ctx < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  lo <= slot /\ lo <= d /\ D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\ frag_ids body_st end_st SUBSET ids /\
  header_st.cs_next_id NOTIN frag_ids middle end_st /\ b <= d /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz``;

val LoopAt = ``\label index j (s,Hout,qout,A).
  (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
    loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared j j s /\
  ~s.vs_halted /\ s.vs_current_bb = label /\ s.vs_inst_idx = index /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  FLOOKUP Hout slot_var = SOME (slot,32) /\ FLOOKUP Hout dst_var = SOME (b,sz) /\
  op_taint qout (Var slot_var) = {} /\ op_taint qout (Var dst_var) = {} /\ op_taint qout src = {} /\
  DISJOINT qout.t_mem {a | slot <= a /\ a < slot+32} /\
  FINITE A /\ A SUBSET range_bytes [(d,32+j*type_memory_size tv)] /\ DISJOINT A qout.t_mem /\
  (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 s.vs_memory) ==>
    mload d (s with vs_memory := mem) = n2w (LENGTH vs) /\
    elems_in_memory (TAKE j vs) (d+32) tv mem)``;

val Frame = ``\(s,G,tn,B) (t,H,qt,A).
  abi_decode_sim ctx func s t /\ qt.t_mem SUBSET tn.t_mem /\
  qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
  (!x. abi_decoder_older_vars loop_st.cs_next_var x ==>
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

val SetupResult = ``
    (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
      loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst_var) prepared = SOME (n2w d) /\
    eval_operand (Var slot_var) prepared = SOME (n2w slot) /\
    FLOOKUP H dst_var = SOME (b,sz) /\ FLOOKUP H slot_var = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst_var) = {} /\ op_taint qt (Var slot_var) = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    prepared.vs_code = initial.vs_code /\ prepared.vs_gas_readings = initial.vs_gas_readings /\
    prepared.vs_outcomes = initial.vs_outcomes /\ prepared.vs_tx_ctx = initial.vs_tx_ctx /\
    prepared.vs_block_ctx = initial.vs_block_ctx /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= slot \/ slot+32 <= a) ==>
      mem_bytes_at a n prepared.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial) /\
    (^PreparedPk) /\
    (^LoopAt) prepared.vs_current_bb (LENGTH loop_st.cs_current_insts) 0
      (prepared,H,qt,range_bytes [(d,32)]) /\
    lookup_block prepared.vs_current_bb func.fn_blocks = SOME entry_bb /\
    ?hdr_bb. lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0``;

val SetupPrem = ``
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header (Var dst_var) src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (Var slot_var,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst_var) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst_var) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst_var = SOME (b,sz) /\ b <= d /\
  d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst_var) = {} /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var slot_var) src (Var dst_var)
    DLOAD (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi loop_st.cs_next_var limit_st header_st.cs_next_id /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) initial.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  lo <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids body_st end_st SUBSET ids /\ header_st.cs_next_id NOTIN frag_ids middle end_st /\
  lookup_block loop_st.cs_current_bb func.fn_blocks = SOME entry_bb /\
  entry_bb.bb_instructions = loop_st.cs_current_insts ++ [mk_inst jump_id JMP [Label hdr] []]``;

Theorem prefix_complete_array_setup_exit_pair_exact:
  (^CshiftCode) ty tv ==> (^SetupPrem) ==>
  ?prepared slot H qt actual Hout qout A.
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      lookup_var x prepared = lookup_var x initial) /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      lookup_var x actual = lookup_var x initial) /\ 
    (^SetupResult) /\
    (^LoopAt) exit_lbl 0 (LENGTH vs) (actual,Hout,qout,A) /\
    (^Frame) (prepared,H,qt,range_bytes [(d,32)]) (actual,Hout,qout,A) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem) /\
    abi_decode_sim ctx func initial actual /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG Hout qout actual) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
  disch_then (mk_asm "child") >>
  disch_then (fn th => assume_tac th >>
    mp_tac (MATCH_MP prefix_complete_array_setup_loop_pair_exact th)) >>
  strip_tac >>
  rule_assum_tac BETA_RULE >>
  rpt (first_x_assum (CONJUNCTS_THEN assume_tac)) >>
  `(^SetupResult)` by (simp_tac std_ss [] >> asm_rewrite_tac[SUBSET_REFL] >> simp[]) >>
  `?actual Hout qout A.
    (^LoopAt) exit_lbl 0 (LENGTH vs) (actual,Hout,qout,A) /\
    (^Frame) (prepared,H,qt,range_bytes [(d,32)]) (actual,Hout,qout,A) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem)` by
    (BETA_TAC >> asm "child" (irule o MATCH_MP (BETA_RULE prefix_complete_array_prepared_pair)) >>
     asm_rewrite_tac[] >> conj_tac
     >- (qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (irule_at Any) >> asm_rewrite_tac[]) >>
     qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >>
     qexistsl [`loop_st.cs_current_insts`,`jump_id`,`hdr_bb'`,`entry_bb`] >>
     simp_tac std_ss [SUBSET_REFL] >> asm_rewrite_tac[] >> simp[]) >>
  qexistsl [`prepared`,`slot`,`H`,`qt`,`actual`,`Hout`,`qout`,`A`] >>
  rule_assum_tac (SIMP_RULE std_ss []) >>
  rpt (first_x_assum (CONJUNCTS_THEN assume_tac)) >>
  simp_tac std_ss [] >> asm_rewrite_tac[] >>
  conj_tac >-
    (rpt strip_tac >>
     `st.cs_next_var <= loop_st.cs_next_var` by
       (drule abi_decode_dynarray_prefix_shape >>
        simp[abi_decode_source_opcode_def] >> strip_tac >>
        drule abi_decode_array_header_shape >>
        simp[abi_decode_source_opcode_def] >> strip_tac >>
        drule abi_decode_index_init_shape >> strip_tac >> simp[]) >>
     `abi_decoder_older_vars loop_st.cs_next_var x` by
       (fs[abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  conj_tac >- (qexists `hdr_bb'` >> simp[]) >>
  conj_tac >- (irule abi_decode_sim_trans >> qexists `prepared` >> asm_rewrite_tac[]) >>
  strip_tac >>
  qpat_x_assum `(!fuel. ptr_safe_run _ _ fuel _ _ _ H qt prepared) ==> _` irule >>
  qpat_x_assum `(!fuel. ptr_safe_run _ _ fuel _ _ _ Hout qout actual) ==> _` irule >>
  asm_rewrite_tac[]
QED

Theorem prefix_complete_array_setup_exit_pair:
  (^CshiftCode) ty tv ==> (^SetupPrem) ==>
  ?prepared slot H qt actual Hout qout A.
    (^SetupResult) /\
    (^LoopAt) exit_lbl 0 (LENGTH vs) (actual,Hout,qout,A) /\
    (^Frame) (prepared,H,qt,range_bytes [(d,32)]) (actual,Hout,qout,A) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem) /\
    abi_decode_sim ctx func initial actual /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG Hout qout actual) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
  disch_tac >> drule prefix_complete_array_setup_exit_pair_exact >>
  disch_then (fn th => disch_then (mp_tac o MATCH_MP th)) >>
  disch_then (qspecl_then [`PG`,`Ddead`] strip_assume_tac) >>
  rule_assum_tac (SIMP_RULE std_ss []) >>
  rpt (first_x_assum (CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`prepared`,`slot`,`H`,`qt`,`actual`,`Hout`,`qout`,`A`] >>
  simp_tac std_ss [] >> asm_rewrite_tac[] >> qexists `hdr_bb` >> simp[]
QED


val _ = export_theory();
