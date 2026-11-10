Theory exprSimAbiEncodeTupleResources
Ancestors
  exprSimHashBoundary
    loweringStateRelDefs
  exprSimAbiEncodeProducerAssembly exprSimAbiEncodePrefixWindow
  exprSimAbiEncodeArgsSeparation abiEncodeEndpointMetadata
  exprSimAbiEncodeNonwordResources abiTupleEncodePrepare abiEncoderCounters
  abiBuiltinEncodeCode exprSimAbiEncodeSiteResources
  exprSimHash abiEncodeArgsSim abiTupleProps
  exprSimAbiEncodeRuntimeInputs exprSimAbiEncodeCapacity
  vyperABIValid vyperABI vyperTypeExprSoundness vyperTypeDefaults abiTypeBoundProps
  exprSimHypsDefs abiEncoderWindow exprSimAbiEncodeSourceRoom
  exprSimAlloc localPtrsProps abiBuiltinAllocation compileEnv
  exprLoweringProps venomMemDefs venomInst venomState words list finite_map arithmetic

Theorem abi_encode_args_tuple_allocation_resources:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs initial /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  fn_has_code st allocated func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce st ==>
  let n = abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) in
  let a = abi_builtin_allocate_state st.cs_next_id n initial in
  ?sb. ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
         FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,n)) /\
    sb+n < dimword (:256) /\ alloca_inv a /\ alloca_room ctx func a /\
    FLOOKUP a.vs_allocas st.cs_next_id = SOME (sb,n) /\ sb+n <= a.vs_alloca_next /\
    a.vs_alloca_next < dimword (:256) /\
    (!k tv w. k < LENGTH args /\
      evaluate_type (get_tenv cx) (lowered_value_type ce (EL k args)) = SOME tv /\
      ~is_word_type (lowered_value_type ce (EL k args)) /\ eval_operand (EL k ops) initial = SOME w ==>
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv (EL k vs)) (sb,n))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule abi_args_post_lengths >> strip_tac >>
  `abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) =
    type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args))` by
    simp[abi_tuple_bytes_def, type_memory_bytes_def, MAP_MAP_o, combinTheory.o_DEF, MAP_ZIP] >>
  `abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) < dimword (:256)` by
    (drule abi_encode_endpoint_staging_size >>
     impl_tac >- simp[] >> simp[dimword_def]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' initial` by fs[abi_args_post_def] >>
  drule_at (Pat `MEM _ (fn_insts _)`) abi_encode_allocate_resources >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  disch_then drule >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  first_x_assum (qspec_then `abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexists `p` >> asm_simp_tac bool_ss [] >>
  conj_tac
  >- (Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id` >>
      gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]) >>
  conj_tac >- decide_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id`
  >- (`p = initial.vs_alloca_next` by
        gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
      drule abi_encode_args_value_at >>
      disch_then (qspec_then `k` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
      `alloca_inv initial /\ local_ptrs_rel func ce es'.scopes initial` by
        fs[stmt_state_rel_def, state_rel_def] >>
      drule_all expr_val_at_footprint >> strip_tac
      >- (fs[alloca_inv_def, alloca_next_valid_def,
             venomMemDefsTheory.regions_disjoint_def] >> metis_tac[LESS_EQ_TRANS])
      >- (gvs[local_region_def, local_ptrs_rel_def] >>
          first_x_assum drule_all >> strip_tac >> gvs[lookup_var_def] >>
          simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
      simp[venomMemDefsTheory.regions_disjoint_def]) >>
  `FLOOKUP initial.vs_allocas st.cs_next_id =
    SOME (p,type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args)))` by
    gvs[abi_builtin_allocate_state_def] >>
  `not_local_ptr ce es'.scopes (STRING #"%" (toString st.cs_next_var))` by
    metis_tac[local_ptrs_reserved_fresh, arithmeticTheory.LESS_EQ_REFL] >>
  `alloca_inv initial /\ local_ptrs_rel func ce es'.scopes initial` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`) abi_encode_args_footprint_site_disjoint >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  disch_then (qspecl_then [`w`, `tv`] mp_tac) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspec_then `k` mp_tac) >>
  asm_simp_tac (srw_ss()) []
QED

(* Allocation-only boundary: staging need not preserve the whole state relation. *)
Theorem abi_encode_args_allocate_row[local]:
  alloca_inv s /\ alloca_room ctx func s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) /\
  (!b oldsz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,oldsz) ==> oldsz = sz) ==>
  let a = abi_builtin_allocate_state inst.inst_id sz s in
  alloca_inv a /\ alloca_room ctx func a /\
  ?p. FLOOKUP a.vs_allocas inst.inst_id = SOME (p,sz) /\
    p+sz <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (`inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >> strip_tac >>
      simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
          rw[FLOOKUP_UPDATE] >> gvs[] >> res_tac >> gvs[]) >>
      gvs[w2n_n2w, ADD_COMM]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >> `entry1 = sz` by metis_tac[] >>
  simp[abi_builtin_allocate_state_def] >>
  conj_tac
  >- (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  metis_tac[alloca_room_next_lt]
QED

Theorem abi_encode_args_registered_phase_rows:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  abi_args_post ctx func ce cx es origin st s0 es' args values vs initial /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (values,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  s.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
  s.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)))
    staged = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) buf.buf_operand ei ready = (len,body_end) /\
  fn_has_code st allocated func /\ fn_has_code staged ready func /\
  fn_has_code ready body_end obs /\ fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\ local_ptrs_reserved ce st ==>
  let n = abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args)) in
  let outsz = 32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
    (case mid of NONE => 0 | SOME _ => 4)) in
  let a = abi_builtin_allocate_state staged.cs_next_id outsz s in
  ?sb p. alloca_inv a /\ alloca_room ctx func a /\ outsz < dimword (:256) /\
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (sb,n) /\ sb+n <= s.vs_alloca_next /\
    FLOOKUP a.vs_allocas st.cs_next_id = SOME (sb,n) /\ sb+n <= a.vs_alloca_next /\
    FLOOKUP a.vs_allocas staged.cs_next_id = SOME (p,outsz) /\
    p+outsz <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256) /\
    ((FLOOKUP s.vs_allocas staged.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas staged.cs_next_id = SOME (p,outsz)) /\
    venomMemDefs$regions_disjoint (sb,n) (p,outsz) /\
    (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\ FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,n) (b,sz))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_at (Pat `expr_body_pre _ _ _ _ _`) abi_encode_args_tuple_allocation_resources >>
  disch_then (drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  impl_tac >- simp[] >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sb` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `s.vs_allocas = source.vs_allocas` >>
  `alloca_inv s /\ alloca_room ctx func s` by
    (fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      alloca_room_def, pending_alloca_size_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
      (case mid of NONE => 0 | SOME _ => 4)) < dimword (:256)` by
    (drule abi_encode_endpoint_output_size >>
     Cases_on `LENGTH args = 1` >> Cases_on `mid0` >>
     gvs[] >> simp[dimword_def] >> decide_tac) >>
  drule_all abi_encode_setup_alloca_code >> strip_tac >>
  drule_at (Pat `alloca_room _ _ s`) abi_encode_args_allocate_row >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (qspec_then `32+32*word_size
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
      (case mid of NONE => 0 | SOME _ => 4))` mp_tac) >>
  simp_tac (srw_ss()) [mk_inst_def] >> impl_tac
  >- (asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
      `st.cs_next_id <> staged.cs_next_id` by decide_tac >>
      `FLOOKUP initial.vs_allocas staged.cs_next_id = SOME (b,oldsz)` by
        (qpat_x_assum `FLOOKUP source.vs_allocas _ = SOME (b,oldsz)` mp_tac >>
         asm_simp_tac (srw_ss()) [Abbr `source`, abi_encode_allocate_other_row]) >>
      fs[abi_args_post_def, stmt_state_rel_def] >>
      qpat_x_assum `!inst n base sz. _` (drule_at (Pat `MEM _ _`)) >>
      simp_tac (srw_ss()) [mk_inst_def] >>
      disch_then drule >> simp[w2n_n2w]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `mid = OPTION_MAP _ _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qabbrev_tac `outsz = 32+32*word_size
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
      (case mid of NONE => 0 | SOME _ => 4))` >>
  qabbrev_tac `a = abi_builtin_allocate_state staged.cs_next_id outsz s` >>
  `st.cs_next_id <> staged.cs_next_id` by decide_tac >>
  `FLOOKUP a.vs_allocas st.cs_next_id =
    SOME (sb,abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args)))` by
    simp[Abbr `a`, abi_encode_allocate_other_row] >>
  `sb+abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args)) <= a.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `venomMemDefs$regions_disjoint (sb,abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) (p,outsz)` by
    (fs[alloca_inv_def, allocas_non_overlapping_def, venomMemDefsTheory.regions_disjoint_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`st.cs_next_id`, `staged.cs_next_id`] mp_tac) >> simp[] >> metis_tac[]) >>
  qexistsl [`sb`, `p`] >> simp_tac bool_ss [] >>
  asm_rewrite_tac [] >> conj_tac
  >- (qpat_x_assum `FLOOKUP a.vs_allocas staged.cs_next_id = _` mp_tac >>
      simp[Abbr `a`, abi_builtin_allocate_state_def] >>
      Cases_on `FLOOKUP s.vs_allocas staged.cs_next_id` >> gvs[FLOOKUP_UPDATE]) >>
  suspend "scratch"
QED

Resume abi_encode_args_registered_phase_rows[scratch]:
  rpt gen_tac >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var` by
    (Cases_on `mid` >> fs[] >> decide_tac) >>
  drule_all abi_encode_compiled_scratch_site >>
  disch_then (qspec_then `es'.scopes` strip_assume_tac) >>
  `staged.cs_next_id < inst.inst_id` by
    metis_tac[abi_encode_setup_before_body_id] >>
  `st.cs_next_id <> inst.inst_id /\ staged.cs_next_id <> inst.inst_id` by decide_tac >>
  `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by
    (qpat_x_assum `FLOOKUP a.vs_allocas inst.inst_id = _` mp_tac >>
     asm_simp_tac (srw_ss()) [Abbr `a`, Abbr `source`, abi_encode_allocate_other_row]) >>
  `sz = 32` by
    (fs[abi_args_post_def, stmt_state_rel_def] >>
     qpat_x_assum `!inst n base sz. _` drule_all >> simp[dimword_def]) >>
  asm_rewrite_tac [] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, venomMemDefsTheory.regions_disjoint_def] >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
    (qspecl_then [`st.cs_next_id`, `inst.inst_id`] mp_tac) >> simp[] >>
  metis_tac[]
QED

Finalise abi_encode_args_registered_phase_rows

Theorem abi_encode_args_length_bound:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs ==>
  LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs)) <=
    abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))
Proof
  strip_tac >>
  `EVERY (\e. expr_body_pre ce cx env e es) args` by
    (simp[EVERY_MEM] >> metis_tac[abi_encode_body_arg_pre]) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs` by
    (irule exprSimHypsTheory.eval_exprs_physical_runtime_typed >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[exprSimHypsTheory.memory_rhs_read_lowered_typed_unwidened]) >>
  drule_all abi_encode_body_args_runtime_typed >> strip_tac >>
  drule_all exprSimHypsTheory.physical_runtime_typed_list_layouts >> strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  drule_all exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_physical_tuple_encoding_bound >> simp[]
QED

Theorem abi_encode_args_numerical_capacity:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs ==>
  let bytes = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) in
  let maxlen = abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) in
  let m = case mid of NONE => 0 | SOME _ => 4 in
  let outsz = 32+32*word_size (maxlen+m) in
  LENGTH bytes <= maxlen /\ 32+m+LENGTH bytes <= outsz /\
  outsz < dimword (:256) /\ LENGTH bytes+m < dimword (:256) /\
  32+(case mid of NONE => 0 | SOME _ => 32) <= outsz
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_args_length_bound >> strip_tac >>
  `32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) +
    (case mid of NONE => 0 | SOME _ => 4)) < dimword (:256)` by
    (drule abi_encode_endpoint_output_size >>
     Cases_on `LENGTH args = 1` >> Cases_on `mid0` >>
     gvs[] >> simp[dimword_def] >> decide_tac) >>
  drule abi_encode_payload_capacity >>
  disch_then (qspec_then `(case mid of NONE => 0 | SOME _ => 4)` assume_tac) >>
  qpat_x_assum `mid = OPTION_MAP _ _` (fn th => pure_rewrite_tac [GSYM th]) >>
  Cases_on `mid` >> gvs[] >>
  qspec_then `abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))` mp_tac
    (GEN_ALL abi_builtin_rounded_selector_store) >> simp[]
QED

Theorem abi_encode_args_phase_resources:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
  abi_args_post ctx func ce cx es origin st s0 es' args values vs initial /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (values,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  s.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
  s.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
  eval_operand buf.buf_operand s = SOME (n2w sb) /\
  FLOOKUP s.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) /\
  abi_encoder_open_input ei ct rv sb (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) s.vs_memory /\
  enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)))
    staged = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) buf.buf_operand ei ready = (len,body_end) /\
  fn_has_code st allocated func /\ fn_has_code staged ready func /\
  fn_has_code ready body_end obs /\ fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\
  obs.fn_name = func.fn_name /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\ local_ptrs_reserved ce st ==>
  let n = abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args)) in
  let bytes = enc ct rv in
  let m = case mid of NONE => 0 | SOME _ => 4 in
  let mw = case mid of NONE => 0 | SOME _ => 32 in
  let outsz = 32+32*word_size (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))+m) in
  let a = abi_builtin_allocate_state staged.cs_next_id outsz s in
  ?p. abi_encoder_window_input ei ct rv sb n s.vs_memory /\
    alloca_inv a /\ alloca_room ctx func a /\
    alloca_room (ctx with ctx_functions := [obs]) obs a /\
    ((FLOOKUP s.vs_allocas staged.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas staged.cs_next_id = SOME (p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    sb+n <= a.vs_alloca_next /\ p+32+m+LENGTH bytes <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,n) (p+32+m,LENGTH bytes) /\
    (sb+n <= p+32 \/ p+32+mw <= sb) /\
    venomMemDefs$regions_disjoint (p+32,m) (p+32+m,LENGTH bytes) /\
    (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\ FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (sb,n) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32+m,LENGTH bytes) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32,m) (b,sz))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_encode_args_registered_phase_rows >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_abi_tuple _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`s`, `obs`] mp_tac) >> (impl_tac >- simp[]) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sb0` (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `sb0 = sb` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
  qpat_x_assum `sb0 = sb` SUBST_ALL_TAC >>
  drule_at (Pat `expr_body_pre _ _ _ _ _`) abi_encode_args_numerical_capacity >>
  disch_then (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vyper_to_abi_list _ _ _ = _`)) >>
  disch_then (qspec_then `mid` mp_tac) >>
  (impl_tac >- (conj_tac >- (qpat_x_assum `LENGTH args = 1 ==> ensure` mp_tac >>
      simp_tac bool_ss []) >> first_assum ACCEPT_TAC)) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `mid = OPTION_MAP _ _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qmatch_asmsub_abbrev_tac `alloca_inv (abi_builtin_allocate_state _ outsz _)` >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `alloca_room (ctx with ctx_functions := [obs]) obs a` by
    (irule abi_encode_bridge_local_room >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `func` >> asm_rewrite_tac []) >>
  `st.cs_next_id <> staged.cs_next_id` by
    (drule_all abi_tuple_encode_stage_shape >> simp[]) >>
  qexists `p` >>
  `abi_encoder_window_input ei ct rv sb
    (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) s.vs_memory` by
    metis_tac[abi_encoder_open_input_window] >>
  qpat_x_assum `s.vs_allocas = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_x_assum `s.vs_alloca_next = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_x_assum `mid = OPTION_MAP _ _` kall_tac >>
  qpat_x_assum `enc ct rv = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [GSYM th]) >> pure_rewrite_tac [GSYM th]) >>
  asm_rewrite_tac [] >>
  conj_tac >- decide_tac >>
  conj_tac >- (qpat_assum `32 + (case mid of NONE => 0 | SOME _ => 32) <= outsz` mp_tac >>
    Cases_on `mid` >> simp_tac bool_ss [optionTheory.option_CLAUSES] >> decide_tac) >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (qpat_assum `venomMemDefs$regions_disjoint (sb,_) (p,outsz)` mp_tac >>
      simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (qpat_assum `alloca_inv a` mp_tac >>
      simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >> strip_tac >>
      first_x_assum (qspecl_then [`st.cs_next_id`, `staged.cs_next_id`] mp_tac) >>
      asm_simp_tac bool_ss [optionTheory.SOME_11, pairTheory.PAIR_EQ] >> decide_tac) >>
  conj_tac >- (pure_rewrite_tac [venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  suspend "scratch"
QED

Resume abi_encode_args_phase_resources[scratch]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!inst b sz. _` drule_all >> strip_tac >>
  asm_rewrite_tac [] >>
  drule_all abi_encode_setup_scratch_slices >>
  strip_tac >> qpat_x_assum `sz = 32` SUBST_ALL_TAC >>
  asm_rewrite_tac [] >>
  qpat_x_assum `venomMemDefs$regions_disjoint (p+32,_) (b,32)` mp_tac >>
  Cases_on `mid` >> simp_tac bool_ss [optionTheory.option_CLAUSES,
    venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Finalise abi_encode_args_phase_resources
