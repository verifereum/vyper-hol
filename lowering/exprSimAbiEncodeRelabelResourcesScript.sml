Theory exprSimAbiEncodeRelabelResources
Ancestors
  exprSimAbiEncodeRelabelBoundary exprSimAbiEncodeObliviousSimulation
  exprSimAbiEncodeObliviousContext abiBuiltinEncodeCode abiBuiltinEncodeContext
  exprSimAbiGasBridge compileEnv emitHelperProps abiEncoderCounters abiEncoderProps fragExec list
  exprSimAbiEncodeProducerExecution exprSimAbiEncodeSourceRoom
  abiBuiltinAllocation exprLoweringProps venomState venomInst venomMemDefs

Theorem abi_encode_setup_entry_action[local]:
  entry_action (abi_builtin_encode_setup mid maxlen)
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_setup_def, abi_builtin_encode_method_id_def,
    entry_action_bind, entry_action_ignore_bind, entry_action_return,
    entry_action_alloc_buffer, entry_action_emit_op, entry_action_emit_void]
QED

Theorem abi_encode_relabel_phase_equations:
  abi_builtin_encode_setup mid maxlen sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  abi_builtin_encode_setup mid maxlen (start_relabel L ids sa) =
    (ops,start_swap sa L ids ready) /\
  compile_abi_encode_to_buf (SND ops) src ei (start_swap sa L ids ready) =
    (len,start_swap sa L ids body_end)
Proof
  strip_tac >>
  `entry_shape sa sa` by simp[entry_shape_refl] >>
  mp_tac abi_encode_setup_entry_action >> rewrite_tac[entry_action_def] >>
  disch_then drule_all >> disch_then (qspec_then `L` strip_assume_tac) >>
  conj_tac >- metis_tac[start_swap_initial] >>
  mp_tac (cj 2 entry_action_encoder_mutual) >>
  rewrite_tac[entry_action_def] >> disch_then drule_all >>
  metis_tac[]
QED

Theorem abi_encode_start_swap_resource_fields:
  (start_swap sa L ids st).cs_next_var = st.cs_next_var /\
  (start_swap sa L ids st).cs_next_id = st.cs_next_id /\
  frag_ids (start_swap sa L ids st) (start_swap sa L ids en) = frag_ids st en
Proof
  simp[start_swap_def, frag_ids_def, LET_THM] >>
  Cases_on `NULL (emitted_blocks sa st)` >>
  Cases_on `NULL (emitted_blocks sa en)` >> simp[]
QED

Theorem abi_encode_allocate_relabel_fields:
  abi_builtin_allocate_state site outsz (s with vs_current_bb := L) =
    (abi_builtin_allocate_state site outsz s) with vs_current_bb := L
Proof
  simp[abi_builtin_allocate_state_def] >> IF_CASES_TAC >> simp[]
QED

Theorem abi_encode_alloca_resources_current_bb:
  alloca_inv (s with vs_current_bb := L) = alloca_inv s /\
  alloca_room ctx func (s with vs_current_bb := L) = alloca_room ctx func s
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_room_def, pending_alloca_size_def]
QED

Theorem abi_encode_nonword_relabel_resources:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  abi_enc_plan (get_tenv cx) (expr_type e) ei /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (expr_type e))
    sa = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) op ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code sa final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  obs.fn_name = func.fn_name /\ fn_inst_ids_distinct obs /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)) /\
  LENGTH ids = LENGTH sa.cs_current_insts ==>
  ?w ct rv p.
    let rs = s with vs_current_bb := L in
    let rst = start_relabel L ids sa in
    let rready = start_swap sa L ids ready in
    let rend = start_swap sa L ids body_end in
    let bytes = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    let mw = case mid of NONE => 0 | SOME _ => 32 in
    let outsz = 32+32*word_size (abi_size_bound ce.ce_struct_fields (expr_type e)+m) in
    let a = abi_builtin_allocate_state rst.cs_next_id outsz rs in
    abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (expr_type e))
      rst = (ops,rready) /\
    compile_abi_encode_to_buf (SND ops) op ei rready = (len,rend) /\
    eval_operand op rs = SOME w /\ enc ct rv = bytes /\
    abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) rs.vs_memory /\
    ((val_footprint tv v = 0 /\ ei = AbiCopy 0) \/
     (0 < val_footprint tv v /\ w2n w+val_footprint tv v <= rs.vs_alloca_next)) /\
    alloca_inv a /\ alloca_room ctx func a /\
    alloca_room (ctx with ctx_functions := [obs]) obs a /\
    FLOOKUP a.vs_allocas rst.cs_next_id = SOME (p,outsz) /\
    ((FLOOKUP rs.vs_allocas rst.cs_next_id = NONE /\ p = rs.vs_alloca_next) \/
      FLOOKUP rs.vs_allocas rst.cs_next_id = SOME (p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    p+32+m+LENGTH bytes <= a.vs_alloca_next /\
    (0 < val_footprint tv v ==>
      w2n w+val_footprint tv v <= a.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (p+32+m,LENGTH bytes) /\
      (w2n w+val_footprint tv v <= p+32 \/ p+32+mw <= w2n w)) /\
    venomMemDefs$regions_disjoint (p+32,m) (p+32+m,LENGTH bytes) /\
    (!inst b sz. MEM inst (fn_insts obs) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids rready rend /\
      FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\ venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32+m,LENGTH bytes) (b,sz) /\
      venomMemDefs$regions_disjoint (p+32,m) (b,sz))
Proof
  strip_tac >> drule_all abi_builtin_encode_code >> strip_tac >>
  `!j. MEM j (fn_insts func) /\ j.inst_opcode <> STOP /\
    j.inst_opcode <> NOP ==> MEM j (fn_insts func)` by simp[] >>
  drule_all abi_encode_nonword_phase_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `w` (qx_choose_then `ct` (qx_choose_then `rv`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  qpat_x_assum `mid = OPTION_MAP _ _` kall_tac >>
  drule_all abi_encode_relabel_phase_equations >>
  disch_then (qspec_then `L` strip_assume_tac) >>
  `eval_operand op (s with vs_current_bb := L) = eval_operand op s` by
    (Cases_on `op` >> simp_tac (srw_ss()) [eval_operand_def, lookup_var_def]) >>
  qexistsl_tac [`w`, `ct`, `rv`, `p`] >>
  ` (start_relabel L ids sa).cs_next_id = sa.cs_next_id` by
    simp_tac (srw_ss()) [start_relabel_def] >>
  simp_tac (srw_ss()) [LET_THM,
    abi_encode_allocate_relabel_fields, abi_encode_alloca_resources_current_bb,
    abi_encode_start_swap_resource_fields] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (irule abi_encode_bridge_local_room >> conj_tac >- simp[] >>
      qexists_tac `func` >>
      asm_rewrite_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts func)` by
    (first_x_assum irule >> asm_rewrite_tac[] >> simp[]) >>
  first_x_assum irule >> qexists_tac `inst` >> asm_rewrite_tac[]
QED
