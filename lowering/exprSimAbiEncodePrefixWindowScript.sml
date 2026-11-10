Theory exprSimAbiEncodePrefixWindow
Ancestors
  exprSimHash exprSimAlloc exprSimLiteralBuffer loweringPosts
  exprSimBufferStore abiValueEncoding abiBuiltinEncodeCode loweringHalt fragExec
  abiTupleValueEncoding abiEncoderStaticRepresentative abiEncoderWindow abiEncoderLeaves
  exprSimSource exprSimHypsDefs vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness
  abiBuiltinAllocation exprSimAbiEncodeConcreteResources
  abiEncoderSourceFootprint exprSimAbiEncodeProducerBoundary
  abiEncodeArgsSim abiTupleEncodePrepare abiTupleEncodeInput contractABI exprLowering
  valueEncodingProps compileEnv exprLoweringProps emitHelper emitHelperProps rich_list
  venomMemDefs venomInst venomState words finite_map list arithmetic

(* The actual singleton word staging prefix keeps its allocation certificate.
   In particular this also covers re-entry, where the site already exists. *)
Theorem abi_encode_word_staging:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op] sm = ((),sh) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME w /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?allocated addr.
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated =
      OK (mstore (w2n addr) w allocated) /\
    stmt_state_rel ctx func cenv cx es (mstore (w2n addr) w allocated) /\
    eval_operand buf.buf_operand allocated = SOME addr /\
    eval_operand op allocated = SOME w /\
    FLOOKUP allocated.vs_allocas sa.cs_next_id = SOME (w2n addr,32) /\
    w2n addr + 32 < dimword (:256) /\
    mem_bytes_at (w2n addr) 32 (mstore (w2n addr) w allocated).vs_memory =
      word_to_bytes_be w
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `eval_operand buf.buf_operand allocated = SOME addr` >>
  `allocated.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand op allocated = SOME w` by
    (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sh) allocated =
     OK (mstore (w2n addr) w allocated)` by
    (irule literal_emit_mstore_run >>
     qexistsl_tac [`buf.buf_operand`, `op`] >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mstore (w2n addr) w allocated)` by
    (irule literal_mstore_state_rel >> simp[] >>
     qexistsl_tac [`w2n addr`,
       `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
          [STRING #"%" (toString sa.cs_next_var)]`, `32`] >>
     simp[mk_inst_def] >> rpt strip_tac >>
     first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  qexistsl_tac [`allocated`, `addr`] >>
  simp[mem_bytes_at_mstore_same, byteTheory.word_to_bytes_be_def]
QED

(* Resource-only view of a real ALLOCA site. No execution or scratch budget
   is assumed: both the reuse size and fresh room come from stmt_state_rel. *)
Theorem abi_encode_allocate_resources:
  stmt_state_rel ctx func cenv cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w sz)] /\ sz < dimword (:256) ==>
  let a = abi_builtin_allocate_state inst.inst_id sz s in
  alloca_inv a /\ alloca_room ctx func a /\
  ?p. FLOOKUP a.vs_allocas inst.inst_id = SOME (p,sz) /\
      p+sz <= a.vs_alloca_next /\ a.vs_alloca_next < dimword (:256)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx func s` by fs[stmt_state_rel_def] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (`inst.inst_id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
      drule_all alloca_room_fresh >> strip_tac >>
      simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
      conj_tac
      >- (gvs[alloca_inv_def, allocas_non_overlapping_def,
              alloca_next_valid_def] >>
          rw[FLOOKUP_UPDATE] >> gvs[] >> res_tac >> gvs[]) >>
      gvs[w2n_n2w, ADD_COMM]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  `entry1 = sz` by
    (fs[stmt_state_rel_def] >> first_x_assum drule_all >> simp[]) >>
  simp[abi_builtin_allocate_state_def] >>
  conj_tac
  >- (gvs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  metis_tac[alloca_room_next_lt]
QED

Theorem abi_encode_word_output_resources:
  stmt_state_rel ctx func cenv cx es s /\
  FLOOKUP s.vs_allocas source_id = SOME (sb,32) /\
  source_id <> inst.inst_id /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w outsz)] /\ outsz < dimword (:256) /\
  offset + 32 <= outsz ==>
  let a = abi_builtin_allocate_state inst.inst_id outsz s in
  alloca_inv a /\ alloca_room ctx func a /\
  sb+32 <= a.vs_alloca_next /\
  ?p. FLOOKUP a.vs_allocas inst.inst_id = SOME (p,outsz) /\
      p+offset+32 <= a.vs_alloca_next /\
      venomMemDefs$regions_disjoint (sb,32) (p+offset,32)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_allocate_resources >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `FLOOKUP a.vs_allocas source_id = SOME (sb,32)` by
    simp[Abbr `a`, abiEncodeWindowBuiltinTheory.abi_window_allocate_other_row] >>
  `sb+32 <= a.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `sb+32 <= p \/ p+outsz <= sb` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum drule_all >> simp[]) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

(* Typed source representation at the very same staging endpoint. The type
   and conversion premises are the successful source builtin's checks. *)
Theorem abi_encode_word_expr_post:
  expr_post ctx func cenv cx e es origin sa s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; op] sm = ((),sh) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?allocated addr.
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated =
      OK (mstore (w2n addr) (typed_val_to_w256 tv v) allocated) /\
    stmt_state_rel ctx func cenv cx es'
      (mstore (w2n addr) (typed_val_to_w256 tv v) allocated) /\
    eval_operand buf.buf_operand allocated = SOME addr /\
    FLOOKUP allocated.vs_allocas sa.cs_next_id = SOME (w2n addr,32) /\
    w2n addr+32 < dimword (:256) /\
    mem_bytes_at (w2n addr) 32
      (mstore (w2n addr) (typed_val_to_w256 tv v) allocated).vs_memory =
      enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) = 32
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s /\
   eval_operand op s = SOME (typed_val_to_w256 tv v)` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all abi_encode_word_staging >> strip_tac >>
  drule_all (SRULE [] buffer_store_word_encoding) >> strip_tac >> gvs[] >>
  `w2n addr + 32 <= LENGTH
      (mstore (w2n addr) (typed_val_to_w256 tv v) allocated).vs_memory` by
    (simp[mstore_def, byteTheory.LENGTH_word_to_bytes, LENGTH_TAKE] >>
     rw[] >> simp[]) >>
  drule_all abi_word_memory >> strip_tac >> metis_tac[]
QED

(* The output resource site is the actual setup ALLOCA, also with a selector. *)
Theorem abi_encode_setup_alloca_code:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  fn_has_code st ready func ==>
  MEM (mk_inst st.cs_next_id ALLOCA
    [Lit (n2w (32 + 32 * word_size
      (maxlen + (case mid of NONE => 0 | SOME _ => 4))))]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)
Proof
  strip_tac >> drule abi_builtin_encode_setup_trace >> strip_tac >>
  `cs_extends st allocated` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends allocated ready` by
    (Cases_on `mid` >>
     gvs[abi_builtin_encode_method_id_def, emit_op_def, emit_void_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> simp[]
QED

Theorem abi_encode_word_setup_resources:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  fn_has_code st ready func /\ stmt_state_rel ctx func cenv cx es s /\
  FLOOKUP s.vs_allocas source_id = SOME (sb,32) /\
  source_id <> st.cs_next_id /\
  32 <= maxlen /\
  32 + 32 * word_size (maxlen + (case mid of NONE => 0 | SOME _ => 4))
    < dimword (:256) ==>
  let k = case mid of NONE => 0 | SOME _ => 4 in
  let outsz = 32 + 32 * word_size (maxlen+k) in
  let a = abi_builtin_allocate_state st.cs_next_id outsz s in
  alloca_inv a /\ alloca_room ctx func a /\
  sb+32 <= a.vs_alloca_next /\
  ?p. FLOOKUP a.vs_allocas st.cs_next_id = SOME (p,outsz) /\
      p+(32+k)+32 <= a.vs_alloca_next /\
      venomMemDefs$regions_disjoint (sb,32) (p+(32+k),32)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_setup_alloca_code >> strip_tac >>
  `32 + (case mid of NONE => 0 | SOME _ => 4) + 32 <=
   32 + 32 * word_size (maxlen + (case mid of NONE => 0 | SOME _ => 4))` by
    (mp_tac (Q.SPEC `maxlen + (case (mid:bytes32 option) of NONE => 0 | SOME _ => 4)`
      abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >> decide_tac) >>
  drule_at (Pat `MEM _ _`) abi_encode_word_output_resources >>
  disch_then (irule o SRULE [LET_THM, mk_inst_def, ADD_ASSOC]) >>
  simp[ADD_ASSOC] >> metis_tac[]
QED

(* The window uses a valid bytes32 representative, not the literal source ABI
   type: Fixed 0, for example, is source-typed but not literally ABI-typed. *)
Theorem abi_encode_word_source_window:
  is_word_type ty /\ mem_bytes_at sb 32 mem = enc at av /\
  LENGTH (enc at av) = 32 ==>
  ?ct rv. enc ct rv = enc at av /\
    abi_encoder_window_input (type_to_abi_enc_info sf ce ty) ct rv sb 32 mem
Proof
  strip_tac >> drule abi_word_metadata >> strip_tac >>
  drule abi_encoder_bytes32_representative >> strip_tac >>
  qexistsl_tac [`Bytes (SOME 32)`, `contractABI$BytesV (enc at av)`] >>
  simp[abi_encoder_window_copy_iff]
QED

Theorem abi_encode_word_body_no_alloca:
  is_word_type ty /\
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func ==>
  !inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids st en ==>
    inst.inst_opcode <> ALLOCA
Proof
  strip_tac >> drule abi_word_metadata >> strip_tac >> gvs[] >>
  drule abi_encode_copy_code >> strip_tac >>
  `MEM (mk_inst st.cs_next_id MCOPY [dst;src;Lit 32w] []) (fn_insts func)` by
    (gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, emit_def, fn_has_code_def,
         IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >> simp[]) >>
  `en.cs_next_id = st.cs_next_id + 1` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  rpt strip_tac >>
  `inst.inst_id = st.cs_next_id` by fs[abiEncoderPropsTheory.frag_ids_def] >>
  `inst = mk_inst st.cs_next_id MCOPY [dst;src;Lit 32w] []` by
    (irule localPtrsPropsTheory.fn_inst_ids_distinct_inj >>
     simp[mk_inst_def] >> qexists_tac `func` >> fs[mk_inst_def]) >>
  gvs[mk_inst_def]
QED

(* Source typing is a consequence of the real successful operand semantics,
   not a readiness assumption on the frozen expression simulation. *)
Theorem abi_encode_operand_success_type:
  expr_body_pre ce cx env e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es') ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >> drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
        env_context_consistent_def] >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def]
QED

Theorem abi_encode_singleton_success_conversion:
  evaluate_type_builtin cx (AbiEncode F mid) (TupleT [ty]) [ty] [v] = INL result ==>
  ?av. vyper_to_abi (get_tenv cx) ty v = SOME av
Proof
  simp[vyperContextTheory.evaluate_type_builtin_def,
       vyperABITheory.evaluate_abi_encode_bytes_def,
       vyperABITheory.needs_external_call_wrap_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_encode_word_size_bound:
  is_word_type ty ==> abi_size_bound sf ty = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[is_word_type_def, abi_size_bound_def, abi_static_size_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      simp[is_word_type_def, abi_size_bound_def, abi_static_size_def]) >>
  simp[abi_size_bound_def, abi_static_size_def]
QED

(* Producer checkpoint for the actual word branch. All semantic typing and
   conversion premises below are the successful operand and builtin results. *)
Theorem abi_encode_word_prefix_resources:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  (do result <- eval_expr cx e; read_result cx result od) es = (INL v,es') /\
  evaluate_type_builtin cx (AbiEncode F mid0) (TupleT [expr_type e])
    [expr_type e] [v] = INL result /\
  is_word_type (expr_type e) /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (expr_type e))
    sh = (ops,ready) /\
  fn_has_code sa sm func /\ fn_has_code sh ready func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  ?allocated addr ct rv p.
    let staged = mstore (w2n addr) (typed_val_to_w256
      (THE (evaluate_type (get_tenv cx) (expr_type e))) v) allocated in
    let k = case mid of NONE => 0 | SOME _ => 4 in
    let outsz = 32 + 32 * word_size (32+k) in
    let a = abi_builtin_allocate_state sh.cs_next_id outsz staged in
    run_inst_seq (emitted_insts sa sm) s = OK allocated /\
    run_inst_seq (emitted_insts sm sh) allocated = OK staged /\
    stmt_state_rel ctx func ce cx es' staged /\
    eval_operand buf.buf_operand allocated = SOME addr /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e))
      (THE (vyper_to_abi (get_tenv cx) (expr_type e) v)) /\
    LENGTH (enc ct rv) = 32 /\
    abi_encoder_window_input (type_to_abi_enc_info sf ce (expr_type e))
      ct rv (w2n addr) 32 staged.vs_memory /\
    alloca_inv a /\ alloca_room ctx func a /\
    w2n addr+32 <= a.vs_alloca_next /\
    FLOOKUP a.vs_allocas sh.cs_next_id = SOME (p,outsz) /\
    p+(32+k)+32 <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n addr,32) (p+(32+k),32)
Proof
  strip_tac >> drule_all abi_encode_operand_success_type >> strip_tac >>
  drule abi_encode_singleton_success_conversion >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all abi_encode_word_expr_post >> strip_tac >>
  `sh.cs_next_id = sa.cs_next_id + 2` by
    gvs[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by
    metis_tac[abi_encode_word_size_bound] >> gvs[] >>
  `FLOOKUP (mstore (w2n addr) (typed_val_to_w256 tv v) allocated).vs_allocas
    sa.cs_next_id = SOME (w2n addr,32)` by simp[mstore_def] >>
  `32 + 32 * word_size (32 + (case (mid:bytes32 option) of NONE => 0 | SOME _ => 4))
    < dimword (:256)` by
    (Cases_on `mid` >> simp[vfmConstantsTheory.word_size_def, dimword_def]) >>
  `sa.cs_next_id <> sh.cs_next_id` by decide_tac >>
  `abi_builtin_encode_setup mid 32 sh = (ops,ready)` by fs[] >>
  drule_all (SRULE [] (Q.INST [`maxlen` |-> `32`] abi_encode_word_setup_resources)) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_word_source_window >>
  disch_then (qspecl_then [`sf`, `ce`] strip_assume_tac) >>
  qexistsl_tac [`ct`, `rv`, `p`] >> gvs[]
QED

(* Actual footprint, including dynamic bytelikes and empty aggregates: no
   declared-capacity or literal ABI typing premise is used. *)
Theorem abi_encode_post_lowered_footprint:
  expr_body_pre ce cx env e es /\
  expr_post ctx func ce cx e es0 origin sa s0 es' v op s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v ==>
  ?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
    ~is_word_type (post_value_type ce e) /\
    val_footprint ptv v = val_footprint tv v
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[exprSimHypsTheory.expr_body_pre_lowered_fits] >>
  drule_all abiEncodeMaterializeTheory.materialize_post_lowered_classify >> strip_tac
  >- (qexists `tv` >> simp[] >>
      metis_tac[exprSimLayoutTransportTheory.compatible_word_type]) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv /\
      value_has_type ptv v` by
    (`post_value_type ce e = expr_type e \/
      post_value_type ce e = lowered_value_type ce e` by
       (Cases_on `e` >> simp[post_value_type_def] >>
        rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
        simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
        IF_CASES_TAC >> simp[]) >>
     gvs[] >>
     drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     goal_assum (drule_at Any) >>
     metis_tac[CONJUNCT1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type]) >>
  qexists `ptv` >> simp[] >>
  irule valueCopyBytesTheory.bytestring_val_footprint_eq >> metis_tac[]
QED

Theorem abi_encode_nonword_expr_window:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  ~is_word_type (post_value_type ce e) /\
  abi_enc_plan (get_tenv cx) (post_value_type ce e) ei /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (post_value_type ce e) v = SOME av ==>
  ?w ct rv. eval_operand op s = SOME w /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (post_value_type ce e)) av /\
    abi_encoder_window_input ei ct rv (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  `?w. eval_operand op s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all abi_encoder_source_footprint >> strip_tac >>
  drule abi_encoder_open_input_window >> metis_tac[]
QED

Theorem abi_encode_nonword_expr_bound:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  eval_operand op s = SOME w ==>
  val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= s.vs_alloca_next
Proof
  strip_tac >>
  `expr_val_at ce cx (post_value_type ce e) origin sa es' v op s /\
   alloca_inv s /\ local_ptrs_rel func ce es'.scopes s` by
    fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  drule_all expr_val_at_footprint >> strip_tac
  >- (fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[LESS_EQ_TRANS])
  >- (gvs[local_region_def, local_ptrs_rel_def] >>
      first_x_assum drule_all >> strip_tac >> gvs[lookup_var_def] >> decide_tac) >>
  simp[]
QED

Theorem abi_encode_nonword_expr_site_disjoint:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  ~is_word_type (post_value_type ce e) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
  eval_operand op s = SOME w /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce es'.scopes q /\ sa.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz)
Proof
  strip_tac >> irule abi_encode_expr_footprint_site_disjoint >>
  fs[expr_post_def, stmt_state_rel_def, state_rel_def] >> metis_tac[]
QED

(* A representative nonempty tuple consumer uses the actual args post,
   not an assumed ABI input. The raw word's valid bytes32 representative
   avoids imposing literal ABI validity (e.g. bytes0) on source values. *)
Theorem abi_encode_args_single_word_input:
  abi_args_post ctx func ce cx es sa sb s0 es' [e] [op] [v] s /\
  is_word_type (expr_type e) /\
  abi_decoder_operand_live next op ==>
  ?w. eval_operand op s = SOME w /\
    abi_tuple_encode_inputs sf ce [(op,expr_type e)] [Bytes (SOME 32)]
      [contractABI$BytesV (word_to_bytes w T)] next lo hi s
Proof
  strip_tac >>
  `?w. eval_operand op s = SOME w` by
    (gvs[abi_args_post_def, expr_val_rel_def] >> metis_tac[]) >>
  qexists_tac `w` >>
  simp[abi_tuple_encode_inputs_def, abi_tuple_encode_input_def] >>
  drule abi_word_metadata >> strip_tac >>
  simp[has_type_def, valid_length_def, is_dynamic_def, static_length_def,
       enc_def, type_memory_bytes_def, byteTheory.LENGTH_word_to_bytes,
       dimword_def]
QED

Theorem abi_encode_args_empty_store:
  abi_args_post ctx func ce cx es sa sb s0 es' [] ops vs s ==>
  compile_store_abi_tuple ce buf 0 (ZIP (ops,[])) sb = ((),sb) /\
  run_inst_seq (emitted_insts sb sb) s = OK s
Proof
  strip_tac >> gvs[abi_args_post_def, compile_store_abi_tuple_def,
       comp_return_def, emitted_insts_def, run_inst_seq_def]
QED

Theorem abi_encode_args_single_word_store:
  abi_args_post ctx func ce cx es sa sb s0 es' [e] [op] [v] s /\
  is_word_type (expr_type e) /\
  compile_store_abi_tuple ce buf off [(op,expr_type e)] sb = ((),final) /\
  abi_decoder_operand_live sb.cs_next_var op /\
  eval_operand buf s = SOME (n2w baddr) /\
  abi_decoder_operand_live sb.cs_next_var buf /\
  lo <= baddr+off /\ baddr+off+32 <= hi /\ hi < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?w actual. eval_operand op s = SOME w /\
    abi_tuple_encode_result sf ce [(op,expr_type e)] [Bytes (SOME 32)]
      [contractABI$BytesV (word_to_bytes w T)] sb final limit_st
      (baddr+off) s actual
Proof
  strip_tac >> drule_all (SRULE [] abi_encode_args_single_word_input) >>
  disch_then (qspecl_then [`sf`, `lo`, `hi`] strip_assume_tac) >>
  drule abi_word_metadata >> strip_tac >>
  `abi_tuple_bytes ce [(op,expr_type e)] = 32` by
    simp[abiTuplePropsTheory.abi_tuple_bytes_def] >>
  qexists_tac `w` >> simp[] >> irule abi_tuple_encode_sequence >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[ADD_ASSOC]
QED
