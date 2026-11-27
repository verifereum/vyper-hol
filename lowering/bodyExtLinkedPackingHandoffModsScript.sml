(* Finish a linked external request at its actual physical packing cut. *)
Theory bodyExtLinkedPackingHandoffMods
Ancestors
  bodyExtTuplePayloadMods bodyExtPhysicalPrefixMods bodyExtPackingCursorFrameMods
  bodyFullExtCallEncodeTail bodyExtPackingEndpointMods abiEncodeValuesPhases
  bodyAbiEncodeRegisteredFrameMods abiCallerAllocation bodyPtrIfExpAllocCompiler
  fragGasOriginPtrLoop fragExec loweringHalt exprLoweringProps compileEnv
  stateRelProj bodyFullHashKeccakFixed memoryReadProps exprSimOperands
  bodyFullPostsMods abiEncoderWindowPhase bodyPtrDefs bodyFullShadowBodyInv
  venomInst venomState finite_map pred_set words arithmetic list pair
  exprSimWordArgs wordArgsPtr exprSimProps abiEncoderWindowContract
  ptrDiscipline loweringShapeDefs
Libs horizonTypeLib

(* The physical phase does not run any source action. Its input and output
   therefore share the same source state and horizon family. *)
val input_horizons = ``!H. valid_horizon cx st0 H ee.storage_trace ==>
  stmt_state_rel H ctx func ce cx ee s /\
  storage_well_formed_on cx ee (FST H) /\
  ghost_inv_at_mods (DF H) lo ret ce cx ee G tn s /\
  immutable_frame_mods func ce cx ee s``;

Theorem packed_allocation_site[local]:
  compile_alloc_buffer n sa = (shared,sb) /\ shared.buf_operand = Var root /\
  local_ptrs_reserved ce sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) ==>
  ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
    not_local_ptr ce ee.scopes root
Proof
  strip_tac >>
  `~not_fresh_at sa root` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  qexists `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]` >>
  simp[mk_inst_def] >> irule fresh_not_local_ptr >> metis_tac[]
QED

Theorem packed_encoded_suffix[local]:
  compile_abi_encode_values_to_buf ce (Var dp) rows sd = (out,en) /\
  fn_has_code sd en func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id < sd.cs_next_id /\ 32 <= n /\
  (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
     not_local_ptr ce ee.scopes root) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ^input_horizons /\
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
    sa.cs_next_id p n root dp selector en z Gz tz /\
  emit_op ADD [out;Lit 4w] en = (len,b3) /\ emit_op ADD [Var root;Lit 28w] b3 = (off,sp) /\
  fn_has_code en b3 func /\ fn_has_code b3 sp func /\
  eval_operand out z = SOME (n2w (LENGTH bytes)) /\ op_taint tz out = {} /\
  mem_bytes_at (p+32) (LENGTH bytes) z.vs_memory = bytes /\ LENGTH bytes <= n-32 /\
  (!i. p+32 <= i /\ i < p+32+LENGTH bytes ==> i NOTIN tz.t_mem) ==>
  ?x y t G' tn'. off = Var x /\ len = Var y /\
    not_fresh_at sp x /\ not_fresh_at sp y /\
    eval_operand off t = SOME (n2w (p+28)) /\
    eval_operand len t = SOME (n2w (4+LENGTH bytes)) /\
    op_taint tn' off = {} /\ op_taint tn' len = {} /\
    ptr_covers G' tn' x t (4+LENGTH bytes) /\
    read_memory (p+28) (4+LENGTH bytes) t = selector ++ bytes /\
    (!i. p+28 <= i /\ i < p+32+LENGTH bytes ==> i NOTIN tn'.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,G',tn')) /\
    window_phase ctx func en sp {} [] z t /\ abi_encode_exec_frame func z t /\
    ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
      sa.cs_next_id p n root dp selector sp t G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `^input_horizons` (drule_then (assume_tac o CONJUNCT1)) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ z`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ z`
    (assume_tac o MATCH_MP stmt_state_rel_alloca_room) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp z)` by
    (qpat_assum `stmt_state_rel hz _ _ _ _ _ z`
      (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >> simp[]) >>
  `allocas_from lo z` by fs[ghost_inv_at_mods_def] >>
  `p+n <= z.vs_alloca_next` by
    (irule abi_caller_allocation_end >> simp[] >>
     qexistsl [`n`,`sa.cs_next_id`,`p`] >> simp[]) >>
  `32 + LENGTH bytes <= n` by decide_tac >>
  `read_memory (p+32) (LENGTH bytes) z = bytes` by
    simp[read_memory_eq_mem_bytes_at] >>
  `!i. p+28 <= i /\ i < p+32+LENGTH bytes ==> i NOTIN tz.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i < p+32`
     >- (qpat_assum `!i. p+28 <= i /\ i < p+32 ==> _` irule >> simp[]) >>
     qpat_assum `!i. p+32 <= i /\ _ ==> _` irule >> simp[]) >>
  suspend "execute"
QED

Resume packed_encoded_suffix[execute]:
  drule_all extcall_encoded_request_suffix >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`x`,`y`,`t`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`x`,`y`,`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  suspend "frame"
QED

Resume packed_encoded_suffix[frame]:
  `ci_mono en b3` by
    (qspecl_then [`ADD`,`[out;Lit 4w]`,`en`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono b3 sp` by metis_tac[ci_mono_emit_op,SND] >>
  `ci_mono en sp` by (irule ci_mono_trans >> qexists `b3` >> simp[]) >>
  `tn'.t_mem SUBSET tz.t_mem` by simp[] >>
  `({}:num set) SUBSET {sd.cs_next_id}` by simp[] >>
  `!v. not_fresh_at en v ==> FLOOKUP G' v = FLOOKUP Gz v /\
      op_taint tn' (Var v) = op_taint tz (Var v)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!v. not_fresh_at en v ==> lookup_var v t = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then ACCEPT_TAC ext_packing_cursor_frame_mods
QED

Finalise packed_encoded_suffix

val prefix_inputs = ``
  compile_alloc_buffer n sa = (shared,sb) /\
  emit_void MSTORE [shared.buf_operand;Lit (calldata_method_id selector)] sb = ((),sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  LENGTH selector = 4 /\ 32 <= n /\ n < dimword (:256) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\ ^input_horizons /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts``;

val tuple_inputs = ``
  storage_trace_domain cx st0 ee.storage_trace /\ return_buf_frame ret ce sa s /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!typ rt. evaluate_type (get_tenv cx) typ = SOME rt ==>
    type_memory_bytes ce typ = type_memory_size rt) /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  bytes = enc (Tuple ats) (ListV avs) /\ LENGTH bytes <= n-32 /\
  (!i. i < LENGTH rows ==>
    ?e saved ty v tv. EL i rows = (saved,ty) /\ ty = lowered_value_type ce e /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
      type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
      EL i ats = vyper_to_abi_type (get_tenv cx) ty /\
      vyper_to_abi (get_tenv cx) ty v = SOME (EL i avs) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        ext_pos_saved_row_mods lo ce cx kw_es pos sa H e saved v ee G tn s))``;

val payload_compile = ``
  comp_bind (emit_op ADD [shared.buf_operand;Lit 32w]) (\dst.
    comp_bind (compile_abi_encode_values_to_buf ce dst rows) (\out.
      emit_op ADD [out;Lit 4w]))``;

val packed_frame = ``
  shared.buf_operand = Var root /\ not_fresh_at sp root /\
  lookup_var root t = SOME (n2w p) /\ FLOOKUP G' root = SOME (p,n) /\
  ptr_covers G' tn' root t n /\ lo <= p /\ p+n < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,n) /\ sa.cs_next_id < sp.cs_next_id /\
  sa.cs_next_var <= sp.cs_next_var /\ local_ptrs_reserved ce sp /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo ret ce cx ee G' tn' t /\ immutable_frame_mods func ce cx ee t) /\
  pure_frame ce func ee sa s t /\ wb_frame ce ee ee sa s t /\
  ghost_kept_at lo ce ee sa G tn s G' tn' /\ alloca_history func t /\ window_alloca_growth s t /\
  ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\ t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!a k. (a+k <= lo \/
          (?name b sz. local_region ce ee.scopes s name b sz /\ b <= a /\ a+k <= b+sz) \/
          (?id b sz. id < sa.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,sz) /\
                     b <= a /\ a+k <= b+sz)) ==>
       mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory /\
       (!i. a <= i /\ i < a+k /\ i IN tn'.t_mem ==> i IN tn.t_mem)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn'))``;

fun packed_read payload = ``
  off = Var x /\ not_fresh_at sp x /\
  eval_operand off t = SOME (n2w (p+28)) /\
  eval_operand len t = SOME (n2w (4+LENGTH ^payload)) /\
  op_taint tn' off = {} /\ op_taint tn' len = {} /\
  ptr_covers G' tn' x t (4+LENGTH ^payload) /\
  read_memory (p+28) (4+LENGTH ^payload) t = selector ++ ^payload /\
  (!i. p+28 <= i /\ i < p+32+LENGTH ^payload ==> i NOTIN tn'.t_mem)``;

val empty_packet = ``?root p x u Gu tu t G' tn'.
  len = Lit 4w /\ ^packed_frame /\
  emit_op ADD [Var root;Lit 28w] sc = (off,sp) /\
  read_memory (p+28) 4 u = selector /\
  ^(packed_read ``[]:word8 list``) /\
  window_phase ctx func sc sp {} [] u t /\ abi_encode_exec_frame func u t /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK t,G',tn'))``;

val encoded_packet = ``?root p x y dp sd en out z Gz tz t G' tn'.
  ^packed_frame /\ ^(packed_read ``bytes:word8 list``) /\
  len = Var y /\ not_fresh_at sp y /\
  emit_op ADD [Var root;Lit 32w] sc = (Var dp,sd) /\
  compile_abi_encode_values_to_buf ce (Var dp) rows sd = (out,en) /\
  emit_op ADD [out;Lit 4w] en = (len,b3) /\
  emit_op ADD [Var root;Lit 28w] b3 = (off,sp) /\
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
    sa.cs_next_id p n root dp selector en z Gz tz /\
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
    sa.cs_next_id p n root dp selector sp t G' tn' /\
  window_phase ctx func en sp {} [] z t /\ abi_encode_exec_frame func z t /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK t,G',tn'))``;

Theorem packed_nonempty[local]:
  ^prefix_inputs /\ ^tuple_inputs /\ ^payload_compile sc = (len,b3) /\
  emit_op ADD [shared.buf_operand;Lit 28w] b3 = (off,sp) /\
  fn_has_code sc b3 func /\ fn_has_code b3 sp func ==>
  ^encoded_packet
Proof
  pure_rewrite_tac[comp_bind_def] >>
  Cases_on `emit_op ADD [shared.buf_operand;Lit 32w] sc` >>
  rename1 `emit_op ADD [shared.buf_operand;Lit 32w] sc = (dst,sd)` >>
  pure_rewrite_tac[pairTheory.UNCURRY,LET_THM,pairTheory.FST,pairTheory.SND] >> BETA_TAC >>
  Cases_on `compile_abi_encode_values_to_buf ce dst rows sd` >>
  rename1 `compile_abi_encode_values_to_buf ce dst rows sd = (out,en)` >>
  qpat_assum `compile_abi_encode_values_to_buf ce dst rows sd = _`
    (fn th => pure_rewrite_tac [pairTheory.UNCURRY,LET_THM,comp_bind_def,th,
                                pairTheory.FST,pairTheory.SND]) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sc sd` by
    (qspecl_then [`ADD`,`[shared.buf_operand;Lit 32w]`,`sc`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sd en` by
    (qspecl_then [`ce`,`dst`,`rows`,`sd`] mp_tac ci_mono_compile_abi_encode_values_to_buf >> simp[]) >>
  `ci_mono en b3` by
    (qspecl_then [`ADD`,`[out;Lit 4w]`,`en`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sd b3` by (irule ci_mono_trans >> qexists `en` >> simp[]) >>
  `fn_has_code sc sd func /\ fn_has_code sd b3 func` by
    (irule fn_has_code_split >> simp[GSYM ci_mono_def] >>
     fs[ci_mono_def]) >>
  `fn_has_code sd en func /\ fn_has_code en b3 func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  suspend "tuple"
QED

Resume packed_nonempty[tuple]:
  mp_tac (Q.INST [`bs` |-> `selector`] ext_tuple_payload_mods) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`root`,`dp`,`p`,`z`,`Gz`,`tz`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `dst = Var dp` SUBST_ALL_TAC >>
  `emit_op ADD [Var root;Lit 32w] sc = (Var dp,sd) /\
   emit_op ADD [Var root;Lit 28w] b3 = (off,sp)` by
    (qpat_assum `shared.buf_operand = Var root` (SUBST1_TAC o SYM) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ci_mono sa sb` by
    (qspecl_then [`n`,`sa`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sb sc` by
    (qspecl_then [`MSTORE`,`[shared.buf_operand;Lit (calldata_method_id selector)]`,`sb`]
      mp_tac ci_mono_emit_void >> simp[]) >>
  `ci_mono sa sc` by (irule ci_mono_trans >> qexists `sb` >> simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id < sd.cs_next_id` by
    (qpat_assum `emit_op ADD [Var root;Lit 32w] sc = _`
       (assume_tac o MATCH_MP entryDecodeStructureTheory.emit_op_next_id) >>
     fs[ci_mono_def] >> decide_tac) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = sa.cs_next_id /\ inst.inst_outputs = [root] /\
     not_local_ptr ce ee.scopes root` by
    (irule packed_allocation_site >> first_assum (irule_at Any) >> simp[]) >>
  mp_tac packed_encoded_suffix >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (qexists `inst` >> simp[])))) >>
  disch_then (qx_choosel_then [`x`,`y`,`t`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`root`,`p`,`x`,`y`,`dp`,`sd`,`en`,`out`,`z`,`Gz`,`tz`,`t`,`G'`,`tn'`] >>
  suspend "encoded_packet"
QED

Resume packed_nonempty[encoded_packet]:
  qpat_assum `ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret sa s G tn
    _ _ _ _ _ _ sp t _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  `local_ptrs_reserved ce sp` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gz`,`z`,`tz`] >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise packed_nonempty

Theorem packed_empty[local]:
  ^prefix_inputs /\ len = Lit 4w /\
  emit_op ADD [shared.buf_operand;Lit 28w] sc = (off,sp) /\
  fn_has_code sc sp func ==>
  ^empty_packet
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `^input_horizons` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `es` |-> `ee`, `d` |-> `ret`, `bs` |-> `selector`,
                  `H0` |-> `hz`] ext_physical_prefix_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`]
    (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo ret ce cx ee Gu tu u /\ immutable_frame_mods func ce cx ee u` by
    (gen_tac >> disch_tac >>
     qpat_assum `^input_horizons` (drule_then (map_every assume_tac o CONJUNCTS)) >>
     conj_tac >- metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!D. ghost_inv_at_mods D _ _ _ _ _ G tn s /\ _ ==> _`
       (qspec_then `DF H` mp_tac) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then (assume_tac o CONJUNCT1)) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ u`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ u`
    (assume_tac o MATCH_MP stmt_state_rel_alloca_room) >>
  qpat_assum `stmt_state_rel hz _ _ _ _ _ u`
    (assume_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
  `emit_op ADD [Var root;Lit (n2w 28)] sc = (off,sp)` by
    (qpat_assum `shared.buf_operand = Var root` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `eval_operand (Var root) u = SOME (n2w (w2n (w:256 word)))` by simp[eval_operand_def] >>
  suspend "offset"
QED

Resume packed_empty[offset]:
  `28 + 4 <= n` by simp[] >>
  drule_all (Q.INST [`off` |-> `28`, `n` |-> `4`] abi_encode_values_head_address) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`x`,`t`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS))) >>
  `ci_mono sc sp` by
    (qspecl_then [`ADD`,`[Var root;Lit 28w]`,`sc`] mp_tac ci_mono_emit_op >> simp[]) >>
  `ci_mono sa sp` by (irule ci_mono_trans >> qexists `sc` >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= sp.cs_next_var /\
   sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sa.cs_next_id` by fs[ci_mono_def] >>
  `sa.cs_next_id < sp.cs_next_id` by
    (qpat_assum `emit_op ADD [Var root;Lit 28w] sc = _`
      (assume_tac o MATCH_MP entryDecodeStructureTheory.emit_op_next_id) >> fs[ci_mono_def]) >>
  `!aid. aid IN sa.cs_next_id INSERT ({}:num set) ==>
    ?inst v. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [v] /\ not_local_ptr ce ee.scopes v` by
    (simp[] >> drule_all packed_allocation_site >>
     disch_then (qspec_then `ee` (qx_choose_then `inst` strip_assume_tac)) >>
     qexistsl [`inst`,`root`] >> simp[]) >>
  suspend "frame"
QED

Resume packed_empty[frame]:
  `!aid:num. aid IN {} ==> sa.cs_next_id <= aid` by simp[] >>
  `EVERY (\(p,k). w2n w <= p /\ p+k <= w2n w+n) []` by simp[] >>
  `!i. EVERY (\(p,k). i < p \/ p+k <= i) [] /\
    (!aid p k. aid IN {} /\ FLOOKUP t.vs_allocas aid = SOME (p,k) ==>
      i < p \/ p+k <= i) /\ i IN tn'.t_mem ==> i IN tu.t_mem` by simp[] >>
  drule_all (Q.INST [`ids` |-> `{}:num set`, `outs` |-> `[]:(num # num) list`,
                    `shared` |-> `sa.cs_next_id`] abi_encode_registered_phase_frame_mods) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`root`,`w2n w`,`x`,`u`,`Gu`,`tu`,`t`,`G'`,`tn'`] >>
  suspend "compose_empty"
QED

Resume packed_empty[compose_empty]:
  `wb_frame ce ee ee sa s t` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee sa s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee sa u t` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee sa G tn s G' tn'` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee sa G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee sa Gu tu u G' tn'` (irule_at Any) >> simp[] >>
     qexists `ee` >> simp[]) >>
  `pure_frame ce func ee sa s t` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ee`,`sa`,`u`] >> simp[]) >>
  `window_alloca_growth s t` by
    (drule_then (assume_tac o CONJUNCT2 o CONJUNCT2) window_phase_resources >>
     irule window_alloca_growth_trans >> qexists `u` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  `eval_operand (Var root) t = SOME (n2w (w2n w)) /\ ptr_covers G' tn' root t n` by
    (drule_all_then ACCEPT_TAC abi_encode_values_pointer_frame) >>
  `not_fresh_at sp root` by (irule not_fresh_at_mono >> qexists `sc` >> simp[]) >>
  `local_ptrs_reserved ce sp` by
    (irule local_ptrs_reserved_next_var >> qexists `sc` >> simp[]) >>
  `FLOOKUP G' root = SOME (w2n w,n)` by
    (qpat_assum `!v. not_fresh_at sc v ==> FLOOKUP G' v = _ /\ _`
      (drule_then (assume_tac o CONJUNCT1)) >> simp[]) >>
  `op_taint tn' off = {}` by
    (qpat_assum `off = Var x` SUBST1_TAC >> fs[ptr_covers_def]) >>
  `!i. w2n w+28 <= i /\ i < w2n w+32 ==> i NOTIN tu.t_mem` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. w2n w <= i /\ _ ==> i NOTIN tu.t_mem` irule >> simp[]) >>
  `not_local_ptr ce ee.scopes root` by
    (drule_all packed_allocation_site >> disch_then (qspec_then `ee` strip_assume_tac)) >>
  simp[read_memory_eq_mem_bytes_at, eval_operand_def, op_taint_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `read_memory (w2n w+28) 4 u = selector`
    (ACCEPT_TAC o REWRITE_RULE[read_memory_eq_mem_bytes_at])
QED

Finalise packed_empty

Theorem ext_linked_packing_handoff_mods:
  let rows = ZIP (vals,tys) in
  ^prefix_inputs /\ (vals <> [] ==> ^tuple_inputs) /\
  (if vals = [] then comp_return (Lit 4w) else ^payload_compile) sc = (len,b3) /\
  emit_op ADD [shared.buf_operand;Lit 28w] b3 = (off,sp) /\
  fn_has_code sc b3 func /\ fn_has_code b3 sp func ==>
  (vals = [] ==> ^empty_packet) /\ (vals <> [] ==> ^encoded_packet)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (disch_tac >>
      qpat_x_assum `(if vals = [] then _ else _) sc = _` mp_tac >>
      qpat_assum `vals = []`
        (fn th => pure_rewrite_tac [th,REFL_CLAUSE,COND_CLAUSES,comp_return_def,PAIR_EQ]) >>
      disch_then (CONJUNCTS_THEN2 (assume_tac o SYM) SUBST_ALL_TAC) >>
      mp_tac (Q.INST [`sc` |-> `b3`] packed_empty) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  disch_tac >>
  qpat_x_assum `(if vals = [] then _ else _) sc = _` mp_tac >>
  qpat_assum `vals <> []` (fn th => pure_rewrite_tac [th,COND_CLAUSES]) >>
  disch_tac >>
  qpat_x_assum `vals <> [] ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`rows` |-> `ZIP (vals,tys)`] packed_nonempty) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
