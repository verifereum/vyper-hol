Theory bodyFullAbiDecodeArrayPrepare
Ancestors bodyPtrDefs[qualified,ignore_grammar]
  bodyFullAbiDecodeOwnedStateProps[qualified,ignore_grammar]
  abiEncoderAddressReach[qualified,ignore_grammar]
  abiDecoderDynarrayBound[qualified,ignore_grammar]
  abiDecoderBytesBound[qualified,ignore_grammar]
  bodyFullAbiDecodeGuardReadJoint bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeInputOrigin abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderGuards abiDecoderGuard abiDecoderArrayLoopInit
  exprLoweringProps emitHelperProps compileEnv fragExec emitHelper rich_list abiEncoder
  bodyFullAbiDecodeGuardReadObserved bodyFullAbiDecodeArrayPrepareSuffix
  abiDecoderReentry abiDecodePtrMemberFrame loweringStateRelDefs
  venomState venomExecSemantics words finite_map ptrDiscipline freshWrites
  fragGasOriginPtr fragGasOriginPtrLoop fragGasPath forPtrAllocationFrame
  valueEncodingProps venomMemProps loweringShapeRules
  bodyFullAbiDecodeArrayPrepareCountStride[qualified,ignore_grammar]
  abiCanonicalHeadSize[qualified,ignore_grammar]
  abiStaticAggregateProps[qualified,ignore_grammar]

Theorem array_prepare_count_extends[local]:
  abi_decode_le_guard cnt bound sa = ((),sb) ==> cs_extends sa sb
Proof
  `abi_decode_le_guard cnt bound sa = ((),sb) ==>
   sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    (simp[abi_decode_le_guard_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> strip_tac >> gvs[]) >>
  strip_tac >> drule abi_decode_le_guard_shape >>
  simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
  simp[IS_PREFIX_APPEND]
QED

Theorem array_prepare_payload_extends[local]:
  abi_decode_dynarray_payload_guard head cnt stride hi sa = ((),sb) ==>
  cs_extends sa sb
Proof
  `abi_decode_dynarray_payload_guard head cnt stride hi sa = ((),sb) ==>
   sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb` by
    (simp[abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_def,
          compile_abi_decode_range_check_def, emit_op_def, emit_void_def,
          fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     Cases_on `hi = Lit 0w` >> simp[comp_return_def] >> strip_tac >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def,
         fresh_var_def, fresh_id_def]) >>
  strip_tac >> drule abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_shape >>
  simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
  simp[IS_PREFIX_APPEND]
QED

Theorem array_prepare_trace[local]:
  abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn stride
    start = (addr,guard_st) /\
  abi_decode_array_header dst addr MLOAD guard_st = (cnt,header_st) ==>
  ?head head_st addr_st read_st check_st first reload_st.
    abi_decode_bytes_head src hi start = (head,head_st) /\
    compile_abi_dec_addr (Var input) src head_st = (addr,addr_st) /\
    emit_op MLOAD [addr] addr_st = (first,read_st) /\
    abi_decode_le_guard first (Lit (n2w maxn)) read_st = ((),check_st) /\
    abi_decode_dynarray_payload_guard head first stride hi check_st = ((),guard_st) /\
    emit_op MLOAD [addr] guard_st = (cnt,reload_st) /\
    emit_void MSTORE [dst;cnt] reload_st = ((),header_st) /\
    cs_extends start head_st /\ cs_extends head_st addr_st /\
    cs_extends addr_st read_st /\ cs_extends read_st check_st /\
    cs_extends check_st guard_st /\ cs_extends guard_st reload_st /\
    cs_extends reload_st header_st /\
    (!finish obs. cs_extends header_st finish /\ fn_has_code start finish obs ==>
      fn_has_code start head_st obs /\ fn_has_code head_st read_st obs /\
      fn_has_code read_st check_st obs /\ fn_has_code check_st guard_st obs /\
      fn_has_code guard_st reload_st obs /\ fn_has_code reload_st header_st obs)
Proof
  simp[abi_decode_dynarray_position_prefix_trace] >> strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_decode_bytes_head src hi start = (head,head_st)` >>
  rename1 `compile_abi_dec_addr (Var input) src head_st = (addr,addr_st)` >>
  rename1 `emit_op MLOAD [addr] addr_st = (first,read_st)` >>
  rename1 `emit_op MLOAD [addr] guard_st = (cnt,reload_st)` >>
  rename1 `emit_void MSTORE [dst;cnt] reload_st = ((),header_st)` >>
  `abi_decode_le_guard first (Lit (n2w maxn)) read_st = ((),count_st)` by
    simp[abi_decode_le_guard_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  qexists_tac `count_st` >> asm_rewrite_tac[] >>
  `cs_extends start head_st` by
    (drule abiDecoderBytesBoundTheory.abi_decode_bytes_head_fragment_shape >>
     simp[inst_extends_def] >> strip_tac >> irule cs_extends_same_block >>
     simp[IS_PREFIX_APPEND]) >>
  `emit_op ADD [Var input;src] head_st = (addr,addr_st)` by
    fs[compile_abi_dec_addr_def] >>
  `cs_extends head_st addr_st /\ cs_extends addr_st read_st /\
   cs_extends guard_st reload_st` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  drule array_prepare_count_extends >> strip_tac >>
  drule array_prepare_payload_extends >> strip_tac >>
  `cs_extends reload_st header_st` by
    (qspecl_then [`MSTORE`, `[dst;cnt]`, `reload_st`, `K T`]
       mp_tac externalEntryShapeTheory.emit_void_labels >> simp[]) >>
  asm_rewrite_tac[] >> qx_gen_tac `end_st` >> qx_gen_tac `obs` >> strip_tac >>
  `cs_extends head_st read_st` by metis_tac[cs_extends_trans] >>
  MAP_EVERY (fn (a,b) =>
    qspecl_then [a,b,`end_st`] (fn th => mp_tac th >> simp[] >> strip_tac)
      cs_extends_trans)
    [(`reload_st`,`header_st`), (`guard_st`,`reload_st`),
     (`count_st`,`guard_st`), (`read_st`,`count_st`), (`head_st`,`read_st`)] >>
  MAP_EVERY (fn (a,b) =>
    qspecl_then [a,b,`end_st`,`obs`] (fn th => mp_tac th >> simp[] >> strip_tac)
      fn_has_code_split)
    [(`start`,`head_st`), (`head_st`,`read_st`), (`read_st`,`count_st`),
     (`count_st`,`guard_st`), (`guard_st`,`reload_st`), (`reload_st`,`header_st`)] >>
  asm_rewrite_tac[]
QED

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\
  ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val prepare_origin = ``\s.
  ((?aid ib isz. aid < output_id /\
      FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= w2n (input_word:256 word) /\
      w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
      ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``;

val prepare_resources = ``\st s G tn.
  local_ptrs_reserved ce st /\
  lookup_var dst s = SOME (n2w d) /\
  ptr_covers G tn dst s (type_memory_size (ArrayTV tv (Dynamic maxn))) /\
  FLOOKUP G dst = SOME (output_base,output_cap) /\
  eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn src = {} /\ op_taint tn hi = {} /\
  op_taint tn (Var dst) = {} /\ op_taint tn (Var input) = {} /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var hi /\
  not_fresh_at st dst /\ not_fresh_at st input``;

Theorem abi_decode_array_prepare_width_joint:
  abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn stride
    start = (addr,guard_st) /\
  abi_decode_array_header (Var dst) addr MLOAD guard_st = (cnt,header_st) /\
  fn_has_code start header_st fn /\ fn_inst_ids_distinct fn /\
  (!c. c <= maxn ==> c * stride < dimword (:256)) /\
  (?H. V H) /\ hi <> Lit 0w /\ off < dimword (:256) /\ h <= LENGTH input_bytes /\
  w2n input_word + LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  (^prepare_resources) start s G tn /\ (^owned_decoder_state) start s G tn /\
  output_base <= d /\ d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/
    d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= w2n input_word) /\
  EVERY (\(aid,q,b,k,bytes). b+k <= d \/
    d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= d \/
    d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b) protected /\
  EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
  (^prepare_origin) s ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,Gf,tnf)) /\
    (!obs. fn_has_code start header_st obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t n cvar. r = OK t /\ cnt = Var cvar /\ n <= maxn /\
       off+32+n*stride <= h /\ off+32+n*stride <= LENGTH input_bytes /\
       ~t.vs_halted /\ t.vs_current_bb = header_st.cs_current_bb /\
       t.vs_inst_idx = LENGTH header_st.cs_current_insts /\ allocas_from lo t /\
       (^prepare_resources) header_st t Gf tnf /\
       (^owned_decoder_state) header_st t Gf tnf /\ (^prepare_origin) t /\
       EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
       eval_operand cnt t = SOME (n2w n) /\ op_prov Gf cnt = NONE /\
       op_taint tnf cnt = {} /\ not_fresh_at header_st cvar /\
       mem_word_at d t.vs_memory = n2w n /\
       mem_word_at (w2n input_word + off) t.vs_memory = n2w n /\
       (!i. d <= i /\ i < d+32 ==> i NOTIN tnf.t_mem) /\
       (!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
       (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnf.t_mem ==>
          i IN tn.t_mem)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all array_prepare_trace >>
  disch_then (qx_choose_then `head` (qx_choose_then `head_st`
    (qx_choose_then `addr_st` (qx_choose_then `read_st`
    (qx_choose_then `count_st` (qx_choose_then `first`
    (qx_choose_then `reload_st` (map_every assume_tac o CONJUNCTS)))))))) >>
  `!obs. fn_has_code start header_st obs ==>
       fn_has_code start head_st obs /\ fn_has_code head_st read_st obs /\
       fn_has_code read_st count_st obs /\ fn_has_code count_st guard_st obs /\
       fn_has_code guard_st reload_st obs /\ fn_has_code reload_st header_st obs` by
    (gen_tac >> disch_tac >> qpat_assum `!finish obs. _` (qspecl_then [`header_st`,`obs`] mp_tac) >>
     simp[cs_extends_refl]) >>
  `fn_has_code start head_st fn` by simp[] >>
  `h < dimword(:256)` by simp[] >>
  `allocas_from lo s /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    (conj_tac
     >- ((qpat_x_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
         qpat_assum `!H. V H ==> _` (qspec_then `H0` mp_tac) >>
         simp[bodyPtrDefsTheory.ghost_inv_at_def] >> (metis_tac[bodyPtrDefsTheory.ghost_inv_at_def]))) >>
     conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `origin` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (abi_decode_bytes_head_joint_observed |> SPEC_ALL |> BETA_RULE |>
          Q.INST [`sa` |-> `start`, `sb` |-> `head_st`]) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `sh` (qx_choose_then `Gh` (qx_choose_then `tnh`
      (map_every assume_tac o CONJUNCTS)))))
  >- suspend "load" >>
  qexistsl_tac [`Abort Revert_abort sh`,`Gh`,`tnh`] >> simp[]
QED

Resume abi_decode_array_prepare_width_joint[load]:
  `start.cs_next_var <= head_st.cs_next_var /\
   abi_decoder_operand_live head_st.cs_next_var head` by
    (qpat_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
          compile_abi_decode_range_check_def, emit_op_def, emit_void_def,
          fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> irule fresh_var_distinct >> decide_tac) >>
  `sh.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK sh,_,_)`
       (qspec_then `ARB` (mp_then Any ACCEPT_TAC
          gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `eval_operand src sh = SOME (n2w off) /\ op_taint tnh src = {}` by
    (qpat_assum `!x. _ ==> lookup_var x sh = _ /\ _` mp_tac >>
     qpat_assum `abi_decoder_operand_live start.cs_next_var src` mp_tac >>
     qpat_assum `eval_operand src s = _` mp_tac >>
     qpat_assum `op_taint tn src = _` mp_tac >>
     qpat_assum `sh.vs_labels = s.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `src` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          not_fresh_at_def, eval_operand_def, op_taint_def] >> metis_tac[]) >>
  `not_fresh_at head_st input /\ local_ptrs_reserved ce head_st /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at head_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at head_st x)` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
     conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `origin` >> simp[]) >>
  `off + 32 <= LENGTH input_bytes` by (simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sh` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es sh /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (abi_decode_bytes_owned_load_frame_joint_observed |> SPEC_ALL |> BETA_RULE |>
          Q.INST [`sa` |-> `head_st`, `sb` |-> `addr_st`, `sc` |-> `read_st`,
                  `pos` |-> `src`, `v` |-> `first`, `p` |-> `off`,
                  `s` |-> `sh`, `G` |-> `Gh`, `tn` |-> `tnh`]) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `first_var` (qx_choose_then `ar`
    (qx_choose_then `sl` (qx_choose_then `Gl` (qx_choose_then `tnl`
      (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "count"
QED

Resume abi_decode_array_prepare_width_joint[count]:
  `head_st.cs_next_var <= read_st.cs_next_var` by
    (qpat_assum `compile_abi_dec_addr _ _ _ = _` mp_tac >>
     qpat_assum `emit_op MLOAD [_] addr_st = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_abi_dec_addr_def, emit_op_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def] >> rpt strip_tac >> gvs[]) >>
  `not_fresh_at read_st input /\ local_ptrs_reserved ce read_st /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at read_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at read_st x)` by
    (conj_tac >- (irule not_fresh_at_mono >> qexists_tac `head_st` >> simp[]) >>
     conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `head_st` >> simp[]) >>
     conj_tac >> rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `head_st` >> simp[] >> first_assum irule >> simp[]) >>
  `abi_decoder_operand_live read_st.cs_next_var first` by
    (qpat_assum `first = Var first_var` SUBST1_TAC >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  qabbrev_tac `c = w2n (mload (w2n input_word + off) sh)` >>
  `eval_operand first sl = SOME (n2w c) /\ c < dimword (:256)` by
    simp[Abbr `c`, w2n_lt] >>
  `fn_has_code read_st count_st fn /\ maxn MOD dimword (:256) < dimword (:256)` by
    simp[arithmeticTheory.MOD_LESS] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sl` by
    (strip_tac >>
     irule bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp >>
     qexistsl [`V`,`ce`,`ctx`,`cx`,`es`,`fn`] >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es sl /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  mp_tac (abi_decode_bytes_count_joint_observed |> SPEC_ALL |> BETA_RULE |>
          Q.INST [`sa` |-> `read_st`, `sb` |-> `count_st`, `cnt` |-> `first`,
                  `s` |-> `sl`, `G` |-> `Gl`, `tn` |-> `tnl`,
                  `n` |-> `maxn MOD dimword (:256)`]) >>
  (impl_tac >-
    (rewrite_tac[n2w_mod] >> conj_tac >- first_assum ACCEPT_TAC >>
     asm_rewrite_tac[] >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
      (map_every assume_tac o CONJUNCTS)))))
  >- suspend "prepared"
  >> suspend "count_revert"
QED

Resume abi_decode_array_prepare_width_joint[count_revert]:
  qexistsl_tac [`Abort Revert_abort u`,`Gu`,`tnu`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gl`,`sl`,`tnl`] >>
      conj_tac
      >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`,`sh`,`tnh`] >> simp[]) >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
        (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_path_then))) >>
      qexists_tac `sl` >> reverse conj_tac >- simp[] >>
      irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
        (Q.INST [`n` |-> `0`, `m` |-> `0`] (SPEC_ALL gas_path_then))) >>
      qexists_tac `sh` >> simp[]) >>
  simp[]
QED

Resume abi_decode_array_prepare_width_joint[prepared]:
  `read_st.cs_next_var <= count_st.cs_next_var` by
    (qpat_assum `abi_decode_le_guard _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decode_le_guard_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> strip_tac >> gvs[]) >>
  `(!x. not_fresh_at start x ==> not_fresh_at head_st x) /\
   (!x. not_fresh_at head_st x ==> not_fresh_at read_st x) /\
   (!x. not_fresh_at read_st x ==> not_fresh_at count_st x)` by
    (conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
     conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `head_st` >> simp[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `read_st` >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\ op_taint tnu (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK u,Gu,tnu)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gl`,`sl`,`tnl`] >> conj_tac
     >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gh`,`sh`,`tnh`] >> simp[]) >>
     simp[]) >>
  Q_TAC (fn tm => SUBGOAL_THEN (rhs (concl (BETA_CONV tm))) ASSUME_TAC)
    `(^prepare_origin) u` >-
    (irule abi_decode_input_origin_transport >> qexistsl_tac [`s`,`start`] >>
     asm_rewrite_tac[] >> conj_tac >- simp[] >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK u,_,_)`
       (qspec_then `ARB` (mp_then Any mp_tac gas_origin_ptr_path_projections)) >>
     strip_tac >> drule gas_path_ptr_old_allocations >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ (OK u,_,_)`
       (qspec_then `ARB` (mp_then Any ACCEPT_TAC
          gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels))) >>
  `u.vs_labels = sh.vs_labels` by simp[] >>
  `!x. not_fresh_at head_st x ==> lookup_var x u = lookup_var x sh /\
    FLOOKUP Gu x = FLOOKUP Gh x /\ op_taint tnu (Var x) = op_taint tnh (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `eval_operand head u = SOME (n2w (off+32)) /\ op_prov Gu head = NONE /\
   op_taint tnu head = {}` by
    (Cases_on `head` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        GSYM not_fresh_at_def, eval_operand_def, op_prov_def, op_taint_def]) >>
  `eval_operand hi u = SOME (n2w h) /\ op_prov Gu hi = NONE /\ op_taint tnu hi = {}` by
    (Cases_on `hi` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
        GSYM not_fresh_at_def, eval_operand_def, op_prov_def, op_taint_def]) >>
  `eval_operand first u = SOME (n2w c) /\ op_prov Gu first = NONE /\
   op_taint tnu first = {}` by
    (qpat_assum `first = Var first_var` mp_tac >>
     qpat_assum `eval_operand first sl = SOME (n2w c)` mp_tac >>
     qpat_assum `op_prov Gl first = NONE` mp_tac >>
     qpat_assum `op_taint tnl first = {}` mp_tac >>
     qpat_assum `!x. not_fresh_at read_st x ==> lookup_var x u = _ /\ _`
       (qspec_then `first_var` mp_tac) >>
     qpat_assum `not_fresh_at read_st first_var` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> simp[] >>
     rpt strip_tac >> gvs[eval_operand_def, op_prov_def]) >>
  `c <= maxn` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `maxn MOD dimword(:256)` >>
     simp[arithmeticTheory.MOD_LESS_EQ]) >>
  `cs_extends guard_st header_st /\ cs_extends count_st header_st` by
    (conj_asm1_tac
     >- (irule cs_extends_trans >> qexists_tac `reload_st` >> simp[]) >>
     irule cs_extends_trans >> qexists_tac `guard_st` >> simp[]) >>
  `cs_extends start count_st` by
    (irule cs_extends_trans >> qexists_tac `head_st` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `read_st` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `addr_st` >> simp[]) >>
  `!obs. fn_has_code start header_st obs ==> fn_has_code count_st header_st obs` by
    (rpt strip_tac >> qspecl_then [`start`,`count_st`,`header_st`,`obs`] mp_tac fn_has_code_split >> simp[]) >>
  `!obs. fn_has_code count_st header_st obs ==>
    fn_has_code count_st guard_st obs /\ fn_has_code guard_st reload_st obs /\
    fn_has_code reload_st header_st obs` by
    (rpt strip_tac >>
     qspecl_then [`count_st`,`guard_st`,`header_st`,`obs`] mp_tac fn_has_code_split >>
     simp[] >> strip_tac >>
     qspecl_then [`guard_st`,`reload_st`,`header_st`,`obs`] mp_tac fn_has_code_split >> simp[]) >>
  `start.cs_next_var <= count_st.cs_next_var /\
   head_st.cs_next_var <= count_st.cs_next_var /\
   off+32 < dimword(:256)` by simp[] >>
  `abi_decoder_operand_live count_st.cs_next_var head /\
   abi_decoder_operand_live count_st.cs_next_var hi` by
    (conj_tac >> irule abi_decoder_operand_live_mono
     >- (qexists_tac `head_st.cs_next_var` >> simp[]) >>
     qexists_tac `start.cs_next_var` >> simp[]) >>
  `not_fresh_at count_st input /\ not_fresh_at count_st dst /\
   not_fresh_at count_st ar /\ local_ptrs_reserved ce count_st /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at count_st x)` by
    (simp[] >> irule local_ptrs_reserved_next_var >> qexists_tac `read_st` >> simp[]) >>
  suspend "suffix"
QED

Resume abi_decode_array_prepare_width_joint[suffix]:
  `w2n (input_word + n2w off) = w2n input_word + off` by
    (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> simp[]) >>
  `abi_decode_ptr_window Gu tnu u ar (input_word + n2w off) (LENGTH input_bytes-off)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gl`,`sl`,`tnl`] >> simp[]) >>
  `abi_decode_ptr_window Gu tnu u ar (input_word + n2w off) 32` by
    (qpat_assum `abi_decode_ptr_window Gu tnu u ar _ _` mp_tac >>
     rewrite_tac[abi_decode_ptr_window_def] >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `LENGTH input_bytes-off` >> simp[]) >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!j. w2n (input_word + n2w off) <= j /\ j < _ ==> j NOTIN tnu.t_mem`
       (qspec_then `i` irule) >> simp[]) >>
  `w2n (input_word + n2w off) + 32 <= u.vs_alloca_next` by simp[] >>
  `mem_word_at (w2n (input_word + n2w off)) u.vs_memory = n2w c` by
    simp[Abbr `c`, mem_word_at_eq_mload, mload_def] >>
  suspend "destination"
QED

Resume abi_decode_array_prepare_width_joint[destination]:
  `32 <= type_memory_size (ArrayTV tv (Dynamic maxn))` by
    simp[valueEncodingTheory.type_memory_size_def] >>
  `d < dimword (:256) /\ d+32 <= output_base+output_cap` by simp[] >>
  `alloca_inv u` by
    (qpat_assum `?H. V H` (qx_choose_then `H0` assume_tac) >>
     qpat_assum `!H. V H ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >>
     disch_then (mp_then Any ACCEPT_TAC
       (cj 2 stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) o CONJUNCT1)) >>
  `d+32 <= u.vs_alloca_next` by
    (qpat_assum `FLOOKUP u.vs_allocas output_id = SOME (output_base,output_cap)`
       (mp_then Any irule abiCallerAllocationTheory.abi_caller_allocation_end) >> simp[]) >>
  `ptr_covers Gu tnu dst u (type_memory_size (ArrayTV tv (Dynamic maxn)))` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `ptr_covers Gu tnu dst u 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >>
     qexists_tac `type_memory_size (ArrayTV tv (Dynamic maxn))` >> simp[]) >>
  `EVERY (\(aid,q,b,k,bytes). b+k <= d \/ d+32 <= b) live` by
    (irule listTheory.EVERY_MONOTONIC >>
     qexists_tac `\(aid,q,b,k,bytes). b+k <= d \/
       d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b` >>
     simp[] >> qx_gen_tac `row` >> PairCases_on `row` >> simp[] >> decide_tac) >>
  `EVERY (\(b,bytes). b+LENGTH bytes <= d \/ d+32 <= b) protected` by
    (irule listTheory.EVERY_MONOTONIC >>
     qexists_tac `\(b,bytes). b+LENGTH bytes <= d \/
       d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b` >>
     simp[pairTheory.FORALL_PROD] >> decide_tac) >>
  qpat_assum `emit_op MLOAD [addr] guard_st = (cnt,reload_st)`
    (mp_then Any (qx_choose_then `reload_var` (strip_assume_tac o CONJUNCT1))
       loweringShapeRulesTheory.emit_op_facts) >>
  qpat_x_assum `cnt = Var reload_var` SUBST_ALL_TAC >>
  qpat_x_assum `addr = Var ar` SUBST_ALL_TAC >>
  suspend "suffix_call"
QED

Resume abi_decode_array_prepare_width_joint[suffix_call]:
  `c * stride < dimword (:256)` by simp[] >>
  mp_tac (abi_decode_array_prepare_suffix_width_joint |> SPEC_ALL |> BETA_RULE |>
    Q.INST [`addr` |-> `ar`, `cnt` |-> `reload_var`, `p` |-> `off+32`,
            `a` |-> `input_word + n2w off`, `dw` |-> `n2w d`]) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[w2n_n2w])) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gp` (qx_choose_then `tnp`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r`,`Gp`,`tnp`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gu`,`u`,`tnu`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `u` >> reverse conj_tac >- simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `sl` >> reverse conj_tac >- simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `sh` >> simp[]) >>
  qpat_x_assum `(?t. r = Abort Revert_abort t) \/ (?t. r = OK t /\ _)`
    (DISJ_CASES_THEN (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >> qexists_tac `t` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`t`,`c`,`reload_var`] >>
  suspend "finish"
QED

Resume abi_decode_array_prepare_width_joint[finish]:
  `!mem. mem_bytes_at (w2n input_word) (LENGTH input_bytes) mem = input_bytes ==>
     mem_bytes_at (w2n input_word + off) 32 mem = TAKE 32 (DROP off input_bytes)` by
    (gen_tac >> disch_tac >>
     qspecl_then [`w2n input_word`,`off`,`32`,`LENGTH input_bytes`,`mem`] mp_tac
       abiCanonicalHeadSizeTheory.mem_bytes_at_window >> simp[]) >>
  `mem_bytes_at (w2n input_word + off) 32 t.vs_memory =
   mem_bytes_at (w2n input_word + off) 32 u.vs_memory` by simp[] >>
  `mem_word_at (w2n input_word + off) t.vs_memory = n2w c` by
    (irule EQ_TRANS >> qexists_tac `mem_word_at (w2n input_word + off) u.vs_memory` >>
     conj_tac
     >- (qpat_assum `mem_bytes_at _ 32 t.vs_memory = mem_bytes_at _ 32 u.vs_memory`
           (fn th => rewrite_tac [abiStaticAggregatePropsTheory.mem_word_at_bytes, th])) >>
     qpat_assum `w2n (input_word + n2w off) = _` (fn addr_eq =>
       qpat_assum `mem_word_at (w2n (input_word + n2w off)) u.vs_memory = _`
         (ACCEPT_TAC o REWRITE_RULE [addr_eq]))) >>
  `count_st.cs_next_var <= guard_st.cs_next_var` by
    (qpat_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
     qpat_assum `hi <> Lit 0w` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[abiDecoderDynarrayBoundTheory.abi_decode_dynarray_payload_guard_def,
          compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
          emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
          comp_return_def] >> strip_tac >> gvs[]) >>
  `start.cs_next_var <= header_st.cs_next_var` by
    (qpat_assum `emit_op MLOAD [Var ar] guard_st = _`
       (mp_then Any (assume_tac o cj 4) emitted_insts_emit_op) >>
     qpat_assum `emit_void MSTORE _ reload_st = _`
       (mp_then Any (assume_tac o cj 3) emitted_insts_emit_void) >> simp[]) >>
  `(!x. not_fresh_at start x ==> not_fresh_at header_st x) /\
   local_ptrs_reserved ce header_st` by
    (conj_tac >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `start` >> simp[]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
  `abi_decoder_operand_live header_st.cs_next_var src /\
   abi_decoder_operand_live header_st.cs_next_var hi` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  `!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `!D. gas_origin_ptr_path _ (u,Gu,tnu) _ (r,_,_)`
       (qspec_then `ARB` mp_tac) >>
     qpat_assum `r = OK t` (rewrite_tac o single) >>
     disch_then (mp_then Any assume_tac gasOriginPtrLabelsTheory.gas_origin_ptr_path_preserves_labels) >> simp[]) >>
  `!opnd. abi_decoder_operand_live start.cs_next_var opnd ==>
     eval_operand opnd t = eval_operand opnd s /\
     op_prov Gp opnd = op_prov G opnd /\ op_taint tnp opnd = op_taint tn opnd` by
    (rpt gen_tac >> disch_tac >>
     MATCH_MP_TAC (abiDecodePtrScalarFrameTheory.abi_decode_scalar_protected_operand |>
       Q.INST [`R` |-> `{x | not_fresh_at start x}`]) >>
     simp[] >> qx_gen_tac `x` >> disch_then SUBST_ALL_TAC >>
     qpat_assum `abi_decoder_operand_live start.cs_next_var (Var x)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `ptr_covers Gp tnp dst t (type_memory_size (ArrayTV tv (Dynamic maxn)))` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `w2n (n2w d : 256 word) = d` by simp[w2n_n2w] >>
  qpat_assum `mem_word_at (w2n (n2w d : 256 word)) t.vs_memory = _`
    (fn th => qpat_assum `w2n (n2w d : 256 word) = d`
      (fn addr_eq => assume_tac (REWRITE_RULE [addr_eq] th))) >>
  `tnu.t_mem = tn.t_mem` by simp[] >>
  `!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnp.t_mem ==>
       i IN tn.t_mem` by
    (qpat_assum `!i. _ /\ _ /\ i IN tnp.t_mem ==> i IN tnu.t_mem`
      (fn th => qpat_assum `tnu.t_mem = tn.t_mem`
        (fn mem_eq => ACCEPT_TAC (REWRITE_RULE [mem_eq] th)))) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_decode_array_prepare_width_joint

(* Canonical array metadata supplies the uniform width at the old entry. *)
Theorem abi_decode_array_prepare_joint:
  abi_decode_dynarray_position_prefix src MLOAD (Var input) hi maxn stride
    start = (addr,guard_st) /\
  abi_decode_array_header (Var dst) addr MLOAD guard_st = (cnt,header_st) /\
  fn_has_code start header_st fn /\ fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray child stride mem_sz dyn maxn /\
  abi_decoder_coherent ce env ce.ce_struct_fields
    (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  (?H. V H) /\ hi <> Lit 0w /\ off <= h /\ h <= LENGTH input_bytes /\
  w2n input_word + LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  (^prepare_resources) start s G tn /\ (^owned_decoder_state) start s G tn /\
  output_base <= d /\ d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/
    d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= w2n input_word) /\
  EVERY (\(aid,q,b,k,bytes). b+k <= d \/
    d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= d \/
    d+type_memory_size (ArrayTV tv (Dynamic maxn)) <= b) protected /\
  EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
  (^prepare_origin) s ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,Gf,tnf)) /\
    (!obs. fn_has_code start header_st obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t n cvar. r = OK t /\ cnt = Var cvar /\ n <= maxn /\
       off+32+n*stride <= h /\ off+32+n*stride <= LENGTH input_bytes /\
       ~t.vs_halted /\ t.vs_current_bb = header_st.cs_current_bb /\
       t.vs_inst_idx = LENGTH header_st.cs_current_insts /\ allocas_from lo t /\
       (^prepare_resources) header_st t Gf tnf /\
       (^owned_decoder_state) header_st t Gf tnf /\ (^prepare_origin) t /\
       EVERY (\(b,bytes). output_base <= b /\ b+LENGTH bytes <= output_base+output_cap) protected /\
       eval_operand cnt t = SOME (n2w n) /\ op_prov Gf cnt = NONE /\
       op_taint tnf cnt = {} /\ not_fresh_at header_st cvar /\
       mem_word_at d t.vs_memory = n2w n /\
       (!i. d <= i /\ i < d+32 ==> i NOTIN tnf.t_mem) /\
       (!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s /\
          FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
       (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tnf.t_mem ==>
          i IN tn.t_mem)))
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `off < dimword (:256)` by simp[] >>
  `!c. c <= maxn ==> c * stride < dimword (:256)` by
    (rpt strip_tac >>
     drule_all bodyFullAbiDecodeArrayPrepareCountStrideTheory.abi_decode_array_prepare_count_stride >>
     simp[]) >>
  mp_tac (BETA_RULE (SPEC_ALL abi_decode_array_prepare_width_joint)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `r` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`r`,`Gf`,`tnf`] >> asm_rewrite_tac[] >>
  qpat_x_assum `(?t. r = Abort Revert_abort t) \/ (?t n cvar. r = OK t /\ _)`
    (DISJ_CASES_THEN2 (qx_choose_then `t` assume_tac)
      (qx_choose_then `t` (qx_choose_then `n` (qx_choose_then `cvar`
        (map_every assume_tac o CONJUNCTS)))))
  >- (disj1_tac >> qexists_tac `t` >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl_tac [`t`,`n`,`cvar`] >> asm_rewrite_tac[]
QED
