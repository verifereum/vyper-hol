Theory calldataNoneRegisterOne
Ancestors defaultBytesRegistrationPrelude defaultBytesAddressPrelude
  registrationGuardRejectOrigin ctorDeployMemoryRunPtrPrefixRegisterAddress
  fragGasOriginPtr loweringShapeDefs loweringStateRelDefs fragExec
  emitHelperProps context compileEnv abiEncoder abiDecoderContract words arithmetic
  venomState venomExecSemantics ptrDiscipline finite_map ASCIInumbers
  entryPtrSeamRegister calldataRegistrationRawAddress calldataRegistration
  calldataSourceCorrespondence calldataRegistrationExec abiDecoderAppend
  loweringHalt compileVyper ctorRegisterArgs abiDecoderCounters fragGasOriginPtrLoop vyperCalldata

Theorem registration_wrapped_prefix_origin:
  compile_alloc_buffer cap st = (buf,allocated) /\
  emit_op ADD [Lit 4w; Lit (n2w (off-4))] allocated = (head,after_head) /\
  emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
  emit_op ADD [Lit 4w;offset] after_load = (src,mid) /\
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) mid = ((),first) /\
  fn_has_code st allocated fn /\ fn_has_code allocated mid fn /\
  fn_has_code mid first fn /\ fn_inst_ids_distinct fn /\
  (4w + abi_decode_load CALLDATALOAD ((4w+n2w (off-4)):bytes32) s) <+ 4w /\
  cap < dimword (:256) /\ FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `a = (update_var p (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (st.cs_next_id,(s.vs_alloca_next,cap));
        vs_alloca_next := s.vs_alloca_next+cap|>))
      with vs_inst_idx := LENGTH allocated.cs_current_insts` >>
  qabbrev_tac `G0 = G |+ (p,(s.vs_alloca_next,cap))` >>
  qabbrev_tac `u0 = tn with <|t_var := tn.t_var |+ (p,{});
      t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\
                                    j < s.vs_alloca_next+cap}|>` >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK a,G0,u0)` by
    (drule_all default_bytes_alloc_origin >>
     disch_then (qspecl_then [`tn`,`PG`,`G`] mp_tac) >>
     simp[Abbr `a`, Abbr `p`, Abbr `G0`, Abbr `u0`]) >>
  `allocated.cs_current_bb = st.cs_current_bb /\
   allocated.cs_next_var = st.cs_next_var+1` by
    (Cases_on `emit_op ALLOCA [Lit (n2w cap)] st` >>
     gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def,
         prefix_register_address_emit_shape] >>
     drule prefix_register_address_emit_shape >> simp[]) >>
  `allocas_from lo a /\ ~a.vs_halted /\ a.vs_current_bb = allocated.cs_current_bb /\
   a.vs_inst_idx = LENGTH allocated.cs_current_insts /\
   a.vs_call_ctx = s.vs_call_ctx` by
    (simp[Abbr `a`, update_var_def, allocas_from_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `st.cs_next_id = aid` >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  drule_all default_bytes_address_joint >>
  disch_then (qspecl_then [`u0`,`PG`,`G0`] strip_assume_tac) >>
  suspend "guard"
QED

Resume registration_wrapped_prefix_origin[guard]:
  drule_all default_bytes_address_shape >> strip_tac >>
  `!v. src = Var v ==> not_fresh_at mid v` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, toString_11] >>
  `fresh_vars_wrt mid t` by
    (drule_all default_bytes_address_exec >> strip_tac >>
     qpat_assum `!v. run_inst_seq (emitted_insts allocated mid) v = _`
       (qspec_then `a` assume_tac) >>
     qpat_x_assum `t = a with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
     gvs[fresh_vars_wrt_def, Abbr `a`, Abbr `p`, update_var_def, toString_11] >>
     rpt strip_tac >> first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  `allocas_from lo t` by
    (qpat_assum `t = a with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[allocas_from_def] >> fs[allocas_from_def] >> metis_tac[]) >>
  `(4w + abi_decode_load CALLDATALOAD ((4w+n2w (off-4)):bytes32) a) <+ 4w` by
    gvs[abi_decode_load_def, abi_decode_source_def] >>
  `?z H1 u1. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (t,H,u) [] (Abort Revert_abort z,H1,u1)` by
    (irule registration_ptr_guard_reject_origin >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl [`mid`,`first`,`src`] >>
     goal_assum $ drule_at (Pat `eval_operand src t = SOME _`) >>
     rpt conj_tac >> FIRST_PROVE [first_assum ACCEPT_TAC,
       gvs[abi_decode_load_def, abi_decode_source_def]]) >>
  qexistsl [`z`,`H1`,`u1`] >> simp[] >> rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u)` by
    metis_tac[gas_origin_ptr_path_append, listTheory.APPEND] >>
  metis_tac[gas_origin_ptr_path_append, listTheory.APPEND]
QED
Finalise registration_wrapped_prefix_origin

Theorem none_registration_singleton_wrap[local]:
  compile_register_positional_args ce [(name,F,T,sz,di)] (4+ofs) st = (ce1,last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME cap /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  abi_decode_load CALLDATALOAD (n2w (4+ofs):bytes32) s = n2w delta /\
  (4+delta) MOD dimword (:256) < 4 /\
  cap < dimword (:256) /\ FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  fresh_vars_wrt st s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  strip_tac >> drule_all registration_aggregate_prepare_phases >> simp[] >> strip_tac >>
  `cs_extends st a /\ cs_extends a b /\ cs_extends b c /\ cs_extends c g /\
   cs_extends g first /\ cs_extends first last` by
    metis_tac[compile_alloc_buffer_extends, prefix_register_address_emit_shape,
      registration_ptr_guard_extends, cs_extends_abi_decode] >>
  `cs_extends a g` by metis_tac[cs_extends_trans] >>
  `fn_has_code st a fn /\ fn_has_code a g fn /\ fn_has_code g first fn` by
    metis_tac[cs_extends_trans, fn_has_code_split] >>
  `(4w + abi_decode_load CALLDATALOAD ((4w+n2w ofs):bytes32) s) <+ 4w` by
    (gvs[word_add_n2w, WORD_LO, w2n_n2w, ADD_COMM, dimword_def] >>
     simp[word_add_n2w, WORD_LO, w2n_n2w, ADD_COMM, dimword_def]) >>
  rename1 `emit_op CALLDATALOAD [head] b = (offset_operand,c)` >>
  irule registration_wrapped_prefix_origin >> simp[] >>
  qexistsl [`b`,`c`,`a`,`buf`,`cap`,`first`,`head`,`g`,`4+ofs`,`offset_operand`,`src`,`st`] >>
  simp[]
QED

Theorem none_registration_singleton_paths:
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME (type_memory_size tv) /\
  type_memory_size tv < dimword (:256) /\
  compile_register_positional_args ce [build_positional_arg ce (name,ty)]
    (4+ofs) st = (ce1,last) /\ fn_has_code st last fn /\
  4+ofs+tv_abi_size tv < dimword (:256) /\
  s.vs_call_ctx.cc_calldata = cd /\
  fn_inst_ids_distinct fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> id < st.cs_next_id) /\
  fresh_vars_wrt st s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!first t src q p d oid H u.
     compile_abi_decode_to_buf (Var q) src CALLDATALOAD (Lit 0w) (Lit 0w)
       (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
     fn_has_code first last fn /\ eval_operand src t = SOME p /\
     eval_operand (Var q) t = SOME (n2w d) /\
     abi_decoder_operand_live first.cs_next_var src /\
     abi_decoder_operand_live first.cs_next_var (Var q) /\
     alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
     (!id. first.cs_next_id <= id ==> FLOOKUP t.vs_allocas id = NONE) /\
     FLOOKUP t.vs_allocas oid = SOME (d,type_memory_size tv) /\
     oid < first.cs_next_id /\ d+type_memory_size tv < dimword (:256) /\
     ptr_covers H u q t (type_memory_size tv) /\
     op_taint u src = {} /\ op_prov H src = NONE /\
     fresh_vars_wrt last t /\ ~t.vs_halted /\
     t.vs_current_bb = first.cs_current_bb /\
     t.vs_inst_idx = LENGTH first.cs_current_insts ==>
       (?z K w. z.vs_returndata = [] /\
         !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
           (t,H,u) [] (Abort Revert_abort z,K,w)) \/
       (?v K w. IS_SOME (cd_decode F t.vs_call_ctx.cc_calldata tv (w2n p)) /\
         v.vs_call_ctx = t.vs_call_ctx /\ alloca_inv v /\
         alloca_frontier_inv ctx fn site v /\
         (!id. last.cs_next_id <= id ==>
            FLOOKUP v.vs_allocas id = FLOOKUP t.vs_allocas id) /\
         fresh_vars_wrt last v /\ ~v.vs_halted /\
         v.vs_current_bb = last.cs_current_bb /\
         v.vs_inst_idx = LENGTH last.cs_current_insts /\
         !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
           (t,H,u) [] (OK v,K,w))) ==>
  (?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,G,tn) [] (Abort Revert_abort z,H,u)) \/
  (?v H u. IS_SOME (calldata_decode_args cd [tv] ofs) /\
    v.vs_call_ctx.cc_calldata = cd /\ alloca_inv v /\
    alloca_frontier_inv ctx fn site v /\
    (!id entry. FLOOKUP v.vs_allocas id = SOME entry ==> id < last.cs_next_id) /\
    fresh_vars_wrt last v /\ ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    !D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
      (s,G,tn) [] (OK v,H,u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv` by
    (drule calldata_coherent_dynamic >> simp[]) >>
  `compile_register_positional_args ce
     [(name,F,tv_abi_dynamic tv,abi_embedded_static_size ce.ce_struct_fields ty,
       type_to_abi_dec_info ce.ce_struct_fields ce ty)] (4+ofs) st = (ce1,last)` by
    (qpat_x_assum `compile_register_positional_args ce _ _ st = _` mp_tac >>
     Cases_on `is_word_type ty` >-
       (`~tv_abi_dynamic tv` by metis_tac[ctor_word_type_static] >>
        `?cl. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord cl` by
          simp[word_type_decoder_primitive] >>
        gvs[build_positional_arg_def, registration_primitive_as_aggregate]) >>
     simp[build_positional_arg_def]) >>
  qpat_x_assum `compile_register_positional_args ce [build_positional_arg ce _] _ st = _`
    kall_tac >>
  `4+ofs < dimword (:256)` by decide_tac >>
  qabbrev_tac `delta = w2n (cd_word cd (4+ofs))` >>
  qabbrev_tac `p = if tv_abi_dynamic tv then (4+delta) MOD dimword (:256) else 4+ofs` >>
  `abi_decode_load CALLDATALOAD (n2w (4+ofs):bytes32) s = n2w delta /\
   (4 <= p ==> (tv_abi_dynamic tv ==> 4+delta < dimword (:256)) /\
      p = 4 + (if tv_abi_dynamic tv then delta else ofs)) /\
   (!vals. calldata_decode_args cd [tv] ofs = SOME vals <=>
      ?x. 4 <= p /\ cd_decode F cd tv p = SOME x /\ vals = [x])` by
    (`cd = s.vs_call_ctx.cc_calldata /\ delta = w2n (cd_word cd (4+ofs)) /\
      p = (if tv_abi_dynamic tv then (4+delta) MOD dimword (:256) else 4+ofs)` by
       simp[Abbr `p`, Abbr `delta`] >>
     drule_all (Q.INST [`tvs` |-> `[]`] calldata_decode_args_step_exact) >>
     strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!vals. calldata_decode_args cd [tv] ofs = SOME vals <=> _`
       (fn th => simp[NoAsms, th, CONJUNCT1 calldata_decode_args_def])) >>
  `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
    (Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >- simp[] >>
     rename1 `FLOOKUP s.vs_allocas st.cs_next_id = SOME data` >>
     qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==> _`
       (qspecl_then [`st.cs_next_id`,`data`] mp_tac) >>
     qpat_assum `FLOOKUP s.vs_allocas st.cs_next_id = SOME data`
       (fn th => simp[NoAsms, th, prim_recTheory.LESS_REFL])) >>
  Cases_on `p < 4`
  >- suspend "wrap"
  >> suspend "pass"
QED

Resume none_registration_singleton_paths[wrap]:
  `tv_abi_dynamic tv /\ (4+delta) MOD dimword (:256) < 4` by
    (Cases_on `tv_abi_dynamic tv` >> fs[Abbr `p`]) >>
  disj1_tac >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  `0 <= s.vs_alloca_next` by simp[] >>
  `compile_register_positional_args ce
     [(name,F,T,abi_embedded_static_size ce.ce_struct_fields ty,
       type_to_abi_dec_info ce.ce_struct_fields ce ty)] (4+ofs) st = (ce1,last)` by
    (qpat_x_assum `compile_register_positional_args ce _ _ st = _` mp_tac >>
     qpat_assum `tv_abi_dynamic tv` (fn th => simp[NoAsms, th])) >>
  drule_all (Q.INST [`lo` |-> `0`] none_registration_singleton_wrap) >>
  disch_then (qspecl_then [`tn`,`[]`,`G`] ACCEPT_TAC)
QED

Resume none_registration_singleton_paths[pass]:
  `4 <= p` by decide_tac >>
  `allocas_from 0 s` by simp[allocas_from_def] >>
  `(tv_abi_dynamic tv ==> abi_decode_load CALLDATALOAD (n2w (4+ofs):bytes32) s = n2w delta /\
      4+delta < dimword (:256)) /\
    p = 4 + (if tv_abi_dynamic tv then delta else ofs)` by
    (qpat_x_assum `4 <= p ==> _` drule >> simp[]) >>
  drule_all entryPtrSeamRegisterTheory.registration_aggregate_phases >> strip_tac >>
  `cs_extends st a /\ cs_extends a mid /\ cs_extends first last` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends, cs_appends_abi_member_pointer,
      cs_appends_def, cs_extends_abi_decode] >>
  `cs_extends mid first /\ mid.cs_next_id <= first.cs_next_id` by
    (qpat_x_assum `if tv_abi_dynamic tv then _ else _` mp_tac >>
     Cases_on `tv_abi_dynamic tv`
     >- (qpat_assum `tv_abi_dynamic tv` (fn th => simp[NoAsms, th]) >>
         strip_tac >> conj_tac
         >- metis_tac[registration_ptr_guard_extends] >>
         drule registration_ptr_guard_code >> simp[NoAsms]) >>
     qpat_assum `~tv_abi_dynamic tv` (fn th => simp[NoAsms, th]) >>
     disch_then SUBST1_TAC >> simp[NoAsms, cs_extends_refl]) >>
  `cs_extends a first` by metis_tac[cs_extends_trans] >>
  `fn_has_code st a fn /\ fn_has_code a first fn /\ fn_has_code first last fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?d. entry = (d,type_memory_size tv) /\ d+type_memory_size tv < dimword (:256)` by
    (qpat_assum `FLOOKUP s.vs_allocas st.cs_next_id = NONE` (fn th => simp[NoAsms, th])) >>
  `0 <= s.vs_alloca_next` by simp[] >>
  drule_all (Q.INST [`lo` |-> `0`] entryPtrSeamRegisterTheory.registration_argument_prepare_guarded_joint) >>
  disch_then (qspecl_then [`tn`,`[]`,`G`] strip_assume_tac) >>
  rename1 `lookup_var q t = SOME (n2w d)` >>
  drule_all entryPtrSeamRegisterTheory.registration_preparation_forward_slots >> strip_tac >>
  `st.cs_next_id < first.cs_next_id` by
    (`st.cs_next_id < mid.cs_next_id` by
       (qpat_assum `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> _` irule >>
        qexists_tac `(d,type_memory_size tv)` >> first_assum ACCEPT_TAC) >> decide_tac) >>
  `!id. first.cs_next_id <= id ==> FLOOKUP t.vs_allocas id = NONE` by
    (rpt strip_tac >> qpat_assum `!id. mid.cs_next_id <= id ==> _` irule >> decide_tac) >>
  `first.cs_next_id <= last.cs_next_id` by
    (drule abiDecoderCodeTheory.abi_decoder_to_buf_code >>
     simp[NoAsms, abiDecoderContractTheory.abi_decode_source_opcode_def,
       abiDecoderCodeTheory.abi_decoder_code_def]) >>
  `fresh_vars_wrt last t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `first` >>
     drule abi_decoder_variable_counter >> strip_tac >>
     conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  `p < dimword (:256)` by
    (qpat_assum `p = 4 + _` SUBST1_TAC >>
     Cases_on `tv_abi_dynamic tv`
     >- (qpat_assum `tv_abi_dynamic tv ==> _` drule >> strip_tac >>
         qpat_assum `tv_abi_dynamic tv` (fn th => simp[NoAsms, th]) >> decide_tac) >>
     qpat_assum `~tv_abi_dynamic tv` (fn th => simp[NoAsms, th]) >> decide_tac) >>
  `eval_operand src t = SOME (n2w p)` by metis_tac[] >>
  `eval_operand (Var q) t = SOME (n2w d)` by
    (rewrite_tac[venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `compile_abi_decode_to_buf (Var q) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last)` by metis_tac[] >>
  qpat_x_assum `!first t src q p d oid H u. _` (drule_all_then strip_assume_tac)
  >- suspend "child_abort"
  >> suspend "child_ok"
QED

Resume none_registration_singleton_paths[child_abort]:
  rename1 `!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (t,H,u) [] (Abort Revert_abort z,Hout,w)` >>
  disj1_tac >> qexistsl [`z`,`Hout`,`w`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl [`H`,`t`,`u`] >>
  metis_tac[]
QED

Resume none_registration_singleton_paths[child_ok]:
  rename1 `!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (t,H,u) [] (OK v,Hout,w)` >>
  `IS_SOME (cd_decode F cd tv p)` by
    (`w2n (n2w p : bytes32) = p` by
       (rewrite_tac[w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  `IS_SOME (calldata_decode_args cd [tv] ofs)` by
    (qpat_assum `IS_SOME (cd_decode F cd tv p)`
       (qx_choose_then `x` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
     rewrite_tac[optionTheory.IS_SOME_EXISTS] >> qexists_tac `[x]` >>
     qpat_assum `!vals. calldata_decode_args cd [tv] ofs = SOME vals <=> _`
       (fn th => rewrite_tac[th]) >>
     qexists_tac `x` >> asm_rewrite_tac[]) >>
  `!id entry. FLOOKUP v.vs_allocas id = SOME entry ==> id < last.cs_next_id` by
    (rpt strip_tac >> CCONTR_TAC >>
     `last.cs_next_id <= id /\ first.cs_next_id <= id` by decide_tac >>
     qpat_assum `!id. last.cs_next_id <= id ==> _` (drule_then assume_tac) >>
     qpat_assum `!id. first.cs_next_id <= id ==> _` (drule_then assume_tac) >>
     qpat_assum `FLOOKUP v.vs_allocas id = SOME entry` mp_tac >>
     qpat_assum `FLOOKUP v.vs_allocas id = FLOOKUP t.vs_allocas id` mp_tac >>
     qpat_assum `FLOOKUP t.vs_allocas id = NONE` (fn th => simp[NoAsms, th])) >>
  disj2_tac >> qexistsl [`v`,`Hout`,`w`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- metis_tac[] >>
  rpt gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl [`H`,`t`,`u`] >> metis_tac[]
QED

Finalise none_registration_singleton_paths
