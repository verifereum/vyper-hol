Theory calldataNoneRegisterOne
Ancestors defaultBytesRegistrationPrelude defaultBytesAddressPrelude
  registrationGuardRejectOrigin ctorDeployMemoryRunPtrPrefixRegisterAddress
  fragGasOriginPtr loweringShapeDefs loweringStateRelDefs fragExec
  emitHelperProps context compileEnv abiEncoder abiDecoderContract words arithmetic
  venomState venomExecSemantics ptrDiscipline finite_map ASCIInumbers
  entryPtrSeamRegister calldataRegistrationRawAddress calldataRegistration
  calldataSourceCorrespondence calldataRegistrationExec abiDecoderAppend
  loweringHalt

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
  irule registration_wrapped_prefix_origin >> simp[] >>
  qexistsl [`b`,`c`,`a`,`buf`,`cap`,`first`,`head`,`g`,`4+ofs`,`delta'`,`src`,`st`] >>
  simp[]
QED
