(* Actual guarded dynamic positional-registration compilation boundary. *)
Theory defaultBytesRegistrationPrelude
Ancestors calldataRegistrationExec moduleLowering compileEnv emitHelper finite_map
  ctorDeployMemoryRunPtrPrefixRegisterAlloc ctorDeployMemoryRunPtrPrefixRegisterAddress
  fragGasOriginPtr ptrSafeRun ptrDiscipline venomState venomExecSemantics venomInst
  codegenRel contextCodegenRel unitTransformDefs words list arithmetic
  exprLoweringProps fragExec context
  ctorDeployLoweringEntryRegisterRun ctorDeployMemoryRunMemEntryRegistration
  abiDecoderReentry freshWrites bodyPtrDefs localPtrsProps allocaFrontierBound
  entryDispatchPtr abiDecoderGuard emitHelperProps defaultBytesAddressPrelude
  defaultBytesGuardPrelude loweringShapeDefs loweringStateRelDefs loweringHalt

Theorem default_bytes_registration_split:
  compile_register_positional_args ce
    ((name,F,T,sz,DecBytestring maxn)::rest) off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME cap ==>
  ?buf allocated ce1 head after_head offset after_load src after_src first decoded.
    compile_alloc_buffer cap st = (buf,allocated) /\
    ce1 = (ce with ce_vars := ce.ce_vars |+ (name,PtrVar buf.buf_operand cap)) /\
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
    emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
    emit_op ADD [Lit (n2w 4);offset] after_load = (src,after_src) /\
    compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) after_src = ((),first) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w)
      (DecBytestring maxn) first = ((),decoded) /\
    compile_register_positional_args ce1 rest (off+sz) decoded = (cef,final)
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[Once compile_register_positional_args_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `_0` >>
  `var_location_decode_operand (PtrVar buf.buf_operand cap) =
     SOME buf.buf_operand` by simp[var_location_decode_operand_def] >>
  drule registration_decoder_prelude >>
  simp[FLOOKUP_UPDATE] >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`head`, `after_head`, `offset`, `after_load`, `src`, `after_src`, `first`, `cs''`] >> gvs[] >>
  `ce with ce_vars := ce.ce_vars |+ (name,PtrVar buf.buf_operand cap) =
   ce with ce_vars updated_by (\m. m |+ (name,PtrVar buf.buf_operand cap))` by
    simp[compile_env_component_equality] >>
  pop_assum SUBST1_TAC >> simp[]
QED

(* Capacity-polymorphic allocation origin, without a source-state invariant. *)
Theorem default_bytes_alloc_origin:
  compile_alloc_buffer cap st = (buf,allocated) /\
  fn_has_code st allocated fn /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ cap < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let p = STRING #"%" (toString st.cs_next_var);
      a = (update_var p (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (st.cs_next_id,(s.vs_alloca_next,cap));
          vs_alloca_next := s.vs_alloca_next+cap|>))
        with vs_inst_idx := LENGTH allocated.cs_current_insts;
      H = G |+ (p,(s.vs_alloca_next,cap));
      u = tn with <|t_var := tn.t_var |+ (p,{});
        t_mem := tn.t_mem UNION
          {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+cap}|>
  in !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK a,H,u)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >> rpt gen_tac >>
  `emit_op ALLOCA [Lit (n2w cap)] st = (buf.buf_operand,allocated)` by
    (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  irule prefix_register_address_emit_origin >> simp[] >>
  qexistsl_tac [`ALLOCA`,`[Lit (n2w cap)]`,`buf.buf_operand`,`st`] >>
  drule_all prefix_register_alloc_pair >>
  disch_then (qspecl_then [`STRING #"%" (toString st.cs_next_var)`,
    `tn`,`0`,`fn`,`PG`,`G`,`D`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  simp[run_inst_seq_def, mk_inst_def, is_terminator_def,
    inst_mem_below_frontier_def, source_memory_read_ranges_def,
    source_memory_write_ranges_def]
QED

(* The guard executes even in the presence of unrelated pre-existing variables. *)
Theorem default_bytes_guard_sequence:
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) sa = ((),sb) /\
  eval_operand src s = SOME w /\ 4 <= w2n w ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (update_var ("%" ++ toString (sa.cs_next_var + 1)) 1w
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
Proof
  strip_tac >>
  qabbrev_tac `v0 = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `v1 = "%" ++ toString (sa.cs_next_var + 1)` >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id LT [src; Lit 4w] [v0];
     mk_inst (sa.cs_next_id + 1) ISZERO [Var v0] [v1];
     mk_inst (sa.cs_next_id + 2) ASSERT [Var v1] []]` by
    (qpat_x_assum `compile_abi_arg_ptr_guard _ _ _ _ = _` mp_tac >>
     simp[compile_abi_arg_ptr_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[emitted_insts_def, APPEND_ASSOC, DROP_PREFIX,
       Abbr `v0`, Abbr `v1`]) >>
  `step_inst_base (mk_inst sa.cs_next_id LT [src;Lit 4w] [v0]) s =
    OK (update_var v0 0w s)` by
    (qspecl_then [`src`,`Lit 4w`,`w`,`4w`] mp_tac step_LT >>
     simp[eval_operand_def, bool_to_word_def, dimword_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+1) ISZERO [Var v0] [v1])
    (update_var v0 0w s) = OK (update_var v1 1w (update_var v0 0w s))` by
    (qspecl_then [`Var v0`,`0w`] mp_tac step_ISZERO >>
     simp[eval_operand_def, lookup_var_update_var, bool_to_word_def]) >>
  `step_inst_base (mk_inst (sa.cs_next_id+2) ASSERT [Var v1] [])
    (update_var v1 1w (update_var v0 0w s)) =
    OK (update_var v1 1w (update_var v0 0w s))` by
    (irule step_ASSERT_ok >> qexists `1w` >>
     simp[eval_operand_def, lookup_var_update_var]) >>
  gvs[Abbr `v0`, Abbr `v1`] >> simp[run_inst_seq_def]
QED

Theorem default_bytes_registration_prelude:
  compile_alloc_buffer cap st = (buf,allocated) /\
  emit_op ADD [Lit 4w; Lit (n2w (off-4))] allocated = (head,after_head) /\
  emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
  emit_op ADD [Lit 4w;offset] after_load = (src,after_src) /\
  compile_abi_arg_ptr_guard CALLDATALOAD src (Lit 4w) after_src = ((),first) /\
  0 < cap /\ cap < dimword (:256) /\ fn_has_code st first fn /\
  4 <= w2n ((4w + abi_decode_load CALLDATALOAD ((4w+n2w(off-4)):bytes32) s):bytes32) /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  fn_inst_ids_distinct fn /\ k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready H u p.
    buf.buf_operand = Var p /\
    eval_operand (Var p) ready = SOME (n2w s.vs_alloca_next) /\
    eval_operand src ready = SOME ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32) /\
    abi_decoder_operand_live first.cs_next_var (Var p) /\
    abi_decoder_operand_live first.cs_next_var src /\
    not_fresh_at first p /\ (!v. src = Var v ==> not_fresh_at first v) /\
    ptr_covers H u p ready cap /\ op_taint u src = {} /\ op_prov H src = NONE /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,cap) /\
    ready.vs_alloca_next = s.vs_alloca_next+cap /\
    s.vs_alloca_next+cap < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv_from k ctx fn site ready /\
    allocas_from lo ready /\ lo <= ready.vs_alloca_next /\ alloca_history fn ready /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts /\
    ready = (s with <|vs_vars := ready.vs_vars; vs_allocas := ready.vs_allocas;
      vs_alloca_next := ready.vs_alloca_next;
      vs_inst_idx := LENGTH first.cs_current_insts|>) /\
    st.cs_next_id < first.cs_next_id /\ st.cs_next_var <= first.cs_next_var /\
    (!id. id <> st.cs_next_id ==> FLOOKUP ready.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op s) /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    u.t_mem = tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+cap} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    gas_path_mem ctx fn s 0 (OK ready) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK ready,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u ready) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule default_bytes_guard_shape >> strip_tac >>
  `cs_extends after_src first` by
    (fs[same_blocks_def, inst_extends_def] >>
     simp[cs_extends_def] >> qexists `[]` >> simp[]) >>
  `cs_extends st after_src` by
    (drule compile_alloc_buffer_extends >> strip_tac >>
     qpat_assum `emit_op ADD _ allocated = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     qpat_assum `emit_op CALLDATALOAD _ after_head = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     qpat_assum `emit_op ADD _ after_load = _`
       (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
     metis_tac[cs_extends_trans]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all default_bytes_address_prelude >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] (qx_choose_then `a`
    (qx_choose_then `H0` (qx_choose_then `u0` (qx_choose_then `p` strip_assume_tac))))) >>
  drule_all default_bytes_guard_prelude >>
  disch_then (qspec_then `PG` (qx_choose_then `ready` (qx_choose_then `H`
    (qx_choose_then `u` strip_assume_tac)))) >>
  qexistsl [`ready`,`H`,`u`,`p`] >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- suspend "pullback" >>
  reverse conj_tac >- suspend "origin" >>
  reverse conj_tac >- suspend "memory" >>
  suspend "fields"
QED
Resume default_bytes_registration_prelude[pullback]:
  metis_tac[]
QED
Resume default_bytes_registration_prelude[origin]:
  rpt gen_tac >>
  metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, APPEND]
QED
Resume default_bytes_registration_prelude[memory]:
  metis_tac[fragGasPathMemTheory.gas_path_mem_then, ADD]
QED
Resume default_bytes_registration_prelude[fields]:
  `ready.vs_allocas = a.vs_allocas /\ ready.vs_alloca_next = a.vs_alloca_next` by
    (qpat_assum `ready = a with <|vs_vars := _; vs_inst_idx := _|>`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qpat_x_assum `ready = _ with vs_inst_idx := _` kall_tac >>
  pure_rewrite_tac[GSYM CONJ_ASSOC] >> simp[] >>
  conj_tac >- (irule abi_decoder_operand_live_mono >>
    qexists `after_src.cs_next_var` >> simp[]) >>
  conj_tac >- (irule abi_decoder_operand_live_mono >>
    qexists `after_src.cs_next_var` >> simp[]) >>
  conj_tac >- (irule loweringShapeDefsTheory.not_fresh_at_mono >>
    qexists `after_src` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
    qexists `after_src` >> simp[]) >>
  conj_tac >- (
    `eval_operand (Var p) ready = eval_operand (Var p) a` by metis_tac[] >>
    fs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists `a` >> simp[]) >>
  conj_tac >- (irule ctorDeployMemoryRunMemEntryShiftedFrameTheory.alloca_frontier_inv_from_frame >>
    qexistsl [`a`,`site`] >> simp[]) >>
  conj_tac >- gvs[venom_state_component_equality] >>
  conj_tac >- (rpt strip_tac >>
    `abi_decoder_operand_live after_src.cs_next_var op` by
      (irule abi_decoder_operand_live_mono >> qexists `st.cs_next_var` >> simp[]) >>
    metis_tac[]) >>
  `!v. not_fresh_at st v ==> not_fresh_at after_src v` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `st` >> simp[]) >> metis_tac[]
QED
Finalise default_bytes_registration_prelude
