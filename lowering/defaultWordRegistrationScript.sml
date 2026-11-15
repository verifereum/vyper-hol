(* Staged exact primitive-word registration, retaining the modular address. *)
Theory defaultWordRegistration
Ancestors defaultWordRegistrationPrelude defaultWordDecodeExec defaultWordDecodeGhost
  fragExecMem fragGasOriginPtrLoop abiDecoderContract abiDecoderCoherence
  moduleLowering compileEnv words finite_map pred_set abiEncoderWindowLookup
  abiDecoderClampedWord abiDecoderClamp emitHelper emitHelperProps list rich_list
  abiEncoder exprLoweringProps loweringStateRelDefs venomInst

Theorem default_word_decode_output_bounds[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
    EVERY (not_fresh_at sb) i.inst_outputs) (emitted_insts sa sb)
Proof
  Cases_on `clamp` >>
  FIRST [rename1 `IntClamp bits signed` >> Cases_on `signed`, all_tac] >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def, emitted_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[ASCIInumbersTheory.toString_11]
QED

Theorem default_word_registration_step_footprint:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (src,first) /\
  compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),decoded) /\
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n ((n2w 4 + n2w (off-4)):bytes32)) = SOME x /\
  fn_has_code st first fn /\ fn_has_code first decoded fn /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  fn_inst_ids_distinct fn /\ k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?out H u p.
    buf.buf_operand = Var p /\
    eval_operand (Var p) out = SOME (n2w s.vs_alloca_next) /\
    ptr_covers H u p out 32 /\
    val_in_memory tv x s.vs_alloca_next out.vs_memory /\
    value_has_type tv x /\ val_wf tv x /\
    abi_decode_frame s.vs_alloca_next 32 s out /\
    FLOOKUP out.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,32) /\
    out.vs_alloca_next = s.vs_alloca_next + 32 /\
    s.vs_alloca_next + 32 < dimword (:256) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP out.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
       eval_operand op out = eval_operand op s) /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
       op_taint u (Var v) = op_taint tn (Var v)) /\
    (!i. s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32 ==> i NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    alloca_inv out /\ alloca_frontier_inv_from k ctx fn site out /\
    allocas_from lo out /\ lo <= out.vs_alloca_next /\ alloca_history fn out /\
    ~out.vs_halted /\ out.vs_current_bb = decoded.cs_current_bb /\
    out.vs_inst_idx = LENGTH decoded.cs_current_insts /\
    out = (s with <|vs_vars := out.vs_vars; vs_memory := out.vs_memory;
      vs_allocas := out.vs_allocas; vs_alloca_next := out.vs_alloca_next;
      vs_inst_idx := LENGTH decoded.cs_current_insts|>) /\
    gas_path_mem ctx fn s 0 (OK out) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK out,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u out) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    (!v. v IN FDOM out.vs_vars ==>
      v IN FDOM s.vs_vars \/ not_fresh_at decoded v)
Proof
  strip_tac >>
  drule_all default_word_registration_prelude_footprint >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  `ready.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `ready = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),decoded)` by metis_tac[] >>
  `cd_decode F ready.vs_call_ctx.cc_calldata tv
    (w2n ((4w + n2w (off-4)):bytes32)) = SOME x` by metis_tac[] >>
  `s.vs_alloca_next + 32 <= ready.vs_alloca_next` by simp[] >>
  drule_all default_word_decode_exact_sequence >> strip_tac >>
  `compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecPrimWord clamp) first = ((),decoded)` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     i.inst_opcode <> GAS) (emitted_insts first decoded)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all default_word_decode_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qabbrev_tac `out = t with vs_inst_idx := LENGTH decoded.cs_current_insts` >>
  `first.cs_next_var <= decoded.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\
      EVERY (not_fresh_at decoded) i.inst_outputs) (emitted_insts first decoded)` by
    metis_tac[default_word_decode_output_bounds] >>
  `!v. ~not_fresh_at decoded v ==> lookup_var v t = lookup_var v ready` by
    (drule abi_window_seq_high_vars >>
     disch_then (qspec_then `decoded` mp_tac) >> simp[]) >>
  `!v. ~not_fresh_at decoded v ==> lookup_var v t = lookup_var v s` by
    metis_tac[abi_window_high_vars_trans] >>
  `!v. v IN FDOM out.vs_vars ==>
     v IN FDOM s.vs_vars \/ not_fresh_at decoded v` by
    (rpt strip_tac >> spose_not_then strip_assume_tac >>
     qpat_x_assum `!v. ~not_fresh_at decoded v ==> lookup_var v t = lookup_var v s`
       (qspec_then `v` mp_tac) >>
     simp[venomStateTheory.lookup_var_def, FLOOKUP_DEF] >>
     fs[Abbr `out`] >>
     metis_tac[venomStateTheory.lookup_var_def, FLOOKUP_DEF, optionTheory.NOT_SOME_NONE]) >>
  qexistsl [`out`,`H'`,`u'`,`p`] >>
  simp[Abbr `out`] >>
  conj_tac >- suspend "memory_frame" >>
  conj_tac >- suspend "operands" >>
  conj_tac >- suspend "old_ghost" >>
  conj_tac >- suspend "taints" >>
  suspend "execution_frame"
QED

Resume default_word_registration_step_footprint[memory_frame]:
  qpat_x_assum `abi_decode_frame _ _ ready t` mp_tac >>
  simp[abi_decode_frame_def] >>
  qpat_x_assum `ready = _` (fn th => once_rewrite_tac [th]) >> simp[] >>
  metis_tac[]
QED

Resume default_word_registration_step_footprint[operands]:
  rpt strip_tac >>
  `abi_decoder_operand_live first.cs_next_var op` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists `st.cs_next_var` >> simp[]) >>
  metis_tac[]
QED

Resume default_word_registration_step_footprint[old_ghost]:
  rpt strip_tac >>
  `not_fresh_at first v` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED

Resume default_word_registration_step_footprint[taints]:
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  gvs[w2n_n2w] >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Resume default_word_registration_step_footprint[execution_frame]:
  `t.vs_current_bb = ready.vs_current_bb /\ t.vs_halted = ready.vs_halted` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
      (emitted_insts first decoded)` by
    (`abi_decode_source_opcode CALLDATALOAD` by
       simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
     drule_all abiDecoderWordOutcomeTheory.abi_decoder_word_opcodes >>
     simp[listTheory.EVERY_MEM, abiDecoderWordOutcomeTheory.abi_word_opcode_def] >>
     strip_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
  drule_all ctorDeployMemoryRunMemEntryCompositeSetupTheory.ctor_checked_emitted_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- suspend "alloca_inv" >>
  conj_tac >- suspend "frontier" >>
  conj_tac >- suspend "allocas_from" >>
  simp[] >>
  conj_tac >- suspend "record_frame" >>
  conj_tac >- (metis_tac[fragGasPathMemTheory.gas_path_mem_then, arithmeticTheory.ADD]) >>
  rpt gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspecl_then [`D`,`explicit`] mp_tac) >>
  disch_then (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[NoAsms] >> metis_tac[]
QED

Resume default_word_registration_step_footprint[alloca_inv]:
  irule localPtrsPropsTheory.alloca_inv_fields >> qexists `ready` >> simp[]
QED

Resume default_word_registration_step_footprint[frontier]:
  irule ctorDeployMemoryRunMemEntryShiftedFrameTheory.alloca_frontier_inv_from_frame >>
  qexistsl [`ready`,`site`] >> simp[]
QED

Resume default_word_registration_step_footprint[allocas_from]:
  gvs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]
QED

Resume default_word_registration_step_footprint[record_frame]:
  qpat_x_assum `t = _` (fn th => once_rewrite_tac [th]) >>
  qpat_x_assum `ready = _` (fn th => once_rewrite_tac [th]) >> simp[]
QED

Finalise default_word_registration_step_footprint

(* Preserve the legacy contract and its inferred polymorphism exactly. *)
Theorem default_word_registration_step:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (src,first) /\
  compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) first = ((),decoded) /\
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n ((n2w 4 + n2w (off-4)):bytes32)) = SOME x /\
  fn_has_code st first fn /\ fn_has_code first decoded fn /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  fn_inst_ids_distinct fn /\ k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?out H u p.
    buf.buf_operand = Var p /\
    eval_operand (Var p) out = SOME (n2w s.vs_alloca_next) /\
    ptr_covers H u p out 32 /\
    val_in_memory tv x s.vs_alloca_next out.vs_memory /\
    value_has_type tv x /\ val_wf tv x /\
    abi_decode_frame s.vs_alloca_next 32 s out /\
    FLOOKUP out.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,32) /\
    out.vs_alloca_next = s.vs_alloca_next + 32 /\
    s.vs_alloca_next + 32 < dimword (:256) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP out.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
       eval_operand op out = eval_operand op s) /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
       op_taint u (Var v) = op_taint tn (Var v)) /\
    (!i. s.vs_alloca_next <= i /\ i < s.vs_alloca_next+32 ==> i NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    alloca_inv out /\ alloca_frontier_inv_from k ctx fn site out /\
    allocas_from lo out /\ lo <= out.vs_alloca_next /\ alloca_history fn out /\
    ~out.vs_halted /\ out.vs_current_bb = decoded.cs_current_bb /\
    out.vs_inst_idx = LENGTH decoded.cs_current_insts /\
    out = (s with <|vs_vars := out.vs_vars; vs_memory := out.vs_memory;
      vs_allocas := out.vs_allocas; vs_alloca_next := out.vs_alloca_next;
      vs_inst_idx := LENGTH decoded.cs_current_insts|>) /\
    gas_path_mem ctx fn s 0 (OK out) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (OK out,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u out) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> drule_all default_word_registration_step_footprint >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  qexistsl [`out`,`H`,`u`,`p`] >> simp[]
QED
