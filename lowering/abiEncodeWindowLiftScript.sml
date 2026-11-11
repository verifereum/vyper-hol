(* Composition of the live-window ABI builtin phases. *)
Theory abiEncodeWindowLift
Ancestors
  abiEncodeWindowMemory abiBuiltinEncodeCode abiBuiltinEncodeContext
  abiEncoderWindowRunMem windowPhaseMem abiEncoderWindowPhase
  abiEncoderWindowChild abiEncoderAddressReach abiEncoderWindowContract
  abiEncoderRegisteredEffect emitHelperProps exprLoweringProps compileEnv
  emitHelper fragExec memContinuation venomState venomExecSemantics freshWrites
  venomInst words list rich_list arithmetic pred_set finite_map
  abiEncodeAllocationPhase loweringHalt abiBuiltinAllocation pair

Theorem abi_encode_method_id_shape[local]:
  abi_builtin_encode_method_id mid buf st = ((),en) ==>
  cs_extends st en /\ st.cs_next_var <= en.cs_next_var
Proof
  Cases_on `mid` >>
  simp[abi_builtin_encode_method_id_def, comp_return_def, comp_bind_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[cs_extends_def, emitted_insts_def, IS_PREFIX_APPEND, is_terminator_def, mk_inst_def,
    GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]
QED

Theorem abi_encode_address_prefix_mem[local]:
  emit_op ADD [buf;Lit (n2w (32 + (case mid of NONE => 0 | SOME _ => 4)))] st = (data,en) /\
  abi_builtin_encode_method_id mid buf en = ((),ready) /\
  fn_has_code st ready func /\ eval_operand buf s = SOME (n2w p) /\
  (!x. buf = Var x ==> not_fresh_at st x) /\
  p+32 < dimword (:256) /\ (IS_SOME mid ==> p+64 <= s.vs_alloca_next) /\
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. window_phase ctx func st ready {} (case mid of NONE => [] | SOME _ => [(p+32,32)]) s t /\
    mem_cont_sim ctx func s t /\ eval_operand buf t = SOME (n2w p) /\
    eval_operand data t = SOME (n2w (p+32+(case mid of NONE => 0 | SOME _ => 4)))
Proof
  strip_tac >>
  `fn_has_code st en func /\ fn_has_code en ready func /\
   st.cs_next_var <= en.cs_next_var /\ en.cs_next_var <= ready.cs_next_var` by
    (drule abi_encoder_emit_address_shape >> strip_tac >>
     drule window_child_emit_counter >> strip_tac >>
     drule abi_encode_method_id_shape >> strip_tac >>
     drule_all fn_has_code_split >> simp[]) >>
  `eval_operand (Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))) s =
    SOME (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))` by simp[eval_operand_def] >>
  drule_all window_emit_add_phase_mem >> strip_tac >>
  rename1 `window_phase ctx func st en {} [] s addressed` >>
  `eval_operand buf addressed = SOME (n2w p)` by metis_tac[window_phase_operand] >>
  `(!x. buf = Var x ==> not_fresh_at en x)` by metis_tac[not_fresh_at_mono] >>
  `alloca_inv addressed /\ alloca_room ctx func addressed /\
   ~addressed.vs_halted /\ addressed.vs_current_bb = en.cs_current_bb /\
   addressed.vs_inst_idx = LENGTH en.cs_current_insts /\
   (IS_SOME mid ==> p+64 <= addressed.vs_alloca_next)` by
    (fs[window_phase_def, window_alloca_growth_def] >> strip_tac >>
     `p+64 <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  drule_all abi_encode_method_id_window_mem >> strip_tac >>
  qexists_tac `t` >> conj_tac
  >- (irule window_phase_chain >> qexistsl_tac [`{}`, `[]`, `en`, `{}`,
       `case mid of NONE => [] | SOME _ => [(p+32,32)]`, `addressed`] >> simp[]) >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `eval_operand data t = SOME (n2w p + n2w (32+(case mid of NONE => 0 | SOME _ => 4)))` by
    metis_tac[window_phase_operand] >>
  metis_tac[word_add_n2w, ADD_ASSOC]
QED

Theorem abi_encode_setup_parts[local]:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  compile_alloc_buffer (32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4))) st = (buf,allocated) /\
  emit_op ADD [buf.buf_operand;Lit (n2w (32+(case mid of NONE => 0 | SOME _ => 4)))] allocated = (data,addressed) /\
  abi_builtin_encode_method_id mid buf.buf_operand addressed = ((),ready) /\
  fn_has_code st ready func ==>
  fn_has_code st allocated func /\ fn_has_code allocated ready func /\
  st.cs_next_var <= allocated.cs_next_var
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule abi_encode_method_id_shape >> strip_tac >>
  `cs_extends allocated ready` by metis_tac[cs_extends_trans] >>
  `cs_extends st allocated` by
    (irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> simp[]
QED

Theorem abi_encode_setup_window_mem:
  abi_builtin_encode_setup mid maxlen st = (ops,ready) /\
  fn_has_code st ready func /\ alloca_room ctx func s /\ alloca_inv s /\
  32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) < dimword (:256) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==>
    sz = 32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4))) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t p. window_phase ctx func st ready {st.cs_next_id}
      (case mid of NONE => [] | SOME _ => [(p+32,32)]) s t /\
    mem_cont_sim ctx func s t /\
    eval_operand (FST ops) t = SOME (n2w p) /\
    eval_operand (SND ops) t = SOME (n2w (p+32+(case mid of NONE => 0 | SOME _ => 4))) /\
    FLOOKUP t.vs_allocas st.cs_next_id =
      SOME (p,32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4))) /\
    p+32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) <= t.vs_alloca_next /\
    p+32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4)) < dimword (:256) /\
    ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
     FLOOKUP s.vs_allocas st.cs_next_id =
       SOME (p,32+32*word_size (maxlen+(case mid of NONE => 0 | SOME _ => 4))))
Proof
  strip_tac >> drule abi_builtin_encode_setup_trace >> strip_tac >>
  drule_all abi_encode_setup_parts >> strip_tac >>
  drule_all abi_encode_alloc_window_phase >>
  disch_then (qx_choose_then `allocated_s` (qx_choose_then `p`
    (map_every assume_tac o CONJUNCTS))) >>
  rename1 `window_phase ctx func st allocated {st.cs_next_id} [] s allocated_s` >>
  rename1 `eval_operand buf.buf_operand allocated_s = SOME (n2w p)` >>
  `p+32 < dimword (:256)` by decide_tac >>
  `(IS_SOME mid ==> p+64 <= allocated_s.vs_alloca_next)` by
    (qpat_x_assum `p + (32 + _) <= _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     mp_tac abi_builtin_rounded_selector_store >>
     Cases_on `mid` >> simp[] >> decide_tac) >>
  `alloca_inv allocated_s /\ alloca_room ctx func allocated_s /\
   ~allocated_s.vs_halted /\ allocated_s.vs_current_bb = allocated.cs_current_bb /\
   allocated_s.vs_inst_idx = LENGTH allocated.cs_current_insts` by
    metis_tac[window_phase_resources, window_phase_control] >>
  drule_all abi_encode_address_prefix_mem >> strip_tac >>
  qexistsl_tac [`t`, `p`] >> conj_tac
  >- (irule window_phase_chain >> qexistsl_tac [`{st.cs_next_id}`, `[]`, `allocated`,
       `{}`, `case mid of NONE => [] | SOME _ => [(p+32,32)]`, `allocated_s`] >> simp[]) >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  conj_tac >- metis_tac[FST] >>
  conj_tac >- metis_tac[SND] >>
  conj_tac >- metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  `allocated_s.vs_alloca_next <= t.vs_alloca_next` by
    metis_tac[window_phase_resources, window_alloca_growth_def] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_setup_source[local]:
  window_phase ctx func st en {st.cs_next_id}
    (case mid of NONE => [] | SOME _ => [(p+32,32)]) s t /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n) /\
  venomMemDefs$regions_disjoint (sb,cap) (p,n) /\
  (IS_SOME mid ==> 64 <= n) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  strip_tac >> irule abi_encoder_window_effect_source >>
  qexistsl_tac [`{st.cs_next_id}`,
    `case mid of NONE => [] | SOME _ => [(p+32,32)]`, `s`] >>
  conj_tac >- simp[window_phase_effect] >> conj_tac
  >- (Cases_on `mid` >> simp[] >>
      fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[window_phase_effect]
QED
