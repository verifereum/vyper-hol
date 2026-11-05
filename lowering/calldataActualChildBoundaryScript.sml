(* Actual decoder child setup: resources and continuation-independent safety. *)
Theory calldataActualChildBoundary
Ancestors
  calldataValidOwnedChild calldataDynOwned calldataDynStep abiDecoderArraySetupInputs decoderPrefixEdges
  abiDecoderValidArrayEntry abiDecoderValidContract abiDecoderContract abiDecoderLoopRegisters
  abiDecoderArrayInvariant abiDecoderArrayBackedge abiDecoderReentry abiDecoderExecution abiDecoderTypedContract
  safeSequence fragExecMem fragExec instIdxIndep rich_list compileEnv emitHelperProps exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Theorem actual_child_sequence_pullback[local]:
  inst_extends st ready /\ fn_has_code st ready fn /\
  ready.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st ready) /\
  run_inst_seq_mem_ok (emitted_insts st ready) s /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((!fuel. mem_safe_run fuel ctx fn
    (t with vs_inst_idx := LENGTH ready.cs_current_insts)) ==>
   !fuel. mem_safe_run fuel ctx fn s)
Proof
  strip_tac >>
  `?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX ready.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `?xs. ready.cs_current_insts = st.cs_current_insts ++ xs /\
    emitted_insts st ready = xs` by
    (fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_LENGTH_APPEND]) >>
  strip_tac >> gen_tac >>
  qspecl_then [`xs`, `s`, `fuel`, `ctx`, `fn`, `bb`] mp_tac mem_safe_run_inst_seq >>
  asm_rewrite_tac[] >>
  (impl_tac >- (fs[IS_PREFIX_APPEND] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[])) >>
  disch_then (irule o CONJUNCT1) >> qexists_tac `t` >> gvs[]
QED

Theorem actual_header_prepare[local]:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d outsz b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    ~head.vs_halted /\ head.vs_current_bb = body_lbl /\ head.vs_inst_idx = 0 /\
    fresh_vars_wrt limit_st head /\
    abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
      d outsz b cap head /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD head) = bs /\
    eval_operand ip head = SOME (n2w p) /\ mload p head = n2w j /\
    head.vs_memory = u.vs_memory /\ head.vs_call_ctx = u.vs_call_ctx /\
    head.vs_data_section = u.vs_data_section /\ head.vs_allocas = u.vs_allocas /\
    head.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op head = eval_operand op u) /\
    ((!fuel. mem_safe_run fuel ctx fn head) ==> !fuel. mem_safe_run fuel ctx fn u) /\
    (!fuel r. run_from fuel ctx fn head = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn head ==> mem_safe_run fuel' ctx fn u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `head = jump_to body_lbl
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j (LENGTH vs) u)` >>
  `src <> Var (STRING #"%" (toString next))` by
    (irule abi_decoder_live_excludes_output >> qexists_tac `next` >> simp[]) >>
  `STRING #"%" (toString next) <> STRING #"%" (toString (next+1))` by simp[] >>
  `mload (w2n (n2w p:bytes32)) u = n2w j /\
    w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by simp[] >>
  `head = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString next))
      (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
      (STRING #"%" (toString (next+3))) j (LENGTH vs) u)` by simp[Abbr `head`] >>
  `j <= LENGTH vs` by decide_tac >>
  `lookup_block (if j < LENGTH vs then body_lbl else exit_lbl) fn.fn_blocks =
    SOME body_bb` by simp[] >>
  `(!fuel. mem_safe_run fuel ctx fn head) ==> !fuel. mem_safe_run fuel ctx fn u` by
    (ho_match_mp_tac (GEN_ALL calldata_header_all_fuel_pullback) >>
     goal_assum (drule_at (Pos hd)) >>
     qexistsl_tac [`srcword`, `n2w p`, `body_bb`, `LENGTH vs`, `j`] >>
     asm_rewrite_tac[]) >>
  drule_all calldata_header_owned_safe_transfer >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  qpat_x_assum `head = jump_to _ _` kall_tac >>
  drule_all abi_decoder_header_registers >> strip_tac >>
  `fresh_vars_wrt limit_st head /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op head = eval_operand op u)` by
    simp[Abbr `head`] >>
  `~head.vs_halted /\ head.vs_current_bb = body_lbl /\ head.vs_inst_idx = 0` by
    simp[Abbr `head`, jump_to_def, abi_decode_header_state_def, update_var_def] >>
  qexists_tac `head` >> conj_tac >- simp[Abbr `head`] >>
  asm_rewrite_tac[] >> suspend "source_fields"
QED

Resume actual_header_prepare[source_fields]:
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ u` mp_tac >>
  qpat_assum `mem_bytes_at _ _ (abi_decode_source _ u) = _` mp_tac >>
  qpat_assum `!op. abi_decoder_operand_live next op ==> eval_operand op head = _` mp_tac >>
  qpat_assum `abi_decoder_operand_live next src` mp_tac >>
  qpat_assum `abi_decoder_operand_live next dst` mp_tac >>
  qpat_assum `head.vs_call_ctx = u.vs_call_ctx` mp_tac >>
  qpat_assum `head.vs_data_section = u.vs_data_section` mp_tac >>
  qpat_assum `abi_decoder_operand_live next ip` mp_tac >>
  qpat_assum `head.vs_memory = u.vs_memory` mp_tac >>
  qpat_assum `eval_operand ip u = SOME (n2w p)` mp_tac >>
  qpat_assum `mload p u = n2w j` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  fs[abi_decoder_ranges_def, abi_decode_source_def, mload_def]
QED
Finalise actual_header_prepare

Theorem actual_setup_reach[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st = (ops,ready) /\ fn_has_code st ready fn /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\ j < LENGTH vs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  eval_operand ip initial = SOME (n2w slot) /\ mload slot initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  slot < dimword (:256) /\ slot+32 <= initial.vs_alloca_next /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?entry.
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st.cs_next_var limit_st initial entry /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op entry = eval_operand op initial) /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ((!fuel. mem_safe_run fuel ctx fn entry) ==> !fuel. mem_safe_run fuel ctx fn initial) /\
    (!fuel r. run_from fuel ctx fn entry = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn entry ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mload (w2n (n2w slot:bytes32)) initial = n2w j` by simp[] >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by simp[abi_decoder_operand_live_def] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all abi_decoder_valid_array_setup_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  `eval_operand src initial = SOME (n2w sb) /\
   eval_operand dst initial = SOME (n2w d)` by fs[abi_decoder_ranges_def] >>
  drule_all calldata_element_setup_repeat >> strip_tac >> gvs[] >>
  `run_inst_seq_mem_ok (emitted_insts st ready) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >> reverse conj_tac
     >- (drule calldata_element_setup_opcodes >> simp[EVERY_MEM]) >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     qexistsl_tac [`src`, `n2w slot`] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "package"
QED

Resume actual_setup_reach[package]:
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_metadata _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `vyper_decode_valid_enc _ _` kall_tac >>
  qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` kall_tac >>
  qpat_x_assum `eval_operand (FST (SND ops)) prepared = _` kall_tac >>
  qpat_x_assum `eval_operand (SND (SND ops)) prepared = _` kall_tac >>
  `frag_exec_mem ctx st ready (\s. s = initial)
    (\t. t = (prepared with vs_inst_idx := LENGTH ready.cs_current_insts)) (K F)` by
    (irule frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
     gen_tac >> strip_tac >> gvs[] >> qexists_tac `prepared` >> simp[]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  qexists_tac `prepared with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  asm_rewrite_tac[abi_decoder_valid_array_entry_inst_idx, eval_op_inst_idx,
    venom_state_accfupds, venom_state_accessors, combinTheory.K_THM] >>
  ho_match_mp_tac (GEN_ALL actual_child_sequence_pullback) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]
QED
Finalise actual_setup_reach

Theorem calldata_actual_dynamic_header_child_reach:
  lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD
        (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
        (STRING #"%" (toString (next+2))) (STRING #"%" (toString (next+3)))
        body_lbl exit_lbl|> /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    st0 = (ops,ready) /\ fn_has_code st0 ready fn /\
  st0.cs_current_bb = body_lbl /\ st0.cs_current_insts = [] /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  ~u.vs_halted /\ u.vs_inst_idx = 0 /\ j < LENGTH vs /\
  LENGTH vs < dimword (:256) /\
  eval_operand ip u = SOME (n2w p) /\ mload p u = n2w j /\
  eval_operand src u = SOME srcword /\
  abi_decode_load CALLDATALOAD srcword u = n2w (LENGTH vs) /\
  p < dimword (:256) /\ p+32 <= u.vs_alloca_next /\
  FLOOKUP u.vs_allocas iid = SOME (p,32) /\ alloca_inv u /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next ip /\ next <= st0.cs_next_var /\
  next+4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st u /\
  ready.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap u /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD u) = bs ==>
  ?head entry.
    head = jump_to body_lbl
      (abi_decode_header_state (STRING #"%" (toString next))
        (STRING #"%" (toString (next+1))) (STRING #"%" (toString (next+2)))
        (STRING #"%" (toString (next+3))) j (LENGTH vs) u) /\
    abi_decoder_valid_array_entry ce env sf ty tv bs vs j ready ops CALLDATALOAD
      (Lit 0w) sb d b cap st0.cs_next_var limit_st head entry /\
    ~entry.vs_halted /\ entry.vs_current_bb = ready.cs_current_bb /\
    entry.vs_inst_idx = LENGTH ready.cs_current_insts /\
    entry.vs_memory = u.vs_memory /\ entry.vs_call_ctx = u.vs_call_ctx /\
    entry.vs_data_section = u.vs_data_section /\ entry.vs_allocas = u.vs_allocas /\
    entry.vs_alloca_next = u.vs_alloca_next /\
    (!op. abi_decoder_operand_live next op ==> eval_operand op entry = eval_operand op u) /\
    fresh_vars_wrt limit_st entry /\ alloca_inv entry /\
    FLOOKUP entry.vs_allocas iid = SOME (p,32) /\
    ((!fuel. mem_safe_run fuel ctx fn entry) ==> !fuel. mem_safe_run fuel ctx fn u) /\
    (!fuel r. run_from fuel ctx fn entry = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn entry ==> mem_safe_run fuel' ctx fn u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all actual_header_prepare >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `head = jump_to _ _` (mk_asm "headdef") >>
  qpat_x_assum `lookup_block u.vs_current_bb _ = _` kall_tac >>
  qpat_x_assum `lookup_block body_lbl _ = _` kall_tac >>
  qpat_x_assum `phi_prefix_length _ = _` kall_tac >>
  `abi_decoder_operand_live st0.cs_next_var src /\
   abi_decoder_operand_live st0.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `p+32 <= head.vs_alloca_next /\
   head.vs_current_bb = st0.cs_current_bb /\
   head.vs_inst_idx = LENGTH st0.cs_current_insts` by simp[] >>
  drule_all actual_setup_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  asm "headdef" (fn th => pure_rewrite_tac[GSYM th]) >>
  asm_x "headdef" kall_tac >>
  qexistsl_tac [`head`, `entry`] >> asm_rewrite_tac[] >> suspend "compose"
QED

Resume calldata_actual_dynamic_header_child_reach[compose]:
  `abi_decoder_address_frame st0.cs_next_var head entry /\
   fresh_vars_wrt limit_st entry` by fs[abi_decoder_valid_array_entry_def] >>
  qpat_x_assum `abi_decoder_valid_array_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_decoder_metadata _ _ _ _ _ _ _` kall_tac >>
  rpt (qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` kall_tac) >>
  fs[abiDecoderDynamicLoopSetupTheory.abi_decoder_address_frame_def] >>
  conj_tac >- metis_tac[abi_decoder_operand_live_mono] >>
  conj_tac >- metis_tac[cj 1 calldata_alloca_invariants_fields] >>
  qpat_x_assum `!fuel. (!e. run_from fuel _ _ entry <> Error e) ==> _` mp_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel _ _ head <> Error e) ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> ntac 2 disch_tac >>
  rpt strip_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel _ _ entry <> Error e) ==> _` drule >>
  disch_then (qx_choose_then `fhead` strip_assume_tac) >>
  qpat_x_assum `!fuel. (!e. run_from fuel _ _ head <> Error e) ==> _`
    (qspec_then `fhead` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED
Finalise calldata_actual_dynamic_header_child_reach
