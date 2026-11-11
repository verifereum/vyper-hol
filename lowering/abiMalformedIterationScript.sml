(* A real primitive array body on arbitrary bytes, including clamp rejection. *)
Theory abiMalformedIteration
Ancestors
  abiMalformedResources abiMalformedLeafProbe abiMalformedPrefix abiMalformedRuntime
  abiDecoderPrimitiveReflected abiDecoderPrimitiveMemory abiDecoderStaticLoopSetup abiDecoderLoopSetup
  abiDecoderPrimitiveLoopFragment abiDecoderReentry abiDecoderReentryAddress
  abiDecoderFrameCompose abiDecoderContract abiDecoderCoherence
  abiDecoderAbortReentry abiDecoderExecution abiDecoderArrayHeader
  abiDecoderGuards abiDecoderClampedWord abiDecoderArrayBackedge abiDecoderFrame
  abiEncoder emitHelperProps exprLoweringProps compileEnv
  valueEncoding valueEncodingProps venomState venomExecSemantics words list arithmetic
  fragExec instIdxIndep

Theorem abi_malformed_primitive_body:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi
    (DecPrimWord clamp) middle = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  has_type (vyper_to_abi_type env ty) av /\
  eval_operand ip initial = SOME ipw /\ mload (w2n ipw) initial = n2w j /\
  eval_operand src initial = SOME (n2w p) /\
  eval_operand dst initial = SOME (n2w d) /\
  eval_operand base_op initial = SOME (n2w B) /\
  mem_bytes_at B L initial.vs_memory = xs /\
  p + 32 + j * 32 + 32 <= L /\ B + L < dimword (:256) /\
  d + 32 + j * 32 < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var ip /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  (?t. run_inst_seq (emitted_insts st en) initial = Abort Revert_abort t) \/
  ?t v. run_inst_seq (emitted_insts st en) initial = OK t /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty)
      (TAKE 32 (DROP (p + 32 + j * 32) xs)) /\
    abi_vyper_admissible env ty
      (dec (vyper_to_abi_type env ty) (TAKE 32 (DROP (p + 32 + j * 32) xs))) /\
    value_has_type tv v /\ val_in_memory tv v (d + 32 + j * 32) t.vs_memory /\
    eval_operand (FST ops) t = SOME (n2w j) /\ eval_operand ip t = SOME ipw /\
    fresh_vars_wrt limit_st t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_frame (d + 32 + j * 32) 32 initial t /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
    t.vs_halted = initial.vs_halted /\ inst_extends st en
Proof
  strip_tac >>
  `~dec_info_needs_offset (DecPrimWord clamp)` by simp[dec_info_needs_offset_def] >>
  drule abi_decoder_primitive_memory_counters >> strip_tac >>
  drule_all abi_decode_static_element_setup_operands >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `inst_extends middle en` by
    (gvs[inst_extends_def, emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND] >> simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st middle) initial = OK prepared` >>
  `abi_decoder_operand_live middle.cs_next_var base_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand base_op prepared = SOME (n2w B)` by metis_tac[] >>
  `B + (p + 32 + j * 32) < dimword (:256)` by decide_tac >>
  `mem_bytes_at (B + (p + 32 + j * 32)) 32 prepared.vs_memory =
      TAKE 32 (DROP (p + 32 + j * 32) xs)` by
    (irule (cj 1 abi_checked_source_word_window) >>
     simp[abi_decode_source_def] >> qexists_tac `L` >> simp[] >> decide_tac) >>
  `LENGTH (TAKE 32 (DROP (p + 32 + j * 32) xs)) = 32` by
    (qpat_x_assum `mem_bytes_at _ 32 _ = _` (mp_tac o AP_TERM ``LENGTH:word8 list -> num``) >> simp[]) >>
  `32 <= LENGTH (TAKE 32 (DROP (p + 32 + j * 32) xs))` by simp[] >>
  `mem_bytes_at (B + (p + 32 + j * 32))
    (LENGTH (TAKE 32 (DROP (p + 32 + j * 32) xs))) prepared.vs_memory =
    TAKE 32 (DROP (p + 32 + j * 32) xs)` by gvs[] >>
  drule_all abi_decoder_readable_primitive_reentry >> strip_tac
  >- (disj1_tac >>
      drule_all run_inst_seq_emit_extend >> metis_tac[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
        abi_decoder_operand_live middle.cs_next_var op` by
    (rpt strip_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `run_inst_seq (emitted_insts st en) initial = OK t` by
    (drule_all run_inst_seq_emit_extend >> simp[]) >>
  disj2_tac >> qexistsl_tac [`t`, `v`] >>
  simp[] >>
  conj_tac >- (gvs[abi_decode_frame_def] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  irule inst_extends_trans >> qexists_tac `middle` >> simp[]
QED

(* The actual generated backedge preserves an arbitrary-byte window and
   advances only the already reflected prefix. *)
Theorem abi_malformed_backedge:
  abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
    env ty array_xs first ip (n2w slot) n j avs s /\
  abi_reflected_head_ok a array_xs j /\
  vyper_decode_valid_enc a (abi_reflected_child a array_xs j) /\
  abi_vyper_admissible env ty (dec a (abi_reflected_child a array_xs j)) /\
  a = vyper_to_abi_type env ty /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString next)) ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\ j < n /\ n < dimword (:256) /\
  slot < dimword (:256) /\ b <= slot /\ slot + 32 <= b + k /\
  EVERY (abi_decoder_operand_live first) [base_op;hi;src;dst] /\
  first <= next /\ next < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. exec_block fuel ctx bb s = OK t /\
    abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
      env ty array_xs first ip (n2w slot) n (SUC j)
      (avs ++ [dec a (abi_reflected_child a array_xs j)]) t /\
    abi_decode_footprint_frame [(d,outsz);(b,k)] s t /\
    fresh_vars_wrt limit_st t /\
    (!op w. abi_decoder_operand_live first op /\ eval_operand op s = SOME w ==>
       eval_operand op t = SOME w) /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand ip s = SOME (n2w slot) /\ abi_decoder_operand_live first ip` by
    fs[abi_malformed_loop_def] >>
  `ip <> Var (STRING #"%" (toString next))` by
    (drule_all abi_decoder_live_excludes_output >> simp[]) >>
  qabbrev_tac `result = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString next)) (n2w (SUC j)) s))` >>
  `exec_block fuel ctx bb s = OK result` by
    (drule_all abi_decode_backedge_control >> simp[Abbr `result`, w2n_n2w]) >>
  `abi_decode_footprint_frame [(slot,32)] s result /\
    mload slot result = n2w (SUC j)` by
    (mp_tac (Q.INST [`p` |-> `(n2w slot:bytes32)`, `fp` |-> `[(slot:num,32:num)]`,
       `nv` |-> `STRING #"%" (toString (next:num))`, `w` |-> `(n2w (SUC j):bytes32)`]
       (INST_TYPE [alpha |-> ``:256``] abi_decode_backedge_observations)) >>
     simp[Abbr `result`, w2n_n2w]) >>
  `abi_decode_footprint_frame [(d,outsz);(b,k)] s result` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(slot,32)]` >> simp[] >>
     qexistsl_tac [`b`, `k`] >> simp[]) >>
  `result.vs_vars = s.vs_vars |+ (STRING #"%" (toString next),n2w (SUC j)) /\
    result.vs_labels = s.vs_labels` by
    simp[Abbr `result`, jump_to_def, mstore_def, update_var_def,
         write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `!op w. abi_decoder_operand_live first op /\ eval_operand op s = SOME w ==>
     eval_operand op result = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live next op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `first` >> simp[]) >>
     simp[]) >>
  `abi_malformed_window opc base_op hi src dst B L p d outsz b k xs result` by
    (irule abi_malformed_window_frame >> qexists_tac `s` >>
     fs[abi_malformed_loop_def] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `abi_malformed_loop opc base_op hi src dst B L p d outsz b k xs
    env ty array_xs first ip (n2w slot) n (SUC j)
    (avs ++ [dec a (abi_reflected_child a array_xs j)]) result` by
    (irule abi_malformed_loop_advance >> simp[w2n_n2w] >>
     qexists_tac `s` >> simp[]) >>
  qexists_tac `result` >> simp[] >>
  simp[Abbr `result`, jump_to_def, mstore_def, update_var_def,
       write_memory_with_expansion_def]
QED

(* Transport the loop observation across the current output word, without
   assuming any unprocessed child is well formed. *)
Theorem abi_malformed_primitive_observation:
  abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
    env ty (DROP (p+32) xs) first ip (n2w slot) n j avs s /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  static_length (vyper_to_abi_type env ty) = 32 /\
  p + 32 + j * 32 + 32 <= L /\
  d + 32 + j * 32 + 32 <= d + outsz /\
  b <= slot /\ slot + 32 <= b + k /\ slot < dimword (:256) /\
  abi_decode_frame (d + 32 + j * 32) 32 s t /\
  (!op w. abi_decoder_operand_live first op /\ eval_operand op s = SOME w ==>
     eval_operand op t = SOME w) /\
  EVERY (abi_decoder_operand_live first) [base_op;hi;src;dst] ==>
  abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
    env ty (DROP (p+32) xs) first ip (n2w slot) n j avs t /\
  abi_reflected_head_ok (vyper_to_abi_type env ty) (DROP (p+32) xs) j /\
  abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j =
    TAKE 32 (DROP (p+32+j*32) xs) /\
  abi_decode_footprint_frame [(d,outsz);(b,k)] s t
Proof
  strip_tac >>
  `abi_malformed_window MLOAD base_op hi src dst B L p d outsz b k xs s` by
    fs[abi_malformed_loop_def] >>
  `abi_decode_footprint_frame [(d,outsz);(b,k)] s t` by
    (irule abi_decode_footprint_frame_weaken >>
     qexists_tac `[(d+32+j*32,32)]` >>
     simp[GSYM abi_decode_frame_footprint] >> qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  `abi_malformed_window MLOAD base_op hi src dst B L p d outsz b k xs t` by
    (irule abi_malformed_window_frame >> qexists_tac `s` >>
     simp[] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `abi_footprint_disjoint slot 32 [(d+32+j*32,32)]` by
    (fs[abi_malformed_window_def, abi_footprint_disjoint_def] >> rpt strip_tac >> decide_tac) >>
  `mload slot t = mload slot s` by
    (irule abi_decode_footprint_frame_mload >>
     qexists_tac `[(d+32+j*32,32)]` >> simp[GSYM abi_decode_frame_footprint]) >>
  `LENGTH xs = L` by
    (fs[abi_malformed_window_def, abi_decode_source_def] >>
     metis_tac[LENGTH_mem_bytes_at]) >>
  simp[abi_malformed_loop_def, w2n_n2w] >>
  fs[abi_malformed_loop_def] >>
  simp[abi_reflected_head_ok_def, abi_reflected_child_def,
       rich_listTheory.DROP_DROP_T, LENGTH_DROP] >> decide_tac
QED

(* One complete block iteration: setup, rejecting primitive child, then the
   emitted increment/store/backedge. No acceptance assumption on future cells. *)
Theorem abi_malformed_primitive_iteration:
  abi_decode_array_element_setup ip src dst MLOAD base_op hi (DecPrimWord clamp) 32 32
    st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi
    (DecPrimWord clamp) middle = ((),en) /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  has_type (vyper_to_abi_type env ty) av /\
  ~is_dynamic (vyper_to_abi_type env ty) /\ static_length (vyper_to_abi_type env ty) = 32 /\
  abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
    env ty (DROP (p+32) xs) st.cs_next_var ip (n2w slot) n j avs initial /\
  EVERY (abi_decoder_operand_live st.cs_next_var) [base_op;hi;src;dst] /\
  p + 32 + j * 32 + 32 <= L /\ d + 32 + j * 32 + 32 <= d + outsz /\
  b <= slot /\ slot + 32 <= b + k /\ slot < dimword (:256) /\
  j < n /\ n < dimword (:256) /\
  en.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  bb.bb_instructions = en.cs_current_insts ++
    abi_decode_backedge_insts en.cs_next_id iv
      (STRING #"%" (toString en.cs_next_var)) ip hdr /\
  FST ops = Var iv /\ initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~initial.vs_halted ==>
  (?t. exec_block fuel ctx bb initial = Abort Revert_abort t) \/
  ?t. exec_block fuel ctx bb initial = OK t /\
    abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
      env ty (DROP (p+32) xs) st.cs_next_var ip (n2w slot) n (SUC j)
      (avs ++ [dec (vyper_to_abi_type env ty)
        (abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j)]) t /\
    abi_decode_footprint_frame [(d,outsz);(b,k)] initial t /\
    fresh_vars_wrt limit_st t /\ t.vs_current_bb = hdr /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_primitive_loop_body_shape >> strip_tac >>
  `st.cs_current_insts ++ emitted_insts st en = en.cs_current_insts` by
    (gvs[emitted_insts_def, rich_listTheory.IS_PREFIX_APPEND] >>
     simp[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX (emitted_insts st en) (DROP initial.vs_inst_idx bb.bb_instructions)` by
    (simp[] >> qpat_x_assum `st.cs_current_insts ++ _ = _` (SUBST1_TAC o SYM) >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  qspecl_then [`emitted_insts st en`, `initial`, `fuel`, `ctx`, `bb`]
    mp_tac exec_block_run_inst_seq >> simp[] >> strip_tac >>
  `eval_operand ip initial = SOME (n2w slot) /\
    mload (w2n (n2w slot:bytes32)) initial = n2w j /\
    abi_decoder_operand_live st.cs_next_var ip` by fs[abi_malformed_loop_def] >>
  `eval_operand src initial = SOME (n2w p) /\
    eval_operand dst initial = SOME (n2w d) /\
    eval_operand base_op initial = SOME (n2w B) /\
    mem_bytes_at B L initial.vs_memory = xs /\ B+L < dimword (:256) /\
    d+outsz < dimword (:256)` by
    fs[abi_malformed_loop_def, abi_malformed_window_def, abi_decode_source_def] >>
  `d + 32 + j*32 < dimword (:256) /\
    en.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\
    abi_decoder_operand_live st.cs_next_var base_op` by fs[] >>
  drule_all abi_malformed_primitive_body >> strip_tac
  >- (disj1_tac >> first_x_assum drule >> strip_tac >> metis_tac[]) >>
  drule_all abi_malformed_primitive_observation >> strip_tac >>
  `LENGTH en.cs_current_insts = LENGTH st.cs_current_insts + LENGTH (emitted_insts st en)` by
    (qpat_x_assum `st.cs_current_insts ++ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `exec_block fuel ctx bb initial =
    exec_block fuel ctx bb (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (qpat_x_assum `!s'. run_inst_seq _ _ = OK s' ==> _` drule >> simp[]) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH en.cs_current_insts` >>
  `abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
    env ty (DROP (p+32) xs) st.cs_next_var ip (n2w slot) n j avs u` by
    ( `abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
        env ty (DROP (p+32) xs) st.cs_next_var ip (n2w slot) n j avs u =
        abi_malformed_loop MLOAD base_op hi src dst B L p d outsz b k xs
        env ty (DROP (p+32) xs) st.cs_next_var ip (n2w slot) n j avs t` by
        simp_tac (srw_ss()) [Abbr `u`, abi_malformed_loop_def, abi_malformed_window_def,
          eval_op_inst_idx, mload_def, abi_decode_source_def] >>
      asm_rewrite_tac []) >>
  `u.vs_inst_idx = LENGTH en.cs_current_insts /\ ~u.vs_halted /\
    eval_operand (Var iv) u = SOME (n2w j) /\ fresh_vars_wrt limit_st u` by
    (fs[Abbr `u`, eval_op_inst_idx, fresh_vars_wrt_def] >>
     qpat_x_assum `eval_operand (FST ops) t = _` mp_tac >> simp[]) >>
  `~dec_info_needs_offset (DecPrimWord clamp)` by simp[dec_info_needs_offset_def] >>
  `st.cs_next_var <= en.cs_next_var` by
    (drule_all abi_decode_static_element_setup_operands >> strip_tac >>
     drule abi_decoder_primitive_memory_counters >> strip_tac >> decide_tac) >>
  `vyper_decode_valid_enc (vyper_to_abi_type env ty)
    (abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j) /\
   abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty)
    (abi_reflected_child (vyper_to_abi_type env ty) (DROP (p+32) xs) j))` by gvs[] >>
  drule abi_malformed_backedge >> simp[] >>
  disch_then (qspecl_then [`en.cs_current_insts`, `en.cs_next_var`, `limit_st`] mp_tac) >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  disj2_tac >> qexists_tac `t'` >> simp[Abbr `u`] >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `t` >>
  simp[] >>
  qpat_x_assum `abi_decode_footprint_frame _ (t with vs_inst_idx := _) _` mp_tac >>
  simp[abi_decode_footprint_frame_def]
QED
