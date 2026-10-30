Theory abiBuiltinSetupReach
Ancestors
  abiBuiltinDecodeSetup abiBuiltinDecodeAllocation abiBuiltinSetupFrames abiBuiltinAllocation
  abiBuiltinDecodeHeader abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderGuards abiDecoderContract context compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomState finite_map words arithmetic list
  abiDecoderLoop fragExec instIdxIndep venomInst

(* Execute header, output allocation and upper-bound ADD before decoding.
   TOP-LEVEL: abi_builtin_decode_setup_execute, abi_builtin_decode_setup_live. *)
Theorem abi_builtin_decode_setup_live:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) ==>
  abi_decoder_operand_live ready.cs_next_var (FST ops) /\
  abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live ready.cs_next_var (SND (SND ops))
Proof
  strip_tac >> drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_decode_header_live >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `abi_decoder_operand_live ready.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `allocation_st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live ready.cs_next_var (SND inputs)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `header_st.cs_next_var` >> simp[] >> decide_tac) >>
  qpat_x_assum `ops = _` (fn th => PURE_REWRITE_TAC [th, pairTheory.FST, pairTheory.SND]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_builtin_decode_setup_execute:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  ?t. run_inst_seq (emitted_insts st ready) initial = OK t /\
    eval_operand (FST ops) t = SOME (n2w d) /\
    eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
    eval_operand (SND (SND ops)) t = SOME (p + 32w + n2w cnt) /\
    fresh_vars_wrt limit_st t /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) outsz initial t /\
    inst_extends st ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_decode_header_live >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_decoder_operand_live_emit >>
  `header_st.cs_next_id = abi_builtin_decode_output_site st min_size max_size /\
   allocation_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= allocation_st.cs_next_var`
    by (asm_simp_tac bool_ss [abi_builtin_decode_output_site_def] >> decide_tac) >>
  mp_tac abi_builtin_decode_allocation >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_allocation_frame st.cs_next_var header_st.cs_next_id outsz initial allocated` >>
  mp_tac (Q.INST [`lhs` |-> `SND (inputs:operand # operand)`,
    `rhs` |-> `FST (inputs:operand # operand)`, `out` |-> `hi`,
    `a` |-> `(p:bytes32) + 32w`, `b` |-> `n2w cnt:bytes32`,
    `st` |-> `allocation_st`, `st'` |-> `ready`, `s` |-> `allocated:venom_state`]
    abi_builtin_emit_add) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_builtin_prefix allocation_st ready limit_st allocated actual` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `abi_builtin_allocation_frame st.cs_next_var header_st.cs_next_id outsz initial actual` by
    (irule abi_builtin_allocation_frame_suffix >>
     qexistsl_tac [`allocated`, `allocation_st.cs_next_var`] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live allocation_st.cs_next_var (SND inputs)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `header_st.cs_next_var` >> simp[]) >>
  `eval_operand buf.buf_operand actual = SOME (n2w d)` by
    (qpat_assum `!op w. abi_decoder_operand_live allocation_st.cs_next_var op /\ _ ==> _`
      (qspecl_then [`buf.buf_operand`, `n2w d:bytes32`] mp_tac) >> asm_simp_tac bool_ss []) >>
  `eval_operand (SND inputs) actual = SOME (p + 32w)` by
    (qpat_assum `!op w. abi_decoder_operand_live allocation_st.cs_next_var op /\ _ ==> _`
      (qspecl_then [`SND (inputs:operand # operand)`, `(p:bytes32) + 32w`] mp_tac) >>
     asm_simp_tac bool_ss []) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `actual` >>
  qpat_x_assum `ops = _` (fn th => PURE_REWRITE_TAC [th, pairTheory.FST, pairTheory.SND]) >>
  qpat_x_assum `header_st.cs_next_id = abi_builtin_decode_output_site st min_size max_size`
    (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Reach the actual recursive decoder entry after all builtin setup actions. *)
Theorem abi_builtin_decode_setup_from_state:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st ready (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w d) /\
      eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
      eval_operand (SND (SND ops)) t = SOME (p + 32w + n2w cnt) /\
      fresh_vars_wrt limit_st t /\
      abi_builtin_allocation_frame st.cs_next_var
        (abi_builtin_decode_output_site st min_size max_size) outsz initial t) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_builtin_decode_setup_execute >> strip_tac >>
  rename1 `abi_builtin_allocation_frame _ _ _ initial actual` >>
  qexists_tac `actual` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_builtin_decode_setup_reach:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\ fn_has_code st ready func /\
  eval_operand data initial = SOME p /\ mload (w2n p) initial = n2w cnt /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w d) /\
    eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
    eval_operand (SND (SND ops)) t = SOME (p + 32w + n2w cnt) /\ fresh_vars_wrt limit_st t /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) outsz initial t /\
    t.vs_current_bb = ready.cs_current_bb /\ t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_decode_setup_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
