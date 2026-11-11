(*
 * Fuel bound for the static-element dynamic-array ABI encode loop.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_abi_encode_dyn_static_loop
 *)

Theory fragFuelLoopAbiEncStatic
Ancestors
  fragFuel fragFuelContextBase abiEncoder compileEnv emitHelper context
  venomInst abiEncoderArrayLoopContext abiEncoderArrayLoopLayout
  abiEncoderArrayRound abiEncoderCounters abiEncoderAppend
  abiEncoderArrayCode abiEncoderArrayBodyCode fragExec rich_list
  venomExecSemantics emitHelperProps list arithmetic exprSimAbiEncodeObliviousFacts
  exprSimAbiEncodeObliviousCode exprSimAbiEncodeObliviousContext
Libs
  fragFuelLib

(* These element actions are straight-line for every info constructor, not
   only for the constructors produced by the ABI type analysis. *)
Theorem fuel_ok_encode_static_info[local]:
  !dst src ei Wv E.
    fuel_ok Wv {} E (compile_abi_encode_static_info dst src ei)
Proof
  rpt gen_tac >> Cases_on `ei` >>
  simp_tac std_ss [compile_abi_encode_static_info_def,
    compile_abi_encode_static_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

(* In particular Wv = {} protects the allocated pointer, the saved index,
   and all variables below the body entry supply through element encoding. *)
Theorem fuel_ok_encode_static_body[local]:
  !ip src dst ei asz msz Wv E.
    fuel_ok Wv {} E (abi_encode_array_static_body ip src dst ei asz msz)
Proof
  rpt gen_tac >>
  simp_tac std_ss [abi_encode_array_static_body_def,
    abi_encode_array_addresses_def,
    abiDecoderDynamicLoopSetupTheory.abi_decode_array_head_setup_def,
    abiDecoderDynamicLoopSetupTheory.abi_decode_indexed_coordinates_def] >>
  fuel_auto [fuel_ok_encode_static_info, fuel_ok_emit_op] >>
  simp[is_terminator_def]
QED

Theorem encode_static_body_entry[local]:
  abi_encode_array_static_body ip src dst ei asz msz st = (idx,end_st) /\
  fn_has_code st end_st func /\ st.cs_current_insts = [] ==>
  ?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule abi_encode_array_static_body_trace >> strip_tac >>
  `cs_extends st prepared` by
    (drule abi_encode_array_addresses_shape >>
     simp[inst_extends_def, cs_extends_def] >> metis_tac[]) >>
  `cs_extends prepared end_st` by
    metis_tac[cs_appends_abi_encode_static_info, cs_appends_def] >>
  `fn_has_code st prepared func` by metis_tac[fn_has_code_split] >>
  drule abi_encode_array_addresses_head >> strip_tac >>
  qpat_assum `fn_has_code st prepared func`
    (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [fn_has_code_def]) >>
  strip_tac >> qexists_tac `bb` >>
  gvs[IS_PREFIX_APPEND, phi_prefix_length_def, mk_inst_def]
QED

Theorem encode_static_register_bounds[local]:
  abiDecoderIndexInit$abi_decode_index_init st = (ip,owner_st) /\
  abi_encode_array_header ip len owner_st = (labels,body_st) /\
  abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  (!x. len = Var x ==> var_below st.cs_next_var x) ==>
  st.cs_next_var < body_st.cs_next_var /\
  body_st.cs_next_var < body_end.cs_next_var /\
  ip <> idx /\ len <> ip /\ len <> idx /\
  len <> Var (STRING #"%" (toString body_end.cs_next_var))
Proof
  strip_tac >> drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >>
  strip_tac >>
  `body_st.cs_next_var = owner_st.cs_next_var + 3` by
    (qpat_x_assum `abi_encode_array_header _ _ _ = _` mp_tac >>
     simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_shape] >>
     strip_tac >> gvs[]) >>
  drule abi_encode_array_static_body_index >> strip_tac >>
  drule abi_encode_array_static_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `prepared.cs_next_var <= body_end.cs_next_var` by
    metis_tac[fuel_ok_encode_static_info, fuel_ok_def] >>
  `st.cs_next_var < body_st.cs_next_var /\
   body_st.cs_next_var < body_end.cs_next_var` by decide_tac >>
  asm_simp_tac (srw_ss()) [ASCIInumbersTheory.toString_11] >>
  `st.cs_next_var <= body_end.cs_next_var` by decide_tac >>
  Cases_on `len` >> gvs[var_below_def] >> metis_tac[]
QED

Theorem encode_static_loop_no_phi[local]:
  compile_abi_encode_dyn_static_loop dst src ei asz msz len st = (out,st') /\
  cs_no_phi st ==> cs_no_phi st'
Proof
  strip_tac >>
  drule (REWRITE_RULE [code_action_def] code_action_static_loop) >>
  simp_tac std_ss [code_step_def, enc_safe_opcode_def] >> strip_tac >>
  gvs[entry_shape_def] >>
  gvs[exprSimAbiGasBridgeTheory.frag_code_def, emitted_blocks_def,
      exprLoweringPropsTheory.emitted_insts_def, LAST_APPEND, FRONT_APPEND, DROP_LENGTH_APPEND,
      TAKE_APPEND, TAKE_LENGTH_TOO_LONG,
      cs_no_phi_def, EVERY_APPEND, EVERY_FLAT, EVERY_MAP] >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

(* The loop counter lives in a buffer the function allocates itself and
   starts at 0.  Each round, while the counter is below len_op (unsigned),
   encodes one element with straight-line code (no calls back into the
   encoder) and adds 1, then jumps back to the header.  len_op is a
   parameter: when it is a variable it was allocated before the call, and
   the body writes only variables it allocates itself, so the bound stays
   fixed.  The counter is at most len_op < 2 ** 256, so it does not wrap
   and the loop leaves within 2 ** 256 rounds.  (The body's memory writes
   go to the destination buffer, disjoint from the counter's buffer.) *)
Theorem fuel_okS_compile_abi_encode_dyn_static_loop:
  !dst src elem_info elem_abi_sz elem_mem_sz len_op Wv E.
    fuel_okS (\st. !x. len_op = Var x ==> var_below st.cs_next_var x) Wv {} E
      (compile_abi_encode_dyn_static_loop dst src elem_info elem_abi_sz
         elem_mem_sz len_op)
Proof
  cheat
QED
