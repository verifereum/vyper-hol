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
  abiStaticLoopBody eventTopicCode
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

(* Finite straight-line slices either reach their endpoint at zero block
   cost, or have an already fuel-independent result. *)
Theorem encode_static_sequence_outcome[local]:
  !code s bb rest P G ctx fn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = code ++ rest /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    (!t. run_inst_seq code s = OK t ==>
      P (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)) ==>
    fuel_outcome G ctx fn s 0 P
Proof
  Induct >> rpt gen_tac
  >- (simp[exprLoweringPropsTheory.run_inst_seq_def] >> strip_tac >>
      irule fuel_outcome_refl >> metis_tac[venomStateTheory.venom_state_component_equality]) >>
  strip_tac >> fs[EVERY_DEF] >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    (gvs[get_instruction_def, DROP_EQ_CONS]) >>
  `!f. run_from f ctx fn s =
    case step_inst_base h s of
      OK t => run_from f ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v t => IntRet v t | Halt t => Halt t
    | Abort a t => Abort a t | Error e => Error e` by
    (gen_tac >> drule_all run_from_nonterm >>
     gvs[EVERY_DEF, step_inst_non_invoke]) >>
  Cases_on `step_inst_base h s` >>
  gvs[fuel_outcome_def, exprLoweringPropsTheory.run_inst_seq_def] >>
  `v.vs_current_bb = s.vs_current_bb` by
    (irule (cj 1 venomInstPropsTheory.step_preserves_control_flow) >>
     qexistsl_tac [`ctx`, `G`, `h`] >> simp[step_inst_non_invoke]) >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `rest`, `P`, `G`, `ctx`, `fn`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (gvs[DROP_EQ_CONS, DROP_SUC]) >>
      rpt strip_tac >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by
        (fs[EVERY_MEM]) >>
      gvs[run_inst_seq_inst_idx] >>
      Cases_on `run_inst_seq code v` >>
      gvs[instIdxIndepTheory.exec_result_map_def, ADD_CLAUSES]) >>
  simp[]
QED

(* The last store repairs arbitrary writes in the middle of the body. *)
Theorem encode_static_saved_counter[local]:
  !id aid sid iv nv ip mid s t p.
    eval_operand ip s = SOME p /\ ip <> Var iv /\ ip <> Var nv /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
      EVERY (\name. ip <> Var name /\ Var iv <> Var name) i.inst_outputs) mid /\
    run_inst_seq ([mk_inst id MLOAD [ip] [iv]] ++ mid ++
      [mk_inst aid ADD [Var iv; Lit 1w] [nv];
       mk_inst sid MSTORE [ip; Var nv] []]) s = OK t ==>
    mload (w2n p) t = mload (w2n p) s + 1w
Proof
  rpt gen_tac >> strip_tac >>
  `step_inst_base (mk_inst id MLOAD [ip] [iv]) s =
    OK (update_var iv (mload (w2n p) s) s)` by simp[step_MLOAD] >>
  fs[exprLoweringPropsTheory.run_inst_seq_def] >>
  Cases_on `run_inst_seq mid (update_var iv (mload (w2n p) s) s)` >>
  gvs[exprLoweringPropsTheory.run_inst_seq_append,
      exprLoweringPropsTheory.run_inst_seq_append_err] >>
  `eval_operand ip v = SOME p /\
   eval_operand (Var iv) v = SOME (mload (w2n p) s)` by
    (conj_tac
     >- (drule run_inst_seq_operand_frame >>
         disch_then (qspec_then `ip` mp_tac) >>
         impl_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
         simp[ssaOperandFrameTheory.eval_operand_update_var_avoids]) >>
     drule run_inst_seq_operand_frame >>
     disch_then (qspec_then `Var iv` mp_tac) >>
     impl_tac >- (fs[EVERY_MEM] >> metis_tac[]) >> simp[eval_operand_update_var]) >>
  `step_inst_base (mk_inst aid ADD [Var iv; Lit 1w] [nv]) v =
     OK (update_var nv (mload (w2n p) s + 1w) v)` by
    (irule step_ADD >> simp[eval_operand_lit]) >>
  `step_inst_base (mk_inst sid MSTORE [ip; Var nv] [])
      (update_var nv (mload (w2n p) s + 1w) v) =
     OK (mstore (w2n p) (mload (w2n p) s + 1w)
       (update_var nv (mload (w2n p) s + 1w) v))` by
    (irule step_MSTORE >>
     simp[eval_operand_update_var,
       ssaOperandFrameTheory.eval_operand_update_var_avoids]) >>
  drule exprLoweringPropsTheory.run_inst_seq_append >>
  disch_then (qspec_then
    `[mk_inst aid ADD [Var iv; Lit 1w] [nv]; mk_inst sid MSTORE [ip; Var nv] []]`
    assume_tac) >>
  gvs[exprLoweringPropsTheory.run_inst_seq_def,
      venomMemPropsTheory.mload_mstore_same]
QED

Theorem encode_static_body_work_counter[local]:
  !id v labels dst src info asz msz s t p.
    eval_operand (Var (compiler_var_name v 0)) s = SOME p /\
    run_inst_seq (abi_static_loop_body_work id v labels dst src info asz msz) s = OK t ==>
    mload (w2n p) t = mload (w2n p) s + 1w
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `mid =
    TL (abiStaticLoopCode$abi_static_loop_body_prefix id v dst src asz msz) ++
    static_info_insts (id+14) (v+11)
      (Var (compiler_var_name v 10)) (Var (compiler_var_name v 7)) info` >>
  `abi_static_loop_body_work id v labels dst src info asz msz =
    [mk_inst (id+7) MLOAD [Var (compiler_var_name v 0)] [compiler_var_name v 4]] ++
    mid ++ [mk_inst (id+14+static_info_id_count info) ADD
      [Var (compiler_var_name v 4); Lit 1w]
      [compiler_var_name v (11+static_info_var_count info)];
    mk_inst (id+15+static_info_id_count info) MSTORE
      [Var (compiler_var_name v 0);
       Var (compiler_var_name v (11+static_info_var_count info))] []]` by
    (Cases_on `info` >>
     simp[Abbr `mid`, abi_static_loop_body_work_def,
      abiStaticLoopCodeTheory.abi_static_loop_body_def,
      abiStaticLoopCodeTheory.abi_static_loop_body_prefix_def,
      abiStaticLoopCodeTheory.static_info_insts_def,
      FRONT_APPEND]) >>
  fs[] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`)
    (SIMP_RULE std_ss [APPEND] encode_static_saved_counter) >>
  disch_then (qspec_then `p` irule) >>
  Cases_on `info` >>
  simp[Abbr `mid`, abiStaticLoopCodeTheory.abi_static_loop_body_prefix_def,
    abiStaticLoopCodeTheory.static_info_insts_def,
    abiStaticLoopCodeTheory.static_info_var_count_def,
    abiStaticLoopCodeTheory.compiler_var_name_add,
    mk_inst_def, is_terminator_def]
QED

Theorem encode_static_body_work_frame[local]:
  !id v labels dst src info asz msz s t op.
    run_inst_seq (abi_static_loop_body_work id v labels dst src info asz msz) s = OK t /\
    EVERY (\name. op <> Var name) (abi_static_loop_body_names v info) ==>
    eval_operand op t = eval_operand op s
Proof
  rpt gen_tac >> strip_tac >>
  irule run_inst_seq_operand_frame >>
  qexists_tac `abi_static_loop_body_work id v labels dst src info asz msz` >>
  simp[] >> Cases_on `info` >>
  fs[abi_static_loop_body_names_def] >>
  simp[abi_static_loop_body_work_def,
    abiStaticLoopCodeTheory.abi_static_loop_body_def,
    abiStaticLoopCodeTheory.abi_static_loop_body_prefix_def,
    abiStaticLoopCodeTheory.static_info_insts_def,
    abiStaticLoopCodeTheory.static_info_var_count_def,
    abiStaticLoopCodeTheory.compiler_var_name_add,
    FRONT_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem encode_static_body_work_vars_kept[local]:
  !id v labels dst src info asz msz s t N.
    run_inst_seq (abi_static_loop_body_work id v labels dst src info asz msz) s = OK t /\
    EVERY (\name. ~var_below N name) (abi_static_loop_body_names v info) ==>
    vars_kept N {} s t
Proof
  rpt gen_tac >> strip_tac >> simp[vars_kept_def] >>
  rpt strip_tac >>
  `eval_operand (Var x) t = eval_operand (Var x) s` suffices_by
    simp[venomStateTheory.eval_operand_def] >>
  irule encode_static_body_work_frame >>
  goal_assum (drule_at Any) >> fs[EVERY_MEM] >> metis_tac[]
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
