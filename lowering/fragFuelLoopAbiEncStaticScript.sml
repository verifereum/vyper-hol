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
  abiStaticLoopBody abiStaticLoopCodeProps abiStaticLoopEntry eventTopicCode
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

Theorem encode_static_header_prefix[local]:
  !ip s p len iv nw id cmp done body_lbl exit_lbl.
    eval_operand ip s = SOME p /\ len <> Var iv /\
    eval_operand len s = SOME nw ==>
    run_inst_seq (TAKE 3 (abi_encode_array_header_insts
      id ip len iv cmp done body_lbl exit_lbl)) s =
    OK (abi_encode_array_header_state iv cmp done
      (w2n (mload (w2n p) s)) (w2n nw) s)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand len (update_var iv (mload (w2n p) s) s) = SOME nw` by
    simp[ssaOperandFrameTheory.eval_operand_update_var_avoids] >>
  `step_inst_base (mk_inst id MLOAD [ip] [iv]) s =
     OK (update_var iv (mload (w2n p) s) s)` by simp[step_MLOAD] >>
  simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
    exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    venomStateTheory.eval_operand_def, lookup_var_update_var] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
    venomStateTheory.eval_operand_def, lookup_var_update_var,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def] >>
  Cases_on `w2n (mload (w2n p) s) < w2n nw` >>
  simp[bool_to_word_def]
QED

Theorem encode_static_header_missing_bound[local]:
  !ip s p len iv id cmp done body_lbl exit_lbl t.
    eval_operand ip s = SOME p /\ len <> Var iv /\
    eval_operand len s = NONE ==>
    run_inst_seq (TAKE 3 (abi_encode_array_header_insts
      id ip len iv cmp done body_lbl exit_lbl)) s <> OK t
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand len (update_var iv (mload (w2n p) s) s) = NONE` by
    simp[ssaOperandFrameTheory.eval_operand_update_var_avoids] >>
  `step_inst_base (mk_inst id MLOAD [ip] [iv]) s =
     OK (update_var iv (mload (w2n p) s) s)` by simp[step_MLOAD] >>
  simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
    exprLoweringPropsTheory.run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    venomStateTheory.eval_operand_def, lookup_var_update_var]
QED

Theorem encode_static_header_branch[local]:
  !id iv cmp done i n s body_lbl exit_lbl.
    step_inst_base (mk_inst id JNZ
      [Var done; Label exit_lbl; Label body_lbl] [])
      (abi_encode_array_header_state iv cmp done i n s) =
    OK (jump_to (if i < n then body_lbl else exit_lbl)
      (abi_encode_array_header_state iv cmp done i n s))
Proof
  rpt gen_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
    venomStateTheory.eval_operand_def, lookup_var_update_var] >>
  Cases_on `i < n` >> simp[bool_to_word_def]
QED

Theorem encode_static_header_frame[local]:
  !iv cmp done i n s op.
    op <> Var iv /\ op <> Var cmp /\ op <> Var done ==>
    eval_operand op (abi_encode_array_header_state iv cmp done i n s) =
    eval_operand op s
Proof
  simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
    ssaOperandFrameTheory.eval_operand_update_var_avoids]
QED

Theorem encode_static_header_memory[local]:
  !iv cmp done i n s addr.
    mload addr (abi_encode_array_header_state iv cmp done i n s) = mload addr s
Proof
  simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
    ssaOperandFrameTheory.mload_update_var]
QED

Theorem encode_static_header_vars_kept[local]:
  !iv cmp done i n s N.
    ~var_below N iv /\ ~var_below N cmp /\ ~var_below N done ==>
    vars_kept N {} s (abi_encode_array_header_state iv cmp done i n s)
Proof
  rpt gen_tac >> strip_tac >> simp[vars_kept_def] >> rpt strip_tac >>
  `eval_operand (Var x) (abi_encode_array_header_state iv cmp done i n s) =
   eval_operand (Var x) s` suffices_by simp[venomStateTheory.eval_operand_def] >>
  irule encode_static_header_frame >> simp[] >> metis_tac[]
QED

Theorem encode_static_countdown_range[local]:
  !s p. dimword (:256) - 1 - w2n (mload (w2n p) s) < dimword (:256)
Proof
  rpt gen_tac >>
  `1 < dimword (:256)` by simp[] >>
  mp_tac (arithmeticTheory.SUB_LESS_EQ |>
    Q.SPECL [`dimword (:256) - 1`, `w2n (mload (w2n p) s)`]) >>
  decide_tac
QED

Theorem encode_static_round_outcome[local]:
  !G ctx fn id v labels dst src info asz msz len N initial p.
    no_phi_fn fn /\
    lookup_block (fresh_label_output "enc_dyn_hdr" labels) fn.fn_blocks =
      SOME <|bb_label := fresh_label_output "enc_dyn_hdr" labels;
        bb_instructions := abiStaticLoopCode$abi_static_loop_header id v labels len|> /\
    lookup_block (fresh_label_output "enc_dyn_body" (labels+1)) fn.fn_blocks =
      SOME <|bb_label := fresh_label_output "enc_dyn_body" (labels+1);
        bb_instructions := abiStaticLoopCode$abi_static_loop_body id v labels dst src info asz msz|> /\
    len <> Var (compiler_var_name v 1) /\
    EVERY (\name. ~var_below N name)
      ([compiler_var_name v 1; compiler_var_name v 2; compiler_var_name v 3] ++
       abi_static_loop_body_names v info) ==>
    let H = \s. s.vs_current_bb = fresh_label_output "enc_dyn_hdr" labels /\
      s.vs_inst_idx = 0 /\
      eval_operand (Var (compiler_var_name v 0)) s = SOME p /\
      vars_kept N {} initial s in
    let Q = \t. t.vs_current_bb = fresh_label_output "enc_dyn_exit" (labels+2) /\
      t.vs_inst_idx = 0 /\ vars_kept N {} initial t in
    let mu = \s. dimword (:256) - 1 - w2n (mload (w2n p) s) in
    !s. H s ==> ?j. j <= 2 /\
      fuel_outcome G ctx fn s j (\t. Q t \/ (H t /\ mu t < mu s))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
  gen_tac >> strip_tac >>
  Cases_on `eval_operand len s`
  >- suspend "missing"
  >> rename1 `eval_operand len s = SOME nw` >>
  suspend "success"
QED

Resume encode_static_round_outcome[missing]:
  qexists_tac `0` >> simp[] >>
  irule encode_static_sequence_outcome >>
  qexistsl_tac
    [`<|bb_label := fresh_label_output "enc_dyn_hdr" labels;
        bb_instructions := abiStaticLoopCode$abi_static_loop_header id v labels len|>`,
     `TAKE 3 (abi_encode_array_header_insts (id+3)
       (Var (compiler_var_name v 0)) len (compiler_var_name v 1)
       (compiler_var_name v 2) (compiler_var_name v 3)
       (fresh_label_output "enc_dyn_body" (labels+1))
       (fresh_label_output "enc_dyn_exit" (labels+2)))`,
     `[mk_inst (id+6) JNZ [Var (compiler_var_name v 3);
       Label (fresh_label_output "enc_dyn_exit" (labels+2));
       Label (fresh_label_output "enc_dyn_body" (labels+1))] []]`] >>
  simp[abiStaticLoopCodeTheory.abi_static_loop_header_def,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
    mk_inst_def, is_terminator_def] >>
  rpt strip_tac >>
  drule_all encode_static_header_missing_bound >> simp[] >>
  qexistsl_tac [`id+3`, `compiler_var_name v 2`, `compiler_var_name v 3`,
    `fresh_label_output "enc_dyn_body" (labels+1)`,
    `fresh_label_output "enc_dyn_exit" (labels+2)`, `t`] >>
  simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def, mk_inst_def]
QED
Resume encode_static_round_outcome[success]:
  qmatch_goalsub_abbrev_tac `?j. j <= 2 /\ fuel_outcome G ctx fn s j post` >>
  qabbrev_tac `hs = abi_encode_array_header_state
    (compiler_var_name v 1) (compiler_var_name v 2) (compiler_var_name v 3)
    (w2n (mload (w2n p) s)) (w2n nw) s with vs_inst_idx := 3` >>
  `fuel_outcome G ctx fn s 0 (\t. t = hs)` by
    (irule encode_static_sequence_outcome >>
     qexistsl_tac
      [`<|bb_label := fresh_label_output "enc_dyn_hdr" labels;
        bb_instructions := abiStaticLoopCode$abi_static_loop_header id v labels len|>`,
       `TAKE 3 (abi_encode_array_header_insts (id+3)
         (Var (compiler_var_name v 0)) len (compiler_var_name v 1)
         (compiler_var_name v 2) (compiler_var_name v 3)
         (fresh_label_output "enc_dyn_body" (labels+1))
         (fresh_label_output "enc_dyn_exit" (labels+2)))`,
       `[mk_inst (id+6) JNZ [Var (compiler_var_name v 3);
         Label (fresh_label_output "enc_dyn_exit" (labels+2));
         Label (fresh_label_output "enc_dyn_body" (labels+1))] []]`] >>
     simp[abiStaticLoopCodeTheory.abi_static_loop_header_def,
       abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
       mk_inst_def, is_terminator_def] >>
     rpt strip_tac >>
     qpat_assum `eval_operand (Var (compiler_var_name v 0)) s = SOME p`
       (mp_then Any mp_tac encode_static_header_prefix) >>
     disch_then (qspecl_then [`len`, `compiler_var_name v 1`, `nw`,
       `id+3`, `compiler_var_name v 2`, `compiler_var_name v 3`,
       `fresh_label_output "enc_dyn_body" (labels+1)`,
       `fresh_label_output "enc_dyn_exit" (labels+2)`] mp_tac) >>
     simp[abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
       mk_inst_def, Abbr `hs`] >> metis_tac[]) >>
  `?j. j <= 2 /\ fuel_outcome G ctx fn hs j post` suffices_by
    (strip_tac >>
     qpat_assum `fuel_outcome G ctx fn s 0 _`
       (mp_then Any mp_tac fuel_outcome_compose) >>
     disch_then (qspecl_then [`post`, `2`] mp_tac) >> simp[] >>
     metis_tac[]) >>
  Cases_on `w2n (mload (w2n p) s) < w2n nw`
  >- suspend "body" >>
  suspend "exit"
QED
Resume encode_static_round_outcome[exit]:
  qexists_tac `1` >> simp[] >>
  irule fuel_outcome_jump >>
  conj_tac >- simp[] >>
  qexistsl_tac [
    `<|bb_label := fresh_label_output "enc_dyn_hdr" labels;
       bb_instructions := abiStaticLoopCode$abi_static_loop_header id v labels len|>`,
    `mk_inst (id+6) JNZ [Var (compiler_var_name v 3);
       Label (fresh_label_output "enc_dyn_exit" (labels+2));
       Label (fresh_label_output "enc_dyn_body" (labels+1))] []`,
    `fresh_label_output "enc_dyn_exit" (labels+2)`] >>
  simp[Abbr `hs`, abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
    abiStaticLoopCodeTheory.abi_static_loop_header_def,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
    get_instruction_def, mk_inst_def, is_terminator_def] >>
  fs[abiStaticLoopCodeTheory.abi_static_loop_header_def,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, venomStateTheory.update_var_def,
    venomStateTheory.eval_operand_def, lookup_var_update_var, bool_to_word_def,
    Abbr `post`, venomStateTheory.jump_to_def, vars_kept_def] >>
  fs[EVERY_DEF, vars_kept_def] >> rpt strip_tac >>
  simp[venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    abiStaticLoopCodeTheory.compiler_var_name_add,
    abiStaticLoopCodeTheory.compiler_var_name_def,
    ASCIInumbersTheory.toString_11] >>
  metis_tac[venomStateTheory.lookup_var_def,
    abiStaticLoopCodeTheory.compiler_var_name_def]
QED
Resume encode_static_round_outcome[body]:
  qabbrev_tac `bs = jump_to (fresh_label_output "enc_dyn_body" (labels+1)) hs` >>
  `fuel_outcome G ctx fn hs 1 (\t. t = bs)` by
    suspend "header_jump" >>
  `?j. j <= 1 /\ fuel_outcome G ctx fn bs j post` suffices_by
    (strip_tac >>
     qpat_assum `fuel_outcome G ctx fn hs 1 _`
       (mp_then Any mp_tac fuel_outcome_compose) >>
     disch_then (qspecl_then [`post`, `1`] mp_tac) >> simp[] >>
     metis_tac[]) >>
  suspend "body_work"
QED
Resume encode_static_round_outcome[header_jump]:
  irule fuel_outcome_jump >> conj_tac >- simp[] >>
  qexistsl_tac [
    `<|bb_label := fresh_label_output "enc_dyn_hdr" labels;
       bb_instructions := abiStaticLoopCode$abi_static_loop_header id v labels len|>`,
    `mk_inst (id+6) JNZ [Var (compiler_var_name v 3);
       Label (fresh_label_output "enc_dyn_exit" (labels+2));
       Label (fresh_label_output "enc_dyn_body" (labels+1))] []`,
    `fresh_label_output "enc_dyn_body" (labels+1)`] >>
  simp[Abbr `hs`, Abbr `bs`,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
    abiStaticLoopCodeTheory.abi_static_loop_header_def,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def,
    get_instruction_def, mk_inst_def, is_terminator_def] >>
  fs[abiStaticLoopCodeTheory.abi_static_loop_header_def,
    abiEncoderArrayHeaderTheory.abi_encode_array_header_insts_def, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, venomStateTheory.update_var_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, bool_to_word_def,
    abiStaticLoopCodeTheory.compiler_var_name_def,
    ASCIInumbersTheory.toString_11]
QED
Resume encode_static_round_outcome[body_work]:
  qabbrev_tac `code = abi_static_loop_body_work id v labels dst src info asz msz` >>
  qabbrev_tac `R = \t. ?out. run_inst_seq code bs = OK out /\
    t = out with vs_inst_idx := LENGTH code` >>
  `fuel_outcome G ctx fn bs 0 R` by
    (irule encode_static_sequence_outcome >>
     qexistsl_tac [
       `<|bb_label := fresh_label_output "enc_dyn_body" (labels+1);
          bb_instructions := abiStaticLoopCode$abi_static_loop_body id v labels dst src info asz msz|>`,
       `code`, `[mk_inst (id+16+static_info_id_count info) JMP
         [Label (fresh_label_output "enc_dyn_hdr" labels)] []]`] >>
     simp[Abbr `bs`, Abbr `hs`,
       abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
       venomStateTheory.update_var_def, venomStateTheory.jump_to_def,
       abi_static_loop_body_split, Abbr `code`, abi_static_loop_body_work_straight] >>
     rpt strip_tac >>
     simp[Abbr `R`, abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
       venomStateTheory.update_var_def, venomStateTheory.jump_to_def] >>
     metis_tac[]) >>
  qpat_assum `fuel_outcome G ctx fn bs 0 R`
    (mp_then Any mp_tac fuel_outcome_compose) >>
  disch_then (qspecl_then [`post`, `1`] mp_tac) >> simp[] >>
  impl_tac >- suspend "backedge" >> simp[]
QED
Resume encode_static_round_outcome[backedge]:
  gen_tac >> simp[Abbr `R`] >> strip_tac >>
  `out.vs_current_bb = bs.vs_current_bb` by
    (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
     qexists_tac `code` >> goal_assum (drule_at Any) >>
     rpt strip_tac >>
     irule (cj 1 venomInstPropsTheory.step_preserves_control_flow) >>
     qexistsl_tac [`ctx`, `G`, `i`] >>
     mp_tac abi_static_loop_body_work_straight >>
     disch_then (qspecl_then [`id`, `v`, `labels`, `dst`, `src`, `info`, `asz`, `msz`] mp_tac) >>
     simp[EVERY_MEM] >> strip_tac >>
     fs[Abbr `code`, step_inst_non_invoke] >> metis_tac[]) >>
  qexists_tac `1` >> simp[] >>
  irule fuel_outcome_jump >> conj_tac >- simp[] >>
  qexistsl_tac [
    `<|bb_label := fresh_label_output "enc_dyn_body" (labels+1);
       bb_instructions := abiStaticLoopCode$abi_static_loop_body id v labels dst src info asz msz|>`,
    `mk_inst (id+16+static_info_id_count info) JMP
       [Label (fresh_label_output "enc_dyn_hdr" labels)] []`,
    `fresh_label_output "enc_dyn_hdr" labels`] >>
  simp[abi_static_loop_body_split, GSYM markerTheory.Abbrev_def] >>
  `bs.vs_current_bb = fresh_label_output "enc_dyn_body" (labels+1)` by
    simp[Abbr `bs`, venomStateTheory.jump_to_def] >>
  fs[abi_static_loop_body_split, GSYM markerTheory.Abbrev_def] >>
  simp[is_terminator_def, step_inst_base_opcode_eqs, mk_inst_def,
    get_instruction_def, EL_APPEND_EQN] >>
  strip_tac >> suspend "post"
QED
Resume encode_static_round_outcome[post]:
  `eval_operand (Var (compiler_var_name v 0)) bs = SOME p` by
    (simp[Abbr `bs`, Abbr `hs`,
      abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
      venomStateTheory.update_var_def, venomStateTheory.jump_to_def,
      venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE,
      abiStaticLoopCodeTheory.compiler_var_name_def,
      ASCIInumbersTheory.toString_11] >>
     fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
       abiStaticLoopCodeTheory.compiler_var_name_def]) >>
  `mload (w2n p) bs = mload (w2n p) s` by
    simp[Abbr `bs`, Abbr `hs`,
      abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
      venomStateTheory.update_var_def, venomStateTheory.jump_to_def,
      venomStateTheory.mload_def] >>
  `mload (w2n p) out = mload (w2n p) s + 1w` by
    (qpat_assum `run_inst_seq code bs = OK out` mp_tac >>
     simp[Abbr `code`] >>
     drule_all encode_static_body_work_counter >> simp[]) >>
  suspend "frames_countdown"
QED
Resume encode_static_round_outcome[frames_countdown]:
  `eval_operand (Var (compiler_var_name v 0)) out = SOME p` by
    (fs[Abbr `code`] >>
     qpat_assum `run_inst_seq _ bs = OK out`
       (mp_then Any mp_tac encode_static_body_work_frame) >>
     disch_then (qspec_then `Var (compiler_var_name v 0)` mp_tac) >>
     simp[abi_static_loop_body_names_def,
       abiStaticLoopCodeTheory.compiler_var_name_def,
       ASCIInumbersTheory.toString_11] >>
     Cases_on `info` >> simp[]) >>
  `vars_kept N {} bs out` by
    (fs[Abbr `code`] >> drule_all encode_static_body_work_vars_kept >> simp[]) >>
  `vars_kept N {} s bs` by
    (simp[vars_kept_def, Abbr `bs`, Abbr `hs`,
      abiEncoderArrayHeaderTheory.abi_encode_array_header_state_def,
      venomStateTheory.update_var_def, venomStateTheory.jump_to_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     rpt strip_tac >> rpt IF_CASES_TAC >> gvs[]) >>
  `vars_kept N {} initial out` by metis_tac[vars_kept_trans] >>
  simp[Abbr `post`, venomStateTheory.jump_to_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
    vars_kept_def, venomStateTheory.mload_def] >>
  suspend "countdown"
QED
Resume encode_static_round_outcome[countdown]:
  `w2n (mload (w2n p) s) + 1 < dimword (:256)` by
    (mp_tac (wordsTheory.w2n_lt |> Q.ISPEC `nw:bytes32`) >> decide_tac) >>
  `w2n (mload (w2n p) s + 1w) = w2n (mload (w2n p) s) + 1` by
    simp[wordsTheory.w2n_add_2] >>
  disj2_tac >>
  fs[venomStateTheory.mload_def, vars_kept_def,
    venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  decide_tac
QED
Finalise encode_static_round_outcome

(* The loop counter lives in a buffer the function allocates itself and
   starts at 0.  Each round, while the counter is below len_op (unsigned),
   encodes one element with straight-line code (no calls back into the
   encoder) and adds 1, then jumps back to the header.  len_op is a
   parameter: when it is a variable it was allocated before the call, and
   the body writes only variables it allocates itself, so the bound stays
   fixed.  The counter is at most len_op < 2 ** 256, so it does not wrap
   and the loop leaves within 2 ** 256 rounds. The final counter store
   repairs any intervening aliasing writes by the element encoder. *)
Theorem fuel_okS_compile_abi_encode_dyn_static_loop:
  !dst src elem_info elem_abi_sz elem_mem_sz len_op Wv E.
    fuel_okS (\st. !x. len_op = Var x ==> var_below st.cs_next_var x) Wv {} E
      (compile_abi_encode_dyn_static_loop dst src elem_info elem_abi_sz
         elem_mem_sz len_op)
Proof
  rpt gen_tac >> simp_tac bool_ss [fuel_okS_def] >> rpt gen_tac >> strip_tac >>
  `cs_extends st st' /\ st.cs_next_var <= st'.cs_next_var` by
    (drule (abiEncoderArrayContextTheory.abi_encode_array_loop_bounds |>
       Q.INST [`active` |-> `F`] |> SIMP_RULE bool_ss []) >> simp[]) >>
  simp[] >> conj_tac >- metis_tac[encode_static_loop_no_phi] >>
  qexists_tac `1 + dimword (:256) * 2` >>
  simp_tac bool_ss [frag_fuel_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_abi_encode_dyn_static_loop_contains >> strip_tac >>
  fs[pred_setTheory.NOT_IN_EMPTY] >>
  suspend "runtime"
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[runtime]:
  qabbrev_tac `es = abi_static_loop_entry_state st.cs_next_id st.cs_next_var s
    with vs_inst_idx := s.vs_inst_idx + 2` >>
  `fuel_outcome G ctx fn s 0 (\t. t = es)` by
    (irule encode_static_sequence_outcome >>
     qexistsl_tac [
       `<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
          abi_static_loop_entry st.cs_next_id st.cs_next_var st.cs_next_label|>`,
       `TAKE 2 (abi_static_loop_entry st.cs_next_id st.cs_next_var st.cs_next_label)`,
       `[mk_inst (st.cs_next_id + 2) JMP
         [Label (fresh_label_output "enc_dyn_hdr" st.cs_next_label)] []]`] >>
     fs[at_point_def] >>
     simp[abi_static_loop_entry_execution, Abbr `es`] >>
     simp[abiStaticLoopCodeTheory.abi_static_loop_entry_def, mk_inst_def, is_terminator_def,
       DROP_LENGTH_APPEND]) >>
  qpat_assum `fuel_outcome G ctx fn s 0 _`
    (mp_then Any mp_tac fuel_outcome_compose) >>
  disch_then (qspec_then
    `\t. vars_kept N Wv s t /\ (at_point st' t \/
      t.vs_current_bb IN E /\ t.vs_inst_idx = 0)` mp_tac) >>
  disch_then (qspec_then `1 + dimword (:256) * 2` mp_tac) >> simp[] >>
  impl_tac >- suspend "entry_jump" >> simp[]
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[entry_jump]:
  qabbrev_tac `hs = jump_to (fresh_label_output "enc_dyn_hdr" st.cs_next_label) es` >>
  `fuel_outcome G ctx fn es 1 (\t. t = hs)` by
    (irule fuel_outcome_jump >> conj_tac >- simp[] >>
     qexistsl_tac [
       `<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
          abi_static_loop_entry st.cs_next_id st.cs_next_var st.cs_next_label|>`,
       `mk_inst (st.cs_next_id+2) JMP
         [Label (fresh_label_output "enc_dyn_hdr" st.cs_next_label)] []`,
       `fresh_label_output "enc_dyn_hdr" st.cs_next_label`] >>
     simp[Abbr `es`, Abbr `hs`, abi_static_loop_entry_state_def,
       abi_static_loop_alloc_frame_def, venomStateTheory.mstore_def,
       venomStateTheory.update_var_def] >>
     fs[at_point_def] >> Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
     simp[abiStaticLoopCodeTheory.abi_static_loop_entry_def, get_instruction_def,
       EL_APPEND_EQN, mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs,
       venomStateTheory.eval_operand_def]) >>
  qpat_assum `fuel_outcome G ctx fn es 1 _`
    (mp_then Any mp_tac fuel_outcome_compose) >>
  disch_then (qspecl_then [
    `\t. vars_kept N Wv s t /\ (at_point st' t \/
      t.vs_current_bb IN E /\ t.vs_inst_idx = 0)`, `dimword (:256) * 2`] mp_tac) >>
  simp[] >> impl_tac >- suspend "iterate" >> simp[]
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[iterate]:
  qabbrev_tac `p = abi_static_loop_counter_addr st.cs_next_id s` >>
  qabbrev_tac `H = \t. t.vs_current_bb = fresh_label_output "enc_dyn_hdr" st.cs_next_label /\
    t.vs_inst_idx = 0 /\ eval_operand (Var (compiler_var_name st.cs_next_var 0)) t = SOME p /\
    vars_kept N {} s t` >>
  qabbrev_tac `Q = \t. t.vs_current_bb = fresh_label_output "enc_dyn_exit" (st.cs_next_label+2) /\
    t.vs_inst_idx = 0 /\ vars_kept N {} s t` >>
  qabbrev_tac `mu = \t. dimword (:256) - 1 - w2n (mload (w2n p) t)` >>
  `!t. H t ==> ?j. j <= 2 /\ fuel_outcome G ctx fn t j
    (\u. Q u \/ (H u /\ mu u < mu t))` by
    suspend "round" >>
  `H hs` by suspend "initial" >>
  `?j. j <= dimword (:256) * 2 /\ fuel_outcome G ctx fn hs j Q` by
    (irule fuel_outcome_iterate >>
     qexistsl_tac [`H`, `mu`] >> simp[] >>
     simp[Abbr `mu`, encode_static_countdown_range]) >>
  qpat_assum `fuel_outcome G ctx fn hs j Q`
    (mp_then Any mp_tac fuel_outcome_compose) >>
  disch_then (qspecl_then [
    `\t. vars_kept N Wv s t /\ (at_point st' t \/
      t.vs_current_bb IN E /\ t.vs_inst_idx = 0)`, `0`] mp_tac) >>
  simp[] >> impl_tac >- suspend "exit_suffix" >> strip_tac >>
  qexists_tac `j'` >> simp[] >> decide_tac
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[round]:
  `len_op <> Var (compiler_var_name st.cs_next_var 1) /\
   EVERY (\name. ~var_below N name)
     ([compiler_var_name st.cs_next_var 1; compiler_var_name st.cs_next_var 2;
       compiler_var_name st.cs_next_var 3] ++ abi_static_loop_body_names st.cs_next_var elem_info)` by
    suspend "freshness" >>
  drule_all encode_static_round_outcome >>
  disch_then (qspecl_then [`G`, `ctx`, `s`, `p`] mp_tac) >>
  simp[Abbr `H`, Abbr `Q`, Abbr `mu`]
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[initial]:
  simp[Abbr `H`, Abbr `hs`, Abbr `es`, Abbr `p`,
    venomStateTheory.jump_to_def, abi_static_loop_entry_state_def,
    ssaOperandFrameTheory.eval_operand_mstore_eq,
    emitHelperPropsTheory.eval_operand_update_var,
    vars_kept_def] >>
  rpt strip_tac >> rename1 `var_below N name` >>
  `name <> compiler_var_name st.cs_next_var 0` by
    (fs[var_below_def, abiStaticLoopCodeTheory.compiler_var_name_def] >> metis_tac[]) >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.mstore_def,
    venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    abi_static_loop_alloc_frame_def] >> IF_CASES_TAC >> simp[]
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[exit_suffix]:
  gen_tac >> simp[Abbr `Q`] >> strip_tac >>
  irule encode_static_sequence_outcome >>
  fs[IS_PREFIX_APPEND] >>
  qexistsl_tac [
    `abi_static_loop_exit st.cs_next_id st.cs_next_var src elem_info elem_abi_sz`, `l`] >>
  simp[abi_static_loop_exit_straight] >> rpt strip_tac >>
  suspend "exit_post"
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[freshness]:
  simp[EVERY_APPEND, abi_static_loop_body_names_def,
    abiStaticLoopCodeTheory.compiler_var_name_add,
    abiStaticLoopCodeTheory.compiler_var_name_def, var_below_def] >>
  conj_tac >- (strip_tac >> first_x_assum (qspec_then
    `STRING #"%" (toString (st.cs_next_var+1))` mp_tac) >>
    simp[var_below_def] >> metis_tac[arithmeticTheory.LE_ADD]) >>
  Cases_on `elem_info` >> simp[] >> rpt conj_tac >>
  qexists_tac `st.cs_next_var + 1` >> simp[] >> decide_tac
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[exit_post]:
  markerLib.RESUME_TAC
  >- (disj1_tac >>
      `t'.vs_current_bb = t.vs_current_bb` by
        (irule exprLoweringPropsTheory.run_inst_seq_preserves_field >>
         goal_assum (drule_at Any) >> rpt strip_tac >>
         irule (cj 1 venomInstPropsTheory.step_preserves_control_flow) >>
         qexistsl_tac [`ctx`, `G`, `i`] >>
         fs[abiStaticLoopCodeTheory.abi_static_loop_exit_def, mk_inst_def,
           is_terminator_def, step_inst_non_invoke] >> metis_tac[]) >>
      qpat_x_assum `compile_abi_encode_dyn_static_loop _ _ _ _ _ _ _ = _` mp_tac >>
      simp[abiStaticLoopCodeTheory.compile_abi_encode_dyn_static_loop_result] >>
      strip_tac >> gvs[at_point_def]) >>
  suspend "exit_frame"
QED
Resume fuel_okS_compile_abi_encode_dyn_static_loop[exit_frame]:
  simp[vars_kept_def] >> rpt strip_tac >> rename1 `var_below N name` >>
  `eval_operand (Var name) t' = eval_operand (Var name) t` by
    (drule run_inst_seq_operand_frame >>
     disch_then (qspec_then `Var name` mp_tac) >>
     impl_tac
     >- (simp[abiStaticLoopCodeTheory.abi_static_loop_exit_def, mk_inst_def,
           is_terminator_def, abiStaticLoopCodeTheory.compiler_var_name_def] >>
         fs[var_below_def] >> metis_tac[arithmeticTheory.LE_ADD,
           arithmeticTheory.LESS_EQ_TRANS]) >> simp[]) >>
  fs[vars_kept_def, venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def]
QED
Finalise fuel_okS_compile_abi_encode_dyn_static_loop
