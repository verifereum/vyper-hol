Theory bodyFullAbiDecodeCallerOperands
Ancestors exprLoweringProps[qualified,ignore_grammar] exprSimAbiDecodeResourceShape exprSimAbiDecodeResourcePrims
  exprSimAbiDecodeShape exprSimAbiDecodeTraceSafe exprSimAbiDecodeResource
  exprSimAbiDecodeTrace exprSimAbiEncodeObliviousLabels exprSimAbiEncodeObliviousContext
  exprSimAbiDecodeSiteCoverage abiDecoderLoopEmit abiDecoderLoopCode abiEncoder builtinAbi
  abiBuiltinDecodeHeader abiBuiltinLengthGuard abiBuiltinBoundTests
  abiDecoderExecution abiDecoderLoopSetup abiDecoderIndexedAddress abiDecoderArraySetupCode
  compileEnv emitHelper emitHelperProps fragExec exprSimAbiGasBridge abiDecoderRange
  context venomInst list rich_list sorting pred_set

(* A label operand is harmless for this syntactic test if the action
   opened that label itself. The result condition tracks data operands. *)
val operand_action = ``\ex post m. !a v b. m a = (v,b) ==>
  cs_extends a b /\ post v /\
  (~MEM ex (opened_labels a b) ==>
   EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code a b))``;

Theorem decode_operand_entry_shape[local]:
  cs_extends a b ==> entry_shape a b
Proof
  rw[cs_extends_def] >> Cases_on `new = []`
  >- gvs[entry_shape_def, IS_PREFIX_APPEND] >>
  gvs[entry_shape_def, IS_PREFIX_APPEND] >>
  qexistsl_tac [`FRONT new`, `l`] >>
  `LAST new = <|bb_label := a.cs_current_bb;
                 bb_instructions := a.cs_current_insts ++ l|>` by
    simp[basic_block_component_equality] >>
  drule APPEND_FRONT_LAST >> simp[]
QED

Theorem decode_operand_compose[local]:
  cs_extends a b /\ cs_extends b c /\
  (~MEM ex (opened_labels a b) ==>
    EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code a b)) /\
  (~MEM ex (opened_labels b c) ==>
    EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code b c)) ==>
  cs_extends a c /\
  (~MEM ex (opened_labels a c) ==>
    EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code a c))
Proof
  strip_tac >> conj_tac >- metis_tac[cs_extends_trans] >>
  `opened_labels a c = opened_labels a b ++ opened_labels b c` by
    metis_tac[opened_labels_compose, decode_operand_entry_shape] >>
  simp[] >> strip_tac >>
  drule_all abi_decode_frag_code_compose >> simp[EVERY_MEM] >>
  gvs[EVERY_MEM]
  >> (metis_tac[])
QED

Theorem decode_operand_bind[local]:
  ^operand_action ex mid m /\
  (!v. mid v ==> ^operand_action ex post (f v)) ==>
  ^operand_action ex post (comp_bind m f)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> simp[comp_bind_def] >>
  Cases_on `m a` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  simp[] >> metis_tac[decode_operand_compose]
QED

Theorem decode_straight_operand_action[local]:
  decode_straight ex m post /\
  (!a v b. m a = (v,b) ==> a.cs_blocks = b.cs_blocks) ==>
  ^operand_action ex post m
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `decode_straight _ _ _` mp_tac >>
  rewrite_tac[decode_straight_def] >>
  disch_then (qspecl_then [`a`, `EMPTY`] mp_tac) >> simp[] >> strip_tac >>
  drule decode_resource_run_trace >> strip_tac >> gvs[] >>
  `a.cs_blocks = (decode_replay es a).cs_blocks` by
    (qpat_x_assum `b = decode_history _ _` (mp_tac o AP_TERM ``\s:compile_state. s.cs_blocks``) >>
     simp[decode_history_def] >> metis_tac[]) >>
  `decode_switches es = []` by
    (mp_tac (Q.SPECL [`es`, `a`] decode_replay_labels_raw) >>
     disch_then (mp_tac o AP_TERM ``LENGTH : string list -> num``) >> simp[]) >>
  conj_tac >- metis_tac[decode_history_extends, decode_replay_extends] >>
  fs[decode_trace_safe_def] >> strip_tac >>
  metis_tac[decode_replay_frag_code_history, PERM_EVERY]
QED

fun operand_action_at ty = Term.inst [Type.alpha |-> ty] operand_action;
val operand_result = operand_action_at ``:operand``;
val void_result = operand_action_at ``:unit``;

Theorem decode_operand_emit[local]:
  (~MEM (Label ex) ops ==>
   ^operand_result ex (\v. v <> Label ex) (emit_op opc ops)) /\
  (~MEM (Label ex) ops ==>
   ^void_result ex (\u. T) (emit_void opc ops))
Proof
  BETA_TAC >> simp[emit_op_def, emit_void_def, emit_inst_def, fresh_var_def,
    fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[cs_extends_def, frag_code_def, emitted_blocks_def,
    exprLoweringPropsTheory.emitted_insts_def, DROP_APPEND, IS_PREFIX_APPEND, mk_inst_def]
QED

val buffer_result = operand_action_at ``:buffer``;

Theorem decode_addr_blocks[local]:
  compile_abi_dec_addr base_op src a = (v,b) ==> a.cs_blocks = b.cs_blocks
Proof
  Cases_on `base_op = Lit 0w` >-
    simp[compile_abi_dec_addr_def, comp_return_def] >>
  simp[compile_abi_dec_addr_def, emit_op_def, emit_inst_def,
       fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem decode_operand_alloc[local]:
  ^buffer_result ex (\b. b.buf_operand <> Label ex) (compile_alloc_buffer n)
Proof
  match_mp_tac (Q.INST [`m` |-> `compile_alloc_buffer n`,
    `post` |-> `\v:buffer. v.buf_operand <> Label ex`]
      (INST_TYPE [Type.alpha |-> ``:buffer``] decode_straight_operand_action)) >>
  conj_tac >- MATCH_ACCEPT_TAC decode_straight_alloc_buffer >>
  rpt gen_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_inst_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem decode_operand_addr[local]:
  base_op <> Label ex /\ src <> Label ex ==>
  ^operand_result ex (\v. v <> Label ex) (compile_abi_dec_addr base_op src)
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`m` |-> `compile_abi_dec_addr base_op src`,
    `post` |-> `\v:operand. v <> Label ex`]
      (INST_TYPE [Type.alpha |-> ``:operand``] decode_straight_operand_action)) >>
  conj_tac >- simp[decode_straight_dec_addr] >>
  rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC decode_addr_blocks
QED

Theorem decode_operand_range[local]:
  src <> Label ex /\ e <> Label ex /\ hi <> Label ex ==>
  ^void_result ex (\u. T) (compile_abi_decode_range_check src e hi)
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`m` |-> `compile_abi_decode_range_check src e hi`,
    `post` |-> `\u:unit. T`]
      (INST_TYPE [Type.alpha |-> ``:unit``] decode_straight_operand_action)) >>
  conj_tac >- simp[decode_straight_range_check] >>
  rpt gen_tac >> Cases_on `v` >> strip_tac >>
  drule compile_abi_decode_range_check_fragment_shape >> simp[]
QED

Theorem decode_operand_getelem[local]:
  src <> Label ex /\ base_op <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN ==>
  ^operand_result ex (\v. v <> Label ex) (compile_getelemptr_abi src dyn off opc base_op hi)
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`m` |-> `compile_getelemptr_abi src dyn off opc base_op hi`,
    `post` |-> `\v:operand. v <> Label ex`]
      (INST_TYPE [Type.alpha |-> ``:operand``] decode_straight_operand_action)) >>
  conj_tac >- simp[decode_straight_getelemptr] >>
  rpt gen_tac >> Cases_on `dyn` >> Cases_on `base_op = Lit 0w` >>
  Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, compile_abi_dec_addr_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, emit_inst_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[]
QED

Theorem decode_operand_dynptr[local]:
  base_op <> Label ex /\ head <> Label ex /\ src <> Label ex /\ hi <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN ==>
  ^operand_result ex (\v. v <> Label ex)
    (compile_abi_decode_dyn_elem_ptr opc base_op head src hi sz)
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`m` |-> `compile_abi_decode_dyn_elem_ptr opc base_op head src hi sz`,
    `post` |-> `\v:operand. v <> Label ex`]
      (INST_TYPE [Type.alpha |-> ``:operand``] decode_straight_operand_action)) >>
  conj_tac >- simp[decode_straight_dyn_elem_ptr] >>
  rpt gen_tac >> Cases_on `base_op = Lit 0w` >> Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, emit_inst_def, fresh_id_def,
    fresh_var_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem decode_operand_static[local]:
  src <> Label ex /\ dst <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN ==>
  ^void_result ex (\u. T)
    (compile_abi_decode_static src dst opc (\v. compile_abi_clamp_basetype v c))
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`m` |-> `compile_abi_decode_static src dst opc (\v. compile_abi_clamp_basetype v c)`,
    `post` |-> `\u:unit. T`]
      (INST_TYPE [Type.alpha |-> ``:unit``] decode_straight_operand_action)) >>
  conj_tac >- simp[decode_straight_static, decode_straight_clamp_basetype] >>
  rpt gen_tac >> Cases_on `c` >>
  simp[compile_abi_decode_static_def, compile_abi_clamp_basetype_def,
    compile_abi_int_clamp_def, compile_abi_bytes_clamp_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
    SF boolSimps.LIFT_COND_ss] >>
  rpt strip_tac >> gvs[boolTheory.COND_EXPAND_IMP] >>
  rename1 `~signed ==> _ = _` >> Cases_on `signed` >> gvs[]
QED

val operand_result_any = operand_action_at ``:'b``;

Theorem decode_operand_ignore_bind[local]:
  ^operand_action ex (\v. T) m /\ ^operand_result_any ex post n ==>
  ^operand_result_any ex post (comp_ignore_bind m n)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >>
  simp[comp_ignore_bind_def, comp_bind_def] >> Cases_on `m a` >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[] >> metis_tac[decode_operand_compose]
QED

(* Normalize only the proof-rule interface, leaving compiler combinators intact. *)
fun operand_rule rule = simpLib.SIMP_RULE bool_ss [] rule;
Theorem decode_operand_bind_poly[local]:
  ^operand_action ex mid m /\
  (!v. mid v ==> ^operand_result_any ex post (f v)) ==>
  ^operand_result_any ex post (comp_bind m f)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> simp[comp_bind_def] >>
  Cases_on `m a` >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  simp[] >> metis_tac[decode_operand_compose]
QED

val operand_bind_unit =
  operand_rule (Q.INST [`post` |-> `\v:unit. T`]
     (INST_TYPE [``:'b`` |-> ``:unit``] decode_operand_bind_poly));
val operand_ignore_unit =
  operand_rule (Q.INST [`post` |-> `\v:unit. T`]
     (INST_TYPE [``:'b`` |-> ``:unit``] decode_operand_ignore_bind));

val operand_bind_word =
  operand_rule (Q.INST [`post` |-> `\v:operand. v <> Label ex`]
     (INST_TYPE [Type.alpha |-> ``:operand``] decode_operand_bind));
val operand_ignore_word =
  operand_rule (Q.INST [`post` |-> `\v:operand. v <> Label ex`]
     (INST_TYPE [``:'b`` |-> ``:operand``] decode_operand_ignore_bind));

fun operand_leaf th = match_mp_tac (GEN_ALL (operand_rule th)) >> simp[];
val operand_emit_word = operand_leaf (CONJUNCT1 decode_operand_emit);
val operand_emit_void = operand_leaf (CONJUNCT2 decode_operand_emit);
fun operand_bind_with rule mid tac =
  match_mp_tac (GEN_ALL rule) >> qexists_tac mid >> BETA_TAC >>
  conj_tac >- tac >> gen_tac >> disch_tac;
val operand_bind_to_unit = operand_bind_with operand_bind_unit `\v. v <> Label ex`;
fun operand_ignore rule tac = match_mp_tac (GEN_ALL rule) >> conj_tac >- tac;
val operand_ret = simp[comp_return_def, cs_extends_refl, frag_code_def,
    emitted_blocks_def, exprLoweringPropsTheory.emitted_insts_def];

Theorem decode_operand_head[local]:
  src <> Label ex /\ hi <> Label ex ==>
  ^operand_result ex (\v. v <> Label ex)
    (if hi = Lit 0w then comp_return (Lit 0w)
     else do h <- emit_op ADD [src; Lit 32w];
             compile_abi_decode_range_check src h hi; comp_return h od)
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >> simp[] >- operand_ret >>
  operand_bind_with operand_bind_word `\v. v <> Label ex` operand_emit_word >>
  operand_ignore operand_ignore_word (operand_leaf decode_operand_range) >>
  operand_ret
QED

Theorem decode_operand_copy[local]:
  d <> Label ex /\ s <> Label ex /\ n <> Label ex ==>
  ^void_result ex (\u. T)
    (case opc of
       CALLDATALOAD => emit_void CALLDATACOPY [d;s;n]
     | DLOAD => emit_void DLOADBYTES [d;s;n]
     | _ => emit_void MCOPY [d;s;n])
Proof
  strip_tac >> Cases_on `opc` >> simp[] >> operand_emit_void
QED

Theorem decode_operand_loop_prefix[local]:
  abi_decode_loop_prefix ip src opc bop a = ((hdr_lbl,body_lbl,exit_lbl),b) /\
  ip <> Label ex /\ src <> Label ex /\ bop <> Label ex ==>
  opened_labels a b = [hdr_lbl;body_lbl] /\
  (ex <> hdr_lbl /\ ex <> body_lbl /\ ex <> exit_lbl ==>
   EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code a b))
Proof
  simp[abi_decode_loop_prefix_shape] >> strip_tac >> gvs[] >>
  Cases_on `bop = Lit 0w` >>
  simp[abi_decode_loop_prefix_state_def, opened_labels_def, frag_code_def,
       emitted_blocks_def, abi_decode_position_header_insts_def,
       DROP_LENGTH_APPEND, mk_inst_def, arithmeticTheory.ADD1] >> metis_tac[]
QED

Theorem decode_operand_loop_suffix[local]:
  abi_decode_loop_suffix ip (Var iv) hdr exit_lbl a = ((),b) /\ ip <> Label ex ==>
  opened_labels a b = [exit_lbl] /\
  (ex <> hdr ==> EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code a b))
Proof
  simp[abi_decode_loop_suffix_shape] >> strip_tac >> gvs[] >>
  simp[abi_decode_loop_suffix_state_def, opened_labels_def, frag_code_def,
       emitted_blocks_def, abi_decode_backedge_insts_def, DROP_LENGTH_APPEND, mk_inst_def]
QED

val elem_result = operand_action_at ``:operand # operand # operand``;
val elem_post = ``\v:operand # operand # operand.
  FST (SND v) <> Label ex /\ SND (SND v) <> Label ex``;
val operand_bind_elem = operand_rule (Q.INST [`post` |-> `^elem_post`]
  (INST_TYPE [``:'b`` |-> ``:operand # operand # operand``] decode_operand_bind_poly));

Theorem decode_operand_indexed[local]:
  dst <> Label ex /\ idx <> Label ex ==>
  ^operand_result ex (\v. v <> Label ex) (abi_decode_indexed_address dst idx msz)
Proof
  strip_tac >> simp[abi_decode_indexed_address_def] >>
  ntac 2 (operand_bind_with operand_bind_word `\v. v <> Label ex` operand_emit_word) >>
  operand_emit_word
QED

Theorem decode_operand_element_setup[local]:
  ip <> Label ex /\ src <> Label ex /\ dst <> Label ex /\ bop <> Label ex /\ hi <> Label ex /\
  opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN ==>
  ^elem_result ex ^elem_post (abi_decode_array_element_setup ip src dst opc bop hi info asz msz)
Proof
  strip_tac >> simp[abi_decode_array_element_setup_def] >>
  ntac 4 (operand_bind_with operand_bind_elem `\v. v <> Label ex` operand_emit_word) >>
  operand_bind_with operand_bind_elem `\v. v <> Label ex`
    (Cases_on `dec_info_needs_offset info` >> simp[]
     >- operand_leaf decode_operand_dynptr >> operand_ret) >>
  operand_bind_with operand_bind_elem `\v. v <> Label ex`
    (operand_leaf decode_operand_indexed) >>
  operand_ret
QED

Theorem decode_operand_mutual[local]:
  (!dst src opc bop hi info. !ex.
    opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
    dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex ==>
    ^void_result ex (\u. T) (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo. !ex.
    opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
    dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex ==>
    ^void_result ex (\u. T) (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi info asz msz ip cnt. !ex.
    opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\ opc <> STOP /\ opc <> RETURN /\
    dst <> Label ex /\ src <> Label ex /\ bop <> Label ex /\ hi <> Label ex /\
    ip <> Label ex /\ cnt <> Label ex ==>
    ^void_result ex (\u. T) (compile_abi_decode_dyn_loop dst src opc bop hi info asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> simp[Once compile_abi_decode_to_buf_def] >>
      match_mp_tac (GEN_ALL operand_bind_unit) >> qexists_tac `\v. v <> Label ex` >>
      BETA_TAC >>
      conj_tac >- (match_mp_tac (GEN_ALL (operand_rule decode_operand_addr)) >> simp[]) >>
      gen_tac >> disch_tac >> match_mp_tac (GEN_ALL (operand_rule decode_operand_static)) >> simp[])
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- (strip_tac >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
      simp[comp_return_def, cs_extends_refl, frag_code_def, emitted_blocks_def,
           exprLoweringPropsTheory.emitted_insts_def])
  >- suspend "elems"
  >> suspend "loop"
QED

Resume decode_operand_mutual[bytes]:
  strip_tac >> once_rewrite_tac[compile_abi_decode_to_buf_def] >>
  simp[] >> operand_bind_to_unit (operand_leaf decode_operand_head) >>
  operand_bind_to_unit (operand_leaf decode_operand_addr) >>
  ntac 3 (operand_bind_to_unit operand_emit_word) >>
  operand_ignore operand_ignore_unit operand_emit_void >>
  operand_ignore operand_ignore_unit
    (Cases_on `hi = Lit 0w` >> simp[] >- operand_ret >>
     operand_bind_to_unit operand_emit_word >> operand_leaf decode_operand_range) >>
  Cases_on `bop = Lit 0w` >> simp[LET_THM] >- operand_leaf decode_operand_copy >>
  ntac 4 (operand_bind_to_unit operand_emit_word) >>
  operand_ignore operand_ignore_unit operand_emit_void >>
  operand_bind_to_unit operand_emit_word >> operand_emit_void
QED

Resume decode_operand_mutual[array]:
  strip_tac >> gen_tac >> strip_tac >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[] >>
  operand_bind_to_unit (operand_leaf decode_operand_head) >>
  operand_bind_to_unit (operand_leaf decode_operand_addr) >>
  ntac 3 (operand_bind_to_unit operand_emit_word) >>
  operand_ignore operand_ignore_unit operand_emit_void >>
  operand_ignore operand_ignore_unit
    (Cases_on `hi = Lit 0w` >> simp[] >- operand_ret >>
     ntac 2 (operand_bind_to_unit operand_emit_word) >> operand_leaf decode_operand_range) >>
  operand_bind_to_unit operand_emit_word >>
  operand_ignore operand_ignore_unit operand_emit_void >>
  simp[LET_THM] >> Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp info` >> simp[]
  >- (ntac 2 (operand_bind_to_unit operand_emit_word) >>
      operand_bind_to_unit (operand_leaf decode_operand_addr) >>
      operand_bind_to_unit operand_emit_word >> operand_leaf decode_operand_copy) >>
  operand_bind_with operand_bind_unit `\b. b.buf_operand <> Label ex`
    (MATCH_ACCEPT_TAC (operand_rule decode_operand_alloc)) >>
  operand_ignore operand_ignore_unit operand_emit_void >>
  qmatch_goalsub_abbrev_tac `b.buf_operand` >>
  rename1 `compile_abi_decode_dyn_loop _ _ _ _ _ _ _ _ b.buf_operand cnt _ = _` >>
  first_x_assum (qspecl_then [`F`, `b.buf_operand`, `b`, `cnt`] mp_tac) >>
  `elem_is_dyn \/ dec_info_needs_clamp info` by metis_tac[] >>
  simp[] >> disch_then (qspec_then `ex` mp_tac) >> simp[]
QED

Resume decode_operand_mutual[complex]:
  strip_tac >> gen_tac >> strip_tac >> Cases_on `hi = Lit 0w` >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[LET_THM] >>
  rpt (operand_bind_to_unit operand_emit_word) >>
  rpt (operand_ignore operand_ignore_unit (operand_leaf decode_operand_range)) >>
  first_x_assum (qspec_then `ex` mp_tac) >> simp[]
QED

Resume decode_operand_mutual[elems]:
  strip_tac >> gen_tac >> strip_tac >> gvs[] >>
  once_rewrite_tac[compile_abi_decode_to_buf_def] >> simp[LET_THM] >>
  operand_bind_to_unit (operand_leaf decode_operand_getelem) >>
  operand_bind_to_unit operand_emit_word >>
  operand_ignore operand_ignore_unit (simp[] >> metis_tac[]) >> simp[] >> metis_tac[]
QED

Resume decode_operand_mutual[loop]:
  disch_then (fn th => assume_tac (operand_rule th)) >> gen_tac >> strip_tac >>
  BETA_TAC >> map_every qx_gen_tac [`a`,`u`,`b`] >> Cases_on `u` >>
  simp[] >> strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  PairCases_on `labels` >> gvs[] >>
  drule_then strip_assume_tac abi_decoder_array_setup_head >>
  gvs[] >>
  drule_then assume_tac abi_decoder_loop_prefix_extends >>
  drule_then assume_tac abi_decoder_loop_suffix_extends >>
  drule_at (Pat `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _`)
    (operand_rule decode_operand_element_setup) >>
  disch_then (qspec_then `ex` mp_tac) >> simp[] >> strip_tac >>
  `cs_extends middle st1 /\
   (~MEM ex (opened_labels middle st1) ==>
    EVERY (\i. ~MEM (Label ex) i.inst_operands) (frag_code middle st1))` by
    (first_x_assum (qspecl_then [`SND (SND ops)`, `FST (SND ops)`, `ex`] mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac (Q.INST [`ex` |-> `ex`] decode_operand_loop_prefix) >>
  drule_all_then strip_assume_tac (Q.INST [`ex` |-> `ex`] decode_operand_loop_suffix) >>
  `cs_extends a st1 /\ cs_extends st0 st1` by metis_tac[cs_extends_trans] >>
  conj_tac >- metis_tac[cs_extends_trans] >> strip_tac >>
  `opened_labels a b = [labels0;labels1] ++
      opened_labels st0 middle ++ opened_labels middle st1 ++ [labels2]` by
    (metis_tac[opened_labels_compose, decode_operand_entry_shape, APPEND_ASSOC]) >>
  fs[MEM_APPEND] >>
  mp_tac (Q.INST [`a` |-> `a`, `b` |-> `st1`, `c` |-> `b`]
    abi_decode_frag_code_compose) >> (impl_tac >- simp[]) >> disch_then assume_tac >>
  mp_tac (Q.INST [`a` |-> `a`, `b` |-> `st0`, `c` |-> `st1`]
    abi_decode_frag_code_compose) >> (impl_tac >- simp[]) >> disch_then assume_tac >>
  mp_tac (Q.INST [`a` |-> `st0`, `b` |-> `middle`, `c` |-> `st1`]
    abi_decode_frag_code_compose) >> (impl_tac >- simp[]) >> disch_then assume_tac >>
  gs[EVERY_MEM, boolTheory.DISJ_IMP_THM, boolTheory.FORALL_AND_THM]
QED
Finalise decode_operand_mutual[local]

val header_result = operand_action_at ``:operand # operand``;
val header_post = ``\p:operand # operand. FST p <> Label ex /\ SND p <> Label ex``;
val operand_bind_header = operand_rule (Q.INST [`post` |-> `^header_post`]
  (INST_TYPE [``:'b`` |-> ``:operand # operand``] decode_operand_bind_poly));
val operand_ignore_header = operand_rule (Q.INST [`post` |-> `^header_post`]
  (INST_TYPE [``:'b`` |-> ``:operand # operand``] decode_operand_ignore_bind));

Theorem decode_operand_length_guard[local]:
  len <> Label ex ==>
  ^void_result ex (\u. T) (abi_builtin_length_guard len mn mx)
Proof
  strip_tac >> Cases_on `mn = mx` >> simp[abi_builtin_length_guard_def]
  >- (simp[abi_builtin_eq_guard_def] >>
      operand_bind_to_unit operand_emit_word >> operand_emit_void) >>
  simp[abi_builtin_interval_guard_def] >>
  ntac 2 (operand_bind_to_unit
    (simp[abi_builtin_bound_test_def] >>
     operand_bind_with operand_bind_word `\v. v <> Label ex` operand_emit_word >>
     operand_emit_word)) >>
  operand_bind_to_unit operand_emit_word >> operand_emit_void
QED

Theorem decode_operand_header[local]:
  data <> Label ex ==>
  ^header_result ex ^header_post (abi_builtin_decode_header data mn mx)
Proof
  strip_tac >> simp[abi_builtin_decode_header_def] >>
  ntac 2 (operand_bind_with operand_bind_header `\v. v <> Label ex` operand_emit_word) >>
  operand_ignore operand_ignore_header (operand_leaf decode_operand_length_guard) >>
  operand_ret
QED

Theorem lower_abi_decode_unopened_operand:
  lower_abi_decode data di mn mx cap a = (out,b) /\ data <> Label x /\
  ~MEM x (opened_labels a b) ==>
  EVERY (\i. ~MEM (Label x) i.inst_operands) (frag_code a b)
Proof
  strip_tac >> drule lower_abi_decode_trace >> strip_tac >>
  drule_at (Pat `abi_builtin_decode_header _ _ _ _ = _`)
    (operand_rule decode_operand_header) >> disch_then (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >>
  drule (operand_rule decode_operand_alloc) >> disch_then (qspec_then `x` strip_assume_tac) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)
    (operand_rule (CONJUNCT1 decode_operand_mutual)) >>
  disch_then (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[decode_operand_compose]
QED
