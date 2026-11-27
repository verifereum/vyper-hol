Theory bodyAbiDecodeGuardedWordLoadMods
Ancestors
  bodyFullAbiDecodeRelativeLoadExact bodyFullAbiDecodeFiniteObserved
  emitHelperProps abiEncoder exprLoweringProps stateFrame
  fragExec fragGasPath venomInst venomState list rich_list

local
  val template = abi_decode_owned_relative_load_exact
  val (_, raw_post) = dest_imp (concl template)
  val (_, raw_body) = strip_exists raw_post
  val owned_state = #1 (strip_comb (find_term (fn tm =>
    let val (head,args) = strip_comb tm
    in is_abs head andalso length args = 4 end) raw_body))
  val (entry, post) = dest_imp (concl (BETA_RULE template))
  val (results, body) = strip_exists post
  val effect = ``tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t))``
  val tm = mk_imp (entry, list_mk_exists (results, mk_conj (body, effect)))
in
  val owned_decoder_state = owned_state
  val relative_load_effect_statement = list_mk_forall (free_vars tm, tm)
end

(* The physical run fixes the normal endpoint and its ghosts before an
   observer is chosen. The observer replays only the emitted ADD/MLOAD. *)
Theorem abi_decode_owned_relative_load_effect_mods:
  ^relative_load_effect_statement
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_decode_relative_load_joint_lower >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `emit_op ADD [Var input;pos] sa = (addr,sb)` by
    gvs[compile_abi_dec_addr_def] >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `inst_extends sa sb /\ inst_extends sb sc` by simp[inst_extends_def] >>
  `inst_extends sa sc` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  `sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    gvs[inst_extends_def] >>
  `sc.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`, `sa`, `sc`] >> simp[IS_PREFIX_APPEND, mk_inst_def]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by simp[] >>
  `(^owned_decoder_state) sc t Gf tnf` by
    (BETA_TAC >> irule (BETA_RULE abi_decode_owned_scalar_frame_with_history_lower) >>
     conj_tac >- (qexists_tac `inst` >> asm_rewrite_tac[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_labels = s.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `t = ((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sc.cs_current_insts)` by
    simp[venom_state_component_equality] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sc) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sc)) = 0` by
    simp[mk_inst_def,is_terminator_def] >>
  `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t)` by
    (qpat_x_assum `fn_has_code sa sc fn` kall_tac >> rpt strip_tac >>
     drule_all abi_decode_finite_success_observed >>
     disch_then (qspec_then `ctx` mp_tac) >>
     qpat_assum `t = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     disch_then ACCEPT_TAC) >>
  `eval_operand v t = SOME (mload (w2n input_word+p) s)` by
    (qpat_assum `v = Var out` (fn th => pure_once_rewrite_tac[th]) >>
     pure_rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(^owned_decoder_state) sc t Gf tnf` (assume_tac o BETA_RULE) >>
  qexistsl_tac [`out`, `t`, `Gf`, `tnf`] >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qexists_tac `t with vs_inst_idx := s.vs_inst_idx` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
