(* Relabeled observer execution and resource transport for the bare encoder. *)
Theory extRequestEncoderFrameRelabel
Ancestors
  exprSimAbiEncodeFramedBody exprSimAbiEncodeWindowRoom exprSimAbiEncodeSourceRoom
  exprSimAbiEncodeSiteResources exprSimAbiEncodeSiteRecovery
  exprSimAbiEncodeOblivious exprSimAbiEncodeObliviousSimulation
  exprSimAbiEncodeObliviousContext exprSimAbiEncodeSiteEncoder
  exprSimAbiEncodeObliviousFacts exprSimAbiEncodeObliviousCode
  exprSimAbiEncodeObliviousLabels
  exprSimAbiEncodeChargeTransfer abiEncoderExitPhi venomInstIdsProps
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderProps exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic
  exprLoweringProps compileEnv fragExec list pred_set finite_map venomState
  exprSimAbiGasBridge emitHelperProps venomMemDefs loweringStateRelDefs

Theorem encoder_window_sites_code[local]:
  site_step a b /\ cs_extends a b /\ cs_extends ra rb /\
  fn_has_code a b func /\ fn_has_code ra rb obs /\
  fn_inst_ids_distinct func /\
  frag_code ra rb = frag_code a b /\ frag_ids ra rb = frag_ids a b /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) ==>
  window_alloca_sites obs (frag_ids ra rb) =
  window_alloca_sites func (frag_ids a b)
Proof
  strip_tac >> simp[EXTENSION, window_alloca_sites_def] >> gen_tac >>
  eq_tac
  >- metis_tac[] >>
  strip_tac >> rename1 `MEM inst (fn_insts func)` >>
  `MEM inst (frag_code a b)` by
    (irule site_interval_instruction >>
     fs[frag_ids_def] >>
     qexists_tac `func` >>
     metis_tac[abi_encode_frag_code_members,
       fn_inst_ids_distinct_all_distinct]) >>
  simp[] >> qexists_tac `inst` >> simp[] >>
  irule abi_encode_frag_code_members >>
  qexistsl_tac [`ra`, `rb`] >> simp[]
QED

Theorem encoder_window_relabel_pre[local]:
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  cs_extends st en /\ st.cs_blocks <> en.cs_blocks /\
  LENGTH ids = LENGTH st.cs_current_insts /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids en) obs /\
  fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) ==>
  abi_encoder_window_pre (ctx with ctx_functions := [obs]) obs
    (start_relabel L ids st) (start_swap st L ids en)
    dst src ei at av sb cap d (s with vs_current_bb := L)
Proof
  strip_tac >>
  `alloca_room (ctx with ctx_functions := [obs]) obs s` by
    (irule abi_encode_bridge_local_room >>
     fs[abi_encoder_window_pre_def] >> metis_tac[]) >>
  `alloca_room (ctx with ctx_functions := [obs]) obs
     (s with vs_current_bb := L)` by
    (irule alloca_room_fields >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_window_pre_def]) >>
  `frag_ids (start_relabel L ids st) (start_swap st L ids en) =
     frag_ids st en` by
    (pure_rewrite_tac[frag_ids_def, start_relabel_def, start_swap_def, LET_THM] >>
     Cases_on `NULL (emitted_blocks st en)` >> simp[]) >>
  `(!x. not_fresh_at (start_relabel L ids st) x = not_fresh_at st x) /\
   (start_relabel L ids st).cs_current_bb = L /\
   LENGTH (start_relabel L ids st).cs_current_insts = LENGTH st.cs_current_insts` by
    simp[start_relabel_def, not_fresh_at_def] >>
  `alloca_inv (s with vs_current_bb := L)` by
    (fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     metis_tac[]) >>
  `eval_operand src (s with vs_current_bb := L) = SOME (n2w sb) /\
   eval_operand dst (s with vs_current_bb := L) = SOME (n2w d)` by
    (conj_tac
     >- (qpat_x_assum `eval_operand src s = _` mp_tac >>
         Cases_on `src` >> simp[NoAsms, eval_operand_def, lookup_var_def]) >>
     qpat_x_assum `eval_operand dst s = _` mp_tac >>
     Cases_on `dst` >> simp[NoAsms, eval_operand_def, lookup_var_def]) >>
  pure_rewrite_tac[abi_encoder_window_pre_def] >>
  rpt conj_tac >> simp[NoAsms] >>
  ASM_REWRITE_TAC []
  >~ [`cap + sb <= s.vs_alloca_next`] >- decide_tac >>
  rpt strip_tac >>
  `MEM inst (fn_insts func)` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!inst b sz. _` (drule_all_then strip_assume_tac) >>
  simp[]
QED

Theorem encoder_window_observer_frame[local]:
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = ALLOCA ==>
       MEM i (fn_insts func)) /\
  abi_encoder_registered_effect (window_alloca_sites obs ids) outs s t /\
  abi_encode_exec_frame obs s t ==>
  abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `!i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
       ~MEM i (fn_insts obs) ==>
       FLOOKUP t.vs_allocas i.inst_id = FLOOKUP s.vs_allocas i.inst_id` by
    (rpt strip_tac >>
     `i.inst_id NOTIN window_alloca_sites obs ids` by
       (simp[window_alloca_sites_def] >>
        metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_inj]) >>
     fs[abi_encoder_registered_effect_def]) >>
  qpat_x_assum `abi_encode_exec_frame obs s t`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_exec_frame_def]) >>
  pure_rewrite_tac[abi_encode_exec_frame_def] >>
  reverse (rpt conj_tac) >> ASM_REWRITE_TAC [] >>
  irule abi_encode_charge_difference_lift >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `obs` >> ASM_REWRITE_TAC []
QED

Theorem encoder_window_relabel_observer[local]:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  cs_extends st en /\ st.cs_blocks <> en.cs_blocks /\
  LENGTH ids = LENGTH st.cs_current_insts /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids en) obs /\
  fn_inst_ids_distinct obs /\ obs.fn_name = func.fn_name /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\
       i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) ==>
  ?t. window_strong_result (ctx with ctx_functions := [obs]) obs
        (start_relabel L ids st) (start_swap st L ids en) out at av d
        (s with vs_current_bb := L) t /\
      abi_encode_exec_frame func (s with vs_current_bb := L) t /\
      abi_decode_sim ctx obs (s with vs_current_bb := L) t /\
      window_alloca_sites obs
        (frag_ids (start_relabel L ids st) (start_swap st L ids en)) =
      window_alloca_sites func (frag_ids st en)
Proof
  strip_tac >>
  `abi_encoder_window_pre (ctx with ctx_functions := [obs]) obs
     (start_relabel L ids st) (start_swap st L ids en)
     dst src ei at av sb cap d (s with vs_current_bb := L)` by
    (irule encoder_window_relabel_pre >> metis_tac[]) >>
  `compile_abi_encode_to_buf dst src ei (start_relabel L ids st) =
     (out,start_swap st L ids en)` by
    (`entry_shape st st` by simp[entry_shape_refl] >>
     qspecl_then [`dst`, `src`, `ei`] mp_tac (cj 2 entry_action_encoder_mutual) >>
     rewrite_tac[entry_action_def] >>
     disch_then drule_all >>
     disch_then (qspec_then `L` mp_tac) >> simp[start_swap_initial]) >>
  drule_all compile_abi_encode_to_buf_framed_run >> strip_tac >>
  `abi_decode_sim ctx obs (s with vs_current_bb := L) t` by
    (irule abi_decode_sim_ctx_no_invoke >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `ctx with ctx_functions := [obs]` >> simp[] >>
     drule window_strong_result_public >> simp[abi_encoder_window_result_def]) >>
  `abi_encode_exec_frame func (s with vs_current_bb := L) t` by
    (irule encoder_window_observer_frame >>
     conj_tac
     >- (qpat_x_assum `abi_encoder_window_pre ctx func _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_window_pre_def]) >>
         first_assum ACCEPT_TAC) >>
     qexistsl_tac [`frag_ids (start_relabel L ids st) (start_swap st L ids en)`,
       `obs`, `[(d,LENGTH (enc at av))]`] >>
     qpat_x_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [window_strong_result_def]) >>
     ASM_REWRITE_TAC [] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qexists_tac `t` >> ASM_REWRITE_TAC [] >>
  irule encoder_window_sites_code >>
  qpat_x_assum `abi_encoder_window_pre ctx func _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_window_pre_def]) >>
  `site_step st en` by metis_tac[abi_encode_body_site_step] >>
  rpt conj_tac >> ASM_REWRITE_TAC []
  >- (rpt strip_tac >> first_x_assum irule >> simp[])
  >- (pure_rewrite_tac[frag_ids_def, start_relabel_def, start_swap_def, LET_THM] >>
      Cases_on `NULL (emitted_blocks st en)` >> simp[])
  >- (irule start_relabel_frag_code >> simp[]) >>
  irule start_relabel_extends >> simp[]
QED

Theorem abi_encoder_window_run_fmp_blocks:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_encoder_window_pre ctx func st st' dst src ei at av sb cap d s /\
  st.cs_blocks <> st'.cs_blocks ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\
      mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
        [(d,LENGTH (enc at av))] s t /\
      alloca_inv t /\
      (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) /\
      window_alloca_growth s t /\
      (!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
         FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
      t.vs_labels = s.vs_labels /\
      t.vs_alloca_next + pending_alloca_size func t <=
        s.vs_alloca_next + pending_alloca_size func s /\
      t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
      t.vs_data_section = s.vs_data_section /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  strip_tac >>
  `code_step enc_safe_opcode st st'` by
    metis_tac[code_action_def, cj 2 code_action_encoder_mutual] >>
  `label_step st st'` by
    metis_tac[label_action_def, cj 2 label_action_encoder_mutual] >>
  `cs_extends st st' /\ frag_ops_free st st' /\
   ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code st st'))` by
    (qpat_x_assum `code_step _ _ _` mp_tac >>
     rewrite_tac[GSYM enc_safe_opcode_def, ETA_THM] >>
     metis_tac[REWRITE_RULE [GSYM enc_safe_opcode_def, ETA_THM] code_step_frag_facts]) >>
  `~MEM st'.cs_current_bb
     (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks st st')))` by
    metis_tac[label_step_current_excluded] >>
  `st'.cs_current_insts <> []` by metis_tac[abi_encoder_core_exit_nonempty] >>
  qabbrev_tac `Q = \t.
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st st'))
      [(d,LENGTH (enc at av))] s t /\
    alloca_inv t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    window_alloca_growth s t /\
    (!i b sz. i IN window_alloca_sites func (frag_ids st st') /\
      FLOOKUP t.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    t.vs_labels = s.vs_labels /\ abi_encode_exec_frame func s t` >>
  `(!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
   (!t prev. Q t ==> Q (t with vs_prev_bb := prev))` by
    (simp_tac bool_ss [Abbr `Q`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `out` >>
     pure_rewrite_tac[abi_encoder_registered_effect_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, window_alloca_growth_def,
       eval_operand_def, lookup_var_def] >>
     pure_rewrite_tac [venom_state_accfupds] >>
     conj_tac >> rpt gen_tac >> strip_tac >> rpt conj_tac >>
     metis_tac[abi_encode_exec_frame_bridge_updates]) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
       t.vs_current_bb = st'.cs_current_bb /\
       t.vs_inst_idx = LENGTH st'.cs_current_insts` suffices_by
    (strip_tac >> qexists_tac `t` >>
     qunabbrev_tac `Q` >> rule_assum_tac BETA_RULE >>
     qpat_x_assum `mem_bytes_at _ _ _ = _ /\ _` strip_assume_tac >>
     qpat_x_assum `abi_encode_exec_frame _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_encode_exec_frame_def]) >>
     metis_tac[abi_encode_semantic_obs_fields]) >>
  qpat_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_window_pre_def]) >>
  irule abi_decode_sim_gas_path_relabel >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `st` >>
  reverse conj_tac
  >- (qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_window_pre_def]) >>
      ASM_REWRITE_TAC []) >>
  rpt gen_tac >> strip_tac >>
  drule_all encoder_window_relabel_observer >> strip_tac >>
  qexists_tac `t` >>
  qpat_x_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [window_strong_result_def]) >>
  qpat_x_assum `abi_encoder_window_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_window_result_def]) >>
  qpat_x_assum `!t rd. Q t ==> Q (t with vs_returndata := rd)` kall_tac >>
  qpat_x_assum `!t prev. Q t ==> Q (t with vs_prev_bb := prev)` kall_tac >>
  simp_tac bool_ss [Abbr `Q`] >>
  drule_all start_swap_fields >>
  disch_then (qspecl_then [`ids`, `L`] strip_assume_tac) >>
  qpat_x_assum `window_alloca_sites fn' _ = _` SUBST_ALL_TAC >>
  qpat_x_assum `(start_swap _ _ _ _).cs_current_bb = _` SUBST_ALL_TAC >>
  qpat_x_assum `(start_swap _ _ _ _).cs_current_insts = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [start_relabel_def,
    not_fresh_at_def, lookup_var_def, abi_encoder_registered_effect_def,
    window_alloca_growth_def, abi_encode_exec_frame_def, pending_alloca_size_def,
    abi_encode_semantic_obs_updates, venom_state_accfupds, compile_state_accfupds]) >>
  pure_rewrite_tac [not_fresh_at_def, lookup_var_def,
    abi_encoder_registered_effect_def, window_alloca_growth_def,
    abi_encode_exec_frame_def, pending_alloca_size_def] >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
