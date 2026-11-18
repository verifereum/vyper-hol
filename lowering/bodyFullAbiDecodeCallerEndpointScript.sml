Theory bodyFullAbiDecodeCallerEndpoint
Ancestors
  exprSimAbiDecodeImmutableOutcome exprSimAbiGasBridge abiEncoderObserver
  fragGasPath fragExec abiDecoderLoop venomState venomExecSemantics

Theorem abi_decode_completed_runs_equal[local]:
  run_from n ctx fn s = a /\ exit_result a /\
  run_from m ctx fn s = b /\ exit_result b ==> a = b
Proof
  strip_tac >>
  `run_from (n + m) ctx fn s = a` by
    (irule gas_run_from_fuel_mono >>
     (conj_tac >- metis_tac[exit_result_not_error]) >> qexists_tac `n` >>
     simp[] >> metis_tac[exit_result_not_error]) >>
  `run_from (n + m) ctx fn s = b` by
    (irule gas_run_from_fuel_mono >>
     (conj_tac >- metis_tac[exit_result_not_error]) >> qexists_tac `m` >>
     simp[] >> metis_tac[exit_result_not_error]) >>
  gvs[]
QED

Theorem abi_decode_caller_endpoint_observed:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final func /\
  frag_gas_free start final /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s /\
  (!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r) /\
  ((?t. r = OK t /\ ~t.vs_halted /\
     t.vs_current_bb = final.cs_current_bb /\
     t.vs_inst_idx = LENGTH final.cs_current_insts) \/
   (?u. r = Abort Revert_abort u)) ==>
  (?t. r = OK t /\
    abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t) \/
  ((?u. r = Abort Revert_abort u) /\
   ?e. evaluate_abi_decode env ty bs = INR e)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?id. !inst. MEM inst (fn_insts func) ==> inst.inst_id <> id` by
    metis_tac[frag_observer_fresh_id] >>
  qabbrev_tac `obs = frag_observer start final func id` >>
  `fn_has_code start final obs` by simp[Abbr `obs`, frag_observer_has_code] >>
  `fn_inst_ids_distinct obs` by
    (simp[Abbr `obs`] >> irule frag_observer_ids_distinct >> simp[]) >>
  `!i. MEM i (fn_insts obs) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)` by
    (simp[Abbr `obs`] >> metis_tac[frag_observer_nonstop_inclusion]) >>
  `gas_path ctx obs s 0 r` by metis_tac[] >>
  `!t. t.vs_current_bb = final.cs_current_bb /\
       t.vs_inst_idx = LENGTH final.cs_current_insts ==>
       run_from 0 ctx obs t = Halt (stop_view t)` by
    (rpt strip_tac >> irule run_from_stop_view >> simp[] >>
     qexistsl_tac [
       `<|bb_label := final.cs_current_bb;
          bb_instructions := final.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[Abbr `obs`, frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  mp_tac (Q.INST [`fn` |-> `obs`] abi_decode_original_entry_immutable_outcome) >>
  (impl_tac >- (simp[] >> metis_tac[frag_observer_end_phi_zero])) >>
  strip_tac
  >- (rename1 `abi_decode_sim ctx obs s u` >>
      `?fuel. run_from fuel ctx obs s = Halt (stop_view u)` by
        metis_tac[abi_decode_sim_def, exec_result_distinct] >>
      qpat_x_assum `(?t. r = OK t /\ _) \/ _`
        (DISJ_CASES_THEN2 (qx_choose_then `t` strip_assume_tac)
                         (qx_choose_then `z` strip_assume_tac)) >> gvs[]
      >- (`?fuel'. run_from fuel' ctx obs s = Halt (stop_view t)` by
            metis_tac[gas_path_normal, exec_result_distinct] >>
          `stop_view t = stop_view u` by
            metis_tac[abi_decode_completed_runs_equal, exit_result_def,
                      exec_result_11] >>
          `t = u with vs_returndata := t.vs_returndata` by
            metis_tac[stop_view_recover] >>
          qpat_x_assum `t = _` SUBST1_TAC >>
          `u with <|vs_returndata := t.vs_returndata;
                    vs_prev_bb := u.vs_prev_bb|> =
           u with vs_returndata := t.vs_returndata` by
            simp[venom_state_component_equality] >>
          drule abi_decode_immutable_success_updates >>
          disch_then (qspecl_then [`t.vs_returndata`, `u.vs_prev_bb`] mp_tac) >>
          simp[]) >>
      `?fuel'. run_from fuel' ctx obs s = Abort Revert_abort z` by
        metis_tac[gas_path_exit, exit_result_def] >>
      metis_tac[abi_decode_completed_runs_equal, exit_result_def,
                exec_result_distinct]) >>
  qpat_x_assum `(?t. r = OK t /\ _) \/ _`
        (DISJ_CASES_THEN2 (qx_choose_then `t` strip_assume_tac)
                         (qx_choose_then `z` strip_assume_tac)) >> gvs[] >>
  `?fuel'. run_from fuel' ctx obs s = Halt (stop_view t)` by
    metis_tac[gas_path_normal, exec_result_distinct] >>
  metis_tac[abi_decode_completed_runs_equal, exit_result_def, exec_result_distinct]
QED
