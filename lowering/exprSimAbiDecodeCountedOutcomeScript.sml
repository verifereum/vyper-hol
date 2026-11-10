Theory exprSimAbiDecodeCountedOutcome
Ancestors
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeRestrictedBridge exprSimAbiDecodeRunOutcome
  exprSimAbiDecodeOblivious exprSimAbiGasBridge abiDecoderLoop gasCount venomExecSemantics
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeSuccessRelabel
  exprSimAbiDecodeBoundary exprSimAbiDecodeFreshBridge
  localPtrsProps fragGasMode venomState

Theorem abi_decode_same_block_counted_outcome:
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
  start.cs_blocks = final.cs_blocks /\ frag_gas_free start final /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s ==>
  (?t. gas_marked_path F ctx func s 0 (OK t) /\
    abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts) \/
  (?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
    (?e u. evaluate_abi_decode env ty bs = INR e /\ r = Abort Revert_abort u))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `cs_extends start final` by metis_tac[lower_abi_decode_frag_facts] >>
  ho_match_mp_tac abi_decode_restricted_gas_path >>
  qexistsl_tac [`start`, `\u. u = s`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      `(?t. abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t /\
        ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
        t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn' s t) \/
        (?fuel. exit_result (run_from fuel ctx fn' s) /\
          ?e u. evaluate_abi_decode env ty bs = INR e /\
            run_from fuel ctx fn' s = Abort Revert_abort u)` by
        (irule abi_decode_same_block_run_outcome >> simp[] >>
         conj_tac >- (qexists_tac `limit_st` >> simp[]) >>
         qexistsl_tac [`data`, `n`, `p`] >> simp[]) >>
      metis_tac[abi_decode_sim_def]) >>
  rpt conj_tac >> rpt strip_tac >>
  fs[abi_decode_immutable_success_def, abi_decode_immutable_memory_def] >>
  metis_tac[abi_decode_success_closed_returndata]
QED

Theorem abi_decode_counted_outcome:
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
  data <> Label start.cs_current_bb /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s ==>
  (?t. gas_marked_path F ctx func s 0 (OK t) /\
    abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts) \/
  (?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
    (?e u. evaluate_abi_decode env ty bs = INR e /\ r = Abort Revert_abort u))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  Cases_on `start.cs_blocks = final.cs_blocks`
  >- (irule abi_decode_same_block_counted_outcome >> simp[] >>
      conj_tac >- (qexists_tac `limit_st` >> simp[]) >>
      qexistsl_tac [`data`, `n`, `p`] >> simp[]) >>
  ho_match_mp_tac abi_decode_fresh_frag_exec_gas_path_edge >>
  qexists_tac `start` >> simp[] >>
  conj_tac
  >- suspend "run" >>
  rpt conj_tac >> rpt strip_tac >>
  fs[abi_decode_immutable_success_def, abi_decode_immutable_memory_def] >>
  metis_tac[abi_decode_success_closed_returndata, abi_decode_success_closed_prev_bb]
QED

Resume abi_decode_counted_outcome[run]:
  rpt gen_tac >> strip_tac >>
  `lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (start_relabel L ids start) =
      (out, start_swap start L ids final)` by
    metis_tac[lower_abi_decode_start_oblivious, frag_start_oblivious_def] >>
  drule_all start_swap_fields >> strip_tac >>
  `(?t. abi_decode_immutable_success ce env ty tv bs out d
      (start_relabel L ids start) (start_swap start L ids final)
      ctx func cx es (s with vs_current_bb := L) t /\
    ~t.vs_halted /\ t.vs_current_bb = (start_swap start L ids final).cs_current_bb /\
    t.vs_inst_idx = LENGTH (start_swap start L ids final).cs_current_insts /\
    abi_decode_sim ctx fn' (s with vs_current_bb := L) t /\
    local_prefix ctx fn' (frag_observer_cut (start_swap start L ids final))
      (s with vs_current_bb := L) t) \/
    ((?e. evaluate_abi_decode env ty bs = INR e) /\
      ?fuel u. run_from fuel ctx fn' (s with vs_current_bb := L) = Abort Revert_abort u)` by
    (irule abi_decode_original_entry_immutable_outcome >> simp[] >>
     `immutable_alloca_sep func ce cx es (s with vs_current_bb := L)` by
       (fs[exprLoweringPropsTheory.immutable_alloca_sep_def, loweringStateRelDefsTheory.local_region_def,
           lookup_var_def] >> metis_tac[]) >>
     simp[start_relabel_extends] >>
     conj_tac >- (qexists_tac `limit_st` >> simp[start_swap_def, start_relabel_def] >>
       Cases_on `NULL (emitted_blocks start final)` >> simp[]) >>
     simp[start_relabel_def] >>
     qexistsl_tac [`data`, `n`, `p`] >>
     gvs[GSYM start_relabel_def, abi_decode_site_resources_relabel] >>
     Cases_on `data` >> gvs[eval_operand_def, lookup_var_def]) >>
  metis_tac[abi_decode_immutable_success_relabel, abi_decode_sim_def, fragExecTheory.exit_result_def]
QED
Finalise abi_decode_counted_outcome
