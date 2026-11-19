Theory bodyFullAbiDecodeCallerCutEndpoint
Ancestors exprLoweringProps[qualified,ignore_grammar] loweringStateRelDefs[qualified,ignore_grammar]
  bodyFullAbiDecodeCallerEndpoint bodyFullAbiDecodeCallerRegularEndpoint
  exprSimAbiDecodeOblivious
  exprSimAbiDecodeBoundary exprSimAbiDecodeSuccessRelabel
  abiEncoderObserver fragGasPath exprSimAbiGasBridge fragExec
  exprSimAbiDecodeImmutableOutcome abiDecoderLoop venomState venomExecSemantics

val cut_entry = ``
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
  fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s``;

val cut_observer = ``
  LENGTH ids = LENGTH start.cs_current_insts /\ L <> final.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) /\
  frag_gas_free (start_relabel L ids start) (start_swap start L ids final) /\
  fn_has_code (start_relabel L ids start) (start_swap start L ids final)
    (frag_relabel_observer start final L ids func id) /\
  fn_inst_ids_distinct (frag_relabel_observer start final L ids func id) /\
  (!i. MEM i (fn_insts (frag_relabel_observer start final L ids func id)) /\
       i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts func)) /\
  (!i. MEM i (fn_insts (frag_relabel_observer start final L ids func id)) ==>
       i.inst_opcode <> INVOKE) /\
  (!bb. lookup_block final.cs_current_bb
     (frag_relabel_observer start final L ids func id).fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0)``;

val cut_run = ``
  (?t u k. r = OK t /\ ~u.vs_halted /\
    (u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut final /\
    frag_relabel_state L start.cs_current_bb u t /\
    run_from k ctx (frag_relabel_observer start final L ids func id)
      (s with vs_current_bb := L) = Halt (stop_view u)) \/
  (?t u k. r = Abort Revert_abort t /\
    frag_relabel_state L start.cs_current_bb u t /\
    run_from k ctx (frag_relabel_observer start final L ids func id)
      (s with vs_current_bb := L) = Abort Revert_abort u)``;

val cut_post = ``
  (?t. r = OK t /\
    abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t) \/
  ((?u. r = Abort Revert_abort u) /\
   ?e. evaluate_abi_decode env ty bs = INR e)``;

Theorem abi_decode_shadow_semantics[local]:
  ^cut_entry /\ start.cs_blocks <> final.cs_blocks /\ ^cut_observer ==>
  (?v k. abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s v /\
     ~v.vs_halted /\
     run_from k ctx (frag_relabel_observer start final L ids func id)
       (s with vs_current_bb := L) = Halt (stop_view v)) \/
  ((?e. evaluate_abi_decode env ty bs = INR e) /\
   ?v k. run_from k ctx (frag_relabel_observer start final L ids func id)
     (s with vs_current_bb := L) = Abort Revert_abort v)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `obs = frag_relabel_observer start final L ids func id` >>
  qabbrev_tac `sL = s with vs_current_bb := L` >>
  `lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (start_relabel L ids start) =
    (out,start_swap start L ids final)` by
    metis_tac[lower_abi_decode_start_oblivious, frag_start_oblivious_def] >>
  drule_all start_swap_fields >> strip_tac >>
  mp_tac (Q.INST [`fn` |-> `obs`, `s` |-> `sL`,
                  `start` |-> `start_relabel L ids start`,
                  `final` |-> `start_swap start L ids final`]
                 abi_decode_original_entry_immutable_outcome) >>
  (impl_tac >- suspend "relabel_entry") >>
  strip_tac
  >- (rename1 `abi_decode_sim ctx obs sL v` >>
      `run_from 0 ctx obs v = Halt (stop_view v)` by
        (irule run_from_stop_view >>
         qexistsl_tac [`<|bb_label := final.cs_current_bb;
          bb_instructions := final.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
         simp[Abbr `obs`, frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
      `abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s v` by
        (unabbrev_all_tac >> metis_tac[abi_decode_immutable_success_relabel]) >>
      disj1_tac >> qexists_tac `v` >> simp[] >>
      metis_tac[abi_decode_sim_def, exec_result_distinct]) >>
  disj2_tac >> simp[] >> metis_tac[]
QED

Resume abi_decode_shadow_semantics[relabel_entry]:
  `immutable_alloca_sep func ce cx es sL` by
    ((simp[Abbr `sL`, exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     fs[exprLoweringPropsTheory.immutable_alloca_sep_def,
        loweringStateRelDefsTheory.local_region_def, lookup_var_def] >> (metis_tac[Abbr `sL`, exprLoweringPropsTheory.immutable_alloca_sep_def, loweringStateRelDefsTheory.local_region_def, lookup_var_def]))) >>
  `eval_operand data sL = eval_operand data s` by
    (Cases_on `data` >> gvs[Abbr `sL`, eval_operand_def, lookup_var_def]) >>
  `abi_builtin_decode_site_resources ctx func (start_relabel L ids start)
    (start_swap start L ids final).cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d sL` by
    simp[Abbr `sL`, abi_decode_site_resources_relabel] >>
  simp[start_relabel_extends] >>
  Cases_on `NULL (emitted_blocks start final)` >>
  simp[start_relabel_def, start_swap_def, Abbr `sL`]
QED
Finalise abi_decode_shadow_semantics

val cut_collision = ``
  start.cs_blocks <> final.cs_blocks /\ start.cs_current_bb = final.cs_current_bb``;

Theorem abi_decode_caller_endpoint_collision[local]:
  ^cut_entry /\
  ^cut_collision /\
  (?L ids id. ^cut_observer /\ ^cut_run) ==>
  ^cut_post
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `?L ids id. _`
    (qx_choose_then `L` (qx_choose_then `ids` (qx_choose_then `id`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  drule_all abi_decode_shadow_semantics >>
  qabbrev_tac `obs = frag_relabel_observer start final L ids func id` >>
  qabbrev_tac `sL = s with vs_current_bb := L` >>
  disch_tac >>
  `?a f. run_from f ctx obs sL = a /\
     ((?v. a = Halt (stop_view v) /\ ~v.vs_halted /\
        abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s v) \/
      ((?v. a = Abort Revert_abort v) /\ ?e. evaluate_abi_decode env ty bs = INR e))` by
    metis_tac[] >>
  `?b k. run_from k ctx obs sL = b /\
     ((?t u. r = OK t /\ b = Halt (stop_view u) /\ ~u.vs_halted /\
        (u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut final /\
        frag_relabel_state L start.cs_current_bb u t) \/
      ((?t. r = Abort Revert_abort t) /\ ?u. b = Abort Revert_abort u))` by
    metis_tac[] >>
  qpat_x_assum `(?v k. abi_decode_immutable_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ v /\ _) \/ _` kall_tac >>
  qpat_x_assum `(?t u k. r = OK t /\ _) \/ _` kall_tac >>
  `!e. a <> Error e` by metis_tac[exec_result_distinct] >>
  `!e. b <> Error e` by metis_tac[exec_result_distinct] >>
  `run_from (f + k) ctx obs sL = a` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `f` >> simp[]) >>
  `run_from (f + k) ctx obs sL = b` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `k` >> simp[]) >>
  `a = b` by metis_tac[] >>
  gvs[frag_observer_cut_def]
  >- (`u = v with vs_returndata := u.vs_returndata` by metis_tac[stop_view_recover] >>
      `t = u with vs_prev_bb := t.vs_prev_bb` by metis_tac[frag_relabel_state_cut] >>
      `t = v with <|vs_returndata := u.vs_returndata; vs_prev_bb := t.vs_prev_bb|>` by
        (qpat_assum `t = u with vs_prev_bb := _` (fn th =>
           CONV_TAC (LAND_CONV (REWR_CONV th))) >>
         qpat_assum `u = v with vs_returndata := _` (fn th =>
           CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV th)))) >> simp[]) >>
      metis_tac[abi_decode_immutable_success_updates]) >>
  metis_tac[]
QED


Theorem abi_decode_caller_endpoint_committed:
  !ce env ty tv data start out final limit_st p n bs d ctx func cx es s r.
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
    fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
    s.vs_inst_idx = LENGTH start.cs_current_insts /\
    immutable_alloca_sep func ce cx es s /\
    (!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
      t.vs_current_bb = final.cs_current_bb /\
      t.vs_inst_idx = LENGTH final.cs_current_insts) \/
     (?u. r = Abort Revert_abort u)) /\
    (~(^cut_collision) ==> data <> Label start.cs_current_bb) /\
    ((^cut_collision) ==> ?L ids id.
        LENGTH ids = LENGTH start.cs_current_insts /\ L <> final.cs_current_bb /\
        ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks start final)) /\
        EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code start final) /\
        frag_gas_free (start_relabel L ids start) (start_swap start L ids final) /\
        fn_has_code (start_relabel L ids start) (start_swap start L ids final) (frag_relabel_observer
          start final L ids func id) /\
        fn_inst_ids_distinct (frag_relabel_observer start final L ids func id) /\
        (!i. MEM i (fn_insts (frag_relabel_observer start final L ids func id)) /\ i.inst_opcode <> STOP
          /\ i.inst_opcode <> NOP ==>
          MEM i (fn_insts func)) /\
        (!i. MEM i (fn_insts (frag_relabel_observer start final L ids func id)) ==> i.inst_opcode <>
          INVOKE) /\
        (!bb. lookup_block final.cs_current_bb (frag_relabel_observer start final L ids func
          id).fn_blocks = SOME bb ==>
          phi_prefix_length bb.bb_instructions = 0) /\
        ((?t u k. r = OK t /\ ~u.vs_halted /\
           (u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut final /\
           frag_relabel_state L start.cs_current_bb u t /\
           run_from k ctx (frag_relabel_observer start final L ids func id) (s with vs_current_bb := L) =
             Halt (stop_view u)) \/
         (?t u k. r = Abort Revert_abort t /\
           frag_relabel_state L start.cs_current_bb u t /\
           run_from k ctx (frag_relabel_observer start final L ids func id) (s with vs_current_bb := L) =
             Abort Revert_abort u))) ==>
    ^cut_post
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Q_TAC ASM_CASES_TAC `^cut_collision`
  >- (qpat_x_assum `_ ==> ?L ids id. _` mp_tac >> simp[] >> disch_tac >>
      mp_tac abi_decode_caller_endpoint_collision >> simp[GSYM CONJ_ASSOC]) >>
  qpat_x_assum `_ ==> data <> Label start.cs_current_bb` (fn guard =>
    qpat_assum `~(^cut_collision)` (assume_tac o MATCH_MP guard)) >>
  mp_tac abi_decode_caller_endpoint_regular >> asm_rewrite_tac[]
QED
