(* Concrete counted execution of nonbulk array loops. *)
Theory abiDecodeMemLoop
Ancestors
  abiDecodeMemArrayBody abiDecodeMemLoopEntry abiDecodeMemArrayEntry
  abiDecoderRecursiveLoopLayout abiDecoderLoopEmit abiDecoderLoopCode
  abiDecoderArraySetupInputs abiDecoderArraySetupCode abiDecoderCounters
  abiDecoderReentry abiDecodeMemLoopIteration abiDecodeMemLoopControl
  abiDecoderFrame fragGasPathMem fragGasMode localPtrsProps allocaHistory
  emitHelperProps exprLoweringProps compileEnv venomState venomExecSemantics
  finite_map alist list arithmetic words

Theorem abi_decode_mem_dyn_loop:
  let slot = w2n (p:bytes32) in
  let P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H a.vs_memory /\
       (!q. protected q ==> mload q u = mload q a) /\
       u.vs_call_ctx = a.vs_call_ctx /\ u.vs_data_section = a.vs_data_section) in
  let F = (\u. MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
                          (fmap_to_alist u.vs_allocas))) in
  let J = (\j lbl k u. P u /\ alloca_inv u /\ alloca_room ctx fn u /\
       alloca_history fn u /\ ~u.vs_halted /\ u.vs_current_bb = lbl /\
       u.vs_inst_idx = k /\ eval_operand ip u = SOME p /\
       eval_operand src u = SOME (n2w sb) /\ eval_operand base_op u = SOME (n2w B) /\
       eval_operand dst u = SOME (n2w d) /\ eval_operand hi_op u = SOME (n2w H) /\
       mload slot u = n2w j /\ mload (B+sb) u = n2w ncount /\
       j <= ncount /\ B+H <= u.vs_alloca_next /\
       d+sz <= u.vs_alloca_next /\ slot+32 <= u.vs_alloca_next) in
  let R = (\u v. u.vs_alloca_next <= v.vs_alloca_next /\
       (!op. abi_decoder_operand_live first op ==> eval_operand op v = eval_operand op u) /\
       (!q. q < lo \/ hi <= q ==> FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
       abi_decode_footprint_frame ((d,sz)::(slot,32)::F v) u v) in
  compile_abi_decode_dyn_loop dst src MLOAD base_op hi_op di asz msz ip cnt start = ((),final) /\
  abi_decode_loop_prefix ip src MLOAD base_op start = (labels,st) /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi_op di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi_op di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  fn_has_code start final fn /\ fn_inst_ids_distinct fn /\
  (!bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  first <= start.cs_next_var /\ lo <= middle.cs_next_id /\ end_st.cs_next_id <= hi /\ lo <= hi /\
  abi_decoder_operand_live start.cs_next_var ip /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi_op /\
  hi_op <> Lit 0w /\ B+H < dimword(:256) /\ d+sz < dimword(:256) /\
  asz < dimword(:256) /\ sb+32+ncount*asz <= H /\ 32+ncount*msz <= sz /\
  ncount < dimword(:256) /\ (dec_info_needs_offset di ==> 32 <= asz) /\
  (slot+32 <= B \/ B+H <= slot) /\
  (!q. protected q ==> q+32 <= slot \/ slot+32 <= q) /\
  J i start.cs_current_bb (LENGTH start.cs_current_insts) s /\
  (!u c e.
    alloca_inv u /\ alloca_room ctx fn u /\ alloca_history fn u /\ ~u.vs_halted /\
    u.vs_current_bb = middle.cs_current_bb /\ u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    B+H <= u.vs_alloca_next /\ e+msz <= u.vs_alloca_next /\
    d+32 <= e /\ e+msz <= d+sz /\
    eval_operand (FST (SND ops)) u = SOME c /\
    eval_operand (SND (SND ops)) u = SOME (n2w e) /\
    eval_operand base_op u = SOME (n2w B) /\ eval_operand hi_op u = SOME (n2w H) /\
    w2n c + asz <= H ==>
    ((?v. gas_path_mem ctx fn u 0 (OK v) /\
      alloca_inv v /\ alloca_room ctx fn v /\ alloca_history fn v /\ ~v.vs_halted /\
      v.vs_current_bb = end_st.cs_current_bb /\ v.vs_inst_idx = LENGTH end_st.cs_current_insts /\
      u.vs_alloca_next <= v.vs_alloca_next /\
      mem_bytes_at B H v.vs_memory = mem_bytes_at B H u.vs_memory /\
      (!q. protected q \/ q = slot \/ q = B+sb ==> mload q v = mload q u) /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==> eval_operand op v = eval_operand op u) /\
      (!q. q < middle.cs_next_id \/ end_st.cs_next_id <= q ==>
        FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
      ?fp. (!q n. MEM (q,n) fp <=> ?id. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP v.vs_allocas id = SOME (q,n)) /\
        abi_decode_footprint_frame ((e,msz)::fp) u v) \/
     (?v. gas_marked_path T ctx fn u 0 (Abort Revert_abort v)))) ==>
  ((?t. gas_path_mem ctx fn s 0 (OK t) /\
        J ncount final.cs_current_bb (LENGTH final.cs_current_insts) t /\ R s t) \/
   (?t. gas_marked_path T ctx fn s 0 (Abort Revert_abort t)))
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  `abi_decode_source_opcode MLOAD` by simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_cfg >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  `abi_decode_loop_suffix ip (Var (STRING #"%" (toString st.cs_next_var)))
     (FST labels) (SND (SND labels)) end_st = ((),final)` by metis_tac[] >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `middle.cs_next_var <= end_st.cs_next_var` by metis_tac[abi_decoder_variable_counter] >>
  `st.cs_next_var <= middle.cs_next_var` by metis_tac[abi_decode_array_element_setup_operands] >>
  `start.cs_next_var <= end_st.cs_next_var` by decide_tac >>
  qabbrev_tac `RR = (\u v. u.vs_alloca_next <= v.vs_alloca_next /\
       (!op. abi_decoder_operand_live start.cs_next_var op ==>
         eval_operand op v = eval_operand op u) /\
       (!q. q < lo \/ hi <= q ==> FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
       abi_decode_footprint_frame ((d,sz)::(slot,32)::F' v) u v)` >>
  `!j u. j < ncount /\ J j (FST labels) 0 u ==>
    let b = jump_to st.cs_current_bb
       (abi_decode_position_header_state base_op start.cs_next_var B sb j ncount u) in
    ((?v. gas_path_mem ctx fn b 0 (OK v) /\
       J j end_st.cs_current_bb (LENGTH end_st.cs_current_insts) v /\
       eval_operand (FST ops) v = SOME (n2w j) /\ RR b v) \/
     (?v. gas_marked_path T ctx fn b 0 (Abort Revert_abort v)))` by suspend "body" >>
  `s.vs_current_bb = start.cs_current_bb /\
   s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted` by fs[Abbr `J`] >>
  drule_all abi_decode_mem_loop_prefix_path >> disch_then (qspec_then `ctx` mp_tac) >>
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `OK h` >> strip_tac >>
  `alloca_inv s /\ alloca_room ctx fn s /\ alloca_history fn s` by fs[Abbr `J`] >>
  `alloca_inv h /\ alloca_room ctx fn h /\ alloca_history fn h` by metis_tac[] >>
  `J i (FST labels) 0 h` by gvs[Abbr `J`, Abbr `P`, mload_def] >>
  `((?t. gas_path_mem ctx fn h 0 (OK t) /\
        J ncount final.cs_current_bb 0 t /\ R h t) \/
    (?t. gas_marked_path T ctx fn h 0 (Abort Revert_abort t)))` by suspend "iterate" >>
  FIRST [qpat_assum `R h _` (K (suspend "success")),
    disj2_tac >> fs[gas_marked_path_def] >>
    pop_assum mp_tac >>
    qpat_x_assum `gas_path_mem ctx fn s 0 (OK h)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> qexists_tac `t` >>
    irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
    qexists_tac `h` >> simp[]]
QED
Resume abi_decode_mem_dyn_loop[body]:
  markerLib.RESUME_TAC >> rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `gas_path_mem ctx fn b 0` >>
  `alloca_inv u /\ alloca_room ctx fn u /\ alloca_history fn u` by fs[Abbr `J`] >>
  `alloca_inv b /\ alloca_room ctx fn b /\ alloca_history fn b /\
   b.vs_allocas = u.vs_allocas /\ b.vs_alloca_next = u.vs_alloca_next /\
   b.vs_memory = u.vs_memory /\
   (!op. abi_decoder_operand_live start.cs_next_var op ==> eval_operand op b = eval_operand op u)` by
    (simp_tac bool_ss [Abbr `b`] >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_decode_position_header_resources) >> simp[]) >>
  suspend "body_resources"
QED
Resume abi_decode_mem_dyn_loop[body_resources]:
  markerLib.RESUME_TAC >>
  simp_tac bool_ss [Abbr `J`, Abbr `RR`, Abbr `P`, Abbr `F'`, Abbr `slot`] >>
  mp_tac (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`first` |-> `start.cs_next_var`] abi_decode_mem_array_body)) >>
  (impl_tac >- suspend "body_premises") >>
  `j <= ncount` by decide_tac >>
  simp[CONJ_ASSOC]
QED
Resume abi_decode_mem_dyn_loop[body_premises]:
  markerLib.RESUME_TAC >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `start.cs_next_var <= st.cs_next_var` by decide_tac >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
        abi_decoder_operand_live st.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `b.vs_call_ctx = u.vs_call_ctx /\ b.vs_data_section = u.vs_data_section /\
   b.vs_current_bb = st.cs_current_bb /\ b.vs_inst_idx = 0 /\
   b.vs_halted = u.vs_halted` by
    (Cases_on `base_op = Lit 0w` >>
     asm_simp_tac (srw_ss()) [Abbr `b`,
       abiDecoderExecutionTheory.abi_decode_position_header_state_def,
       jump_to_def, update_var_def, LET_THM]) >>
  gvs[mload_def]
QED
Resume abi_decode_mem_dyn_loop[iterate]:
  markerLib.RESUME_TAC >>
  `!op. abi_decoder_operand_live start.cs_next_var op ==>
        op <> Var (STRING #"%" (toString end_st.cs_next_var))` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> gvs[ASCIInumbersTheory.toString_11] >> decide_tac) >>
  `sb+32 <= H` by decide_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`first` |-> `start.cs_next_var`, `hdr` |-> `FST (labels:string # string # string)`,
      `body_lbl` |-> `st.cs_current_bb`, `exit_lbl` |-> `final.cs_current_bb`,
      `hid` |-> `start.cs_next_id+1`, `suffix_lbl` |-> `end_st.cs_current_bb`,
      `prefix` |-> `end_st.cs_current_insts`, `bid` |-> `end_st.cs_next_id`,
      `iv` |-> `STRING #"%" (toString st.cs_next_var)`,
      `nv` |-> `STRING #"%" (toString end_st.cs_next_var)`, `s` |-> `h`,
      `bb` |-> `<|bb_label := end_st.cs_current_bb;
        bb_instructions := end_st.cs_current_insts ++
          abi_decode_backedge_insts end_st.cs_next_id
            (STRING #"%" (toString st.cs_next_var))
            (STRING #"%" (toString end_st.cs_next_var)) ip (FST (labels:string # string # string))|>`]
      abi_decode_mem_loop_iteration)) >>
  (impl_tac >- suspend "iteration_premises") >>
  disch_then (DISJ_CASES_THEN2
    (fn th => qx_choose_then `out` strip_assume_tac th >> suspend "iteration_success")
    (fn th => disj2_tac >> ACCEPT_TAC th))
QED
Resume abi_decode_mem_dyn_loop[iteration_success]:
  markerLib.RESUME_TAC >>
  disj1_tac >> qexists_tac `out` >>
  asm_simp_tac bool_ss [Abbr `J`, Abbr `P`, Abbr `R`, Abbr `F'`, Abbr `slot`] >>
  metis_tac[abi_decoder_operand_live_mono]
QED
Resume abi_decode_mem_dyn_loop[iteration_premises]:
  markerLib.RESUME_TAC >>
  qpat_assum `st.cs_current_bb = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac [th]) >>
  qpat_assum `FST ops = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac [th]) >>
  qpat_assum `st.cs_next_var = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac [th]) >>
  fs[Abbr `J`, Abbr `P`, Abbr `RR`, Abbr `F'`, Abbr `slot`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume abi_decode_mem_dyn_loop[success]:
  markerLib.RESUME_TAC >>
  qpat_assum `final.cs_current_bb = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> rewrite_tac [th]) >>
  `R s t` by
    (gvs[Abbr `R`, abi_decode_footprint_frame_def] >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists_tac `t` >> fs[] >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    irule (SIMP_RULE (srw_ss()) []
      (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_mem_then)) >>
    qexists_tac `h` >> simp[]]
QED
Finalise abi_decode_mem_dyn_loop
