(* Finite memory-safe execution of the actual decoder position loop. *)
Theory abiDecodeMemLoopIteration
Ancestors
  abiDecoderSiteEffect
  allocationGrowth abiDecoderLoopRegisters
  abiDecodeMemLoopControl abiDecoderFrame abiStepAllocRecords
  fragGasPathMem fragGasMode abiDecoderExecution abiDecoderReentry
  valueEncodingProps venomMemProofs allocaHistory localPtrsProps
  venomExecSemantics venomState finite_map alist list arithmetic words

Theorem abi_decode_mem_path_allocas[local]:
  !ctx fn s n r. gas_path_mem ctx fn s n r ==>
    !t. r = OK t ==> s.vs_allocas SUBMAP t.vs_allocas
Proof
  ho_match_mp_tac gas_path_mem_ind >> rpt conj_tac
  >- simp[]
  >- suspend "continue"
  >> rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED
Resume abi_decode_mem_path_allocas[continue]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  `s.vs_allocas SUBMAP t.vs_allocas` by
    (fs[gas_path_mem_edge_def, fragExecTheory.exit_result_def] >>
     imp_res_tac venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
     gvs[jump_to_def] >>
     imp_res_tac step_inst_allocas_extend >>
     gvs[SUBMAP_FLOOKUP_EQN] >>
     qpat_x_assum `OK _ = step_inst _ _ _ _` (mp_tac o SYM) >>
     strip_tac >> drule_then assume_tac step_inst_allocas_extend >>
     gvs[SUBMAP_FLOOKUP_EQN]) >>
  metis_tac[SUBMAP_TRANS]
QED
Finalise abi_decode_mem_path_allocas

Theorem abi_decode_mem_repeated_frame[local]:
  let F = (\u. MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
                        (fmap_to_alist u.vs_allocas))) in
  abi_decode_footprint_frame ((d,sz)::(slot,32)::F t) s t /\
  abi_decode_footprint_frame ((d,sz)::(slot,32)::F u) t u /\
  t.vs_allocas SUBMAP u.vs_allocas ==>
  abi_decode_footprint_frame ((d,sz)::(slot,32)::F u) s u
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `t` >> simp[] >>
  irule abi_decode_footprint_frame_weaken >>
  goal_assum (drule_at Any) >>
  simp[MEM_MAP, MEM_FILTER, MEM_fmap_to_alist_FLOOKUP] >>
  rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`d`,`sz`] >> simp[])
  >- (qexistsl_tac [`slot`,`32`] >> simp[]) >>
  qexistsl_tac [`d'`,`sz'`] >> simp[] >> disj2_tac >> disj2_tac >>
  qexists_tac `y` >> simp[] >> metis_tac[FLOOKUP_SUBMAP]
QED

val _ = Parse.hide "W";

val abi_decode_mem_loop_iteration_observed_quote = ``
  let slot = w2n (p:bytes32) in
  let P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H a.vs_memory /\
       (!q. protected q ==> mload q u = mload q a) /\
       u.vs_call_ctx = a.vs_call_ctx /\ u.vs_data_section = a.vs_data_section) in
  let F = (\u. MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
                          (fmap_to_alist u.vs_allocas))) in
  let J = (\j lbl k u. P u /\ alloca_inv u /\ alloca_room ctx fn u /\
       alloca_history fn u /\
       fresh_vars_wrt limit_st u /\ allocation_growth anchor u /\
       (!inst w q n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit w] /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (q,n) ==>
         n = w2n w) /\ FLOOKUP u.vs_allocas index_site = SOME (slot,32) /\
       (!q. protected q ==> (B <= q /\ q+32 <= B+H) \/
         ?id. id < lo /\ FLOOKUP u.vs_allocas id = SOME (q,32)) /\ ~u.vs_halted /\ u.vs_current_bb = lbl /\
       u.vs_inst_idx = k /\ eval_operand ip u = SOME p /\
       eval_operand src u = SOME (n2w sb) /\
       eval_operand base_op u = SOME (n2w B) /\
       eval_operand dst u = SOME (n2w d) /\
       eval_operand hi_op u = SOME (n2w H) /\
       mload slot u = n2w j /\ mload (B+sb) u = n2w ncount /\
       j <= ncount /\ B+H <= u.vs_alloca_next /\
       d+sz <= u.vs_alloca_next /\ slot+32 <= u.vs_alloca_next) in
  let R = (\u v. u.vs_alloca_next <= v.vs_alloca_next /\
       (!op. abi_decoder_operand_live first op ==> eval_operand op v = eval_operand op u) /\
       (!q. q < lo \/ hi <= q ==> FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
       abi_decode_footprint_frame ((d,sz)::(slot,32)::F v) u v) in
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid ip src MLOAD base_op first body_lbl exit_lbl|> /\
  lookup_block suffix_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts bid iv nv ip hdr /\
  lo <= hi /\ index_site < lo /\
  first+4+abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  (?next. nv = STRING #"%" (toString next) /\ next < limit_st.cs_next_var) /\
  ncount < dimword(:256) /\ B+H < dimword(:256) /\ sb+32 <= H /\
  d+sz < dimword(:256) /\ (slot+32 <= B \/ B+H <= slot) /\
  (!q. protected q ==> q+32 <= slot \/ slot+32 <= q) /\
  abi_decoder_operand_live first ip /\ abi_decoder_operand_live first src /\
  abi_decoder_operand_live first base_op /\
  abi_decoder_operand_live first dst /\ abi_decoder_operand_live first hi_op /\
  (!op. abi_decoder_operand_live first op ==> op <> Var nv) /\
  (!j u v. j <= ncount /\ W j u /\
    abi_decode_footprint_frame [(slot,32)] u v /\ decode_static_frame u v /\
    v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next /\
    (!n. limit_st.cs_next_var <= n ==>
      lookup_var (STRING #"%" (toString n)) v = lookup_var (STRING #"%" (toString n)) u) ==> W j v) /\
  (!j u. j < ncount /\ J j hdr 0 u /\ W j u ==>
    let b = jump_to body_lbl
       (abi_decode_position_header_state base_op first B sb j ncount u) in
    ((?v. gas_path_mem ctx fn b 0 (OK v) /\ J j suffix_lbl (LENGTH prefix) v /\
           eval_operand (Var iv) v = SOME (n2w j) /\ R b v /\ W (SUC j) v) \/
     (?v. gas_marked_path T ctx fn b 0 (Abort Revert_abort v) /\ Bad))) /\
  J i hdr 0 s /\ W i s ==>
  ((?t. gas_path_mem ctx fn s 0 (OK t) /\ J ncount exit_lbl 0 t /\ R s t /\ W ncount t) \/
   (?t. gas_marked_path T ctx fn s 0 (Abort Revert_abort t) /\ Bad))
``;
val abi_decode_mem_loop_iteration_observed_expansion = SIMP_CONV bool_ss [LET_THM] abi_decode_mem_loop_iteration_observed_quote;

Theorem abi_decode_mem_loop_iteration_observed:
  ^(rhs (concl abi_decode_mem_loop_iteration_observed_expansion))
Proof
  CONV_TAC (K (SYM abi_decode_mem_loop_iteration_observed_expansion)) >>
  rpt BasicProvers.LET_ELIM_TAC >> rpt strip_tac >>
  `!j u. J j hdr 0 u /\ W j u ==>
    let t = jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B sb j ncount u) in
    gas_path_mem ctx fn u 0 (OK t) /\
    J j (if j < ncount then body_lbl else exit_lbl) 0 t /\ R u t /\ W j t` by
    suspend "header" >>
  `!j v. j < ncount /\ J j suffix_lbl (LENGTH prefix) v /\
      eval_operand (Var iv) v = SOME (n2w j) /\ W (SUC j) v ==>
    let t = jump_to hdr (mstore slot (n2w (SUC j))
      (update_var nv (n2w (SUC j)) v)) in
    gas_path_mem ctx fn v 0 (OK t) /\ J (SUC j) hdr 0 t /\ R v t /\ W (SUC j) t` by
    suspend "backedge" >>
  `!u v w. gas_path_mem ctx fn v 0 (OK w) /\ R u v /\ R v w ==> R u w` by
    suspend "compose" >>
  suspend "finite"
QED
Resume abi_decode_mem_loop_iteration_observed[header]:
  markerLib.RESUME_TAC >> (rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `OK t` >>
  `alloca_inv t /\ alloca_room ctx fn t /\ alloca_history fn t /\
   t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
   t.vs_memory = u.vs_memory /\
   (!op. abi_decoder_operand_live first op ==> eval_operand op t = eval_operand op u)` by
    (simp_tac bool_ss [Abbr `t`] >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_decode_position_header_resources) >> gvs[Abbr `J`]) >>
  `src <> Var (STRING #"%" (toString first)) /\
   base_op <> Var (STRING #"%" (toString first))` by
    (conj_tac >> strip_tac >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  conj_tac
  >- (simp_tac bool_ss [Abbr `t`] >> irule abi_decode_position_header_path_mem >>
      simp[] >>
      gvs[Abbr `J`, Abbr `slot`, abi_decode_position_loop_ready_def,
          abiDecoderContractTheory.abi_decode_load_def] >>
      `B+sb < dimword(:256)` by decide_tac >> simp[] >>
      qexistsl_tac [`hid`,`ip`,`p`,`src`] >> simp[]) >>
  `fresh_vars_wrt limit_st u` by fs[Abbr `J`] >>
  drule_all abi_decoder_position_header_registers >> strip_tac >>
  `fresh_vars_wrt limit_st t` by simp[Abbr `t`] >>
  suspend "header_observe")
QED
Resume abi_decode_mem_loop_iteration_observed[header_observe]:
  markerLib.RESUME_TAC >> (
  `t.vs_call_ctx = u.vs_call_ctx /\ t.vs_data_section = u.vs_data_section /\
   t.vs_current_bb = (if j < ncount then body_lbl else exit_lbl) /\
   t.vs_inst_idx = 0 /\ t.vs_halted = u.vs_halted` by
    (Cases_on `base_op = Lit 0w` >>
     simp[Abbr `t`, jump_to_def, abi_decode_position_header_state_def, update_var_def]) >>
  `decode_static_frame u t` by
    (Cases_on `base_op = Lit 0w` >>
     simp[decode_static_frame_def, Abbr `t`, abi_decode_position_header_state_def,
       jump_to_def, update_var_def, LET_THM] >> simp[venom_state_component_equality]) >>
  `!n. limit_st.cs_next_var <= n ==>
    lookup_var (STRING #"%" (toString n)) t = lookup_var (STRING #"%" (toString n)) u` by
    fs[loweringStateRelDefsTheory.fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >>
  `W j t` by
    (`j <= ncount` by fs[Abbr `J`] >>
     qpat_assum `!j u v. j <= ncount /\ W j u /\ _ ==> _`
       (qspecl_then [`j`,`u`,`t`] MATCH_MP_TAC) >>
     simp[abi_decode_footprint_frame_def]) >>
  asm_rewrite_tac [] >> conj_tac
  >- (gvs[Abbr `J`, Abbr `P`, mload_def, allocation_growth_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[Abbr `R`, abi_decode_footprint_frame_def])
QED
Resume abi_decode_mem_loop_iteration_observed[backedge]:
  markerLib.RESUME_TAC >> (rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `OK t` >>
  `alloca_inv t /\ alloca_room ctx fn t /\ alloca_history fn t /\
   t.vs_allocas = v.vs_allocas /\ t.vs_alloca_next = v.vs_alloca_next /\
   mload slot t = n2w (SUC j) /\ abi_decode_frame slot 32 v t /\
   (!op. op <> Var nv ==> eval_operand op t = eval_operand op v)` by
    (simp_tac bool_ss [Abbr `t`, Abbr `slot`] >>
     irule (SIMP_RULE bool_ss [LET_THM] abi_decode_backedge_resources) >>
     qpat_assum `J j suffix_lbl (LENGTH prefix) v` mp_tac >>
     simp_tac bool_ss [Abbr `J`] >> strip_tac >> asm_simp_tac bool_ss []) >>
  `fresh_vars_wrt limit_st t` by
    (simp[Abbr `t`, emitHelperPropsTheory.fresh_vars_wrt_mstore] >>
     irule emitHelperPropsTheory.fresh_vars_wrt_mstore >>
     irule abi_decoder_generated_update_fresh >>
     qpat_assum `J j suffix_lbl (LENGTH prefix) v` mp_tac >>
     simp_tac bool_ss [Abbr `J`] >> strip_tac >> asm_simp_tac bool_ss []) >>
  `ip <> Var nv` by metis_tac[] >>
  conj_tac
  >- (simp_tac bool_ss [Abbr `t`, Abbr `slot`] >> irule abi_decode_backedge_path_mem >>
      qpat_assum `J j suffix_lbl (LENGTH prefix) v` mp_tac >>
      simp_tac bool_ss [Abbr `J`] >> strip_tac >> metis_tac[]) >>
  `P t /\ mload (B+sb) t = n2w ncount` by
    (`!q. q+32 <= slot \/ slot+32 <= q ==> mload q t = mload q v` by
       (rpt strip_tac >> rewrite_tac[GSYM mem_word_at_eq_mload] >>
        irule abiDecoderFrameComposeTheory.abi_decode_frame_mem_word >>
        qexistsl_tac [`slot`,`32`] >> simp[]) >>
     `mem_bytes_at B H t.vs_memory = mem_bytes_at B H v.vs_memory` by
       (fs[abiDecoderContractTheory.abi_decode_frame_def]) >>
     `mload (B+sb) t = mload (B+sb) v` by
       (first_x_assum irule >> decide_tac) >>
     qpat_assum `abi_decode_frame slot 32 v t` mp_tac >>
     simp_tac bool_ss [abiDecoderContractTheory.abi_decode_frame_def] >> strip_tac >>
     qpat_assum `J j suffix_lbl (LENGTH prefix) v` mp_tac >>
     simp_tac bool_ss [Abbr `J`, Abbr `P`] >> strip_tac >> asm_simp_tac bool_ss [] >>
     metis_tac[]) >>
  suspend "backedge_observe")
QED
Resume abi_decode_mem_loop_iteration_observed[backedge_observe]:
  markerLib.RESUME_TAC >> (
  `t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ t.vs_halted = v.vs_halted` by
    simp[Abbr `t`, jump_to_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  `decode_static_frame v t` by
    simp[decode_static_frame_def, Abbr `t`, jump_to_def, mstore_def,
      write_memory_with_expansion_def, update_var_def, venom_state_component_equality] >>
  `fresh_vars_wrt limit_st v` by
    (qpat_assum `J j suffix_lbl (LENGTH prefix) v` mp_tac >>
     simp_tac bool_ss [Abbr `J`] >> strip_tac >> asm_rewrite_tac []) >>
  `!n. limit_st.cs_next_var <= n ==>
    lookup_var (STRING #"%" (toString n)) t = lookup_var (STRING #"%" (toString n)) v` by
    fs[loweringStateRelDefsTheory.fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >>
  `W (SUC j) t` by
    (qpat_assum `!j u v. j <= ncount /\ W j u /\ _ ==> _`
       (qspecl_then [`SUC j`,`v`,`t`] MATCH_MP_TAC) >>
     `SUC j <= ncount` by decide_tac >>
     simp[GSYM abiDecoderFrameComposeTheory.abi_decode_frame_footprint]) >>
  `src <> Var nv /\ base_op <> Var nv /\ dst <> Var nv /\ hi_op <> Var nv`
    by metis_tac[] >>
  `SUC j <= ncount` by decide_tac >>
  asm_rewrite_tac [] >> conj_tac
  >- (qpat_assum `J j suffix_lbl (LENGTH prefix) v` mp_tac >>
      simp_tac bool_ss [Abbr `J`, allocation_growth_def] >> strip_tac >>
      asm_simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  fs[abiDecoderContractTheory.abi_decode_frame_def] >>
  asm_simp_tac (srw_ss()) [Abbr `R`, abi_decode_footprint_frame_def] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[abi_footprint_disjoint_def] >> metis_tac[] )
QED
Resume abi_decode_mem_loop_iteration_observed[compose]:
  markerLib.RESUME_TAC >> (rpt gen_tac >> strip_tac >>
  `v.vs_allocas SUBMAP w.vs_allocas` by
    (drule abi_decode_mem_path_allocas >> simp[]) >>
  gvs[Abbr `R`] >> conj_tac >- metis_tac[] >>
  gvs[Abbr `F'`] >>
  metis_tac[SIMP_RULE bool_ss [LET_THM] abi_decode_mem_repeated_frame])
QED
Resume abi_decode_mem_loop_iteration_observed[finite]:
  markerLib.RESUME_TAC >> (
  qsuff_tac `!r i s. r = ncount-i /\ J i hdr 0 s /\ W i s ==>
    ((?t. gas_path_mem ctx fn s 0 (OK t) /\ J ncount exit_lbl 0 t /\ R s t /\ W ncount t) \/
     (?t. gas_marked_path T ctx fn s 0 (Abort Revert_abort t) /\ Bad))`
  >- metis_tac[] >>
  qpat_x_assum `J i hdr 0 s` kall_tac >> qpat_x_assum `W i s` kall_tac >>
  completeInduct_on `r` >> rpt strip_tac >>
  rename1 `remaining = ncount-i` >>
  `i <= ncount` by
    (qpat_assum `J i hdr 0 s` mp_tac >>
     simp_tac bool_ss [Abbr `J`] >> strip_tac >> asm_rewrite_tac []) >>
  Cases_on `i = ncount`
  >- (gvs[] >> qpat_x_assum `!j u. J j hdr 0 u /\ W j u ==> _`
        (qspecl_then [`i`,`s`] mp_tac) >>
      simp_tac bool_ss [LET_THM] >> (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `gas_path_mem ctx fn s 0 (OK out)` >>
      disj1_tac >> qexists_tac `out` >> simp[]) >>
  `i < ncount` by decide_tac >>
  qpat_x_assum `!j u. J j hdr 0 u /\ W j u ==> _` (qspecl_then [`i`,`s`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> (impl_tac >- simp[]) >>
  qmatch_goalsub_abbrev_tac `OK b` >> strip_tac >> fs[] >>
  qpat_x_assum `!j u b. Abbrev _ ==> _` (qspecl_then [`i`,`s`,`b`] mp_tac) >>
  simp[markerTheory.Abbrev_def, Abbr `b`] >>
  disch_then strip_assume_tac
  >- suspend "success" >>
  disj2_tac >> fs[gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED
Resume abi_decode_mem_loop_iteration_observed[success]:
  markerLib.RESUME_TAC >> (
  `eval_operand (Var iv) v = SOME (n2w i)` by gvs[] >>
  qpat_assum `!j v. j < ncount /\ _ /\ _ ==> _` drule_all >>
  simp_tac bool_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac `OK w` >> strip_tac >>
  qpat_x_assum `!m. m < _ ==> !i s. _`
    (qspec_then `ncount-SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`SUC i`,`w`] mp_tac) >> simp[] >>
  disch_then strip_assume_tac
  >- suspend "finish" >>
  disj2_tac >> fs[gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED
Resume abi_decode_mem_loop_iteration_observed[finish]:
  markerLib.RESUME_TAC >> (
  `gas_path_mem ctx fn s 0 (OK v)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `R s v` by metis_tac[] >>
  `R s w` by metis_tac[] >>
  `R s t` by metis_tac[] >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES])
QED
Finalise abi_decode_mem_loop_iteration_observed

Theorem abi_decode_mem_loop_iteration:
  let slot = w2n (p:bytes32) in
  let P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H a.vs_memory /\
       (!q. protected q ==> mload q u = mload q a) /\
       u.vs_call_ctx = a.vs_call_ctx /\ u.vs_data_section = a.vs_data_section) in
  let F = (\u. MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
                          (fmap_to_alist u.vs_allocas))) in
  let J = (\j lbl k u. P u /\ alloca_inv u /\ alloca_room ctx fn u /\
       alloca_history fn u /\
       fresh_vars_wrt limit_st u /\ allocation_growth anchor u /\
       (!inst w q n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit w] /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (q,n) ==>
         n = w2n w) /\ FLOOKUP u.vs_allocas index_site = SOME (slot,32) /\
       (!q. protected q ==> (B <= q /\ q+32 <= B+H) \/
         ?id. id < lo /\ FLOOKUP u.vs_allocas id = SOME (q,32)) /\ ~u.vs_halted /\ u.vs_current_bb = lbl /\
       u.vs_inst_idx = k /\ eval_operand ip u = SOME p /\
       eval_operand src u = SOME (n2w sb) /\
       eval_operand base_op u = SOME (n2w B) /\
       eval_operand dst u = SOME (n2w d) /\
       eval_operand hi_op u = SOME (n2w H) /\
       mload slot u = n2w j /\ mload (B+sb) u = n2w ncount /\
       j <= ncount /\ B+H <= u.vs_alloca_next /\
       d+sz <= u.vs_alloca_next /\ slot+32 <= u.vs_alloca_next) in
  let R = (\u v. u.vs_alloca_next <= v.vs_alloca_next /\
       (!op. abi_decoder_operand_live first op ==> eval_operand op v = eval_operand op u) /\
       (!q. q < lo \/ hi <= q ==> FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
       abi_decode_footprint_frame ((d,sz)::(slot,32)::F v) u v) in
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl hid ip src MLOAD base_op first /\
  lookup_block suffix_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts bid iv nv ip hdr /\
  lo <= hi /\ index_site < lo /\
  first+4+abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  (?next. nv = STRING #"%" (toString next) /\ next < limit_st.cs_next_var) /\
  ncount < dimword(:256) /\ B+H < dimword(:256) /\ sb+32 <= H /\
  d+sz < dimword(:256) /\ (slot+32 <= B \/ B+H <= slot) /\
  (!q. protected q ==> q+32 <= slot \/ slot+32 <= q) /\
  abi_decoder_operand_live first ip /\ abi_decoder_operand_live first src /\
  abi_decoder_operand_live first base_op /\
  abi_decoder_operand_live first dst /\ abi_decoder_operand_live first hi_op /\
  (!op. abi_decoder_operand_live first op ==> op <> Var nv) /\
  (!j u. j < ncount /\ J j hdr 0 u ==>
    let b = jump_to body_lbl
       (abi_decode_position_header_state base_op first B sb j ncount u) in
    ((?v. gas_path_mem ctx fn b 0 (OK v) /\ J j suffix_lbl (LENGTH prefix) v /\
           eval_operand (Var iv) v = SOME (n2w j) /\ R b v) \/
     (?v. gas_marked_path T ctx fn b 0 (Abort Revert_abort v)))) /\
  J i hdr 0 s ==>
  ((?t. gas_path_mem ctx fn s 0 (OK t) /\ J ncount exit_lbl 0 t /\ R s t) \/
   (?t. gas_marked_path T ctx fn s 0 (Abort Revert_abort t)))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`W` |-> `\(j:num) (u:venom_state). T`, `Bad` |-> `T`]
      abi_decode_mem_loop_iteration_observed)) >>
  qpat_assum `abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl hid ip src MLOAD base_op first` mp_tac >>
  simp_tac bool_ss [abi_decode_position_loop_cfg_def] >> strip_tac >>
  asm_rewrite_tac [] >> simp[ASCIInumbersTheory.toString_11]
QED

(* Constructor entry uses the same anchored contract with a zero index. *)
Theorem abi_decode_mem_loop_zero:
  let slot = w2n (p:bytes32) in
  let P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H a.vs_memory /\
       (!q. protected q ==> mload q u = mload q a) /\
       u.vs_call_ctx = a.vs_call_ctx /\ u.vs_data_section = a.vs_data_section) in
  let F = (\u. MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
                          (fmap_to_alist u.vs_allocas))) in
  let J = (\j lbl k u. P u /\ alloca_inv u /\ alloca_room ctx fn u /\
       alloca_history fn u /\
       fresh_vars_wrt limit_st u /\ allocation_growth anchor u /\
       (!inst w q n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
         inst.inst_operands = [Lit w] /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (q,n) ==>
         n = w2n w) /\ FLOOKUP u.vs_allocas index_site = SOME (slot,32) /\
       (!q. protected q ==> (B <= q /\ q+32 <= B+H) \/
         ?id. id < lo /\ FLOOKUP u.vs_allocas id = SOME (q,32)) /\ ~u.vs_halted /\ u.vs_current_bb = lbl /\
       u.vs_inst_idx = k /\ eval_operand ip u = SOME p /\
       eval_operand src u = SOME (n2w sb) /\
       eval_operand base_op u = SOME (n2w B) /\
       eval_operand dst u = SOME (n2w d) /\
       eval_operand hi_op u = SOME (n2w H) /\
       mload slot u = n2w j /\ mload (B+sb) u = n2w ncount /\
       j <= ncount /\ B+H <= u.vs_alloca_next /\
       d+sz <= u.vs_alloca_next /\ slot+32 <= u.vs_alloca_next) in
  let R = (\u v. u.vs_alloca_next <= v.vs_alloca_next /\
       (!op. abi_decoder_operand_live first op ==> eval_operand op v = eval_operand op u) /\
       (!q. q < lo \/ hi <= q ==> FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
       abi_decode_footprint_frame ((d,sz)::(slot,32)::F v) u v) in
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl hid ip src MLOAD base_op first /\
  lookup_block suffix_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts bid iv nv ip hdr /\
  lo <= hi /\ index_site < lo /\
  first+4+abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  (?next. nv = STRING #"%" (toString next) /\ next < limit_st.cs_next_var) /\
  ncount < dimword(:256) /\ B+H < dimword(:256) /\ sb+32 <= H /\
  d+sz < dimword(:256) /\ (slot+32 <= B \/ B+H <= slot) /\
  (!q. protected q ==> q+32 <= slot \/ slot+32 <= q) /\
  abi_decoder_operand_live first ip /\ abi_decoder_operand_live first src /\
  abi_decoder_operand_live first base_op /\
  abi_decoder_operand_live first dst /\ abi_decoder_operand_live first hi_op /\
  (!op. abi_decoder_operand_live first op ==> op <> Var nv) /\
  (!j u. j < ncount /\ J j hdr 0 u ==>
    let b = jump_to body_lbl
       (abi_decode_position_header_state base_op first B sb j ncount u) in
    ((?v. gas_path_mem ctx fn b 0 (OK v) /\ J j suffix_lbl (LENGTH prefix) v /\
           eval_operand (Var iv) v = SOME (n2w j) /\ R b v) \/
     (?v. gas_marked_path T ctx fn b 0 (Abort Revert_abort v)))) /\
  J 0 hdr 0 s ==>
  ((?t. gas_path_mem ctx fn s 0 (OK t) /\ J ncount exit_lbl 0 t /\ R s t) \/
   (?t. gas_marked_path T ctx fn s 0 (Abort Revert_abort t)))
Proof
  MATCH_ACCEPT_TAC (Q.INST [`i` |-> `0`] abi_decode_mem_loop_iteration)
QED
