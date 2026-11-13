(* Actual body-entry execution, conditional only on the recursive child. *)
Theory abiDecodeMemArrayBody
Ancestors
  abiDecodeMemArraySetup abiDecodeMemLoopIteration abiDecoderArraySetupInputs
  abiDecoderFrame abiDecoderReentry abiDecoderContract fragGasPathMem fragGasMode
  exprLoweringProps localPtrsProps allocaHistory venomState venomExecSemantics
  compileEnv emitHelperProps abiEncoder finite_map alist list arithmetic words

Theorem abi_decode_mem_array_body:
  let slot = w2n (p:bytes32) in
  let P = (\u. mem_bytes_at B H u.vs_memory = mem_bytes_at B H a.vs_memory /\
       (!q. protected q ==> mload q u = mload q a) /\
       u.vs_call_ctx = a.vs_call_ctx /\ u.vs_data_section = a.vs_data_section) in
  let F = (\u. MAP SND (FILTER (\e. lo <= FST e /\ FST e < hi)
                          (fmap_to_alist u.vs_allocas))) in
  let J = (\j lbl k u. P u /\ alloca_inv u /\ alloca_room ctx fn u /\
       alloca_history fn u /\ ~u.vs_halted /\ u.vs_current_bb = lbl /\
       u.vs_inst_idx = k /\ eval_operand ip u = SOME p /\
       eval_operand src u = SOME (n2w sb) /\
       eval_operand base_op u = SOME (n2w B) /\
       mload slot u = n2w j /\ mload (B+sb) u = n2w ncount /\
       j <= ncount /\ B+H <= u.vs_alloca_next /\
       d+sz <= u.vs_alloca_next /\ slot+32 <= u.vs_alloca_next) in
  let R = (\u v. u.vs_alloca_next <= v.vs_alloca_next /\
       (!op. abi_decoder_operand_live first op ==> eval_operand op v = eval_operand op u) /\
       (!q. q < lo \/ hi <= q ==> FLOOKUP v.vs_allocas q = FLOOKUP u.vs_allocas q) /\
       abi_decode_footprint_frame ((d,sz)::(slot,32)::F v) u v) in
  abi_decode_array_element_setup ip src dst MLOAD base_op hi_op di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi_op di middle = ((),end_st) /\
  fn_has_code st middle fn /\ fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  first <= st.cs_next_var /\ lo <= middle.cs_next_id /\ end_st.cs_next_id <= hi /\
  abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var hi_op /\
  abi_decoder_operand_live st.cs_next_var (Var iv) /\
  hi_op <> Lit 0w /\ B+H < dimword(:256) /\ d+sz < dimword(:256) /\
  asz < dimword(:256) /\ sb+32+ncount*asz <= H /\ 32+ncount*msz <= sz /\
  (dec_info_needs_offset di ==> 32 <= asz) /\
  j < ncount /\ J j st.cs_current_bb (LENGTH st.cs_current_insts) b /\
  eval_operand dst b = SOME (n2w d) /\ eval_operand hi_op b = SOME (n2w H) /\
  eval_operand (Var iv) b = SOME (n2w j) /\
  (!u c e.
    alloca_inv u /\ alloca_room ctx fn u /\ alloca_history fn u /\ ~u.vs_halted /\
    u.vs_current_bb = middle.cs_current_bb /\ u.vs_inst_idx = LENGTH middle.cs_current_insts /\
    B+H <= u.vs_alloca_next /\ e+msz <= u.vs_alloca_next /\
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
  ((?v. gas_path_mem ctx fn b 0 (OK v) /\
      J j end_st.cs_current_bb (LENGTH end_st.cs_current_insts) v /\
      eval_operand (Var iv) v = SOME (n2w j) /\ R b v) \/
   (?v. gas_marked_path T ctx fn b 0 (Abort Revert_abort v)))
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  `eval_operand ip b = SOME p /\ mload (w2n p) b = n2w j /\
   w2n p+32 <= b.vs_alloca_next /\ eval_operand src b = SOME (n2w sb) /\
   alloca_history fn b /\ alloca_inv b /\ ~b.vs_halted /\
   b.vs_current_bb = st.cs_current_bb /\ b.vs_inst_idx = LENGTH st.cs_current_insts` by
    gvs[Abbr `J`, Abbr `slot`] >>
  `(dec_info_needs_offset di ==> hi_op <> Lit 0w /\
    eval_operand base_op b = SOME (n2w B) /\ eval_operand hi_op b = SOME (n2w H) /\
    abi_decoder_operand_live st.cs_next_var base_op /\
    abi_decoder_operand_live st.cs_next_var hi_op /\ asz < dimword(:256) /\
    w2n ((n2w B:bytes32)+n2w (sb+32+j*asz):bytes32)+32 <= b.vs_alloca_next)` by
    suspend "head_bound" >>
  drule_all abi_decode_array_element_setup_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `~dec_info_needs_offset di \/ bound` >>
  Cases_on `~dec_info_needs_offset di \/ bound`
  >- suspend "accepted" >>
  disj2_tac >> qpat_x_assum `dec_info_needs_offset di /\ _ ==> _` irule >>
  full_simp_tac bool_ss [DE_MORGAN_THM]
QED
Resume abi_decode_mem_array_body[head_bound]:
  strip_tac >> asm_simp_tac bool_ss [] >>
  `B+H <= b.vs_alloca_next /\ eval_operand base_op b = SOME (n2w B)`
    by fs[Abbr `J`] >>
  `j*asz+asz <= ncount*asz` by
    (irule LESS_EQ_TRANS >> qexists_tac `(j+1)*asz` >>
     simp[RIGHT_ADD_DISTRIB] >> irule LESS_MONO_MULT2 >> decide_tac) >>
  `B+(sb+32+j*asz) < dimword(:256)` by decide_tac >>
  simp[word_add_n2w, w2n_n2w] >> gvs[]
QED
Resume abi_decode_mem_array_body[accepted]:
  qpat_x_assum `~dec_info_needs_offset di \/ _ ==> _` mp_tac >>
  asm_rewrite_tac [] >> disch_then (qx_choose_then `u` strip_assume_tac) >>
  `st.cs_next_var <= middle.cs_next_var` by
    metis_tac[abi_decode_array_element_setup_operands] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    abi_decoder_operand_live middle.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `!op. abi_decoder_operand_live first op ==>
    abi_decoder_operand_live st.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `alloca_inv u /\ alloca_room ctx fn u /\ B+H <= u.vs_alloca_next /\
   d+32+j*msz+msz <= u.vs_alloca_next` by suspend "resources" >>
  `w2n (if dec_info_needs_offset di then
      n2w (sb+32)+abi_decode_load MLOAD ((n2w B:bytes32)+n2w (sb+32+j*asz)) b
      else n2w (sb+32+j*asz):bytes32) + asz <= H` by suspend "child_bound" >>
  qpat_x_assum `!u c e. _` (qspecl_then [`u`,
    `if dec_info_needs_offset di then
      n2w (sb+32)+abi_decode_load MLOAD ((n2w B:bytes32)+n2w (sb+32+j*asz)) b
      else n2w (sb+32+j*asz)`, `d+32+j*msz`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[Abbr `J`]) >>
  strip_tac >- suspend "success" >>
  disj2_tac >> fs[gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
Resume abi_decode_mem_array_body[resources]:
  `j*msz+msz <= ncount*msz` by
    (irule LESS_EQ_TRANS >> qexists_tac `(j+1)*msz` >>
     simp[RIGHT_ADD_DISTRIB] >> irule LESS_MONO_MULT2 >> decide_tac) >>
  `alloca_room ctx fn b /\ d+sz <= b.vs_alloca_next /\ B+H <= b.vs_alloca_next`
    by fs[Abbr `J`] >>
  `alloca_inv u` by metis_tac[alloca_inv_fields] >>
  `alloca_room ctx fn u` by metis_tac[alloca_room_fields] >>
  asm_simp_tac bool_ss [] >> decide_tac
QED
Resume abi_decode_mem_array_body[child_bound]:
  `H < dimword(:256)` by decide_tac >>
  Cases_on `dec_info_needs_offset di` >- gvs[w2n_n2w] >>
  simp[w2n_n2w] >>
  `j*asz+asz <= ncount*asz` by
    (irule LESS_EQ_TRANS >> qexists_tac `(j+1)*asz` >>
     simp[RIGHT_ADD_DISTRIB] >> irule LESS_MONO_MULT2 >> decide_tac) >>
  `sb+32+j*asz < dimword(:256)` by decide_tac >> simp[] >> decide_tac
QED
Resume abi_decode_mem_array_body[success]:
  `gas_path_mem ctx fn b 0 (OK v)` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op b` by metis_tac[] >>
  `J j end_st.cs_current_bb (LENGTH end_st.cs_current_insts) v` by
    (gvs[Abbr `J`, Abbr `P`, Abbr `slot`] >> metis_tac[LESS_EQ_TRANS]) >>
  disj1_tac >> qexists_tac `v` >> asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[] >>
  simp_tac bool_ss [Abbr `R`] >> conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  suspend "frame"
QED
Resume abi_decode_mem_array_body[frame]:
  `abi_decode_footprint_frame ((d+32+j*msz,msz)::fp) b v` by
    gvs[abi_decode_footprint_frame_def] >>
  irule abi_decode_footprint_frame_weaken >> goal_assum (drule_at Any) >>
  simp[Abbr `F`, MEM_MAP, MEM_FILTER, MEM_fmap_to_alist_FLOOKUP] >>
  rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`d`,`sz`] >> simp[] >>
      `j*msz+msz <= ncount*msz` by
        (irule LESS_EQ_TRANS >> qexists_tac `(j+1)*msz` >>
         simp[RIGHT_ADD_DISTRIB] >> irule LESS_MONO_MULT2 >> decide_tac) >> decide_tac) >>
  qexistsl_tac [`d'`,`sz'`] >> simp[] >>
  disj2_tac >> disj2_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `(id,(d',sz'))` >> simp[] >> decide_tac
QED
Finalise abi_decode_mem_array_body
