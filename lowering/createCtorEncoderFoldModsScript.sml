Theory createCtorEncoderFoldMods
Ancestors
  createExprSizeExitDefsMods bodyFullShadowBodyInv
  bodyFullExtCallDirectWindows bodyFullExtCallDirectPhase
  abiEncodeValuesRun abiEncodeValuesCode exprLoweringProps exprSimWordArgs
  exprSimAbiEncodeExecFrame stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs
  fragGasOriginPtr fragExec abiEncoderWindowPhase exprLowering compileEnv context contractABI
  venomState venomInst finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem ctor_encoder_saved_fold_resources[local]:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  valid_horizon cx st0 H ee.storage_trace ==>
  alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)
Proof
  simp_tac bool_ss [abi_encode_saved_state_mods_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  drule_then (assume_tac o cj 2) stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  drule_then assume_tac stmt_state_rel_fmp_room >>
  asm_rewrite_tac[] >> strip_tac >> fs[fmp_room_def] >> decide_tac
QED

Theorem ctor_encoder_saved_fold_cursor[local]:
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce se /\
  se.cs_next_var <= st.cs_next_var ==>
  ?ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_operands = [Lit 32w] /\
    ci.inst_outputs = [r] /\ not_local_ptr ce scopes r
Proof
  strip_tac >> drule_then strip_assume_tac abi_encode_values_to_buf_trace >>
  `ci_mono allocated ready` by metis_tac[ci_mono_emit_void, SND] >>
  `ci_mono ready stored` by metis_tac[ci_mono_compile_abi_encode_value_rows, SND] >>
  `ci_mono stored en` by metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono allocated en` by metis_tac[ci_mono_trans] >>
  `ci_mono st allocated` by metis_tac[ci_mono_emit_op, SND] >>
  `fn_has_code st allocated func` by metis_tac[ci_mono_def, fn_has_code_split] >>
  mp_tac (Q.INST [`cut` |-> `se`, `en` |-> `allocated`, `n` |-> `32w`,
    `out` |-> `cursor`] extcall_direct_alloca_site) >>
  impl_tac >- asm_rewrite_tac[] >> metis_tac[]
QED

(* The callbacks account for registered cursor phases and single rows.
   The machine fold does not inspect the source representation of a row. *)
Theorem ctor_encoder_saved_fold_mods:
  abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix st u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (alen,en) /\ fn_has_code st en func /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  (!a c ids outs v Gv tv z Gz tz.
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a v Gv tv /\
    ci_mono a c /\ window_phase ctx func a c ids outs v z /\ abi_encode_exec_frame func v z /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) /\
    (!x. not_fresh_at a x ==>
      FLOOKUP Gz x = FLOOKUP Gv x /\ op_taint tz (Var x) = op_taint tv (Var x)) /\
    tz.t_stor = tv.t_stor /\ tz.t_trans = tv.t_trans /\ tz.t_imm = tv.t_imm /\
    shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
    EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
    (!aid. aid IN shared INSERT ids ==>
      ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
    (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
      (!aid p n. aid IN ids /\ FLOOKUP z.vs_allocas aid = SOME (p,n) ==>
        i < p \/ p+n <= i) /\ i IN tz.t_mem ==> i IN tv.t_mem) ==>
    (pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix c z Gz tz) /\
  (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
    i < LENGTH rows /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a v Gv tv /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot i a v Gv tv /\
    compile_abi_encode_value_rows ce (Var dst) cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?z Gz tz.
      (pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
      abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix c z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo d se s G tn _ _ _ _ _ _ _ st u Gu tu`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_mods_def]) >>
  `stmt_state_rel hz ctx func ce cx ee u` by
    (qpat_assum `!h. valid_horizon cx st0 h ee.storage_trace ==> stmt_state_rel h ctx func ce cx ee u /\ _`
      (qspec_then `hz` (drule_then (ACCEPT_TAC o cj 1)))) >>
  `?ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_operands = [Lit 32w] /\
    ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r` by
    (irule ctor_encoder_saved_fold_cursor >>
     qpat_assum `compile_abi_encode_values_to_buf _ _ _ _ = _` (irule_at Any) >>
     qexists_tac `se` >> asm_rewrite_tac[]) >>
  `!b sz. FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    (`w2n (32w:256 word) = 32` by
       simp_tac (srw_ss()) [dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     drule stmt_state_rel_alloca_size >> disch_then (qspecl_then [`ci`,`32w`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `!v z. pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v /\
          pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z ==>
          pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_saved_frames_trans >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee u` (irule_at Any) >>
     asm_rewrite_tac[] >> qexistsl_tac [`v`,`se`] >> asm_rewrite_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `payload_var = dst` >>
  qabbrev_tac `disp = d` >>
  mp_tac (BETA_RULE (Q.INST
    [`dst` |-> `Var payload_var`, `out` |-> `alen`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`,
     `owner` |-> `shared`, `b` |-> `pbase`, `cap` |-> `capacity`, `d` |-> `pbase+dst_offset`,
     `P` |-> `\a v Gv tv.
        (pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
        abi_encode_saved_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
          shared pbase capacity root payload_var dst_offset prefix a v Gv tv`]
    abi_encode_values_execute)) >>
  unabbrev_all_tac >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (simp_tac bool_ss [pure_frame_refl, wb_frame_refl] >> NO_TAC)
      >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          irule ctor_encoder_saved_fold_resources >>
          qpat_assum `abi_encode_saved_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
            (irule_at Any) >>
          qexists_tac `hz` >> asm_rewrite_tac[])
      >- (MAP_EVERY qx_gen_tac [`a`,`c`,`ids`,`v`,`Gv`,`tv`,`z`,`Gz`,`tz`] >>
          disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          qpat_assum `ids SUBSET {st.cs_next_id}`
            (assume_tac o SIMP_RULE bool_ss [SUBSET_DEF, IN_SING]) >>
          `shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid)` by
            (conj_tac
             >- (strip_tac >> qpat_assum `!x. x IN ids ==> x = _` drule >> decide_tac) >>
             rpt strip_tac >> qpat_assum `!x. x IN ids ==> x = _` drule >> decide_tac) >>
          qpat_x_assum `!a c ids outs v Gv tv z Gz tz. _`
            (qspecl_then [`a`,`c`,`ids`,`[]`,`v`,`Gv`,`tv`,`z`,`Gz`,`tz`] mp_tac) >>
          asm_rewrite_tac[EVERY_DEF] >>
          (impl_tac
           >- (conj_tac
               >- (simp_tac bool_ss [IN_INSERT] >> gen_tac >> disch_then DISJ_CASES_TAC
                   >- (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
                   `aid = st.cs_next_id` by
                     (qpat_assum `!x. x IN ids ==> x = _` (drule_then ACCEPT_TAC)) >>
                   qexistsl_tac [`ci`,`r`] >> asm_rewrite_tac[]) >>
               rpt strip_tac >>
               qpat_assum `tz.t_mem SUBSET tv.t_mem`
                 (irule o REWRITE_RULE [SUBSET_DEF]) >> asm_rewrite_tac[])) >>
          disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          asm_rewrite_tac[] >>
          qpat_assum `!v z. pure_frame ce func ee se u v /\ _ ==> _`
            (qspecl_then [`v`,`z`] mp_tac) >>
          (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC)
      >> MAP_EVERY qx_gen_tac [`i`,`a`,`c`,`v`,`Gv`,`tv`,`cursor`,`slot`] >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      qpat_x_assum `!ci r. MEM ci (fn_insts func) /\ _ ==> _`
        (qspecl_then [`ci`,`r`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (qspecl_then [`i`,`a`,`c`,`v`,`Gv`,`tv`,`cursor`,`slot`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >>
      qpat_assum `!v z. pure_frame ce func ee se u v /\ _ ==> _`
        (qspecl_then [`v`,`z`] mp_tac) >>
          (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC) >>
  rewrite_tac[CONJ_ASSOC] >> disch_then ACCEPT_TAC
QED
