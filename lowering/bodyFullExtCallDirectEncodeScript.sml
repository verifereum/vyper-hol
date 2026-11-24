Theory bodyFullExtCallDirectEncode
Ancestors
  bodyFullExtCallDirectState bodyFullExtCallDirectWindows bodyFullExtCallDirectPhase
  exprSimWordArgs
  abiEncodeValuesRun abiEncodeValuesCode exprLoweringProps exprSimAbiEncodeExecFrame
  stateRelProj bodyPtrDefs loweringPosts loweringStateRelDefs fragGasOriginPtr fragExec
  abiEncoderWindowPhase exprLowering compileEnv context contractABI
  venomState venomInst finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

(* The cursor site is distinct from the request allocation and is the
   only allocation touched by the loop's initialization and finish. *)
Theorem abi_encode_saved_values_execute_observed:
  abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var dst_offset prefix st u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var payload_var) rows st = (alen,en) /\ fn_has_code st en func /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  abi_encode_values_init_observes ctx func lo explicit PG Obs /\
  abi_encode_values_finish_observes ctx func lo explicit PG Obs /\
  abi_encode_values_observer st en Obs R /\
  (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
    i < LENGTH rows /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var dst_offset prefix a v Gv tv /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot i a v Gv tv /\
    compile_abi_encode_value_rows ce (Var payload_var) cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?z Gz tz.
      (track_frame ==> pure_frame ce func ee se v z /\ wb_frame ce ee ee se v z) /\
      abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
        shared pbase capacity root payload_var dst_offset prefix c z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
      Obs a c v z /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) ==>
  ?z Gz tz.
    (track_frame ==> pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var dst_offset prefix en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+dst_offset <= j /\ j < pbase+dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    R u z /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  qpat_assum `compile_abi_encode_values_to_buf ce (Var payload_var) rows st = _`
    (strip_assume_tac o MATCH_MP abi_encode_values_to_buf_trace) >>
  `ci_mono st allocated /\ ci_mono allocated ready /\ ci_mono ready stored /\ ci_mono stored en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_abi_encode_value_rows, SND] >>
  `fn_has_code st allocated func` by
    metis_tac[ci_mono_def, ci_mono_trans, fn_has_code_split] >>
  `?ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_operands = [Lit 32w] /\
    ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r` by
    (mp_tac (Q.INST [`cut` |-> `se`, `en` |-> `allocated`, `n` |-> `32w`,
       `out` |-> `cursor`, `scopes` |-> `ee.scopes`] extcall_direct_alloca_site) >>
     impl_tac >- asm_rewrite_tac[] >> metis_tac[]) >>
  `!b sz. FLOOKUP u.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = 32` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
       (qx_choose_then `hz` assume_tac) >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
       (qspec_then `hz` (drule_then (assume_tac o cj 1))) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee u`
       (mp_then (Pos hd) assume_tac stmt_state_rel_alloca_size) >>
     qpat_assum `!i w b sz. MEM i (fn_insts func) /\ _ ==> _`
       (qspecl_then [`ci`,`32w`,`b`,`sz`] mp_tac) >>
     asm_simp_tac (srw_ss()) [dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func ce cx ee u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  assume_tac (Q.INST
    [`dst` |-> `Var payload_var`, `out` |-> `alen`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`,
     `owner` |-> `shared`, `b` |-> `pbase`, `cap` |-> `capacity`, `d` |-> `pbase+dst_offset`,
     `P` |-> `\a v Gv tv.
          (track_frame ==> pure_frame ce func ee se u v /\ wb_frame ce ee ee se u v) /\
          abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
            shared pbase capacity root payload_var dst_offset prefix a v Gv tv`]
    abi_encode_values_execute_observed) >>
  pop_assum (assume_tac o BETA_RULE) >>
  pop_assum (mp_tac o SIMP_RULE bool_ss [GSYM CONJ_ASSOC]) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- simp[pure_frame_refl, wb_frame_refl]
      >- (MAP_EVERY qx_gen_tac [`a`,`v`,`Gv`,`tv`] >>
          disch_then (CONJUNCTS_THEN2 kall_tac assume_tac) >>
          drule_all abi_encode_saved_state_resources >> strip_tac >>
          `stmt_state_rel hz ctx func ce cx ee v` by
            (qpat_assum
               `abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
                  shared pbase capacity root payload_var dst_offset prefix a v Gv tv`
               (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
             qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
                               stmt_state_rel H ctx func ce cx ee v /\ _`
               (drule_then (ACCEPT_TAC o cj 1))) >>
          `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
            (drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
          qpat_assum `stmt_state_rel hz ctx func ce cx ee v`
            (assume_tac o MATCH_MP stmt_state_rel_fmp_room) >>
          asm_rewrite_tac[] >> strip_tac >> fs[fmp_room_def] >> decide_tac)
      >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
          `!aid. aid IN ids ==> aid = st.cs_next_id` by
            (qpat_assum `ids SUBSET {st.cs_next_id}`
              (ACCEPT_TAC o SIMP_RULE bool_ss [SUBSET_DEF, IN_SING])) >>
          `shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid)` by
            (rpt conj_tac >> rpt strip_tac >> res_tac >> decide_tac) >>
          `(pure_frame ce func ee se u' v /\ wb_frame ce ee ee se u' v) /\
            abi_encode_saved_state ctx func ce cx st0 ee DF lo disp se s G tn
              shared pbase capacity root payload_var dst_offset prefix c v Gv tv` by
            (irule abi_encode_saved_state_phase_pure >>
            qpat_assum `window_phase ctx func _ _ ids [] _ _` (irule_at Any) >>
            qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
              (irule_at Any) >>
            qexistsl_tac [`explicit`,`PG`] >>
            asm_simp_tac (srw_ss()) [IN_INSERT] >>
            qexists_tac `hz` >> asm_rewrite_tac[] >>
            rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
            >- (gen_tac >> strip_tac >>
                qpat_assum `tv.t_mem SUBSET tu'.t_mem` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
                disch_then (qspec_then `i` irule) >> first_assum ACCEPT_TAC) >>
            gen_tac >> disch_then DISJ_CASES_TAC
            >- (qexistsl_tac [`inst`,`root`] >> asm_rewrite_tac[]) >>
            qexistsl_tac [`ci`,`r`] >> asm_rewrite_tac[] >> metis_tac[]) >>
          asm_rewrite_tac[] >>
          disch_tac >>
          mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `se`,`v` |-> `u'`,`z` |-> `v`]
            abi_encode_saved_frames_trans) >>
          asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL])
      >> qpat_assum `!ci r. MEM ci (fn_insts func) /\ _ ==> !i a c v Gv tv cursor slot. _`
           (qspecl_then [`ci`,`r`] mp_tac) >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (fn rows_step =>
        MAP_EVERY qx_gen_tac [`i`,`a`,`c`,`u'`,`Gu'`,`tu'`,`cur`,`slot`] >>
        disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
        qspecl_then [`i`,`a`,`c`,`u'`,`Gu'`,`tu'`,`cur`,`slot`] mp_tac rows_step) >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
      qexistsl_tac [`z`,`Gz`,`tz`] >>
      asm_rewrite_tac[] >>
      disch_tac >>
      mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `se`,`v` |-> `u'`]
        abi_encode_saved_frames_trans) >>
      asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  qpat_x_assum `bytes = enc (Tuple ats) (ListV avs)` SUBST_ALL_TAC >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_saved_values_execute =
  PURE_REWRITE_RULE [abi_encode_values_observe_trivial, AND_CLAUSES, IMP_CLAUSES]
    (BETA_RULE (Q.INST [`track_frame` |-> `F`, `Obs` |-> `\a c u v. T`, `R` |-> `\u v. T`]
      abi_encode_saved_values_execute_observed))

Theorem abi_encode_saved_values_execute_pure =
  PURE_REWRITE_RULE [abi_encode_values_observe_trivial, AND_CLAUSES, IMP_CLAUSES]
    (BETA_RULE (Q.INST [`track_frame` |-> `T`, `Obs` |-> `\a c u v. T`, `R` |-> `\u v. T`]
      abi_encode_saved_values_execute_observed))


Theorem extcall_direct_values_execute:
  extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var selector st u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\ 32 <= capacity /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var payload_var) rows st = (alen,en) /\ fn_has_code st en func /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
    abi_member_head_size at) rows ats /\ LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
    i < LENGTH rows /\
    extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var selector a v Gv tv /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor st.cs_next_id slot i a v Gv tv /\
    compile_abi_encode_value_rows ce (Var payload_var) cursor
      (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
      [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
    ?z Gz tz.
      extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
        shared pbase capacity root payload_var selector c z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+32) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
      !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK z,Gz,tz)) ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var selector en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\ op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase+32) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase+32 <= j /\ j < pbase+32 + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `32 <= capacity` (fn cap =>
    drule_then (fn len =>
      mp_tac (SIMP_RULE bool_ss [MATCH_MP abi_encode_saved_state_extcall len,cap]
        (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`]
          abi_encode_saved_values_execute)))
      extcall_direct_state_selector_length) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[]
QED
