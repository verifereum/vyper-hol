(* Adapt the physical ABI tuple driver to the linked saved-buffer state. *)
Theory bodyAbiTupleLinkedLoopMods
Ancestors
  abiEncodeValuesRun abiEncodeValuesCode bodyFullExtCallDirectWindows
  bodyAbiTupleBufferResourcesMods bodyAbiTupleBufferPhaseMods bodyAbiTuplePhaseEffectMods
  bodyAbiTupleBufferStateMods loweringStateRelDefs
  stateRelProj entryDecodeStructure abiEncoderWindowPhase abiEncoderRegisteredEffect
  abiEncoderWindowContract contractABI
  exprSimAbiEncodeExecFrame fragGasOriginPtr fragExec exprLoweringProps
  exprLowering compileEnv venomState venomInst finite_map pred_set list pair arithmetic words

(* The driver's abstract phase does not know that the cursor ALLOCA has
   already been emitted. Raise just the bound used in the effect proof;
   the live buffer, executed code, and row callback all use the real cut.
   At a row and at loop exit this adjustment is the identity. *)
Definition loop_effect_cut_def[local]:
  loop_effect_cut k a = (a with cs_next_id := MAX (SUC k) a.cs_next_id)
End

Theorem loop_effect_cut_reached[local]:
  k < a.cs_next_id ==> loop_effect_cut k a = a
Proof
  strip_tac >> `SUC k <= a.cs_next_id` by decide_tac >>
  simp[loop_effect_cut_def, MAX_EQ_GE]
QED

Theorem loop_effect_cut_mono[local]:
  ci_mono a c ==> ci_mono (loop_effect_cut k a) (loop_effect_cut k c)
Proof
  simp[ci_mono_def, loop_effect_cut_def, cs_extends_def, MAX_LE]
QED

Theorem loop_effect_refl[local]:
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset k
    a u Gu tu (loop_effect_cut k a) u Gu tu
Proof
  simp[abi_tuple_row_effects_mods_def, window_alloca_growth_refl] >>
  conj_tac
  >- simp[ci_mono_def, loop_effect_cut_def, cs_extends_def, MAX_LE] >>
  qexistsl [`{}`,`[]`] >> simp[abi_encoder_registered_effect_refl]
QED

(* If the cursor is absent at exit, it excludes no writes, and an old
   entry cannot have disappeared. The effective footprint is then empty. *)
Theorem loop_effect_absent[local]:
  window_phase ctx func a c ids [] u v /\ ids SUBSET {k} /\
  FLOOKUP v.vs_allocas k = NONE ==>
  window_phase ctx func a c {} [] u v
Proof
  simp_tac bool_ss [window_phase_def, abi_encoder_registered_effect_def] >>
  strip_tac >> asm_rewrite_tac[] >> fs[SUBSET_DEF, IN_SING] >>
  `FLOOKUP u.vs_allocas k = NONE` by
    (Cases_on `FLOOKUP u.vs_allocas k` >- simp[] >>
     rename1 `FLOOKUP u.vs_allocas k = SOME bn` >>
     qpat_assum `!i r. FLOOKUP u.vs_allocas i = SOME r ==> _`
       (qspecl_then [`k`,`bn`] (drule_then assume_tac)) >>
     gvs[]) >>
  conj_tac
  >- (gen_tac >> Cases_on `i = k` >- simp[] >>
      qpat_assum `!i. i NOTIN ids ==> _` irule >> metis_tac[]) >>
  gen_tac >> qpat_assum `!a. _ ==> mem_bytes_at a 1 _ = _` irule >>
  rpt strip_tac >> `i = k` by metis_tac[] >> gvs[]
QED

Theorem loop_phase_effect[local]:
  ci_mono a c /\ window_phase ctx func a c ids [] u v /\
  abi_encode_exec_frame func u v /\ ids SUBSET {k} /\ shared <> k /\
  (!p n. FLOOKUP v.vs_allocas k = SOME (p,n) ==> n = 32) /\
  MEM ci (fn_insts func) /\ ci.inst_id = k /\ ci.inst_opcode = ALLOCA /\
  ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  tv.t_mem SUBSET tu.t_mem ==>
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset k
    (loop_effect_cut k a) u Gu tu (loop_effect_cut k c) v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then (qspec_then `k` assume_tac) (GEN_ALL loop_effect_cut_mono) >>
  Cases_on `FLOOKUP v.vs_allocas k` >-
    (drule_all_then assume_tac loop_effect_absent >>
     irule abi_tuple_phase_effect_mods >>
     fs[loop_effect_cut_def, not_fresh_at_def] >>
     qexistsl [`ctx`,`{}`,`[]`] >>
     fs[window_phase_def, not_fresh_at_def, SUBSET_DEF]) >>
  rename1 `FLOOKUP v.vs_allocas k = SOME bn` >> PairCases_on `bn` >>
  qpat_x_assum `!p n. SOME _ = SOME (p,n) ==> _`
    (qspecl_then [`bn0`,`bn1`] mp_tac) >> simp[] >>
  disch_then SUBST_ALL_TAC >>
  irule abi_tuple_phase_effect_mods >>
  fs[loop_effect_cut_def, not_fresh_at_def] >>
  qexistsl [`ctx`,`ids`,`[]`] >>
  fs[window_phase_def, not_fresh_at_def, SUBSET_DEF, IN_SING] >>
  conj_tac >- (rpt strip_tac >> qexistsl [`ci`,`r`] >> simp[]) >>
  strip_tac >> res_tac >> simp[]
QED

Theorem loop_cursor_alloca_size[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var dst_offset prefix a v Gv tv /\
  valid_horizon cx st0 H ee.storage_trace /\
  MEM ci (fn_insts func) /\ ci.inst_opcode = ALLOCA /\ ci.inst_operands = [Lit 32w] ==>
  !p n. FLOOKUP v.vs_allocas ci.inst_id = SOME (p,n) ==> n = 32
Proof
  simp_tac bool_ss [abi_tuple_buffer_state_mods_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `w2n (32w:256 word) = 32` by
    simp_tac (srw_ss()) [wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  drule stmt_state_rel_alloca_size >>
  disch_then (qspecl_then [`ci`,`32w`] mp_tac) >>
  asm_rewrite_tac[]
QED

Theorem loop_cursor_site[local]:
  compile_abi_encode_values_to_buf ce dst rows st = (alen,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce se /\ se.cs_next_var <= st.cs_next_var ==>
  st.cs_next_id < en.cs_next_id /\
  ?ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_operands = [Lit 32w] /\
    ci.inst_outputs = [r] /\ not_local_ptr ce scopes r
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac abi_encode_values_to_buf_trace >>
  `ci_mono st allocated /\ ci_mono allocated ready /\ ci_mono ready stored /\
    ci_mono stored en` by
    metis_tac[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_abi_encode_value_rows, SND] >>
  `ci_mono allocated en` by metis_tac[ci_mono_trans] >>
  conj_tac
  >- (drule emit_op_next_id >> fs[ci_mono_def] >> decide_tac) >>
  `fn_has_code st allocated func` by metis_tac[ci_mono_def, fn_has_code_split] >>
  drule_all extcall_direct_alloca_site >> metis_tac[]
QED

Theorem loop_buffer_pure_phase[local]:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = shared /\ inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM ci (fn_insts func) /\ ci.inst_id = k /\ ci.inst_opcode = ALLOCA /\
  ci.inst_operands = [Lit 32w] /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r /\
  shared < k /\ se.cs_next_id <= k /\
  ci_mono a c /\ window_phase ctx func a c ids [] u v /\
  abi_encode_exec_frame func u v /\ ids SUBSET {k} /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  tv.t_mem SUBSET tu.t_mem ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var dst_offset prefix c v Gv tv /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset k
    (loop_effect_cut k a) u Gu tu (loop_effect_cut k c) v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!aid. aid IN ids ==> aid = k` by fs[SUBSET_DEF] >>
  conj_asm1_tac
  >- (irule abi_tuple_buffer_phase_state_mods >>
      qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
      qhdtm_assum `window_phase` (irule_at Any) >>
      qexistsl [`explicit`,`PG`] >> asm_simp_tac (srw_ss()) [IN_INSERT] >>
      `shared NOTIN ids` by (strip_tac >> res_tac >> decide_tac) >>
      asm_rewrite_tac[] >>
      qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
        (qx_choose_then `hz` assume_tac) >>
      qexists `hz` >> asm_rewrite_tac[] >> conj_tac
      >- fs[SUBSET_DEF] >>
      gen_tac >> disch_then DISJ_CASES_TAC
      >- (qexistsl [`inst`,`root`] >> simp[]) >>
      res_tac >> qexistsl [`ci`,`r`] >> simp[]) >>
  `!p n. FLOOKUP v.vs_allocas k = SOME (p,n) ==> n = 32` by
    (qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c v Gv tv`
      (mp_then (Pos hd) mp_tac loop_cursor_alloca_size) >> metis_tac[]) >>
  irule loop_phase_effect >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qexistsl [`r`,`ci`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem abi_tuple_linked_loop_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
    shared pbase capacity root payload_var dst_offset prefix st u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = shared /\ inst.inst_outputs = [root] /\
  not_local_ptr ce ee.scopes root /\
  compile_abi_encode_values_to_buf ce (Var payload_var) rows st = (alen,en) /\
  fn_has_code st en func /\
  LIST_REL (\row at.
    abi_embedded_static_size ce.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  (!ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
    ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\
    not_local_ptr ce ee.scopes r ==>
    !i a c v Gv tv cursor slot.
      i < LENGTH rows /\
      abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
        shared pbase capacity root payload_var dst_offset prefix a v Gv tv /\
      abi_encode_values_prefix_at ats avs hl
        (pbase + dst_offset) cursor st.cs_next_id slot i a v Gv tv /\
      compile_abi_encode_value_rows ce (Var payload_var) cursor
        (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND)
          (TAKE i rows))) [EL i rows] a = ((),c) /\
      fn_has_code a c func ==>
      ?z Gz tz.
        abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
          shared pbase capacity root payload_var dst_offset prefix c z Gz tz /\
        abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset st.cs_next_id
          a v Gv tv c z Gz tz /\
        abi_encode_values_prefix_at ats avs hl
          (pbase + dst_offset) cursor st.cs_next_id slot (SUC i) c z Gz tz /\
        !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (v,Gv,tv) [] (OK z,Gz,tz)) ==>
  ?z Gz tz.
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
      shared pbase capacity root payload_var dst_offset prefix en z Gz tz /\
    abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset st.cs_next_id
      st u Gu tu en z Gz tz /\
    eval_operand alen z = SOME (n2w (LENGTH bytes)) /\
    op_taint tz alen = {} /\
    (!x. alen = Var x ==> not_fresh_at en x) /\
    mem_bytes_at (pbase + dst_offset) (LENGTH bytes) z.vs_memory = bytes /\
    (!j. pbase + dst_offset <= j /\
      j < pbase + dst_offset + LENGTH bytes ==> j NOTIN tz.t_mem) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `se.cs_next_var <= st.cs_next_var /\ se.cs_next_id <= shared /\
    shared < st.cs_next_id /\ FLOOKUP u.vs_allocas shared = SOME (pbase,capacity)` by
    fs[abi_tuple_buffer_state_mods_def] >>
  drule_all_then (qspec_then `ee.scopes`
    (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`ci`,`r`]
      (MAP_EVERY assume_tac o CONJUNCTS)))) loop_cursor_site >>
  `se.cs_next_id <= st.cs_next_id` by decide_tac >>
  `!p n. FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,n) ==> n = 32` by
    (qhdtm_assum `abi_tuple_buffer_state_mods`
      (mp_then (Pos hd) mp_tac loop_cursor_alloca_size) >> metis_tac[]) >>
  qpat_x_assum `!ci r. MEM ci (fn_insts func) /\ _ ==> _`
    (qspecl_then [`ci`,`r`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (mk_asm "row_step") >>
  mp_tac (Q.INST
    [`dst` |-> `Var payload_var`, `out` |-> `alen`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`,
     `owner` |-> `shared`, `b` |-> `pbase`, `cap` |-> `capacity`, `d` |-> `pbase+dst_offset`,
     `P` |-> `\a v Gv tv.
       abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo disp se s G tn
         shared pbase capacity root payload_var dst_offset prefix a v Gv tv /\
       abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset st.cs_next_id
         st u Gu tu (loop_effect_cut st.cs_next_id a) v Gv tv`]
    abi_encode_values_execute |> BETA_RULE |> PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- simp[loop_effect_refl]
     >- (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC abi_tuple_buffer_resources_mods)
     >- suspend "pure_phase"
     >> suspend "row") >>
  simp[loop_effect_cut_reached]
QED

Resume abi_tuple_linked_loop_mods[pure_phase]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st u Gu tu`
    kall_tac >>
  drule_all_then strip_assume_tac loop_buffer_pure_phase >>
  asm_rewrite_tac[] >>
  irule abi_tuple_row_effects_trans_mods >>
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ st u Gu tu _ _ _ _`
    (irule_at Any) >>
  first_assum ACCEPT_TAC
QED

Resume abi_tuple_linked_loop_mods[row]:
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_x "row_step" (drule_all_then
    (qx_choosel_then [`v`,`Gv`,`tv`] (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `st.cs_next_id < a.cs_next_id /\ st.cs_next_id < c.cs_next_id` by
    (qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ i a _ _ _` mp_tac >>
     qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ (SUC i) c _ _ _` mp_tac >>
     simp_tac (srw_ss()) [abi_encode_values_prefix_at_def] >> metis_tac[]) >>
  `loop_effect_cut st.cs_next_id a = a /\ loop_effect_cut st.cs_next_id c = c` by
    (conj_tac >> irule loop_effect_cut_reached >> first_assum ACCEPT_TAC) >>
  qexistsl [`v`,`Gv`,`tv`] >> asm_rewrite_tac[] >>
  irule abi_tuple_row_effects_trans_mods >>
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ a u' Gu' tu' c v Gv tv`
    (irule_at Any) >>
  qpat_assum `loop_effect_cut st.cs_next_id a = a` (fn cut_eq =>
    qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ st u Gu tu _ _ _ _`
      (ACCEPT_TAC o PURE_REWRITE_RULE [cut_eq]))
QED

Finalise abi_tuple_linked_loop_mods
