Theory bodyFullExtCallDirectRow
Ancestors
  abiEncodeValuesPrefixFrame bodyFullAbiEncodeNonwordWindow exprSimHyps
  abiEncoderWindow abiEncoderAdmissible
  bodyFullExtCallDirectPhase bodyFullExtCallDirectState bodyFullExtCallDirectWord bodyFullExtCallDirectStore
  bodyFullExtCallDirectMaterialize bodyFullExtCallDirectUnwrap
  abiEncodeValuesRun abiEncodeValuesMetadata abiEncodeValuesPhases abiEncodeValuesStatic abiDecodeRanges
  abiEncoderWindowJointPhases abiEncoderWindowPhase abiEncoderWindowContract
  exprSimAbiEncodeExecFrame exprSimAbiEncodePlanMetadata allocaSiteResource
  exprLoweringProps entryDecodeStaticProps reasonCopySourcePtr
  fragGasOriginPtrLoop fragGasOriginPtr fragExec
  compileEnv exprLowering context bodyPtrDefs loweringPosts loweringStateRelDefs ptrDiscipline
  contractABI vyperABI vyperValue vyperTyping venomState venomInst
  finite_map pred_set list arithmetic pair words
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs pureFrameLib

Theorem abi_encode_values_translated_window_input[local]:
  evaluate_type env ty = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields env /\
  (!t u. evaluate_type env t = SOME u ==> type_memory_bytes ce t = type_memory_size u) /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  (!mem. mem_agree_outside tainted initial_mem mem ==> val_in_memory tv v sb mem) ==>
  abi_encoder_admissible (type_to_abi_enc_info ce.ce_struct_fields ce ty) /\
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    !mem. mem_agree_outside tainted initial_mem mem ==>
      abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
        ct rv sb (val_footprint tv v) mem
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  conj_tac >- simp[abi_encoder_translation_admissible] >>
  irule abi_encode_uniform_translated_footprint_window >>
  simp[] >> qexists_tac `env` >> simp[]
QED

(* Restore at the runtime state produced by the head phase.  Arguments
   evaluated before packing stay fixed while the installed cuts vary. *)
Definition abi_static_row_restore_def:
  abi_static_row_restore R ctx func ce cx st0 ee DF lo explicit PG d se s G tn
      shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i <=>
  !a b u Gu tu src.
    unwrap_value ce saved a = (src,b) /\ fn_has_code a b func /\ ci_mono a b /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix a u Gu tu /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i a u Gu tu ==>
    ?z Gz tz.
      (pure_frame ce func ee a u z /\ wb_frame ce ee ee a u z) /\
      abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
        shared pbase capacity root dst dst_offset prefix b z Gz tz /\
      abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i b z Gz tz /\
      expr_val_rel cx ty v src z /\ ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
      (!x. src = Var x ==> not_fresh_at b x) /\
      (!x. not_fresh_at a x ==>
        lookup_var x z = lookup_var x u /\ FLOOKUP Gz x = FLOOKUP Gu x /\
        op_taint tz (Var x) = op_taint tu (Var x)) /\
      z.vs_labels = u.vs_labels /\
      (?first last. expr_val_at ce cx ty first last ee v src z /\
         last.cs_next_id <= b.cs_next_id /\
         (shared < first.cs_next_id \/ last.cs_next_id <= shared)) /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
      R a b u z
End

Theorem abi_encode_saved_static_row_phase:
  abi_static_row_restore R ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i /\
  abi_values_source_phase ctx func lo explicit PG R /\
  (!a u. u.vs_current_bb = a.cs_current_bb /\
         u.vs_inst_idx = LENGTH a.cs_current_insts ==> R a a u u) /\
  (!a b p u. emit_op ADD [Var dst; Lit (n2w h)] a = (Var p,b) /\
    fn_has_code a b func /\ ~u.vs_halted /\
    u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
    lookup_var dst u = SOME (n2w (pbase+dst_offset)) ==>
    R a b u ((update_var p (n2w (pbase+dst_offset) + n2w h) u) with
               vs_inst_idx := SUC u.vs_inst_idx)) /\
  (!a b x y z t. ci_mono su a /\ ci_mono a b /\ ci_mono b en /\
    R su a x y /\ R a b y z /\ R b en z t ==> R su en x t) /\
  ~is_word_type ty /\ ~is_dynamic at /\ ~is_abi_dynamic ce.ce_struct_fields ty /\
  fn_has_code su en func /\ compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\ shared < loc /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  value_has_type tv v /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)) /\
    R su en u z
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func ce cx ee u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  `hl <= off /\ pbase+dst_offset+h <= pbase+capacity /\ pbase+dst_offset+off <= pbase+capacity` by decide_tac >>
  `pbase+capacity <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  drule_all abi_encode_values_static_cuts >>
  disch_then (qx_choosel_then [`head_op`,`su1`,`src`,`su2`] strip_assume_tac) >>
  qabbrev_tac `hs = abi_member_head_size at` >>
  `hs = abi_member_head_size at` by simp[NoAsms, Abbr `hs`] >>
  mp_tac (Q.INST [`b` |-> `pbase+dst_offset`,`off` |-> `h`,`n` |-> `hs`,
    `cap` |-> `capacity-dst_offset`,`st` |-> `su`,`en` |-> `su1`,`head` |-> `head_op`,
    `s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`] abi_encode_values_head_address_endpoint) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`hp`,`u1`,`G1`,`t1`] strip_assume_tac) >>
  `R su su1 u u1` by
    (qpat_assum `u1 = _` SUBST1_TAC >>
     qpat_assum `!a b p u. emit_op ADD _ a = _ /\ _ ==> _` irule >>
     simp[GSYM eval_operand_def] >> metis_tac[eval_operand_def]) >>
  `(pure_frame ce func ee se u u1 /\ wb_frame ce ee ee se u u1) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix su1 u1 G1 t1` by
    (mp_tac (Q.INST [`a` |-> `su`,`c` |-> `su1`,
       `v` |-> `u1`,`Gv` |-> `G1`,`tv` |-> `t1`] abi_encode_saved_state_arith_pure) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su1 u1 G1 t1` by
    (irule abi_encode_values_prefix_arith >>
     qpat_assum `window_phase ctx func su su1 {} [] u u1` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  qhdtm_assum `abi_static_row_restore`
    (mp_tac o Q.SPECL [`su1`,`su2`,`u1`,`G1`,`t1`,`src`] o REWRITE_RULE [abi_static_row_restore_def]) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`u2`,`G2`,`t2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `head_op = Var hp` SUBST_ALL_TAC >>
  `eval_operand (Var hp) u2 = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers G2 t2 hp u2 hs` by
    (irule extcall_direct_unwrap_pointer >> qexistsl_tac [`G1`,`u1`,`su1`,`t1`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `not_fresh_at su2 hp` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `su1` >>
     qpat_assum `ci_mono su1 su2` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`a` |-> `su2`,`c` |-> `en`,
    `u` |-> `u2`,`Gu` |-> `G2`,`tu` |-> `t2`,`head` |-> `hp`]
    abi_encode_saved_store_static_phase) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  strip_tac >>
  `(pure_frame ce func ee se u u2 /\ wb_frame ce ee ee se u u2)` by
    (mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `su1`,`v` |-> `u1`,`z` |-> `u2`]
       (INST_TYPE [alpha |-> ``:num # num``] abi_encode_saved_frames_trans)) >>
     impl_tac >-
       (qpat_assum `ci_mono su su1` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z` by
    (mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `se`,`v` |-> `u2`]
       (INST_TYPE [alpha |-> ``:num # num``] abi_encode_saved_frames_trans)) >>
     asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  qpat_x_assum `u1 = _` kall_tac >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`G1`,`u1`,`t1`] >> asm_rewrite_tac[] >>
      irule gas_origin_ptr_path_trans >> qexistsl_tac [`G2`,`u2`,`t2`] >> asm_rewrite_tac[]) >>
  qpat_assum `!a b x y z t. ci_mono su a /\ _ ==> R su en x t` irule >>
  qexistsl_tac [`su1`,`su2`,`u1`,`u2`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_saved_row_open_pure:
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
  ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  fn_inst_ids_distinct func /\
  fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  cursor_inst.inst_opcode = ALLOCA /\ shared < loc /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  (is_dynamic at ==> off + LENGTH (enc at av) <= capacity-dst_offset) ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_saved_state_resources >> strip_tac >>
  qpat_assum `abi_encode_saved_state _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_saved_state_def]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace` (qx_choose_then `hz` assume_tac) >>
  `stmt_state_rel hz ctx func ce cx ee u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee u /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
  `hl <= off /\ pbase+dst_offset+h <= pbase+capacity /\ pbase+dst_offset+off <= pbase+capacity` by decide_tac >>
  `pbase+capacity <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `~is_abi_dynamic ce.ce_struct_fields ty <=> ~is_dynamic at` by
    metis_tac[abi_encode_translated_dynamic] >>
  Cases_on `is_word_type ty`
  >- (`?tag src. saved = StackValue tag src` by metis_tac[] >>
      mp_tac (Q.INST [`a` |-> `su`] extcall_direct_word_source) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `saved = StackValue tag src` SUBST_ALL_TAC >>
      mp_tac (Q.INST [`a` |-> `su`,`c` |-> `en`]
        abi_encode_saved_word_row_pure) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
      disch_then ACCEPT_TAC) >>
  Cases_on `is_dynamic at`
  >- suspend "dynamic" >>
  suspend "static"
QED

Resume abi_encode_saved_row_open_pure[dynamic]:
  `is_abi_dynamic ce.ce_struct_fields ty /\ abi_member_head_size at = 32` by
    (simp[abi_member_head_size_def] >> metis_tac[]) >>
  drule_all abi_encode_values_dynamic_cuts >>
  disch_then (qx_choosel_then [`head_op`,`offset`,`tail_op`,`su1`,`src`,`su2`,`len`,`mid`]
    strip_assume_tac) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encode_values_prefix_at_def]) >>
  qpat_x_assum `cursor = Var p` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`d` |-> `pbase+dst_offset`,`ho` |-> `h`,`dp` |-> `p`,
    `bound` |-> `capacity-dst_offset`,`st` |-> `su`,`en` |-> `su1`,
    `ops` |-> `(head_op,offset,tail_op)`,`s` |-> `u`,`G` |-> `Gu`,`tn` |-> `tu`]
    window_child_prefix_joint) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`u1`,`G1`,`t1`,`hp`,`tp`]
    (strip_assume_tac o SIMP_RULE bool_ss [FST,SND])) >>
  `(pure_frame ce func ee se u u1 /\ wb_frame ce ee ee se u u1) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix su1 u1 G1 t1` by
    (mp_tac (Q.INST [`a` |-> `su`,`c` |-> `su1`,
       `v` |-> `u1`,`Gv` |-> `G1`,`tv` |-> `t1`] abi_encode_saved_state_arith_pure) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) (Var p) loc slot i su1 u1 G1 t1` by
    (irule abi_encode_values_prefix_arith >>
     qpat_assum `window_phase ctx func su su1 {} [] u u1` (irule_at Any) >>
     qexistsl_tac [`tu`,`Gu`] >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`su` |-> `su1`,`sb` |-> `su2`,`cursor` |-> `Var p`,
    `u` |-> `u1`,`Gu` |-> `G1`,`tu` |-> `t1`] abi_encode_saved_restore_row_pure) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  disch_then (qx_choosel_then [`u2`,`G2`,`t2`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `head_op = Var hp` SUBST_ALL_TAC >>
  qpat_x_assum `tail_op = Var tp` SUBST_ALL_TAC >>
  `!x w n. not_fresh_at su1 x /\ eval_operand (Var x) u1 = SOME w /\ ptr_covers G1 t1 x u1 n ==>
    eval_operand (Var x) u2 = SOME w /\ ptr_covers G2 t2 x u2 n` by
    (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule extcall_direct_unwrap_pointer >> qexistsl_tac [`G1`,`u1`,`su1`,`t1`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var hp) u2 = SOME (n2w (pbase+dst_offset+h)) /\ ptr_covers G2 t2 hp u2 32` by
    (qpat_assum `!x w n. not_fresh_at su1 x /\ _ ==> eval_operand (Var x) u2 = _ /\ _`
       (qspecl_then [`hp`,`n2w (pbase+dst_offset+h)`,`32`] mp_tac) >> metis_tac[]) >>
  `LENGTH (enc at av) <= capacity-dst_offset-off` by
    (qpat_assum `is_dynamic at ==> _` (drule_then assume_tac) >> decide_tac) >>
  `eval_operand (Var tp) u2 = SOME (n2w (pbase+dst_offset+off)) /\
    ptr_covers G2 t2 tp u2 (LENGTH (enc at av))` by
    (qpat_assum `!x w n. not_fresh_at su1 x /\ _ ==> eval_operand (Var x) u2 = _ /\ _`
       (qspecl_then [`tp`,`n2w (pbase+dst_offset+off)`,`capacity-dst_offset-off`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> metis_tac[]) >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule ptr_covers_mono >> qexists_tac `capacity-dst_offset-off` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand offset u2 = SOME (n2w off) /\ op_taint t2 offset = {}` by
    (mp_tac (Q.INST [`st` |-> `su1`,`op` |-> `offset`,`s` |-> `u1`,`t` |-> `u2`,
       `G` |-> `G1`,`G'` |-> `G2`,`tn` |-> `t1`,`tn'` |-> `t2`]
       (INST_TYPE [alpha |-> ``:num # num``] extcall_direct_unwrap_operand)) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       gen_tac >> disch_tac >>
       qpat_assum `!x. Var hp = Var x \/ offset = Var x \/ Var tp = Var x ==> _`
         (qspec_then `x` irule) >> asm_rewrite_tac[]) >>
     asm_rewrite_tac[]) >>
  `ci_mono su2 en` by metis_tac[ci_mono_trans] >>
  `!x. src = Var x \/ Var hp = Var x \/ Var tp = Var x \/ offset = Var x ==>
     not_fresh_at su2 x` by
    (qpat_assum `ci_mono su1 su2` (assume_tac o cj 2 o REWRITE_RULE [ci_mono_def]) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!t u. evaluate_type (get_tenv cx) t = SOME u ==>
      type_memory_bytes ce t = type_memory_size u` by
    (rpt gen_tac >> disch_tac >> drule_all expr_sim_inv_memory_size >>
     disch_then ACCEPT_TAC) >>
  `!sb. (!mem. mem_agree_outside t2.t_mem u2.vs_memory mem ==>
       val_in_memory tv v sb mem) ==>
     abi_encoder_admissible (type_to_abi_enc_info ce.ce_struct_fields ce ty) /\
     ?ct rv. enc ct rv = enc at av /\
       !mem. mem_agree_outside t2.t_mem u2.vs_memory mem ==>
         abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
           ct rv sb (val_footprint tv v) mem` by
    (gen_tac >> disch_tac >>
     qpat_assum `at = vyper_to_abi_type (get_tenv cx) ty`
       (fn th => PURE_REWRITE_TAC [th]) >>
     drule_all abi_encode_values_translated_window_input >> disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`a` |-> `su2`,`c` |-> `en`,
    `u` |-> `u2`,`Gu` |-> `G2`,`tu` |-> `t2`,`cursor` |-> `p`,
    `head` |-> `hp`,`tail` |-> `tp`,
    `ei` |-> `type_to_abi_enc_info ce.ce_struct_fields ce ty`]
    abi_encode_saved_store_dynamic_input_pure) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >> metis_tac[]) >>
  strip_tac >>
  `(pure_frame ce func ee se u u2 /\ wb_frame ce ee ee se u u2)` by
    (mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `su1`,`v` |-> `u1`,`z` |-> `u2`]
       (INST_TYPE [alpha |-> ``:num # num``] abi_encode_saved_frames_trans)) >>
     impl_tac >-
       (qpat_assum `ci_mono su su1` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  `pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z` by
    (mp_tac (Q.INST [`H` |-> `hz`,`a` |-> `se`,`v` |-> `u2`]
       (INST_TYPE [alpha |-> ``:num # num``] abi_encode_saved_frames_trans)) >>
     asm_simp_tac bool_ss [arithmeticTheory.LESS_EQ_REFL]) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G1`,`u1`,`t1`] >> asm_rewrite_tac[] >>
  irule gas_origin_ptr_path_trans >> qexistsl_tac [`G2`,`u2`,`t2`] >> asm_rewrite_tac[]
QED

Resume abi_encode_saved_row_open_pure[static]:
  `~is_abi_dynamic ce.ce_struct_fields ty` by metis_tac[] >>
  mp_tac (Q.INST [`R` |-> `\a b u v. T`] abi_encode_saved_static_row_phase) >>
  simp_tac bool_ss [abi_values_source_phase_trivial, abi_static_row_restore_def] >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     map_every qx_gen_tac [`a`,`b`,`u1`,`G1`,`t1`,`src`] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`su` |-> `a`,`sb` |-> `b`,`u` |-> `u1`,
       `Gu` |-> `G1`,`tu` |-> `t1`] abi_encode_saved_restore_row_pure) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise abi_encode_saved_row_open_pure

Theorem abi_encode_saved_row_pure:
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
  ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  fn_inst_ids_distinct func /\
  fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot i su u Gu tu /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = shared /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  cursor_inst.inst_opcode = ALLOCA /\ shared < loc /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (is_dynamic at ==>
    abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info ce.ce_struct_fields ce ty)) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-dst_offset /\
  (is_dynamic at ==> off + LENGTH (enc at av) <= capacity-dst_offset) ==>
  ?z Gz tz.
    (pure_frame ce func ee se u z /\ wb_frame ce ee ee se u z) /\
    abi_encode_saved_state ctx func ce cx st0 ee DF lo d se s G tn
      shared pbase capacity root dst dst_offset prefix en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+dst_offset) cursor loc slot (SUC i) en z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_encode_saved_row_open_pure >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem abi_encode_saved_row =
  pureFrameLib.drop_frame abi_encode_saved_row_pure

Theorem abi_encode_direct_row:
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
  ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  fn_inst_ids_distinct func /\
  fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id pbase capacity root dst selector su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i su u Gu tu /\
  32 <= capacity /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  cursor_inst.inst_opcode = ALLOCA /\ se.cs_next_id < loc /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-32 /\
  (is_dynamic at ==> off + LENGTH (enc at av) <= capacity-32) ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst selector en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot (SUC i) en z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `32 <= capacity` (fn cap =>
    drule_then (fn len =>
      mp_tac (SIMP_RULE bool_ss [MATCH_MP abi_encode_saved_state_extcall len,cap]
        (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`,
          `shared` |-> `se.cs_next_id`]
          (pureFrameLib.drop_frame abi_encode_saved_row_open_pure))))
      extcall_direct_state_selector_length) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    disch_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Theorem extcall_direct_row:
  ty = lowered_value_type ce e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value ty vv) sm = (saved,ss) /\
  ((?tag op0. saved = StackValue tag op0) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory) \/
   (?p. saved = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location <> LocMemory /\
        ty = expr_type e /\ saved = vv)) /\
  local_ptrs_reserved ce si /\ sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
  ss.cs_next_var <= se.cs_next_var /\ ss.cs_next_id <= se.cs_next_id /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (~is_word_type ty ==> ~is_word_type (expr_type e)) /\
  (!l. vv_operand saved <> Label l) /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2**64 /\ value_has_type tv v /\
  vv_holds ce cx ty raw saved ee s /\ vv_at ce cx ty si ss ee raw saved s /\
  ptr_vv_ok cx ty raw saved ee G tn s /\ vv_store_bound cx ty ty ee raw saved s /\
  ((case saved of StackValue tag op0 => ~is_word_type ty
      | LocatedValue tag p => p.ptr_location = LocMemory) ==>
    ptr_buf_ok ce e (vv_operand saved) G s) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ vv_storage_live H cx saved ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  storage_trace_domain cx st0 ee.storage_trace /\
  fn_inst_ids_distinct func /\
  fn_has_code su en func /\
  compile_abi_encode_value_rows ce (Var dst) cursor h [(saved,ty)] su = ((),en) /\
  extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
    se.cs_next_id pbase capacity root dst selector su u Gu tu /\
  abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot i su u Gu tu /\
  32 <= capacity /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  MEM cursor_inst (fn_insts func) /\ cursor_inst.inst_id = loc /\
  cursor_inst.inst_outputs = [cursor_var] /\ not_local_ptr ce ee.scopes cursor_var /\
  cursor_inst.inst_opcode = ALLOCA /\ se.cs_next_id < loc /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info ce.ce_struct_fields ce ty) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\ at = EL i ats /\ av = EL i avs /\
  at = vyper_to_abi_type (get_tenv cx) ty /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  h + abi_member_head_size at <= hl /\ off <= capacity-32 /\
  (is_dynamic at ==> off + LENGTH (enc at av) <= capacity-32) ==>
  ?z Gz tz.
    extcall_direct_state ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase capacity root dst selector en z Gz tz /\
    abi_encode_values_prefix_at ats avs hl (pbase+32) cursor loc slot (SUC i) en z Gz tz /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK z,Gz,tz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `32 <= capacity` (fn cap =>
    drule_then (fn len =>
      mp_tac (SIMP_RULE bool_ss [MATCH_MP abi_encode_saved_state_extcall len,cap]
        (Q.INST [`dst_offset` |-> `32`,`prefix` |-> `selector`,
          `shared` |-> `se.cs_next_id`]
          abi_encode_saved_row)))
      extcall_direct_state_selector_length) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    disch_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
