Theory entryCreateExtRowStatic
Ancestors
  bodyFullExtCallDirectRow bodyFullExtCallDirectState abiEncodeValuesStatic
  entryCreatePathScope entryCreateCompletedCut entryCreateFocusSpec
  exprLoweringProps fragExec fragGasOriginPtr compileEnv venomState venomInst
  abiEncoderProps pred_set list arithmetic words
  entryCreateExtRowRestore createSizeCutCode createSizeEncodeCoreCode pair
  entryCreateExtPackRow entryCreatePackRowContinuation

(* Work backwards from the final cut. The two lifts need only exclude
   its fetch from the earlier row band, not from the installed function. *)
Theorem static_row_scope_compose[local]:
  ci_mono su a /\ ci_mono a b /\ ci_mono b en /\
  (!bb i. lookup_block en.cs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids su en) /\
  create_operand_full_scope su a E C fn x [] (OK y) /\
  create_operand_full_scope a b E C fn y [] (OK z) /\
  create_operand_full_scope b en E C fn z [] (OK t) ==>
  create_operand_full_scope su en E C fn x [] (OK t)
Proof
  simp[ci_mono_def] >> strip_tac >>
  `a.cs_next_id <= en.cs_next_id` by decide_tac >>
  `create_operand_full_scope a en E C fn y [] (OK t)` by
    (irule (SIMP_RULE bool_ss [APPEND]
       (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_operand_full_scope_prepend)) >>
     qexistsl_tac [`b`,`z`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!bb i. _ ==> _ NOTIN frag_ids su en`
       (qspecl_then [`bb`,`i`] mp_tac) >> fs[frag_ids_def] >> decide_tac) >>
  irule (SIMP_RULE bool_ss [APPEND]
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_operand_full_scope_prepend)) >>
  qexistsl_tac [`a`,`y`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!bb i. _ ==> _ NOTIN frag_ids su en`
    (qspecl_then [`bb`,`i`] mp_tac) >> fs[frag_ids_def] >> decide_tac
QED

Theorem extcall_static_pack_row_from_scoped_phases:
  abi_static_row_restore (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v))
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i /\
  abi_values_source_phase ctx func lo explicit PG
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)) /\
  (!a b p u. emit_op ADD [Var dst; Lit (n2w h)] a = (Var p,b) /\
    fn_has_code a b func /\ ~u.vs_halted /\ create_operand_at a u /\
    lookup_var dst u = SOME (n2w (pbase+dst_offset)) ==>
    create_operand_full_scope a b explicit ctx func u []
      (OK ((update_var p (n2w (pbase+dst_offset) + n2w h) u) with
              vs_inst_idx := SUC u.vs_inst_idx))) /\
  (!bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
          i.inst_id NOTIN frag_ids su en) /\
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
    create_operand_full_scope su en explicit ctx func u [] (OK z)
Proof
  simp_tac bool_ss [create_operand_at_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`R` |-> `\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)`]
    abi_encode_saved_static_row_phase) >>
  simp_tac bool_ss [] >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt strip_tac >> simp[create_operand_full_scope_def])
     >- (rpt strip_tac >> first_assum irule >> simp[]) >>
     map_every qx_gen_tac [`a`,`b`,`x`,`y`,`w`,`t`] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule static_row_scope_compose >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`a`,`b`,`y`,`w`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

val guarded_scope = ``\a b x y.
  (a = b \/ (create_cut_code {} a b /\ fn_has_code a b func)) /\
  ((!bb j. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb (LENGTH b.cs_current_insts) = SOME j ==>
     b.cs_next_id <= j.inst_id) ==>
   create_operand_full_scope a b explicit ctx func x [] (OK y))``;

Theorem static_guarded_source_phase[local]:
  abi_values_source_phase ctx func lo explicit PG
    (\a b x y. create_operand_full_scope a b explicit ctx func x [] (OK y)) ==>
  abi_values_source_phase ctx func lo explicit PG ^guarded_scope
Proof
  simp_tac bool_ss [abi_values_source_phase_def] >> disch_tac >>
  map_every qx_gen_tac [`st`,`en`,`dst`,`src`,`ei`,`out`,`bs`,`sb`,`cap`,`d`,`s`,`G`,`tn`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  first_x_assum (qspecl_then [`st`,`en`,`dst`,`src`,`ei`,`out`,`bs`,
    `sb`,`cap`,`d`,`s`,`G`,`tn`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `create_cut_code {} st en` by metis_tac[create_encode_to_buf_cut_code,SND] >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Theorem static_guarded_restore_phase[local]:
  abi_static_row_restore
    (\a b u z. create_cut_code {} a b /\ fn_has_code a b func /\
      ((!bb j. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH b.cs_current_insts) = SOME j ==>
         b.cs_next_id <= j.inst_id) ==>
       create_operand_full_scope a b explicit ctx func u [] (OK z)))
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i ==>
  abi_static_row_restore ^guarded_scope
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i
Proof
  simp_tac bool_ss [abi_static_row_restore_def] >> disch_tac >>
  map_every qx_gen_tac [`a`,`b`,`u`,`Gu`,`tu`,`src`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  first_x_assum (qspecl_then [`a`,`b`,`u`,`Gu`,`tu`,`src`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >> asm_rewrite_tac[]
QED

Theorem static_guarded_scope_compose[local]:
  ci_mono su a /\ ci_mono a b /\ ci_mono b en /\ fn_has_code su en func /\
  (^guarded_scope) su a x y /\ (^guarded_scope) a b y z /\ (^guarded_scope) b en z t ==>
  (^guarded_scope) su en x t
Proof
  BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `create_cut_code {} su en` by
    metis_tac[create_cut_code_refl,create_cut_code_join] >>
  asm_rewrite_tac[] >> strip_tac >>
  `!bb j. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH b.cs_current_insts) = SOME j ==>
          b.cs_next_id <= j.inst_id` by
    (Cases_on `b = en` >> asm_rewrite_tac[] >>
     mp_tac (Q.INST [`sb` |-> `b`, `en` |-> `en`] abi_restore_exit_fence) >>
     fs[]) >>
  `!bb j. lookup_block a.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH a.cs_current_insts) = SOME j ==>
          a.cs_next_id <= j.inst_id` by
    (Cases_on `a = b` >> asm_rewrite_tac[] >>
     mp_tac (Q.INST [`sb` |-> `a`, `en` |-> `b`] abi_restore_exit_fence) >>
     fs[]) >>
  `!bb j. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH en.cs_current_insts) = SOME j ==>
          j.inst_id NOTIN frag_ids su en` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!bb j. _ ==> en.cs_next_id <= j.inst_id` (drule_all_then assume_tac) >>
     simp[frag_ids_def] >> decide_tac) >>
  irule static_row_scope_compose >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`a`,`b`,`y`,`z`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, first_assum drule >> simp[]]
QED

Theorem extcall_static_pack_row_from_guarded_restore:
  abi_static_row_restore
    (\a b u z. create_cut_code {} a b /\ fn_has_code a b func /\
      ((!bb j. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb (LENGTH b.cs_current_insts) = SOME j ==>
         b.cs_next_id <= j.inst_id) ==>
       create_operand_full_scope a b explicit ctx func u [] (OK z)))
    ctx func ce cx st0 ee DF lo explicit PG d se s G tn
    shared pbase capacity root dst dst_offset prefix saved ty v ats avs hl cursor loc slot i /\
  abi_values_source_phase ctx func lo explicit PG
    (\a b u v. create_operand_full_scope a b explicit ctx func u [] (OK v)) /\
  compile_abi_encode_value_rows ce (Var dst) cursor
    (h + abi_embedded_static_size ce.ce_struct_fields ty) rest en = ((),last) /\
  emit_op MLOAD [cursor] last = (out,fin_cs) /\ fn_has_code en fin_cs func /\
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
    create_operand_full_scope su en explicit ctx func u [] (OK z)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!bb i. lookup_block en.cs_current_bb func.fn_blocks = SOME bb /\
          get_instruction bb (LENGTH en.cs_current_insts) = SOME i ==>
          en.cs_next_id <= i.inst_id` by
    (qpat_assum `compile_abi_encode_value_rows ce (Var dst) cursor _ rest en = _`
       (fn rows => qpat_assum `emit_op MLOAD [cursor] last = _`
         (fn load => qpat_assum `fn_has_code en fin_cs func`
           (fn code => ACCEPT_TAC
             (MATCH_MP pack_row_installed_exit_fetch (LIST_CONJ [rows,load,code])))))) >>
  mp_tac (BETA_RULE (Q.INST [`R` |-> `^guarded_scope`] abi_encode_saved_static_row_phase)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (irule static_guarded_restore_phase >> first_assum ACCEPT_TAC)
     >- (irule static_guarded_source_phase >> first_assum ACCEPT_TAC)
     >- (rpt strip_tac >>
         simp[create_operand_full_scope_def,create_expr_prefix_nil])
     >- (map_every qx_gen_tac [`a`,`b`,`p`,`head_state`] >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         `create_cut_code {} a b` by
           (mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[Var dst; Lit (n2w h)]`,
              `a` |-> `a`, `exits` |-> `{}`] create_cut_code_emit_op) >>
            asm_simp_tac (srw_ss()) [create_cut_targets_def]) >>
         `create_operand_at a head_state` by simp[create_operand_at_def] >>
         mp_tac (Q.INST [`s` |-> `head_state`, `head` |-> `p`, `off` |-> `h`,
           `bw` |-> `n2w (pbase+dst_offset)`] abi_pack_head_add_scope) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then assume_tac >>
         asm_rewrite_tac[] >> fs[])
     >> map_every qx_gen_tac [`a`,`b`,`x`,`y`,`z`,`t`] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     irule (BETA_RULE static_guarded_scope_compose) >>
     conj_tac
     >- (qexistsl_tac [`a`,`b`,`y`,`z`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`z`,`Gz`,`tz`] >>
  asm_rewrite_tac[] >>
  fs[]
QED
