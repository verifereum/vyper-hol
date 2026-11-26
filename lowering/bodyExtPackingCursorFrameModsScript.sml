Theory bodyExtPackingCursorFrameMods
Ancestors
  bodyExtPackingEndpointMods bodyAbiEncodeRegisteredFrameMods
  bodyFullExtCallDirectWindows abiEncodeValuesCode abiEncodeValuesPhases
  abiCanonicalHeadSize abiEncoderWindowPhase abiEncoderRegisteredEffect
  exprSimAbiEncodeExecFrame exprSimWordArgs wordArgsPtr memoryReadProps
  exprSimProps exprLoweringProps fragExec loweringPosts freshWrites
  stateRelProj bodyFullShadowBodyInv venomState abiEncoderWindowContract
  finite_map pred_set list pair arithmetic
Libs horizonTypeLib

Theorem packing_cursor_site[local]:
  compile_abi_encode_values_to_buf ce dst rows st = (out,en) /\
  fn_has_code st en func /\ local_ptrs_reserved ce front /\
  front.cs_next_var <= st.cs_next_var ==>
  ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = st.cs_next_id /\ inst.inst_outputs = [x] /\
    not_local_ptr ce scopes x
Proof
  strip_tac >> drule_then strip_assume_tac abi_encode_values_to_buf_trace >>
  `ci_mono st allocated /\ ci_mono allocated ready /\
   ci_mono ready stored /\ ci_mono stored en` by
    (rpt conj_tac >>
     metis_tac[ci_mono_emit_op,ci_mono_emit_void,
               ci_mono_compile_abi_encode_value_rows,SND]) >>
  `ci_mono allocated en` by metis_tac[ci_mono_trans] >>
  `fn_has_code st allocated func` by metis_tac[ci_mono_def,fn_has_code_split] >>
  drule_all extcall_direct_alloca_site >>
  disch_then (qspec_then `scopes` strip_assume_tac) >>
  qexistsl [`inst`,`q`] >> asm_rewrite_tac[]
QED

Theorem cursor_keeps_subrange[local]:
  p <= b /\ b+n <= p+k /\ mem_bytes_at p k m' = mem_bytes_at p k m ==>
  mem_bytes_at b n m' = mem_bytes_at b n m
Proof
  strip_tac >>
  `b-p+n <= k /\ p+(b-p) = b` by decide_tac >>
  qpat_x_assum `mem_bytes_at p k m' = _`
    (mp_tac o Q.AP_TERM `\bs. TAKE n (DROP (b-p) bs)`) >>
  simp[mem_bytes_at_window]
QED

(* The fold's empty-output phases can only write to the cursor slot.
   The physical cursor registration itself is not a protected read. *)
Theorem ext_packing_cursor_frame_mods:
  compile_abi_encode_values_to_buf ce (Var dst) rows st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  front.cs_next_var <= st.cs_next_var /\ owner < st.cs_next_id /\ 32 <= capacity /\
  (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = owner /\ inst.inst_outputs = [root] /\
     not_local_ptr ce ee.scopes root) /\
  local_ptrs_reserved ce front /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner pbase capacity root dst selector a u Gu tu /\
  ci_mono a c /\ window_phase ctx func a c ids [] u v /\
  abi_encode_exec_frame func u v /\ ids SUBSET {st.cs_next_id} /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  tv.t_mem SUBSET tu.t_mem ==>
  ext_packing_endpoint_mods ctx func ce cx st0 ee DF lo ret front s G tn
    owner pbase capacity root dst selector c v Gv tv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `ext_packing_endpoint_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[ext_packing_endpoint_mods_def]) >>
  `!aid. aid IN ids ==> aid = st.cs_next_id` by fs[SUBSET_DEF] >>
  `!aid. aid IN ids ==> front.cs_next_id <= aid` by
    (rpt strip_tac >> `aid = st.cs_next_id` by simp[] >> decide_tac) >>
  `owner NOTIN ids` by (strip_tac >> `owner = st.cs_next_id` by simp[] >> decide_tac) >>
  `!aid. aid IN owner INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (pure_rewrite_tac[IN_INSERT] >> gen_tac >> disch_then (DISJ_CASES_THEN assume_tac)
     >- (qpat_x_assum `?inst. MEM inst _ /\ _` strip_assume_tac >>
         qexistsl [`inst`,`root`] >> asm_rewrite_tac[]) >>
     `aid = st.cs_next_id` by simp[] >>
     drule_all packing_cursor_site >> disch_then (qspec_then `ee.scopes` mp_tac) >> simp[]) >>
  `!i. EVERY (\(p,n). i < p \/ p+n <= i) ([]:(num # num) list) /\
     (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
        i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem` by
    fs[SUBSET_DEF] >>
  `EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) []` by simp[] >>
  drule_all abi_encode_registered_phase_frame_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "observations"
QED

Resume ext_packing_cursor_frame_mods[observations]:
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  `alloca_inv u` by (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `EVERY (\r. venomMemDefs$regions_disjoint (pbase+28,4) r) []` by simp[] >>
  `read_memory (pbase+28) 4 v = selector` by
    (`pbase <= pbase+28 /\ pbase+28+4 <= pbase+capacity` by decide_tac >>
     drule_all_then (assume_tac o CONJUNCT1 o CONJUNCT2)
       abi_encode_values_registered_window >>
     qpat_assum `read_memory (pbase+28) 4 u = selector`
       (assume_tac o REWRITE_RULE [read_memory_eq_mem_bytes_at]) >>
     asm_rewrite_tac[read_memory_eq_mem_bytes_at]) >>
  `!x w n. not_fresh_at a x /\ lookup_var x u = SOME w /\ ptr_covers Gu tu x u n ==>
     lookup_var x v = SOME w /\ ptr_covers Gv tv x v n` by
    (pure_rewrite_tac[GSYM (cj 2 eval_operand_def)] >> rpt strip_tac >>
     drule_all abi_encode_values_pointer_frame >> simp[]) >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_phase_labels >>
  drule_then assume_tac window_phase_effect >>
  suspend "compose"
QED

Resume ext_packing_cursor_frame_mods[compose]:
  `window_alloca_growth s v` by
    (irule window_alloca_growth_trans >> qexists_tac `u` >> asm_rewrite_tac[]) >>
  `pure_frame ce func ee front s v` by
    (irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`ee`,`front`,`u`] >> fs[wb_frame_def]) >>
  `wb_frame ce ee ee front s v` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front u v` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee front G tn s Gv tv` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee front G tn s Gu tu` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee front Gu tu u Gv tv` (irule_at Any) >> simp[]) >>
  suspend "protected"
QED

Resume ext_packing_cursor_frame_mods[protected]:
  drule_all_then (assume_tac o CONJUNCT1) extcall_direct_encode_windows >>
  `!nm p k. local_region ce ee.scopes s nm p k <=>
             local_region ce ee.scopes u nm p k` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_local_regions) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx ee s` (irule_at Any) >>
     qpat_assum `wb_frame ce ee ee front s u` (irule_at Any) >> simp[]) >>
  qpat_assum `wb_frame ce ee ee front s u`
    (assume_tac o cj 2 o REWRITE_RULE [wb_frame_def]) >>
  `!b n. (b+n <= lo \/
           (?name p k. local_region ce ee.scopes s name p k /\ p <= b /\ b+n <= p+k) \/
           (?id p k. id < front.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (p,k) /\
                     p <= b /\ b+n <= p+k)) ==>
       mem_bytes_at b n v.vs_memory = mem_bytes_at b n u.vs_memory` by
    (rpt gen_tac >> disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN strip_assume_tac)) >>
     irule cursor_keeps_subrange
     >- (qexistsl [`lo`,`0`] >> simp[] >>
         qpat_assum `!b n. _ ==> mem_bytes_at b n v.vs_memory = _ /\ _`
           (qspecl_then [`0`,`lo`] mp_tac) >> simp[])
     >- (qexistsl [`k`,`p`] >> asm_rewrite_tac[] >>
         qpat_assum `!b n. _ ==> mem_bytes_at b n v.vs_memory = _ /\ _`
           (qspecl_then [`p`,`k`] mp_tac) >>
         impl_tac
         >- (disj2_tac >> disj1_tac >> qexists_tac `name` >>
             qpat_assum `!nm p k. local_region _ _ s nm p k <=> _`
               (qspecl_then [`name`,`p`,`k`] (fn th => rewrite_tac[GSYM th])) >>
             first_assum ACCEPT_TAC) >>
         disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     qexistsl [`k`,`p`] >> asm_rewrite_tac[] >>
     qpat_assum `!b n. _ ==> mem_bytes_at b n v.vs_memory = _ /\ _`
       (qspecl_then [`p`,`k`] mp_tac) >>
     impl_tac
     >- (disj2_tac >> disj2_tac >> qexists_tac `id` >> asm_rewrite_tac[] >>
         qpat_assum `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> _` irule >>
         first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  suspend "close"
QED

Resume ext_packing_cursor_frame_mods[close]:
  `v.vs_accounts = u.vs_accounts /\ v.vs_transient = u.vs_transient /\
   v.vs_immutables = u.vs_immutables` by
    (qhdtm_assum `abi_encoder_registered_effect` mp_tac >>
     pure_rewrite_tac[abi_encoder_registered_effect_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `v.vs_call_ctx = u.vs_call_ctx /\ v.vs_data_section = u.vs_data_section /\
   LENGTH u.vs_memory <= LENGTH v.vs_memory` by
    (qhdtm_assum `abi_encode_exec_frame` mp_tac >>
     pure_rewrite_tac[abi_encode_exec_frame_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `lookup_var root v = SOME (n2w pbase) /\ ptr_covers Gv tv root v capacity` by
    (qpat_assum `!x w n. _ ==> lookup_var x v = SOME w /\ _` irule >> asm_rewrite_tac[]) >>
  `lookup_var dst v = SOME (n2w (pbase+32)) /\ ptr_covers Gv tv dst v (capacity-32)` by
    (qpat_assum `!x w n. _ ==> lookup_var x v = SOME w /\ _` irule >> asm_rewrite_tac[]) >>
  `FLOOKUP Gv root = SOME (pbase,capacity)` by
    (qpat_assum `!x. not_fresh_at a x ==> FLOOKUP Gv x = _ /\ _` (drule_then strip_assume_tac) >>
     fs[]) >>
  `FLOOKUP v.vs_allocas owner = SOME (pbase,capacity)` by
    (qpat_assum `!aid row. FLOOKUP u.vs_allocas aid = SOME row ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  qhdtm_x_assum `ci_mono` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `not_fresh_at c root /\ not_fresh_at c dst` by
    (conj_tac >> irule not_fresh_at_mono >> qexists_tac `a` >> asm_rewrite_tac[]) >>
  `front.cs_next_var <= c.cs_next_var /\ owner < c.cs_next_id /\
   LENGTH s.vs_memory <= LENGTH v.vs_memory` by decide_tac >>
  qpat_assum `tv.t_mem SUBSET tu.t_mem`
    (assume_tac o REWRITE_RULE[SUBSET_DEF]) >>
  `!i. pbase+28 <= i /\ i < pbase+32 ==> i NOTIN tv.t_mem` by
    (rpt strip_tac >> qpat_assum `!x. x IN tv.t_mem ==> x IN tu.t_mem`
       (drule_then assume_tac) >>
     qpat_assum `!i. pbase+28 <= i /\ _ ==> i NOTIN tu.t_mem`
       (drule_all_then mp_tac) >> asm_rewrite_tac[]) >>
  qpat_x_assum `!nm p k. local_region _ _ s nm p k <=> _` kall_tac >>
  PURE_REWRITE_TAC [ext_packing_endpoint_mods_def] >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n u.vs_memory = _ /\ _`
    (qspecl_then [`b`,`n`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n v.vs_memory = _`
    (qspecl_then [`b`,`n`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `i IN tu.t_mem` by
    (qpat_assum `!x. x IN tv.t_mem ==> x IN tu.t_mem` (drule_then ACCEPT_TAC)) >>
  qpat_assum `!i. b <= i /\ _ ==> i IN tn.t_mem` (drule_all_then ACCEPT_TAC)
QED

Finalise ext_packing_cursor_frame_mods
