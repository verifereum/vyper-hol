(* Physical output setup for linked ABI encode.  The payload is not run here. *)
Theory bodyAbiEncodeSetupRunMods
Ancestors
  bodyFullAbiEncodeAllocOrigin bodyFullAbiEncodeSetupTail
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  abiBuiltinEncodeCode abiBuiltinEncodeMethod abiBuiltinEncodeRun exprLoweringProps
  typedMemoryCopy fragGasOriginPtr fragExec ptrDiscipline freshWrites
  stateRelProj loweringStateRelDefs bodyPtrDefs venomMemDefs
  memoryReadProps valueEncodingDefs valueEncodingProps compileEnv venomExecSemantics venomState
  words list pair finite_map pred_set arithmetic

Theorem abi_encode_setup_code[local]:
  lower_abi_encode mid maxlen (compile_abi_encode_payload ce single vs tys) st =
    (out,sb) /\ fn_has_code st sb func /\
  k = (case mid of NONE => 0 | SOME _ => 4) /\
  N = 32 + 32 * word_size (maxlen+k) ==>
  ?buf allocated method_st data ready len body_end.
    out = buf.buf_operand /\ compile_alloc_buffer N st = (buf,allocated) /\
    abi_builtin_encode_method_id mid out allocated = ((),method_st) /\
    emit_op ADD [out;Lit (n2w (32+k))] method_st = (data,ready) /\
    compile_abi_encode_payload ce single vs tys data ready = (len,body_end) /\
    abi_builtin_encode_finish out len k body_end = ((),sb) /\
    fn_has_code st allocated func /\ fn_has_code allocated ready func /\
    fn_has_code ready body_end func /\ fn_has_code body_end sb func /\
    st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= ready.cs_next_var
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_trace >> strip_tac >> gvs[] >>
  `ci_mono st allocated` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono allocated method_st` by metis_tac[ci_mono_abi_builtin_encode_method_id, SND] >>
  `ci_mono method_st ready` by metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono ready body_end` by metis_tac[ci_mono_compile_abi_encode_payload, SND] >>
  `cs_extends body_end sb` by
    (drule abi_builtin_encode_finish_shape >> metis_tac[cs_extends_same_block]) >>
  fs[ci_mono_def] >>
  `cs_extends allocated ready /\ cs_extends ready sb` by metis_tac[cs_extends_trans] >>
  `cs_extends allocated sb` by metis_tac[cs_extends_trans] >>
  drule_all (Q.SPECL [`st`,`allocated`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
  drule_all (Q.SPECL [`allocated`,`ready`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
  simp[] >> metis_tac[fn_has_code_split]
QED

Theorem abi_encode_setup_select[local]:
  k = (case mid of NONE => 0 | SOME _ => 4) /\
  write_len = (case mid of NONE => 0 | SOME _ => 32) /\
  (case mid of NONE => T | SOME w =>
     !mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
           mem_word_at (p+32) mem = w << 224) /\
  tf.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} ==>
  LENGTH (abi_builtin_encode_prefix mid) = k /\
  read_memory (p+32) k t = abi_builtin_encode_prefix mid /\
  (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tf.t_mem)
Proof
  Cases_on `mid`
  >- simp[abi_builtin_encode_prefix_def, read_memory_eq_mem_bytes_at, mem_bytes_at_def] >>
  simp[abi_builtin_encode_prefix_def, read_memory_eq_mem_bytes_at] >>
  disch_then strip_assume_tac >>
  irule abi_builtin_encode_method_window >> rewrite_tac[GSYM mem_word_at_eq_mload] >>
  first_x_assum irule >> simp[mem_agree_outside_def]
QED

(* Retain the registration and selector effects at the very same landing. *)
Theorem abi_encode_setup_run_effects_mods:
  lower_abi_encode mid maxlen (compile_abi_encode_payload ce single vs tys) st =
    (out,sb) /\ fn_has_code st sb func /\
  k = (case mid of NONE => 0 | SOME _ => 4) /\
  N = 32 + 32 * word_size (maxlen+k) /\ N < dimword(:256) /\
  write_len = (case mid of NONE => 0 | SOME _ => 32) /\ 32+write_len <= N /\
  prefix = abi_builtin_encode_prefix mid /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?buf allocated method_st dp ready len body_end root p u Gu tu pre Gpre tnpre.
    out = Var root /\ buf.buf_operand = Var root /\
    compile_alloc_buffer N st = (buf,allocated) /\
    abi_builtin_encode_method_id mid out allocated = ((),method_st) /\
    emit_op ADD [out;Lit (n2w (32+k))] method_st = (Var dp,ready) /\
    compile_abi_encode_payload ce single vs tys (Var dp) ready = (len,body_end) /\
    abi_builtin_encode_finish out len k body_end = ((),sb) /\
    fn_has_code st allocated func /\ fn_has_code allocated ready func /\
    fn_has_code ready body_end func /\ fn_has_code body_end sb func /\
    st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= ready.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK pre,Gpre,tnpre)) /\
    ~u.vs_halted /\ u.vs_current_bb = allocated.cs_current_bb /\
    u.vs_inst_idx = LENGTH allocated.cs_current_insts /\
    (!H'. stmt_state_rel (H':(bool # bytes32 # type_value) list # num list) ctx func ce cx es s ==>
          stmt_state_rel H' ctx func ce cx es u) /\
    ~pre.vs_halted /\ pre.vs_current_bb = ready.cs_current_bb /\
    pre.vs_inst_idx = LENGTH ready.cs_current_insts /\
    not_fresh_at allocated root /\ not_fresh_at ready root /\ not_fresh_at ready dp /\
    lookup_var root u = SOME (n2w p) /\ eval_operand out pre = SOME (n2w p) /\
    eval_operand (Var dp) pre = SOME (n2w (p+32+k)) /\
    ptr_covers Gu tu root u N /\ ptr_covers Gpre tnpre root pre N /\
    ptr_covers Gpre tnpre dp pre (N-(32+k)) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,N) /\
    FLOOKUP pre.vs_allocas st.cs_next_id = SOME (p,N) /\
    FLOOKUP Gu root = SOME (p,N) /\ FLOOKUP Gpre root = SOME (p,N) /\
    lo <= p /\ p+N < dimword(:256) /\ p+N <= pre.vs_alloca_next /\
    u.vs_allocas = pre.vs_allocas /\ u.vs_alloca_next = pre.vs_alloca_next /\
    s.vs_alloca_next <= pre.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP pre.vs_allocas aid = SOME e) /\
    (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint p N b n) /\
    (!name b n. local_region ce es.scopes u name b n ==> regions_disjoint p N b n) /\
    alloca_history func u /\ alloca_history func pre /\ alloca_inv pre /\ allocas_from lo pre /\
    (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
       FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
    u.vs_memory = s.vs_memory /\ typed_copy_state_frame allocated (p+32) write_len u pre /\
    LENGTH s.vs_memory <= LENGTH pre.vs_memory /\
    (!a n. a+n <= p+32 \/ p+32+write_len <= a ==>
       mem_bytes_at a n pre.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < p+N)) /\
    tnpre.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
    tnpre.t_stor = tn.t_stor /\ tnpre.t_trans = tn.t_trans /\ tnpre.t_imm = tn.t_imm /\
    LENGTH prefix = k /\ read_memory (p+32) k pre = prefix /\
    (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tnpre.t_mem) /\
    u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
             vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
    u.vs_allocas = (abi_builtin_allocate_state st.cs_next_id N s).vs_allocas /\
    MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func) /\
    (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
    (!op. (!x. op = Var x ==> not_fresh_at allocated x) ==>
       op_taint tnpre op = op_taint tu op /\ op_prov Gpre op = op_prov Gu op) /\
    st.cs_next_id < ready.cs_next_id
Proof
  strip_tac >> drule_all abi_encode_setup_code >> strip_tac >>
  drule_all (INST_TYPE [Type.beta |-> ``:256``] abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  qabbrev_tac `p = w2n (w:bytes32)` >>
  `w = n2w p` by simp[Abbr `p`] >>
  `lo <= p` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then drule >> simp[]) >>
  `stmt_state_rel H ctx func ce cx es u` by
    (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ s ==> _` irule >> simp[]) >>
  `alloca_inv u` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`) stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`)
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `~u.vs_halted /\ u.vs_memory = s.vs_memory` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `u with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _;
                           vs_inst_idx := _ |> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `out = Var root /\ lookup_var root u = SOME (n2w p)` by simp[] >>
  qpat_x_assum `out = Var root` SUBST_ALL_TAC >>
  drule_all abi_encode_setup_tail_origin >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`dp`,`pre`,`Gpre`,`tnpre`] strip_assume_tac)) >>
  suspend "effects"
QED

Resume abi_encode_setup_run_effects_mods[effects]:
  `!x. not_fresh_at allocated x ==> lookup_var x pre = lookup_var x u /\
       FLOOKUP Gpre x = FLOOKUP Gu x /\ op_taint tnpre (Var x) = op_taint tu (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!op. _ ==> eval_operand op pre = eval_operand op u /\ _`
       (qspec_then `Var x` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eval_operand_def, op_prov_def]) >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at allocated x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st` >> simp[]) >>
  `!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
       FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at allocated x ==> lookup_var x pre = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[] >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x u = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `not_fresh_at ready root` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `allocated` >> simp[]) >>
  `typed_copy_frame (p+32) write_len s.vs_memory pre.vs_memory` by
    (qpat_assum `typed_copy_state_frame _ _ _ u pre`
       (mp_tac o REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  drule_all abi_encode_setup_select >> strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func)` by
    (drule_all exprSimAllocTheory.buffer_alloc_code >>
     drule_then (assume_tac o CONJUNCT1) loweringHaltTheory.compile_alloc_buffer_parts >>
     `root = STRING #"%" (toString st.cs_next_var)` by
       (qpat_assum `Var root = buf.buf_operand` mp_tac >>
        qpat_assum `buf.buf_operand = Var (STRING _ _)` (fn th => pure_rewrite_tac [th]) >>
        simp[NoAsms]) >>
     qpat_assum `root = STRING _ _` (fn th => pure_rewrite_tac [th]) >>
     disch_then ACCEPT_TAC) >>
  `st.cs_next_id < ready.cs_next_id` by
    (drule_then strip_assume_tac loweringHaltTheory.compile_alloc_buffer_parts >>
     `ci_mono allocated method_st` by metis_tac[ci_mono_abi_builtin_encode_method_id, SND] >>
     `ci_mono method_st ready` by metis_tac[ci_mono_emit_op, SND] >>
     fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `Var root = buf.buf_operand` kall_tac >>
  `FLOOKUP Gpre root = SOME (p,N)` by
    (qpat_assum `!x. not_fresh_at allocated x ==> lookup_var x pre = _ /\ _`
       (qspec_then `root` mp_tac) >> simp[]) >>
  qpat_assum `typed_copy_frame _ _ s.vs_memory pre.vs_memory`
    (strip_assume_tac o REWRITE_RULE [typed_copy_frame_def]) >>
  qpat_x_assum `data = Var dp` SUBST_ALL_TAC >>
  qpat_x_assum `u.vs_alloca_next = (abi_builtin_allocate_state _ _ _).vs_alloca_next` kall_tac >>
  qpat_x_assum `N = 32 + 32 * word_size _` kall_tac >>
  qpat_x_assum `k = (case mid of NONE => 0 | SOME _ => 4)` kall_tac >>
  qpat_x_assum `write_len = (case mid of NONE => 0 | SOME _ => 32)` kall_tac >>
  qexistsl_tac [`buf`,`allocated`,`method_st`,`dp`,`ready`,`len`,`body_end`,
    `root`,`p`,`u`,`Gu`,`tu`,`pre`,`Gpre`,`tnpre`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  asm_simp_tac bool_ss [] >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qpat_assum `u.vs_allocas = (abi_builtin_allocate_state _ _ _).vs_allocas`
    (fn th => pure_rewrite_tac [SYM th]) >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_setup_run_effects_mods

Theorem abi_encode_setup_run_mods:
  lower_abi_encode mid maxlen (compile_abi_encode_payload ce single vs tys) st =
    (out,sb) /\ fn_has_code st sb func /\
  k = (case mid of NONE => 0 | SOME _ => 4) /\
  N = 32 + 32 * word_size (maxlen+k) /\ N < dimword(:256) /\
  write_len = (case mid of NONE => 0 | SOME _ => 32) /\ 32+write_len <= N /\
  prefix = abi_builtin_encode_prefix mid /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce st /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?buf allocated method_st dp ready len body_end root p u Gu tu pre Gpre tnpre.
    out = Var root /\ buf.buf_operand = Var root /\
    compile_alloc_buffer N st = (buf,allocated) /\
    abi_builtin_encode_method_id mid out allocated = ((),method_st) /\
    emit_op ADD [out;Lit (n2w (32+k))] method_st = (Var dp,ready) /\
    compile_abi_encode_payload ce single vs tys (Var dp) ready = (len,body_end) /\
    abi_builtin_encode_finish out len k body_end = ((),sb) /\
    fn_has_code st allocated func /\ fn_has_code allocated ready func /\
    fn_has_code ready body_end func /\ fn_has_code body_end sb func /\
    st.cs_next_var <= allocated.cs_next_var /\ allocated.cs_next_var <= ready.cs_next_var /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK pre,Gpre,tnpre)) /\
    ~u.vs_halted /\ u.vs_current_bb = allocated.cs_current_bb /\
    u.vs_inst_idx = LENGTH allocated.cs_current_insts /\
    (!H'. stmt_state_rel (H':(bool # bytes32 # type_value) list # num list) ctx func ce cx es s ==>
          stmt_state_rel H' ctx func ce cx es u) /\
    ~pre.vs_halted /\ pre.vs_current_bb = ready.cs_current_bb /\
    pre.vs_inst_idx = LENGTH ready.cs_current_insts /\
    not_fresh_at allocated root /\ not_fresh_at ready root /\ not_fresh_at ready dp /\
    lookup_var root u = SOME (n2w p) /\ eval_operand out pre = SOME (n2w p) /\
    eval_operand (Var dp) pre = SOME (n2w (p+32+k)) /\
    ptr_covers Gu tu root u N /\ ptr_covers Gpre tnpre root pre N /\
    ptr_covers Gpre tnpre dp pre (N-(32+k)) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,N) /\
    FLOOKUP pre.vs_allocas st.cs_next_id = SOME (p,N) /\
    FLOOKUP Gu root = SOME (p,N) /\ FLOOKUP Gpre root = SOME (p,N) /\
    lo <= p /\ p+N < dimword(:256) /\ p+N <= pre.vs_alloca_next /\
    u.vs_allocas = pre.vs_allocas /\ u.vs_alloca_next = pre.vs_alloca_next /\
    s.vs_alloca_next <= pre.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP pre.vs_allocas aid = SOME e) /\
    (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint p N b n) /\
    (!name b n. local_region ce es.scopes u name b n ==> regions_disjoint p N b n) /\
    alloca_history func u /\ alloca_history func pre /\ alloca_inv pre /\ allocas_from lo pre /\
    (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
       FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
    u.vs_memory = s.vs_memory /\ typed_copy_state_frame allocated (p+32) write_len u pre /\
    LENGTH s.vs_memory <= LENGTH pre.vs_memory /\
    (!a n. a+n <= p+32 \/ p+32+write_len <= a ==>
       mem_bytes_at a n pre.vs_memory = mem_bytes_at a n s.vs_memory) /\
    (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < p+N)) /\
    tnpre.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
    tnpre.t_stor = tn.t_stor /\ tnpre.t_trans = tn.t_trans /\ tnpre.t_imm = tn.t_imm /\
    LENGTH prefix = k /\ read_memory (p+32) k pre = prefix /\
    (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tnpre.t_mem)
Proof
  strip_tac >> drule_all abi_encode_setup_run_effects_mods >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`buf`,`allocated`,`method_st`,`dp`,`ready`,`len`,`body_end`,
      `root`,`p`,`u`,`Gu`,`tu`,`pre`,`Gpre`,`tnpre`] strip_assume_tac)) >>
  qexistsl_tac [`buf`,`allocated`,`method_st`,`dp`,`ready`,`len`,`body_end`,
    `root`,`p`,`u`,`Gu`,`tu`,`pre`,`Gpre`,`tnpre`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
