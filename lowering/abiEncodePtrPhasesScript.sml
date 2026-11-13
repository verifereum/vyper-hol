(*
 * lower_abi_encode with the pointer check: the twin of
 * exprSimAbiEncodeFramedSuffix's abi_encode_framed_phases_open_extend.
 * The setup (output alloca, data pointer, method id), the encoder body
 * (the joint window producer) and the length store run as one
 * pointer-checked path that ends where the framed phases end, with the
 * ghost kept and the output buffer covered and untainted.
 *
 * TOP-LEVEL:
 *   abi_encode_framed_phases_ptr
 *)
Theory abiEncodePtrPhases
Ancestors
  exprSimAbiEncodeFramedSuffix bodyPtrDefs fragGasPathPtr
  exprLoweringProps abiBuiltinEncodeCode abiEncoderWindowContract
  exprSimAbiEncodeExecFrame venomState list venomMemDefs
  abiEncodePtrSetup abiEncodePtrFinish abiEncodePtrGhostFrame
  abiEncoderWindowJoint fragGasOriginPtr ptrDiscipline

val _ = Parse.hide "body";

Theorem abi_encode_framed_phases_ptr:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len m body_end = ((),final) /\
  m = (case method_id of NONE => 0 | SOME mid => 4) /\
  w = (case method_id of NONE => 0 | SOME mid => 32) /\
  d = p+32+m /\ outsz = 32+32*word_size (maxlen+m) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p < dimword (:256) /\
  (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem initial.vs_memory mem ==>
     abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  (!x. src = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
  (!x. FST ops = Var x ==> not_fresh_at ready x) /\
  abi_decoder_operand_live body_end.cs_next_var (FST ops) /\
  alloca_inv (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  alloca_room ctx func (abi_builtin_allocate_state st.cs_next_id outsz initial) /\
  sb+cap <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  d+LENGTH (enc at av) <= (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_alloca_next /\
  venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
  (sb+cap <= p+32 \/ p+32+w <= sb) /\
  venomMemDefs$regions_disjoint (p+32,m) (d,LENGTH (enc at av)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids ready body_end /\
    FLOOKUP (abi_builtin_allocate_state st.cs_next_id outsz initial).vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ venomMemDefs$regions_disjoint (sb,cap) (b,sz) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz) /\
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)) /\
  (* the pointer side *)
  LENGTH (enc at av) <= maxlen /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  op_taint tn src = {} /\
  (0 < cap ==> ?x. src = Var x /\ ptr_covers G tn x initial cap) /\
  (0 < cap ==> sb + cap <= initial.vs_alloca_next) /\
  local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  stmt_state_rel ctx func cenv cx es initial /\
  ghost_inv rb cenv cx es G tn initial ==>
  ?prepared body actual G' tn' x.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (enc at av)+m) /\
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_decode_sim ctx func initial actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p w initial prepared /\
    window_strong_result ctx func ready body_end len at av d prepared body /\
    abi_decode_frame p 32 body actual /\
    actual.vs_allocas = body.vs_allocas /\ actual.vs_alloca_next = body.vs_alloca_next /\
    abi_encoder_registered_effect {} [(p,32)] body actual /\
    (!op v. abi_decoder_operand_live body_end.cs_next_var op /\ eval_operand op body = SOME v ==>
      eval_operand op actual = SOME v) /\
    abi_encode_exec_frame func initial actual /\
    LENGTH initial.vs_memory <= LENGTH actual.vs_memory /\
    prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
    prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
    prepared.vs_pending_deletions = initial.vs_pending_deletions /\
    prepared.vs_labels = initial.vs_labels /\ actual.vs_labels = initial.vs_labels /\
    abi_encoder_extend_sim ctx func initial actual /\
    (* the pointer side *)
    gas_path_ptr (cx_dead cx) 0 ctx func PG G tn initial 0 G' tn' (OK actual) /\
    ghost_inv rb cenv cx es G' tn' actual /\
    ghost_kept cenv es st G tn initial G' tn' /\
    FST ops = Var x /\ ptr_covers G' tn' x actual outsz /\
    (!i. p <= i /\ i < p + 32 + m + LENGTH (enc at av) ==> i NOTIN tn'.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_setup_ptr_entry_semantic >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  rename1 `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` >>
  `?body Hbody tbody.
    window_strong_result ctx func ready body_end len at av d prepared body /\
    abi_encode_exec_frame func prepared body /\
    op_taint tbody len = {} /\
    (!x. len = Var x ==> not_fresh_at body_end x) /\
    (!i. d <= i /\ i < d + LENGTH (enc at av) ==> i NOTIN tbody.t_mem) /\
    (!x. not_fresh_at ready x ==> FLOOKUP Hbody x = FLOOKUP H x /\
      op_taint tbody (Var x) = op_taint tf (Var x)) /\
    (!i. (i < d \/ d + LENGTH (enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids ready body_end) /\
        FLOOKUP body.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
      (i IN tbody.t_mem <=> i IN tf.t_mem)) /\
    tbody.t_stor = tf.t_stor /\ tbody.t_trans = tf.t_trans /\ tbody.t_imm = tf.t_imm /\
    !D. gas_origin_ptr_path (D,0,(\j. F),ctx,func,PG)
      (prepared,H,tf) [] (OK body,Hbody,tbody)` by
    (irule compile_abi_encode_to_buf_window_joint >>
     simp_tac bool_ss [allocas_from_def, arithmeticTheory.ZERO_LESS_EQ] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qexistsl [`cap`, `SND ops`, `ei`, `sb`, `src`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [abiBuiltinEncodeSetupTheory.abi_builtin_encode_setup_frame_def]) >>
         rpt strip_tac >>
         metis_tac[]) >>
     rpt strip_tac >> rpt conj_tac >> simp[]) >>
  pop_assum strip_assume_tac >>
  `eval_operand (FST ops) body = SOME (n2w p)` by
    (irule exprSimAbiEncodeExecutionTheory.abi_encode_setup_buffer_eval >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     first_assum ACCEPT_TAC) >>
  `ptr_covers Hbody tbody x body outsz` by
    (`FLOOKUP Hbody x = FLOOKUP H x /\
      op_taint tbody (Var x) = op_taint tf (Var x)` by metis_tac[] >>
     qpat_assum `ptr_covers H tf x prepared outsz`
       (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
     pure_asm_rewrite_tac [ptr_covers_def] >>
     `lookup_var x body = lookup_var x prepared` by
       (qpat_x_assum `eval_operand (FST ops) body = _` mp_tac >>
        qpat_x_assum `eval_operand (FST ops) prepared = _` mp_tac >>
        pure_asm_rewrite_tac [venomStateTheory.eval_operand_def] >>
        simp_tac bool_ss []) >>
     metis_tac[]) >>
  qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE
      [abiEncoderWindowContractTheory.window_strong_result_def,
       abiEncoderWindowContractTheory.abi_encoder_window_result_def]) >>
  `32 <= outsz` by (qpat_x_assum `outsz = _` SUBST1_TAC >> decide_tac) >>
  `eval_operand (Var x) body = SOME (n2w p)` by metis_tac[] >>
  `abi_builtin_encode_finish (Var x) len m body_end = ((),final)` by metis_tac[] >>
  `abi_decoder_operand_live body_end.cs_next_var (Var x)` by metis_tac[] >>
  `mem_bytes_at (p+32) (m+LENGTH (enc at av)) body.vs_memory =
    mem_bytes_at (p+32) (m+LENGTH (enc at av)) body.vs_memory` by REFL_TAC >>
  drule_all abi_encode_finish_ptr_from_body_semantic >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `cx_dead cx`
      (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections)) >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ prepared _ _ _ _`
    (assume_tac o PURE_REWRITE_RULE [listTheory.LENGTH]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn initial 0 H' tf' (OK actual)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn initial _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ H tf prepared _ _ _ _` mp_tac >>
     qpat_assum `gas_path_ptr _ _ _ _ _ Hbody tbody body _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]) >>
  `abi_encode_exec_frame func initial actual` by
    (irule abi_encode_exec_frame_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_encode_exec_frame_trans >> qexists `body` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abiEncoderExtendSimTheory.abi_encoder_extend_sim_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abiEncoderExtendSimTheory.abi_encoder_extend_sim_trans >> qexists `body` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abiDecoderLoopTheory.abi_decode_sim_trans >> qexists `prepared` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abiDecoderLoopTheory.abi_decode_sim_trans >> qexists `body` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule abi_encode_exec_frame_memory_length >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abiEncoderCountersTheory.abi_encoder_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
   st.cs_next_id <= ready.cs_next_id` by
    (qpat_x_assum `ready.cs_next_var = _` mp_tac >>
     qpat_x_assum `ready.cs_next_id = _` mp_tac >>
     qpat_x_assum `ready.cs_next_var <= body_end.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `method_id` >> simp[] >> decide_tac) >>
  `d+LENGTH(enc at av) <= p+outsz` by
    (qspec_then `maxlen+m` mp_tac abiBuiltinAllocationTheory.abi_builtin_word_size_capacity >>
     qpat_x_assum `outsz = _` mp_tac >> qpat_x_assum `d = _` mp_tac >>
     qpat_x_assum `LENGTH(enc at av) <= maxlen` mp_tac >> decide_tac) >>
  `32+w <= outsz` by
    (qspec_then `maxlen+m` mp_tac abiBuiltinAllocationTheory.abi_builtin_word_size_capacity >>
     qpat_x_assum `outsz = _` mp_tac >> qpat_x_assum `m = _` mp_tac >>
     qpat_x_assum `w = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `method_id` >> simp[] >> rpt strip_tac >>
     Cases_on `word_size (maxlen+m)` >> gvs[] >> decide_tac) >>
  `!id b sz. id IN window_alloca_sites func (frag_ids ready body_end) /\
    FLOOKUP prepared.vs_allocas id = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (p+32,m) (b,sz)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `_ IN window_alloca_sites _ _` mp_tac >>
     simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def] >>
     strip_tac >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abiBuiltinEncodeSetupTheory.abi_builtin_encode_setup_frame_def]) >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
     qpat_x_assum `FLOOKUP prepared.vs_allocas id = SOME(b,sz)` mp_tac >>
     pure_asm_rewrite_tac[] >> simp_tac bool_ss [] >> metis_tac[]) >>
  `ghost_inv rb cenv cx es H' tf' actual /\
   ghost_kept cenv es st G tn initial H' tf' /\
   (!i. p <= i /\ i < p+32+m+LENGTH(enc at av) ==> i NOTIN tf'.t_mem)` by
    (irule abi_encode_phases_effects_transport >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ prepared body` (irule_at Any) >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ initial prepared` (irule_at Any) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
     qexistsl [`tf`,`tbody`,`Hbody`,`H`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `abi_encode_exec_frame func prepared body` mp_tac >>
     simp_tac (srw_ss()) [abi_encode_exec_frame_def]) >>
  `mem_bytes_at (p+32) m body.vs_memory = mem_bytes_at (p+32) m prepared.vs_memory` by
    (irule abiEncoderWindowContractTheory.window_alloca_growth_frame >>
     conj_tac >-
       (qpat_x_assum `d + LENGTH _ <= prepared.vs_alloca_next` mp_tac >>
        qpat_x_assum `d = _` mp_tac >> decide_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`window_alloca_sites func (frag_ids ready body_end)`, `[(d,LENGTH(enc at av))]`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av` by
    (qpat_assum `abi_decode_frame p 32 body actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abiDecoderContractTheory.abi_decode_frame_def]) >>
     qpat_x_assum `!p' k. _` (qspecl_then [`d`, `LENGTH (enc at av)`] mp_tac) >>
     (impl_tac >- (qpat_x_assum `d = _` mp_tac >> decide_tac)) >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `(case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid)` by
    (qpat_assum `abi_decode_frame p 32 body actual`
       (strip_assume_tac o PURE_REWRITE_RULE [abiDecoderContractTheory.abi_decode_frame_def]) >>
     `mem_bytes_at (p+32) m actual.vs_memory = mem_bytes_at (p+32) m body.vs_memory` by
       (qpat_x_assum `!p' k. _` (qspecl_then [`p+32`, `m`] mp_tac) >>
        simp_tac bool_ss [arithmeticTheory.LE_REFL]) >>
     qpat_x_assum `mem_bytes_at (p+32) m body.vs_memory = _` mp_tac >>
     qpat_x_assum `mem_bytes_at (p+32) m actual.vs_memory = _` mp_tac >>
     qpat_x_assum `case method_id of NONE => T | SOME mid => _` mp_tac >>
     qpat_x_assum `m = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `method_id` >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  `actual.vs_labels = initial.vs_labels` by
    (qpat_x_assum `actual.vs_labels = prepared.vs_labels` mp_tac >>
     qpat_x_assum `prepared.vs_labels = initial.vs_labels` mp_tac >>
     simp_tac (srw_ss()) []) >>
  qexistsl [`prepared`,`body`,`actual`,`H'`,`tf'`,`x`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
  first_assum ACCEPT_TAC
QED
