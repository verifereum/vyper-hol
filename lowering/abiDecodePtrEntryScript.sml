(* Normalize stale temporaries before the successful builtin setup. *)
Theory abiDecodePtrEntry
Ancestors
  abiDecodePtrReady abiDecodePtrEntryFrame abiDecodePtrReentry abiDecodePtrReentryGhost
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader exprLoweringProps loweringHalt
  abiDecodePtrMemberInterface abiDecodePtrInputWindow
  bodyPtrHashBuiltinsCases exprSimHash loweringPosts abiDecoderReentry
  abiDecoderArrayInitReentry freshWrites compileEnv venomState finite_map
  words arithmetic list valueEncoding abiDecodePtrMemberFrame ptrDiscipline bodyPtrBopHashFrame

Theorem abi_decode_ptr_operand_entry:
  expr_post ctx func cenv cx e es0 s0c sa s0 es (BytesV bs) (Var p) s /\
  ptr_val_ok cx (expr_type e) (BytesV bs) (Var p) G tn s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\
  fn_has_code sa ready func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa p /\ abi_decoder_operand_live sa.cs_next_var (Var p) /\
  mn <= LENGTH bs /\ LENGTH bs <= mx /\ mx < dimword (:256) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ outsz < dimword (:256) ==>
  ?u G2 tn2 out q r w wout.
    eval_operand (Var p) s = SOME w /\
    buf.buf_operand = Var out /\ src = Var q /\ len = Var r /\
    gas_path_ptr D 0 ctx func PG G tn (abi_decoder_prune_vars sa.cs_next_var s)
      0 G2 tn2 (OK u) /\
    run_inst_seq (emitted_insts sa ready) (abi_decoder_prune_vars sa.cs_next_var s) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa ready)
      (abi_decoder_prune_vars sa.cs_next_var s) G2 tn2 /\
    u.vs_memory = s.vs_memory /\
    ghost_kept cenv es sa G tn s G2 tn2 /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
       regions_disjoint (w2n wout) outsz b k) /\
    (!name b k. local_region cenv es.scopes s name b k ==>
       regions_disjoint (w2n wout) outsz b k) /\
    abi_decode_member_live d ctx func cenv cx es q (w+32w) (LENGTH bs)
      out wout outsz (Lit 0w) 0w (Var r) ready G2 tn2 u /\
    abi_decoder_vars_extend s.vs_vars (abi_decoder_prune_vars sa.cs_next_var s) s
Proof
  strip_tac >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all hash_dynamic_bytes_operand >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   expr_val_at cenv cx (expr_type e) s0c sa es (BytesV bs) (Var p) s` by
    fs[expr_post_def] >>
  `sa.cs_next_id <= sh.cs_next_id /\ sa.cs_next_var <= ready.cs_next_var` by
    (drule abi_builtin_decode_header_shape >> strip_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  drule_all abi_decode_bytes_physical_window >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "ownership") assume_tac) >>
  suspend "normalize"
QED

Resume abi_decode_ptr_operand_entry[normalize]:
  gvs[] >>
  `b < dimword (:256)` by decide_tac >>
  `(b:num) MOD dimword (:256) = b` by
    (irule arithmeticTheory.LESS_MOD >> asm_rewrite_tac[]) >>
  asm "ownership" (assume_tac o PURE_REWRITE_RULE [wordsTheory.w2n_n2w]) >>
  qpat_x_assum `(b:num) MOD dimword (:256) = b` SUBST_ALL_TAC >>
  pop_assum (mk_asm "physical") >>
  `!name a k. local_region cenv es.scopes (abi_decoder_prune_vars sa.cs_next_var s) name a k <=>
      local_region cenv es.scopes s name a k` by
    (rpt gen_tac >> irule bop_local_region_readonly_frame >> qexists_tac `sa` >>
     simp[] >> rpt strip_tac >>
     fs[lookup_var_def, abi_decoder_prune_vars_def, FLOOKUP_DRESTRICT,
        not_fresh_at_def, abi_decoder_older_vars_def]) >>
  SUBGOAL_THEN ``((?aid a k. FLOOKUP (abi_decoder_prune_vars sa.cs_next_var s).vs_allocas aid = SOME (a,k) /\
       aid < sh.cs_next_id /\ a <= b /\ b+32+LENGTH bs <= a+k) \/
    (?name a k. local_region cenv es.scopes (abi_decoder_prune_vars sa.cs_next_var s) name a k /\
       a <= b /\ b+32+LENGTH (bs:word8 list) <= a+k))`` (mk_asm "pruned") >-
    (asm "physical" mp_tac >>
     qpat_x_assum `!name a k. local_region _ _ _ _ _ _ <=> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     asm_rewrite_tac[] >> fs[NoAsms, abi_decoder_prune_vars_def] >>
     `b+(LENGTH bs+32) = LENGTH bs+(b+32)` by decide_tac >>
     metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx es (abi_decoder_prune_vars sa.cs_next_var s)` by
    (irule abi_decode_ptr_prune_stmt_state_rel >> simp[]) >>
  `ghost_inv d cenv cx es G tn (abi_decoder_prune_vars sa.cs_next_var s)` by
    (irule abi_decode_ptr_prune_ghost_reserved >> simp[]) >>
  `fresh_vars_wrt ready (abi_decoder_prune_vars sa.cs_next_var s)` by
    (mp_tac (Q.INST [`st` |-> `sa`, `s` |-> `s`] abi_decoder_prune_fresh) >>
     simp[fresh_vars_wrt_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `lookup_var p (abi_decoder_prune_vars sa.cs_next_var s) = SOME (n2w b)` by
    (drule_all abi_decoder_prune_eval >> fs[eval_operand_def]) >>
  `ptr_covers G tn p (abi_decoder_prune_vars sa.cs_next_var s) (32+LENGTH bs)` by
    (simp[abi_decode_ptr_prune_covers]) >>
  `mload (w2n (n2w b:256 word)) (abi_decoder_prune_vars sa.cs_next_var s) =
    n2w (LENGTH bs)` by
    fs[abi_decoder_prune_vars_def, mload_def, mem_word_at_def] >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars sa.cs_next_var s`,
    `w` |-> `(n2w b:256 word)`, `limit_st` |-> `ready`, `cnt` |-> `LENGTH (bs:word8 list)`,
    `n` |-> `LENGTH (bs:word8 list)`] abi_builtin_decode_phased_ready_ptr) >>
  impl_tac >- (simp[abi_decoder_prune_vars_def, mload_def, mem_word_at_def] >>
    metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  disch_then (qx_choose_then `u` (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `out` (qx_choose_then `q`
      (qx_choose_then `r` (qx_choose_then `wout`
        (map_every assume_tac o CONJUNCTS)))))))) >>
  qpat_x_assum `ante ==> cons` mp_tac >>
  impl_tac >- (asm "pruned" mp_tac >>
    qpat_assum `b < dimword (:256)` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
    `b + (LENGTH bs + 32) = b + 32 + LENGTH bs` by decide_tac >>
    asm_rewrite_tac[]) >>
  strip_tac >>
  qexistsl_tac [`u`, `G2`, `tn2`, `out`, `q`, `r`, `wout`] >>
  simp[abi_decoder_prune_vars_def] >>
  conj_tac >- (
    qpat_x_assum `ghost_kept cenv es sa G tn _ G2 tn2` mp_tac >>
    simp_tac bool_ss [bodyPtrDefsTheory.ghost_kept_def] >>
    asm_rewrite_tac[] >> simp[abi_decoder_prune_vars_def] >>
    strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid b k. aid < sh.cs_next_id /\ _ ==> _` irule >>
    simp[abi_decoder_prune_vars_def] >>
    goal_assum (drule_at Any) >> decide_tac) >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (
    `local_ptrs_reserved cenv ready` by
      (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
    `w2n ((n2w b:256 word) + 32w) = b + 32` by
      (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
       irule arithmeticTheory.LESS_MOD >> decide_tac) >>
    simp[abi_decode_member_live_def, abi_decode_ptr_window_def,
      eval_operand_def, op_prov_def, op_taint_def,
      compileEnvTheory.regions_disjoint_def] >>
    conj_tac >- (rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> metis_tac[]) >>
    conj_tac >- (rpt strip_tac >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
      simp[] >> metis_tac[]) >>
    gnvs[compileEnvTheory.regions_disjoint_def] >>
    conj_tac >- (rpt strip_tac >>
      qpat_x_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >>
      metis_tac[]) >> first_assum ACCEPT_TAC) >>
  MATCH_ACCEPT_TAC (REWRITE_RULE [abi_decoder_prune_vars_def] abi_decoder_prune_extension)
QED

Resume abi_decode_ptr_operand_entry[locals]:
  `!name a k. local_region cenv es.scopes u name a k <=>
      local_region cenv es.scopes (abi_decoder_prune_vars sa.cs_next_var s) name a k` by
    (rpt gen_tac >> irule bop_local_region_readonly_frame >>
     qexists_tac `sa` >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!name b k. local_region _ _ u _ _ _ ==> _` irule >>
  asm_rewrite_tac[] >> goal_assum (drule_at Any)
QED

Finalise abi_decode_ptr_operand_entry
