Theory bodyAbiDecodeGuardedWordStoreMods
Ancestors
  bodyFullAbiDecodeOwnedWordStoreObserved[qualified]
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeDecoderFrame calldataOverwritePtr exprSimProps
  emitHelperProps fragGasSeqPtr exprLoweringProps venomInst venomExecSemantics
  pred_set words stateRelProj stateFrame wordLoadStorePtr bodyPtrDefs
  compileEnv loweringStateRelDefs venomState finite_map list rich_list
  valueEncodingProps exprSimCopy abiDecodePtrMemberFrame venomMemDefs
  ptrDiscipline assignTuplePtrStoreWord bodyFullAbiDecodeRelativeLoadExact[qualified]

local
  val old = concl
    bodyFullAbiDecodeOwnedWordStoreObservedTheory.abi_decode_owned_word_store_observed_exact
  val (pre, post) = dest_imp (#2 (strip_forall old))
  val (ws as [t,_,tnf], body) = strip_exists post
  val s = valOf (List.find (fn v => fst (dest_var v) = "s") (free_vars pre))
  val tn = valOf (List.find (fn v => fst (dest_var v) = "tn") (free_vars pre))
  val fields = ``^t.vs_alloca_next = ^s.vs_alloca_next /\
    ^tnf.t_stor = ^tn.t_stor /\ ^tnf.t_trans = ^tn.t_trans /\
    ^tnf.t_imm = ^tn.t_imm``
  val tm = rhs (concl (DEPTH_CONV BETA_CONV
    (mk_imp (pre,list_mk_exists (ws,mk_conj (body,fields))))))
in
  val owned_word_store_effect_statement = list_mk_forall (free_vars tm, tm)
end

(* The pointer certificate and the raw run describe the same physical write.
   Only its cursor changes when the finite run is lifted to an observer. *)
Theorem word_store_selected[local]:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  eval_operand (Var dst) s = SOME dw /\ eval_operand value s = SOME w /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  w2n dw + 32 <= s.vs_alloca_next ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)) /\
    t = (mstore (w2n dw) w s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    Gf = step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] [])
           (mstore (w2n dw) w s) /\
    tnf = step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s
            (mstore (w2n dw) w s) tn /\
    tnf.t_mem SUBSET tn.t_mem /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tnf.t_mem) /\
    t.vs_alloca_next = s.vs_alloca_next /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG` (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` (map_every assume_tac o CONJUNCTS))))) >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s =
     OK (mstore (w2n dw) w s)` by (irule step_MSTORE >> simp[]) >>
  `run_inst_seq [mk_inst sa.cs_next_id MSTORE [Var dst;value] []] s =
     OK (mstore (w2n dw) w s)` by simp[run_inst_seq_def] >>
  `t = (mstore (w2n dw) w s with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf)` by
    (qpat_assum `w2n dw + 32 <= s.vs_alloca_next ==> _` (drule_then irule)) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `t = _` SUBST1_TAC >> rpt strip_tac >>
      irule abi_decode_finite_success_observed >>
      conj_tac >- simp[] >>
      qexistsl_tac [`[mk_inst sa.cs_next_id MSTORE [Var dst;value] []]`, `sa`] >>
      fs[same_blocks_def,mk_inst_def,is_terminator_def]) >>
  qpat_x_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `ARB` mp_tac) >> simp[inst_seq_ptr_def]
QED

(* Apply the write frame at the physical write, identify its ghosts by
   their transfer equations, then transport across the cursor update. *)
Theorem word_store_write_frame[local]:
  fn_inst_ids_distinct fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [output] /\
  not_local_ptr ce es.scopes output /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= w2n dw /\ w2n dw + 32 <= b + sz /\
  lookup_var dst s = SOME dw /\ ptr_covers G tn dst s 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  abi_decode_ptr_window G tn s input input_word n /\
  (w2n input_word + n <= w2n dw \/ w2n dw + 32 <= w2n input_word) /\
  local_ptrs_rel fn ce es.scopes s /\ local_ptrs_reserved ce sa /\
  origin.cs_next_var <= sa.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     w2n dw + 32 <= lb \/ lb + len <= w2n dw) /\ lo <= w2n dw /\
  (?H. V H) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  u = mstore (w2n dw) w s /\ t = (u with vs_inst_idx := idx) /\
  Gf = step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) u /\
  tnf = step_taint (mk_inst sa.cs_next_id MSTORE [Var dst;value] []) s u tn ==>
  abi_decode_ptr_window Gf tnf t input input_word n /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es s` by metis_tac[] >>
  `!H. V H ==> abi_decode_ptr_window Gf tnf u input input_word n /\
    stmt_state_rel H ctx fn ce cx es u /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (qx_gen_tac `h` >> disch_tac >>
     `ghost_inv_at (DF h) lo delta ce cx es G tn s /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn` by metis_tac[] >>
     drule_all abi_decode_output_write_frame_joint >>
     disch_then (qspecl_then [`sa.cs_next_id`, `PG`] mp_tac) >> simp[]) >>
  conj_tac
  >- (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gf`,`u`,`tnf`] >>
      conj_tac >- metis_tac[] >> simp[lookup_var_def]) >>
  ho_match_mp_tac (bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_scalar_joint_frame_lower |>
    Q.INST [`s` |-> `u`, `G` |-> `Gf`, `tn` |-> `tnf`]) >>
  simp[state_frame_def,lookup_var_def] >> metis_tac[]
QED

Theorem abi_decode_owned_word_store_effect_mods:
  ^owned_word_store_effect_statement
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var dst) s = SOME dw /\ allocas_from lo s` by
    (conj_tac >- simp[eval_operand_def] >> metis_tac[ghost_inv_at_def]) >>
  drule_all word_store_selected >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS))))) >>
  qabbrev_tac `u = mstore (w2n dw) w s` >>
  `u = mstore (w2n dw) w s` by simp[Abbr `u`] >>
  qpat_assum `?inst. MEM inst (fn_insts fn) /\ _`
    (qx_choose_then `inst` strip_assume_tac) >>
  `local_ptrs_rel fn ce es.scopes s /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (output_base,output_cap)` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `lo <= w2n dw /\ (!name b k. local_region ce es.scopes s name b k ==>
     w2n dw+32 <= b \/ b+k <= w2n dw)` by
    (conj_tac >- decide_tac >> rpt strip_tac >>
     qpat_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >> decide_tac) >>
  drule_all word_store_write_frame >> strip_tac >>
  suspend "physical_frame"
QED

Resume abi_decode_owned_word_store_effect_mods[physical_frame]:
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_allocas = s.vs_allocas /\
   (!p. lookup_var p t = lookup_var p s)` by
    (qpat_assum `t = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms,mstore_def,lookup_var_def] >> asm_rewrite_tac[]) >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sb`] >> simp[mk_inst_def,IS_PREFIX_APPEND]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`sa.cs_next_id`] strip_assume_tac) >>
  `Gf = G /\ tnf.t_var = tn.t_var /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` by
    (qpat_assum `Gf = step_prov _ _ _ _` SUBST1_TAC >>
     qpat_assum `tnf = _` SUBST1_TAC >>
     qpat_assum `u = _` SUBST1_TAC >> asm_rewrite_tac[]) >>
  `!p k. ptr_covers Gf tnf p t k = ptr_covers G tn p s k` by
    simp[ptr_covers_def,ptrDisciplineTheory.op_taint_def,lookup_var_def] >>
  `!b k. b+k <= w2n dw \/ w2n dw+32 <= b ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    (qpat_assum `t = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms] >> rpt gen_tac >> disch_tac >>
     irule mstore_mem_bytes_at_disjoint >> first_assum ACCEPT_TAC) >>
  `!name b k. local_region ce es.scopes t name b k =
     local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  suspend "package"
QED

Resume abi_decode_owned_word_store_effect_mods[package]:
  `!tv v. type_memory_size tv = 32 /\ val_wf tv v /\
     val_in_memory tv v (w2n dw) t.vs_memory ==>
     !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory tv v (w2n dw) mem` by
    (rpt strip_tac >> drule val_footprint_le >> strip_tac >>
     irule val_in_memory_clean_footprint_ptr >> conj_tac >- simp[] >>
     qexistsl_tac [`tnf.t_mem`, `t.vs_memory`] >>
     reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!i. w2n dw <= i /\ i < w2n dw + 32 ==> _` irule >>
     decide_tac) >>
  `!p. op_taint tnf (Var p) = op_taint tn (Var p)` by
    simp[ptrDisciplineTheory.op_taint_def] >>
  `!p. FLOOKUP Gf p = FLOOKUP G p` by simp[] >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`t = _`, `u = _`, `tnf = _`, `Gf = step_prov _ _ _ _`, `Gf = G`, `tnf.t_mem = _`] >>
  `not_fresh_at sb = not_fresh_at sa` by simp[FUN_EQ_THM,not_fresh_at_def] >>
  simp[] >> asm_rewrite_tac[] >> rpt conj_tac
  >~ [`mem_bytes_at (w2n input_word) _ t.vs_memory = _`]
  >- (qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
         (qspecl_then [`w2n input_word`,`LENGTH input_bytes`] drule) >> simp[])
  >~ [`EVERY _ live`]
  >- suspend "live"
  >~ [`EVERY _ protected`]
  >- suspend "protected" >>
  qpat_assum `(?aid ib isz. aid < output_id /\ FLOOKUP s.vs_allocas aid = _ /\ _) \/ _`
    mp_tac >> simp[NoAsms, arithmeticTheory.ADD_COMM]
QED

Resume abi_decode_owned_word_store_effect_mods[live]:
  simp[EVERY_MEM] >> qx_gen_tac `entry` >> PairCases_on `entry` >> disch_tac >>
  qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < sa.cs_next_id /\ _) live`
    (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
  disch_then (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `EVERY (\(aid,p,b,k,bytes). b+k <= _ \/ _) live`
    (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
  disch_then (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
    (qspecl_then [`entry2`,`entry3`] (drule_then assume_tac)) >>
  simp[] >> decide_tac
QED

Resume abi_decode_owned_word_store_effect_mods[protected]:
  simp[EVERY_MEM] >> qx_gen_tac `entry` >> PairCases_on `entry` >> disch_tac >>
  qpat_assum `EVERY (\(a,bytes). a + LENGTH bytes <= _ \/ _) protected`
    (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
  disch_then (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `EVERY (\(a,bytes). mem_bytes_at a _ s.vs_memory = _) protected`
    (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
  disch_then (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
    (qspecl_then [`entry0`,`LENGTH entry1`] (drule_then assume_tac)) >> simp[]
QED

Finalise abi_decode_owned_word_store_effect_mods
