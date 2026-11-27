Theory bodyAbiDecodeBytesZeroStoreFiniteMods
Ancestors
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeDecoderFrame bodyFullAbiDecodeLeafCases
  calldataOverwritePtr assignTuplePtrStoreWord exprSimProps emitHelperProps
  fragGasSeqPtr exprLoweringProps venomInst venomExecSemantics pred_set words
  stateRelProj stateFrame wordLoadStorePtr bodyPtrDefs compileEnv
  loweringStateRelDefs venomState finite_map list rich_list valueEncodingProps
  exprSimCopy abiDecodePtrMemberFrame venomMemDefs ptrDiscipline
  fragExecMem instMemFrontier memSafeRun unitTransformDefs arithmetic relation
  bodyFullAbiDecodeRelativeLoadExact[qualified]

(* The lift is a closed packet; it is instantiated only on the selected run. *)
val emitted_finite = ``
  fn_has_code sa sb fn /\ inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      dalloca_no_wrap i u) /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  RELPOW (\(u,Gu,tu) (v,Gv,tv).
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
    (LENGTH sb.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn)
    (t with vs_inst_idx := LENGTH sb.cs_current_insts,G',tn')``;

val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\ ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val input_origin = ``\s.
  ((?aid ib isz. aid < output_id /\
     FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= w2n (input_word:256 word) /\
     w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``;

local
  val tm = ``
    emit_void MSTORE [Var dst;Lit 0w] sa = ((),sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
    local_ptrs_reserved ce sa /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    lookup_var dst s = SOME dw /\ ptr_covers G tn dst s 32 /\
    output_base <= w2n dw /\ w2n dw+32 <= output_base+output_cap /\
    w2n dw+32 <= s.vs_alloca_next /\
    (w2n input_word + LENGTH input_bytes <= w2n dw \/ w2n dw+32 <= w2n input_word) /\
    EVERY (\(aid,p,b,k,bytes). b+k <= w2n dw \/ w2n dw+32 <= b) live /\
    EVERY (\(b,bytes). b+LENGTH bytes <= w2n dw \/ w2n dw+32 <= b) protected /\
    (^input_origin) s ==>
    ?t Gf tnf.
      t = ((mstore (w2n dw) 0w s) with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      Gf = G /\
      tnf.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,Gf,tnf)) /\
      (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (^owned_decoder_state) sb t Gf tnf /\ (^input_origin) t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
      tnf.t_mem SUBSET tn.t_mem /\
      (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tnf.t_mem) /\
      (!tv v. type_memory_size tv = 32 /\ val_wf tv v /\
         val_in_memory tv v (w2n dw) t.vs_memory ==>
         !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory tv v (w2n dw) mem) /\
      (!D. RELPOW (\(u,Gu,tu) (v,Gv,tv).
        gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
        (LENGTH sb.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn) (t,Gf,tnf))``
in
  val zero_store_packet =
    let val body = rhs (concl (DEPTH_CONV BETA_CONV tm))
    in list_mk_forall (free_vars_lr body,body) end
end;

Theorem bytes_zero_store_finite:
  ^(list_mk_forall (free_vars_lr emitted_finite,emitted_finite)) ==>
  ^zero_store_packet
Proof
  disch_then (mk_asm "lift") >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var dst) s = SOME dw /\
   eval_operand (Lit 0w) s = SOME 0w /\ op_taint tn (Lit 0w) = {} /\ allocas_from lo s` by
    (simp[eval_operand_def,op_taint_def] >> metis_tac[ghost_inv_at_def]) >>
  drule_all clean_mstore_overwrite_prefix_uniform_origin_joint >>
  disch_then (qspec_then `PG`
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf` strip_assume_tac)))) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `inst_extends sa sb` by simp[inst_extends_def,IS_PREFIX_APPEND] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MSTORE [Var dst;Lit 0w] []` >>
  qabbrev_tac `u = mstore (w2n dw) 0w s` >>
  `u = mstore (w2n dw) 0w s` by simp[Abbr `u`] >>
  `step_inst_base i s = OK u` by
    (simp[Abbr `i`,Abbr `u`] >> irule step_MSTORE >> simp[]) >>
  `emitted_insts sa sb = [i]` by simp[Abbr `i`] >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    (qpat_assum `emitted_insts sa sb = [i]` SUBST1_TAC >>
     qpat_assum `step_inst_base i s = OK u` (fn th => simp[NoAsms,run_inst_seq_def,th])) >>
  `t = (u with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_x_assum `run_inst_seq _ _ = OK (t with vs_inst_idx := _)` mp_tac >>
     qpat_assum `run_inst_seq _ _ = OK u` (fn th => rewrite_tac[th]) >>
     simp[NoAsms] >> disch_then SUBST1_TAC >>
     qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts`
       (fn th => simp[NoAsms,GSYM th])) >>
  suspend "finite"
QED

Resume bytes_zero_store_finite[finite]:
  `ctx_has_dalloca ctx ==>
    !pre j post v. emitted_insts sa sb = pre ++ j::post /\ run_inst_seq pre s = OK v ==>
      dalloca_no_wrap j v` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     `MEM j (emitted_insts sa sb)` by
       (qpat_assum `emitted_insts sa sb = pre ++ j::post`
          (fn th => simp[NoAsms,th,MEM_APPEND])) >>
     qpat_x_assum `MEM j _` mp_tac >>
     qpat_assum `emitted_insts sa sb = [i]` (fn th => simp[NoAsms,th]) >>
     disch_then SUBST1_TAC >> simp[Abbr `i`,mk_inst_def]) >>
  `EVERY (\j. j.inst_opcode <> INVOKE /\ j.inst_opcode <> GAS /\
      ~is_terminator j.inst_opcode) (emitted_insts sa sb)` by
    simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (simp[Abbr `i`,run_inst_seq_mem_ok_last,below_frontier_MSTORE] >>
     simp[mk_inst_def,inst_dload_in_section_def]) >>
  `!D. RELPOW (\(a,Ga,ta) (b,Gb,tb).
     gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (a,Ga,ta) [] (OK b,Gb,tb))
     (LENGTH sb.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn) (t,Gf,tnf)` by
    (gen_tac >> qpat_assum `t = _` SUBST1_TAC >> asm "lift" irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` irule) >>
  asm_x "lift" kall_tac >>
  `(!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,Gf,tnf))` by
    (qpat_assum `_ ==> !D explicit. _` drule >> simp[]) >>
  `!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)` by
    (qpat_assum `t = _` SUBST1_TAC >> rpt strip_tac >>
     irule abi_decode_finite_success_observed >>
     conj_tac >- simp[] >>
     qexistsl_tac [`[i]`,`sa`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `step_inst_base i s = OK u`
           (fn th => simp[NoAsms,run_inst_seq_def,th])) >>
     simp[Abbr `i`,mk_inst_def,is_terminator_def]) >>
  `Gf = step_prov PG G i u /\ tnf = step_taint i s u tn` by
    (qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
      (qspec_then `ARB` mp_tac) >>
     qpat_assum `emitted_insts sa sb = [i]` (fn th => rewrite_tac[th]) >>
     qpat_assum `step_inst_base i s = OK u`
       (fn th => simp[NoAsms,inst_seq_ptr_def,th])) >>
  suspend "transport"
QED

Resume bytes_zero_store_finite[transport]:
  qpat_assum `?inst. MEM inst (fn_insts fn) /\ _`
    (qx_choose_then `inst` strip_assume_tac) >>
  `local_ptrs_rel fn ce es.scopes s /\
   FLOOKUP s.vs_allocas inst.inst_id = SOME (output_base,output_cap)` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `lo <= w2n dw /\ (!name b k. local_region ce es.scopes s name b k ==>
     w2n dw+32 <= b \/ b+k <= w2n dw)` by
    (conj_tac >- decide_tac >> rpt strip_tac >>
     qpat_assum `!name b k. local_region _ _ _ _ _ _ ==> _` drule >> decide_tac) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es s` by metis_tac[] >>
  `!H. V H ==> abi_decode_ptr_window Gf tnf u input input_word (LENGTH input_bytes) /\
    stmt_state_rel H ctx fn ce cx es u /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf u /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (qx_gen_tac `h` >> disch_tac >>
     `ghost_inv_at (DF h) lo delta ce cx es G tn s /\
      ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn` by metis_tac[] >>
     drule_all abi_decode_output_write_frame_joint >>
     disch_then (qspecl_then [`sa.cs_next_id`,`PG`] mp_tac) >>
     qpat_assum `Gf = step_prov _ _ _ _` SUBST1_TAC >>
     qpat_assum `tnf = step_taint _ _ _ _` SUBST1_TAC >>
     qpat_assum `u = mstore _ _ _` SUBST1_TAC >>
     simp[NoAsms,Abbr `i`] >> strip_tac >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window Gf tnf t input input_word (LENGTH input_bytes)` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`Gf`,`u`,`tnf`] >>
     conj_tac >- metis_tac[] >>
     simp[NoAsms] >> conj_tac
     >- (qpat_assum `t = _` SUBST1_TAC >> simp[NoAsms,lookup_var_def]) >>
     metis_tac[]) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es t /\
    ghost_inv_at (DF H) lo delta ce cx es Gf tnf t /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 Gf tnf` by
    (ho_match_mp_tac (bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_scalar_joint_frame_lower |>
       Q.INST [`s` |-> `u`, `G` |-> `Gf`, `tn` |-> `tnf`]) >>
     qpat_assum `t = _` SUBST1_TAC >>
     simp[NoAsms,lookup_var_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!H. V H ==> abi_decode_ptr_window _ _ u _ _ _ /\ _` drule >>
     simp[NoAsms]) >>
  suspend "assemble"
QED

Resume bytes_zero_store_finite[assemble]:
  `!p. lookup_var p t = lookup_var p s` by
    (qpat_assum `t = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[mstore_def,lookup_var_def]) >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`s`,`sa`,`sb`] >> simp[Abbr `i`,mk_inst_def,IS_PREFIX_APPEND]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`,`G`,`sa.cs_next_id`] strip_assume_tac) >>
  `Gf = G /\ tnf.t_var = tn.t_var /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` by
    (qpat_assum `Gf = step_prov _ _ _ _` SUBST1_TAC >>
     qpat_assum `tnf = step_taint _ _ _ _` SUBST1_TAC >>
     simp[Abbr `i`,Abbr `u`]) >>
  `!p k. ptr_covers Gf tnf p t k = ptr_covers G tn p s k` by
    simp[ptr_covers_def,op_taint_def,lookup_var_def] >>
  `!b k. b+k <= w2n dw \/ w2n dw+32 <= b ==>
    mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    (qpat_assum `t = _` SUBST1_TAC >> qpat_assum `u = _` SUBST1_TAC >>
     simp[NoAsms] >> rpt gen_tac >> disch_tac >>
     irule mstore_mem_bytes_at_disjoint >> first_assum ACCEPT_TAC) >>
  `!name b k. local_region ce es.scopes t name b k =
     local_region ce es.scopes s name b k` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `(^input_origin) t` by
    (BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`sa`] >> asm_rewrite_tac[] >> rpt strip_tac >>
     first_assum ACCEPT_TAC) >>
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
  qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac >- asm_rewrite_tac[] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`t = _`, `u = _`, `tnf = _`, `Gf = step_prov _ _ _ _`, `Gf = G`, `tnf.t_mem = _`] >>
  `not_fresh_at sb = not_fresh_at sa` by simp[FUN_EQ_THM,not_fresh_at_def] >>
  suspend "finish"
QED

Resume bytes_zero_store_finite[finish]:
  simp[] >> asm_rewrite_tac[] >> rpt conj_tac
  >~ [`mem_bytes_at (w2n input_word) _ t.vs_memory = _`]
  >- (qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
         (qspecl_then [`w2n input_word`,`LENGTH input_bytes`] drule) >> simp[])
  >~ [`EVERY _ live`]
  >- (simp[EVERY_MEM] >> qx_gen_tac `entry` >> PairCases_on `entry` >>
      disch_tac >>
      qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < sa.cs_next_id /\ _) live`
        (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
      disch_then (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
      qpat_assum `EVERY (\(aid,p,b,k,bytes). b+k <= _ \/ _) live`
        (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
      disch_then (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) >>
      qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
        (qspecl_then [`entry2`,`entry3`] (drule_then assume_tac)) >>
      simp[] >> decide_tac)
  >~ [`EVERY _ protected`]
  >- (simp[EVERY_MEM] >> qx_gen_tac `entry` >> PairCases_on `entry` >> disch_tac >>
      qpat_assum `EVERY (\(a,bytes). a + LENGTH bytes <= _ \/ _) protected`
        (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
      disch_then (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) >>
      qpat_assum `EVERY (\(a,bytes). mem_bytes_at a _ s.vs_memory = _) protected`
        (mp_tac o SIMP_RULE (srw_ss()) [EVERY_MEM]) >>
      disch_then (drule_then (assume_tac o SIMP_RULE (srw_ss()) [])) >>
      qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _`
        (qspecl_then [`entry0`,`LENGTH entry1`] (drule_then assume_tac)) >> simp[]) >>
  qpat_assum `(?aid ib isz. aid < output_id /\ FLOOKUP s.vs_allocas aid = _ /\ _) \/ _`
    mp_tac >> simp[NoAsms,ADD_COMM]
QED

Finalise bytes_zero_store_finite
