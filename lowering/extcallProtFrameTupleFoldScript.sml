(* A singleton endpoint is the operational boundary for list composition. *)
Theory extcallProtFrameTupleFold
Ancestors
  exprExtRequestTupleFold extcallProtFramePath exprExtRequestHistory
  exprExtRequestHistoryCompose exprLoweringProps exprLowering compileEnv
  vyperInterpreter vyperState valueEncodingProps valueTypingMemoryProps
  gasSummary fragGasMode fragExec loweringStateRelDefs valueEncodingDefs

Theorem extcall_tuple_store_fold_protected:
  (!e r vv ty tv v off sm sb s.
    extrequest_tuple_cell ctx func cenv cx eb cb tb ee (e,r,vv,ty,tv,v) /\
    compile_extcall_store_values cenv [(vv,ty)] buf off sm = ((),sb) /\
    stmt_state_rel ctx func cenv cx eb tb /\
    stmt_state_rel ctx func cenv cx ee s /\
    extrequest_history_frame cenv cx eb cb tb ee sm s /\
    cb.cs_next_id <= live /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ee.gas_obs = [] /\ safe_operand sm buf /\ eval_operand buf s = SOME w /\
    FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\ live < sm.cs_next_id /\
    tuple_base <= w2n w + off /\
    w2n w + off + type_memory_size tv <= tuple_base + sz /\
    tuple_base + sz < dimword (:256) /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint tuple_base sz b len) /\
    (cenv.ce_is_ctor ==> !name itv iv io.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint io (type_memory_size itv) tuple_base sz) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
      mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n) ==>
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel ctx func cenv cx ee q /\
      val_in_memory tv v (w2n w + off) q.vs_memory /\
      extrequest_history_frame cenv cx eb cb tb ee sb q /\
      FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
      (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
        regions_disjoint a k (w2n w + off) (type_memory_size tv) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
        lookup_var x q = SOME z) /\
      (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
        FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
        mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
      (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
        mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk original /\
        !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
          loweringStateRelDefs$regions_disjoint pa pk b n)) ==>
  !cells off sm sb s.
    EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells /\
    compile_extcall_store_values cenv
      (MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells) buf off sm = ((),sb) /\
    stmt_state_rel ctx func cenv cx eb tb /\
    stmt_state_rel ctx func cenv cx ee s /\
    extrequest_history_frame cenv cx eb cb tb ee sm s /\
    cb.cs_next_id <= live /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    ee.gas_obs = [] /\ safe_operand sm buf /\ eval_operand buf s = SOME w /\
    FLOOKUP s.vs_allocas live = SOME (tuple_base,sz) /\ live < sm.cs_next_id /\
    tuple_base <= w2n w + off /\
    w2n w + off + SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells) <=
      tuple_base + sz /\
    tuple_base + sz < dimword (:256) /\
    (!name b len. local_region cenv ee.scopes s name b len ==>
      regions_disjoint tuple_base sz b len) /\
    (cenv.ce_is_ctor ==> !name itv iv io.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (itv,iv) ==>
      regions_disjoint io (type_memory_size itv) tuple_base sz) /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!pa pk. prot pa pk ==> pa + pk <= s.vs_alloca_next /\
      mem_bytes_at pa pk s.vs_memory = mem_bytes_at pa pk original /\
      !i b n. FLOOKUP s.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n) ==>
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel ctx func cenv cx ee q /\
      tuple_in_memory (MAP (\(e,r,vv,ty,tv,v). v) cells)
        (MAP (\(e,r,vv,ty,tv,v). tv) cells) (w2n w + off) q.vs_memory /\
      extrequest_history_frame cenv cx eb cb tb ee sb q /\
      FLOOKUP q.vs_allocas live = SOME (tuple_base,sz) /\
      (!a k. tuple_base <= a /\ a + k <= tuple_base + sz /\
        regions_disjoint a k (w2n w + off)
          (SUM (MAP (\(e,r,vv,ty,tv,v). type_memory_size tv) cells)) ==>
        mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
        lookup_var x q = SOME z) /\
      (!aid p k. aid < sm.cs_next_id /\ aid <> live /\
        FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
        mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory) /\
      (!pa pk. prot pa pk ==> pa + pk <= q.vs_alloca_next /\
        mem_bytes_at pa pk q.vs_memory = mem_bytes_at pa pk original /\
        !i b n. FLOOKUP q.vs_allocas i = SOME (b,n) ==>
          loweringStateRelDefs$regions_disjoint pa pk b n)
Proof
  disch_then (mk_asm "single") >> Induct
  >- (simp[compile_extcall_store_values_def, comp_return_def] >>
      rpt strip_tac >> qexists_tac `s` >>
      simp[valueEncodingDefsTheory.val_in_memory_def, gas_marked_path_def] >>
      metis_tac[cj 1 fragGasPathTheory.gas_path_rules]) >>
  qx_gen_tac `cell` >> PairCases_on `cell` >> rpt gen_tac >>
  simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  rename1 `extrequest_tuple_cell _ _ _ _ _ _ _ _ (e,r,vv,ty,tv,v)` >>
  qpat_x_assum `(\(dst,st). _) _ = _` mp_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  strip_tac >>
  rename1 `emit_op ADD _ sm = (dst,sn)` >>
  rename1 `unwrap_value cenv vv sn = (op,su)` >>
  rename1 `(if is_word_type ty then _ else _) su = ((),sh)` >>
  `compile_extcall_store_values cenv [(vv,ty)] buf off sm = ((),sh)` by
    simp[compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  `ci_mono sm sh /\ ci_mono sh sb` by
    metis_tac[extrequest_store_values_mono, pairTheory.SND] >>
  `fn_has_code sm sh func /\ fn_has_code sh sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `w2n w + off + type_memory_size tv <= tuple_base + sz` by decide_tac >>
  asm "single" drule >> disch_then drule >>
  disch_then (qspec_then `s` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  asm_x "single" kall_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK h)` >>
  `type_memory_bytes cenv ty = type_memory_size tv /\ val_wf tv v` by
    (qpat_x_assum `extrequest_tuple_cell _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[extrequest_tuple_cell_def]) >>
  suspend "tail"
QED

Resume extcall_tuple_store_fold_protected[tail]:
  `eval_operand buf h = SOME w` by
    (Cases_on `buf` >>
     gvs[venomStateTheory.eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
     metis_tac[]) >>
  `safe_operand sh buf` by
    (fs[exprSafeOperandTheory.safe_operand_def, ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `!name b len. local_region cenv ee.scopes h name b len ==>
       regions_disjoint tuple_base sz b len` by
    (rpt strip_tac >>
     `local_region cenv eb.scopes tb name b len` by
       metis_tac[extrequest_history_local_regions] >>
     metis_tac[extrequest_history_local_regions]) >>
  `live < sh.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  qpat_x_assum `!off' sm' sb' s'. _`
    (qspecl_then [`off + type_memory_bytes cenv ty`, `sh`, `sb`, `h`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "finish"
QED

Resume extcall_tuple_store_fold_protected[finish]:
  `mem_bytes_at (w2n w + off) (type_memory_size tv) q.vs_memory =
   mem_bytes_at (w2n w + off) (type_memory_size tv) h.vs_memory` by
    (qpat_x_assum `!a k. tuple_base <= a /\ _ ==> mem_bytes_at a k q.vs_memory = _` irule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `val_in_memory tv v (w2n w + off) q.vs_memory` by
    (irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size tv`, `h.vs_memory`] >> simp[]) >>
  `!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
      lookup_var x q = SOME z` by
    (map_every qx_gen_tac [`reg`, `word`] >> strip_tac >>
     `not_fresh_at sh reg` by
       (fs[ci_mono_def] >>
        metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `!aid p k. aid < sm.cs_next_id /\ aid <> live /\
      FLOOKUP s.vs_allocas aid = SOME (p,k) ==>
      mem_bytes_at p k q.vs_memory = mem_bytes_at p k s.vs_memory` by
    (map_every qx_gen_tac [`aid`, `old_base`, `old_size`] >> strip_tac >>
     `FLOOKUP h.vs_allocas aid = SOME (old_base,old_size)` by
       metis_tac[gas_marked_path_allocas_preserved] >>
     `aid < sh.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
     metis_tac[]) >>
  qexists_tac `q` >>
  conj_tac
  >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[valueEncodingDefsTheory.val_in_memory_def] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM] >>
  reverse conj_tac >- metis_tac[] >>
  suspend "windows"
QED

Resume extcall_tuple_store_fold_protected[windows]:
  rpt strip_tac >>
  `mem_bytes_at a k q.vs_memory = mem_bytes_at a k h.vs_memory` by
    (qpat_assum `!a k. tuple_base <= a /\ _ ==> mem_bytes_at a k q.vs_memory = _` irule >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at a k h.vs_memory = mem_bytes_at a k s.vs_memory` by
    (qpat_assum `!a k. tuple_base <= a /\ _ ==> mem_bytes_at a k h.vs_memory = _` irule >> simp[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Finalise extcall_tuple_store_fold_protected
