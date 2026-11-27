(* Join the covered load, length guard, and output registration before
   entering the decoder. The observer replays this same selected result. *)
Theory bodyAbiDecodeLinkedSetupMods
Ancestors
  bodyAbiDecodeLinkedSetupPrefixMods bodyAbiDecodeLinkedSetupGuardMods
  bodyAbiDecodeLinkedSetupAllocationMods bodyAbiDecodeLinkedSetupObserverMods
  abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinLengthGuard
  exprSimAbiDecodeBuiltin abiDecoderFrame bodyFullAbiDecodeInputOrigin
  abiEncoderObserver exprSimAbiGasBridge fragGasOriginPtrLoop fragGasPath
  bodyFullShadowBodyInv bodyFullHashKeccakFixed assignTuplePtrLoadStep
  allocasBelowFmpUpdatesProps stateFrame loweringStateRelDefs
  fragExec exprLoweringProps emitHelperProps abiBuiltinAllocation
  compileEnv exprSimAccounts loweringHalt ptrDiscipline
  abiDecoderReentry abiDecodePtrMemberFrame venomState venomExecSemantics
  finite_map words arithmetic exprSimCopy freshWrites

Theorem decode_setup_parts[local]:
  abi_builtin_decode_setup data mn mx outsz st = (ops,ready) ==>
  ?len sa src sb header_st buf.
    emit_op MLOAD [data] st = (len,sa) /\
    emit_op ADD [data; Lit 32w] sa = (src,sb) /\
    abi_builtin_length_guard len mn mx sb = ((),header_st) /\
    compile_alloc_buffer outsz header_st = (buf,ready) /\
    ops = (buf.buf_operand,src,len) /\
    cs_extends st sb /\ cs_extends sb header_st /\ cs_extends header_st ready /\
    st.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= header_st.cs_next_var /\
    header_st.cs_next_var <= ready.cs_next_var /\
    header_st.cs_next_id = abi_builtin_decode_output_site st mn mx
Proof
  strip_tac >> drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  `?len sa src sb. emit_op MLOAD [data] st = (len,sa) /\
    emit_op ADD [data; Lit 32w] sa = (src,sb) /\
    abi_builtin_length_guard len mn mx sb = ((),header_st) /\ inputs = (len,src)` by
    (qpat_assum `abi_builtin_decode_header _ _ _ _ = _` mp_tac >>
     simp[NoAsms, abi_builtin_decode_header_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
     ntac 3 (pairarg_tac >> simp[]) >> strip_tac >>
     rename1 `emit_op MLOAD [data] st = (len,sa)` >>
     rename1 `emit_op ADD [data; Lit 32w] sa = (src,sb)` >>
     qexistsl_tac [`len`,`sa`,`src`,`sb`] >> simp[]) >>

  drule abi_builtin_length_guard_shape >> strip_tac >>
  `cs_extends st sb /\ st.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var, cs_extends_trans, LESS_EQ_TRANS] >>
  `cs_extends sb header_st` by (irule cs_extends_same_block >> simp[]) >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `header_st.cs_next_var <= ready.cs_next_var` by metis_tac[emit_op_extends_next_var] >>
  qexistsl_tac [`len`,`sa`,`src`,`sb`,`header_st`,`buf`] >>
  asm_rewrite_tac[] >> simp[abi_builtin_decode_output_site_def]
QED

Theorem decode_setup_scalar_fmp[local]:
  state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  (ctx_has_dalloca ctx ==> allocas_below_fmp u)
Proof
  strip_tac >>
  `u = (s with vs_inst_idx := u.vs_inst_idx) with vs_vars := u.vs_vars` by
    metis_tac[state_frame_eq_reconstruct] >>
  pop_assum (fn th => simp[Once th, allocas_below_fmp_updates])
QED

Theorem decode_setup_path_join[local]:
  cs_extends st mid /\ cs_extends mid last /\
  (!H:(bool # bytes32 # type_value) list # num list.
    V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gp,tp)) /\
  (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (u,Gp,tp) [] (r,Gf,tf)) /\
  (!f. fn_has_code st mid f ==> gas_path ctx f s 0 (OK u)) /\
  (!f. fn_has_code mid last f ==> gas_path ctx f u 0 r) ==>
  (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (r,Gf,tf)) /\
  (!f. fn_has_code st last f ==> gas_path ctx f s 0 r)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gp`,`u`,`tp`] >> simp[]) >>
  rpt strip_tac >> drule_all fn_has_code_split >> strip_tac >>
  `gas_path ctx f s 0 (OK u) /\ gas_path ctx f u 0 r` by simp[] >>
  drule_all gas_path_then >> simp[]
QED

Theorem abi_decode_linked_setup_mods:
  abi_builtin_decode_setup data mn mx outsz st = (ops,ready) /\
  fn_has_code st ready fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history fn s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < origin.cs_next_id ==> off + sz <= s.vs_alloca_next) /\
  (!name a sz. local_region ce es0.scopes s0 name a sz ==> a + sz <= s.vs_alloca_next) /\
  (?H:(bool # bytes32 # type_value) list # num list. V H) /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at_mods (DF H) lo delta ce cx es G tn s) /\
  data = Var p /\ eval_operand data s = SOME (n2w b) /\ op_taint tn data = {} /\
  abi_decoder_operand_live st.cs_next_var data /\
  abi_decode_ptr_window G tn s p (n2w b) (32 + LENGTH bs) /\
  mload b s = n2w (LENGTH bs) /\ mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  b + 32 + LENGTH bs < dimword (:256) /\ mn <= mx /\ outsz < dimword (:256) /\
  abi_builtin_decode_site_resources ctx fn st final.cs_next_id mn mx outsz (LENGTH bs) b dst s /\
  ((?aid ib isz. aid < abi_builtin_decode_output_site st mn mx /\
      FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= b + 32 /\
      b + 32 + LENGTH bs <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
      ib <= b + 32 /\ b + 32 + LENGTH bs <= ib + isz)) ==>
  ?r0 Gs ts.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (r0,Gs,ts)) /\
    (!obs. fn_has_code st ready obs ==> gas_path ctx obs s 0 r0) /\
    ((?z. r0 = Abort Revert_abort z /\ ~(mn <= LENGTH bs /\ LENGTH bs <= mx)) \/
     (?t output input. r0 = OK t /\
       ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
       t.vs_inst_idx = LENGTH ready.cs_current_insts /\ alloca_history fn t /\
       FST ops = Var output /\ FST (SND ops) = Var input /\
       lookup_var output t = SOME (n2w dst) /\ ptr_covers Gs ts output t outsz /\
       FLOOKUP t.vs_allocas (abi_builtin_decode_output_site st mn mx) = SOME (dst,outsz) /\
       FLOOKUP Gs output = SOME (dst,outsz) /\ dst + outsz < dimword (:256) /\
       (?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\ i.inst_outputs = [output] /\
           i.inst_id = abi_builtin_decode_output_site st mn mx) /\
       abi_builtin_decode_output_site st mn mx < ready.cs_next_id /\
       not_local_ptr ce es.scopes output /\ not_fresh_at ready output /\
       (!name a n. local_region ce es.scopes t name a n ==> regions_disjoint dst outsz a n) /\
       abi_decode_ptr_window Gs ts t input (n2w (b+32)) (LENGTH bs) /\
       mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
       b + 32 + LENGTH bs <= t.vs_alloca_next /\
       eval_operand (SND (SND ops)) t = SOME (n2w (LENGTH bs)) /\
       op_prov Gs (SND (SND ops)) = NONE /\
       op_taint ts (FST ops) = {} /\ op_taint ts (FST (SND ops)) = {} /\
       op_taint ts (SND (SND ops)) = {} /\
       abi_decoder_operand_live ready.cs_next_var (FST ops) /\
       abi_decoder_operand_live ready.cs_next_var (FST (SND ops)) /\
       abi_decoder_operand_live ready.cs_next_var (SND (SND ops)) /\
       mn <= LENGTH bs /\ LENGTH bs <= mx /\
       (b + 32 + LENGTH bs <= dst \/ dst + outsz <= b + 32) /\
       ((?aid ib isz. aid < abi_builtin_decode_output_site st mn mx /\
           FLOOKUP t.vs_allocas aid = SOME (ib,isz) /\ ib <= b + 32 /\
           b + 32 + LENGTH bs <= ib + isz) \/
        (?name ib isz. local_region ce es.scopes t name ib isz /\
           ib <= b + 32 /\ b + 32 + LENGTH bs <= ib + isz)) /\
       (!H. V H ==> stmt_state_rel H ctx fn ce cx es t) /\
       local_ptrs_reserved ce ready /\ origin.cs_next_var <= ready.cs_next_var /\
       allocas_from lo t /\ lo <= dst /\ lo <= t.vs_alloca_next /\
       s.vs_alloca_next <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
         aid < origin.cs_next_id ==> off + sz <= t.vs_alloca_next) /\
       (!name a sz. local_region ce es0.scopes s0 name a sz ==> a + sz <= t.vs_alloca_next) /\
       t.vs_memory = s.vs_memory /\
       (!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent) /\
       (!name a n. local_region ce es.scopes t name a n <=> local_region ce es.scopes s name a n) /\
       (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP Gs x = FLOOKUP G x /\ op_taint ts (Var x) = op_taint tn (Var x)) /\
       ts.t_stor = tn.t_stor /\ ts.t_trans = tn.t_trans /\ ts.t_imm = tn.t_imm /\
       (!i. i < s.vs_alloca_next /\ i IN ts.t_mem ==> i IN tn.t_mem))) /\
    (!L ids obs.
      cs_extends st final /\ cs_extends ready final /\
      st.cs_blocks <> final.cs_blocks /\ LENGTH ids = LENGTH st.cs_current_insts /\
      fn_has_code (start_relabel L ids st) (start_swap st L ids final) obs /\
      L <> final.cs_current_bb ==>
      (?t w. r0 = OK t /\ ~w.vs_halted /\ w.vs_current_bb = L /\
        w.vs_inst_idx = LENGTH ready.cs_current_insts /\
        frag_relabel_state L st.cs_current_bb w t /\
        local_prefix ctx obs (L,LENGTH ready.cs_current_insts) (s with vs_current_bb := L) w) \/
      (?z w k. r0 = Abort Revert_abort z /\ frag_relabel_state L st.cs_current_bb w z /\
        run_from k ctx obs (s with vs_current_bb := L) = Abort Revert_abort w))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule decode_setup_parts >>
  disch_then (qx_choosel_then [`len`,`sa`,`src`,`sb`,`header_st`,`buf`]
    (map_every assume_tac o CONJUNCTS)) >>
  `fn_has_code st sb fn /\ fn_has_code sb header_st fn /\ fn_has_code header_st ready fn` by
    (drule_all cs_extends_trans >> strip_tac >>
     drule_all fn_has_code_split >> strip_tac >> drule_all fn_has_code_split >> simp[]) >>
  qpat_assum `?H. V H` (qx_choose_then `h` assume_tac) >>
  qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    drule_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp >>
  qpat_assum `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_builtin_decode_site_resources_def]) >>
  `LENGTH bs < dimword (:256)` by decide_tac >>
  `w2n (n2w (b+32):bytes32) = b+32` by (simp[LESS_MOD] >> decide_tac) >>
  Q.SUBGOAL_THEN `b+32+LENGTH bs <= dst \/ dst+outsz <= b+32` assume_tac
  >- (qpat_assum `abi_footprint_disjoint _ _ _` mp_tac >>
      simp[NoAsms, abi_footprint_disjoint_def]) >>
  mp_tac (Q.INST [`start` |-> `st`, `bs` |-> `bs:word8 list`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:word8``,
      beta |-> ``:(bool # bytes32 # type_value) list # num list``]
      abi_decode_linked_setup_prefix_mods))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`Gp`,`tnp`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?input. src = Var input /\ _`
    (qx_choose_then `input` (map_every assume_tac o CONJUNCTS)) >>
  `allocas_from lo u` by
    (qpat_assum `u.vs_allocas = s.vs_allocas` (fn th =>
       pure_rewrite_tac[allocas_from_def, th]) >>
     qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `lo <= u.vs_alloca_next` by asm_rewrite_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (mp_tac (SPEC_ALL decode_setup_scalar_fmp) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (SPEC_ALL abi_decode_linked_setup_guard_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`rg`,`Gh`,`tnh`] (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`mid` |-> `sb`, `last` |-> `header_st`, `tp` |-> `tnp`,
    `r` |-> `rg`, `Gf` |-> `Gh`, `tf` |-> `tnh`] (SPEC_ALL decode_setup_path_join)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(?z. rg = Abort Revert_abort z /\ _) \/ _`
    (DISJ_CASES_THEN2 (qx_choose_then `z` strip_assume_tac)
      (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)))
  >- suspend "reject" >> suspend "allocate"
QED
Resume abi_decode_linked_setup_mods[reject]:
  qexistsl_tac [`rg`,`Gh`,`tnh`] >> conj_tac >- first_assum ACCEPT_TAC >>
  `!obs. fn_has_code st ready obs ==> gas_path ctx obs s 0 rg` by
    (rpt strip_tac >>
     `cs_extends st header_st` by
    (irule cs_extends_trans >> qexists_tac `sb` >> conj_tac >> first_assum ACCEPT_TAC) >>
     `fn_has_code st header_st obs` by (drule_all fn_has_code_split >> simp[]) >>
     qpat_assum `!f. fn_has_code st header_st f ==> _` (drule_then ACCEPT_TAC)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (disj1_tac >> qexists_tac `z` >> simp[]) >>
  rpt strip_tac >>
  `final.cs_current_bb <> L` by
    (strip_tac >> qpat_assum `L <> final.cs_current_bb` (irule o NOT_ELIM) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`r` |-> `rg`, `cut` |-> `(final.cs_current_bb, 0:num)`]
    (SPEC_ALL abi_decode_linked_setup_observer_mods)) >>
  simp_tac pure_ss [pairTheory.FST] >>
  (impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    disj2_tac >> qexists_tac `z` >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
Resume abi_decode_linked_setup_mods[allocate]:
  `local_ptrs_reserved ce sb /\ local_ptrs_reserved ce header_st /\ local_ptrs_reserved ce ready` by
    (rpt conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `st` >>
     asm_rewrite_tac[] >> decide_tac) >>
  `!H. V H ==> stmt_state_rel H ctx fn ce cx es v` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx fn ce cx es s` by
       (qpat_assum `!H. V H ==> stmt_state_rel H _ _ _ _ _ s /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     `stmt_state_rel H ctx fn ce cx es u` by
       (irule stmt_state_rel_old_vars_frame_ptr >> qexistsl_tac [`s`,`st`] >>
        conj_tac >- (rpt strip_tac >>
          qpat_assum `!x. not_fresh_at st x ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule stmt_state_rel_old_vars_frame_ptr >> qexistsl_tac [`u`,`sb`] >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `!x. not_fresh_at sb x ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo v` by
    (qpat_assum `v.vs_allocas = u.vs_allocas` (fn th =>
       pure_rewrite_tac[allocas_from_def, th]) >>
     qpat_assum `allocas_from lo u` (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `lo <= v.vs_alloca_next /\ w2n (n2w (b+32):bytes32) + LENGTH bs <= v.vs_alloca_next /\
   mem_bytes_at (w2n (n2w (b+32):bytes32)) (LENGTH bs) v.vs_memory = bs /\
   abi_decoder_operand_live header_st.cs_next_var (Var input)` by
    (asm_rewrite_tac[] >> qpat_assum `src = Var input` (fn th =>
       qpat_assum `abi_decoder_operand_live header_st.cs_next_var src`
         (ACCEPT_TAC o PURE_REWRITE_RULE[th]))) >>
  Q.SUBGOAL_THEN
    `(FLOOKUP v.vs_allocas header_st.cs_next_id = NONE /\ dst = v.vs_alloca_next) \/
     FLOOKUP v.vs_allocas header_st.cs_next_id = SOME (dst,outsz)` assume_tac
  >- asm_rewrite_tac[] >>
  mp_tac (Q.INST [`s` |-> `v`, `G` |-> `Gh`, `tn` |-> `tnh`, `w` |-> `n2w (b+32):bytes32`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] abi_decode_linked_setup_allocation_mods))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`,`Gs`,`ts`,`output`] (map_every assume_tac o CONJUNCTS)) >>
  `cs_extends st header_st` by
    (irule cs_extends_trans >> qexists_tac `sb` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
    (v,Gh,tnh) [] (OK t,Gs,ts)` by simp[] >>
  qpat_assum `rg = OK v` (fn th => rule_assum_tac (PURE_REWRITE_RULE[th])) >>
  mp_tac (Q.INST [`mid` |-> `header_st`, `last` |-> `ready`, `u` |-> `v`,
    `Gp` |-> `Gh`, `tp` |-> `tnh`, `r` |-> `OK t`, `Gf` |-> `Gs`, `tf` |-> `ts`]
    (SPEC_ALL decode_setup_path_join)) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`OK t`,`Gs`,`ts`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "ready_packet" >>
  rpt strip_tac >>
  `final.cs_current_bb <> L` by
    (strip_tac >> qpat_assum `L <> final.cs_current_bb` (irule o NOT_ELIM) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`r` |-> `OK t`, `cut` |-> `(final.cs_current_bb, 0:num)`]
    (SPEC_ALL abi_decode_linked_setup_observer_mods)) >>
  simp_tac pure_ss [pairTheory.FST] >>
  (impl_tac >- (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    disj1_tac >> qexists_tac `t` >> simp[])) >>
  disch_then ACCEPT_TAC
QED
Resume abi_decode_linked_setup_mods[ready_packet]:
  `!name a n. local_region ce es.scopes t name a n <=> local_region ce es.scopes s name a n` by
    (map_every qx_gen_tac [`name`,`a`,`n`] >>
     `local_region ce es.scopes v name a n <=> local_region ce es.scopes u name a n` by
       (irule copy_buffer_local_region_frame >> qexists_tac `sb` >> simp[]) >>
     `local_region ce es.scopes u name a n <=> local_region ce es.scopes s name a n` by
       (irule copy_buffer_local_region_frame >> qexists_tac `st` >> simp[]) >>
     asm_rewrite_tac[]) >>
  `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> FLOOKUP t.vs_allocas aid = SOME ent` by
    (rpt strip_tac >> qpat_assum `!aid entry. FLOOKUP v.vs_allocas aid = SOME entry ==> _` irule >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gs x = FLOOKUP G x /\ op_taint ts (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at sb x` by (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
     `not_fresh_at header_st x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sb` >> simp[]) >>
     map_every (fn cut => qpat_assum `!x. not_fresh_at ^cut x ==> _` (drule_then strip_assume_tac))
       [``header_st:compile_state``, ``sb:compile_state``, ``st:compile_state``] >>
     asm_rewrite_tac[]) >>
  Q.SUBGOAL_THEN
    `(?aid ib isz. aid < abi_builtin_decode_output_site st mn mx /\
        FLOOKUP t.vs_allocas aid = SOME (ib,isz) /\ ib <= b+32 /\ b+32+LENGTH bs <= ib+isz) \/
     (?name ib isz. local_region ce es.scopes t name ib isz /\
        ib <= b+32 /\ b+32+LENGTH bs <= ib+isz)` assume_tac
  >- (qpat_assum `(?aid ib isz. _ /\ FLOOKUP s.vs_allocas aid = _ /\ _) \/ _` mp_tac >>
      disch_then (DISJ_CASES_THEN (qx_choosel_then [`key`,`ib`,`isz`] strip_assume_tac))
      >- (disj1_tac >> qexistsl_tac [`key`,`ib`,`isz`] >> asm_rewrite_tac[] >>
          qpat_assum `!aid ent. FLOOKUP s.vs_allocas aid = SOME ent ==> _` (drule_then ACCEPT_TAC)) >>
      disj2_tac >> qexistsl_tac [`key`,`ib`,`isz`] >> asm_rewrite_tac[]) >>
  map_every (fn pat => qpat_assum pat (fn th => rule_assum_tac (PURE_REWRITE_RULE[th])))
    [`v.vs_alloca_next = u.vs_alloca_next`, `u.vs_alloca_next = s.vs_alloca_next`,
     `v.vs_memory = u.vs_memory`, `u.vs_memory = s.vs_memory`,
     `tnh.t_stor = tnp.t_stor`, `tnp.t_stor = tn.t_stor`,
     `tnh.t_trans = tnp.t_trans`, `tnp.t_trans = tn.t_trans`,
     `tnh.t_imm = tnp.t_imm`, `tnp.t_imm = tn.t_imm`,
     `tnh.t_mem = tnp.t_mem`, `tnp.t_mem = tn.t_mem`, `w2n (n2w (b+32):bytes32) = b+32`,
     `header_st.cs_next_id = abi_builtin_decode_output_site st mn mx`] >>
  disj2_tac >> qexistsl_tac [`t`,`output`,`input`] >>
  qpat_assum `ops = _` (fn th => pure_rewrite_tac[th,pairTheory.FST,pairTheory.SND]) >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[th]))
    [`buf.buf_operand = Var output`, `src = Var input`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC
  >- (irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >> asm_rewrite_tac[])
  >- (irule LESS_EQ_TRANS >> qexists_tac `st.cs_next_var` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule LESS_EQ_TRANS >> qexists_tac `sb.cs_next_var` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule LESS_EQ_TRANS >> qexists_tac `header_st.cs_next_var` >> asm_rewrite_tac[])
  >- (irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >> asm_rewrite_tac[])
  >- (irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >> asm_rewrite_tac[])
  >- (rpt strip_tac >> irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!aid off sz. _ ==> off + sz <= s.vs_alloca_next` (drule_all_then ACCEPT_TAC))
  >- (rpt strip_tac >> irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!name a sz. _ ==> a + sz <= s.vs_alloca_next` (drule_then ACCEPT_TAC)) >>
  rpt strip_tac >> qpat_assum `!i. i < s.vs_alloca_next ==> _` (drule_then (fn th =>
    pure_once_rewrite_tac[GSYM th])) >> first_assum ACCEPT_TAC
QED
Finalise abi_decode_linked_setup_mods
