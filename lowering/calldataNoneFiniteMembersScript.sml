(* A finite decoder uses a sequence of independently checked child intervals. *)
Theory calldataNoneFiniteMembers
Ancestors
  calldataMembersRawCallsite calldataSourceSize calldataDynOwned
  sourceOwnedComplexPtr abiDecoderMemberCons abiDecoderMemberSetup
  calldataEmptyArrayChild abiDecoderOffset calldataSourceCorrespondence
  fragGasOriginPtrLoop abiDecoderCoherence abiDecoderDynamic vyperCalldata
  venomState option arithmetic words

(* These are SML quotations, not additional HOL constants. *)
val member_history = ``\a b fn s.
  !id q k. a.cs_next_id <= id /\ id < b.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]``;

val member_pc = ``\a s. ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
                         s.vs_inst_idx = LENGTH a.cs_current_insts``;
val member_exit = ``\a b fn. a.cs_blocks = b.cs_blocks \/
  !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0``;
val member_live = ``\a src dst var s p d G tn sz.
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live a.cs_next_var src /\
  abi_decoder_operand_live a.cs_next_var dst /\
  ptr_covers G tn var s sz /\ op_taint tn src = {} /\ op_prov G src = NONE``;
val member_owner = ``\a b s oid base cap d sz.
  FLOOKUP s.vs_allocas oid = SOME (base,cap) /\
  (oid < a.cs_next_id \/ b.cs_next_id <= oid) /\
  base <= d /\ d+sz <= base+cap /\ d+sz < dimword (:256)``;
val member_resources = ``\a b ctx fn site limit lower s.
  (^member_pc) a s /\ (^member_history) a b fn s /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  fresh_vars_wrt limit s /\ allocas_from lower s /\ lower <= s.vs_alloca_next``;
val member_frame = ``\a b ctx fn site limit lower s (G:string |-> num # num) tn d sz t H u sc.
  (^member_resources) b b ctx fn site limit lower t /\
  (^member_history) a b fn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==>
       FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  (!id. id < a.cs_next_id \/ b.cs_next_id <= id ==>
       FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (!op. abi_decoder_operand_live a.cs_next_var op ==>
       eval_operand op t = eval_operand op s) /\
  (!name. not_fresh_at a name ==> FLOOKUP H name = FLOOKUP G name /\
       op_taint u (Var name) = op_taint tn (Var name)) /\
  abi_decode_footprint_frame ((d,sz)::sc) s t /\
  (!q k. MEM (q,k) sc ==> ?id. a.cs_next_id <= id /\ id < b.cs_next_id /\
       FLOOKUP t.vs_allocas id = SOME (q,k)) /\
  u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
  u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm``;
val member_path = ``\lo ctx fn PG s G tn r H u.
  !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
       (s,G,tn) [] (r,H,u)``;
val member_abort = ``\lo ctx fn PG s G tn.
  ?z H u. z.vs_returndata = [] /\ (^member_path) lo ctx fn PG s G tn
       (Abort Revert_abort z) H u``;

val member_child = ``\ctx fn site limit lo PG di tv.
  !mid en q src s p d oid base cap G tn.
    compile_abi_decode_to_buf (Var q) src CALLDATALOAD (Lit 0w) (Lit 0w)
      di mid = ((),en) /\ fn_has_code mid en fn /\ (^member_exit) mid en fn /\
    en.cs_next_var <= limit.cs_next_var /\
    (^member_resources) mid en ctx fn site limit lo s /\
    (^member_live) mid src (Var q) q s p d G tn (type_memory_size tv) /\
    (^member_owner) mid en s oid base cap d (type_memory_size tv) ==>
    (^member_abort) lo ctx fn PG s G tn \/
    ?t H u sc. IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p)) /\
      (^member_path) lo ctx fn PG s G tn (OK t) H u /\
      (^member_frame) mid en ctx fn site limit lo s G tn d (type_memory_size tv) t H u sc``;

Theorem finite_member_frame_join[local]:
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  a.cs_next_var <= b.cs_next_var /\
  (^member_frame) a b ctx fn site limit lo s G tn d n r H u sc /\
  (^member_frame) b c ctx fn site limit lo r H u (d+n) m t J v tc ==>
  (^member_frame) a c ctx fn site limit lo s G tn d (n+m) t J v (sc++tc)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
    (rpt conj_tac >> first_assum ACCEPT_TAC))) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `id < b.cs_next_id`
      >- (`a.cs_next_id <= id /\ id < b.cs_next_id` by decide_tac >>
          `FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id` by metis_tac[] >>
          qpat_assum `!id q k. a.cs_next_id <= id /\ _ ==> _`
            (qspecl_then [`id`,`q`,`k`] mp_tac) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC ORELSE metis_tac[]) >>
          strip_tac >> asm_rewrite_tac[] >> conj_tac
          >- decide_tac >> qexists `ins` >> asm_rewrite_tac[]) >>
      `b.cs_next_id <= id /\ id < c.cs_next_id` by decide_tac >>
      qpat_assum `!id q k. b.cs_next_id <= id /\ id < c.cs_next_id /\
                    FLOOKUP t.vs_allocas id = SOME (q,k) ==> _`
        (qspecl_then [`id`,`q`,`k`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  conj_tac >- decide_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `id < a.cs_next_id \/ b.cs_next_id <= id` by decide_tac >>
      `id < b.cs_next_id \/ c.cs_next_id <= id` by decide_tac >> metis_tac[]) >>
  conj_tac >- metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac
  >- (irule abiDecoderFrameTheory.abi_decode_footprint_frame_trans >>
      qexists `r` >> conj_tac >>
      irule abiDecoderFrameTheory.abi_decode_footprint_frame_weaken >>
      goal_assum (drule_at Any) >>
      rewrite_tac[listTheory.MEM,listTheory.MEM_APPEND] >>
      qx_genl_tac [`range_base`,`range_size`] >> strip_tac
      >- (qexistsl [`d`,`n+m`] >>
          qpat_assum `(range_base,range_size) = _` (strip_assume_tac o REWRITE_RULE[pairTheory.PAIR_EQ]) >>
          asm_rewrite_tac[] >> decide_tac)
      >- (qexistsl [`range_base`,`range_size`] >> asm_rewrite_tac[] >> decide_tac)
      >- (qexistsl [`d`,`n+m`] >>
          qpat_assum `(range_base,range_size) = _` (strip_assume_tac o REWRITE_RULE[pairTheory.PAIR_EQ]) >>
          asm_rewrite_tac[] >> decide_tac) >>
      qexistsl [`range_base`,`range_size`] >> asm_rewrite_tac[] >> decide_tac) >>
  conj_tac
  >- (rewrite_tac[listTheory.MEM_APPEND] >> rpt gen_tac >> strip_tac
      >- (qpat_assum `!q k. MEM (q,k) sc ==> _` drule >>
          disch_then strip_assume_tac >> qexists `id` >>
          rpt (conj_tac >- decide_tac) >>
          qpat_assum `!id q k. FLOOKUP r.vs_allocas id = SOME (q,k) ==> _` irule >>
          first_assum ACCEPT_TAC) >>
      qpat_assum `!q k. MEM (q,k) tc ==> _` drule >>
      disch_then strip_assume_tac >> qexists `id` >>
      rpt (conj_tac >- decide_tac) >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- metis_tac[pred_setTheory.SUBSET_TRANS]) >> metis_tac[]
QED

(* Navigation only changes the PC, the locals and their ghosts. *)
Theorem finite_member_setup[local]:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    dyn ao vo a = (ops,b) /\
  (^member_resources) a c ctx fn site limit lo s /\
  (^member_live) a src (Var root) root s p d G tn extent /\
  vo + sz <= extent /\ d + vo < dimword (:256) /\
  b.cs_next_var <= limit.cs_next_var /\ b.cs_next_id <= c.cs_next_id /\
  fn_has_code a b fn /\ ~ctx_has_dalloca ctx ==>
  ?r H u q.
    SND ops = Var q /\
    (^member_path) lo ctx fn PG s G tn (OK r) H u /\
    (^member_frame) a b ctx fn site limit lo s G tn (d+vo) 0 r H u [] /\
    (^member_resources) b c ctx fn site limit lo r /\
    (^member_live) b (FST ops) (Var q) q r
      (if dyn then p + abi_decode_load CALLDATALOAD (p + n2w ao) s else p + n2w ao)
      (d+vo) H u sz /\
    r.vs_allocas = s.vs_allocas /\ r.vs_call_ctx = s.vs_call_ctx
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderMemberCodeTheory.abi_decode_member_setup_shape >>
  disch_then (assume_tac o cj 4) >>
  `d < dimword (:256)` by decide_tac >>
  `lookup_var root s = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var root) s = _` mp_tac >> rewrite_tac[eval_operand_def]) >>
  `not_fresh_at a root /\ (!q. src = Var q ==> not_fresh_at a q)` by
    metis_tac[calldata_operand_live_not_fresh] >>
  drule_all (Q.INST [`C` |-> `sz:num`] decoderMemberJointModularTheory.calldata_member_setup_joint_modular) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`r`,`H`,`u`,`q`] >>
  `r.vs_allocas = s.vs_allocas /\ r.vs_alloca_next = s.vs_alloca_next /\
   r.vs_halted = s.vs_halted /\ r.vs_call_ctx = s.vs_call_ctx /\
   r.vs_data_section = s.vs_data_section /\ r.vs_memory = s.vs_memory` by
    (qpat_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => ONCE_REWRITE_TAC[th]) >> simp[NoAsms]) >>
  qpat_x_assum `r = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  `alloca_inv r /\ alloca_frontier_inv ctx fn site r /\ allocas_from lo r` by
    (qpat_assum `alloca_inv s` mp_tac >>
     qpat_assum `alloca_frontier_inv ctx fn site s` mp_tac >>
     qpat_assum `allocas_from lo s` mp_tac >>
     rewrite_tac[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def,
         venomMemDefsTheory.allocas_non_overlapping_def, allocaFrontierBoundTheory.alloca_frontier_inv_def,
         allocaBudgetPropsTheory.remaining_alloca_budget_def, ptrDisciplineTheory.allocas_from_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  qpat_assum `SND ops = Var q` (fn th =>
    rule_assum_tac (REWRITE_RULE[th]) >> assume_tac th) >>
  asm_rewrite_tac[listTheory.MEM, pred_setTheory.SUBSET_REFL, LESS_EQ_REFL,
      abiDecoderFrameTheory.abi_decode_footprint_frame_def] >>
  conj_tac
  >- (conj_tac >- (rpt gen_tac >> strip_tac >> `F` by decide_tac) >>
      conj_tac >- (qx_genl_tac [`id`,`slot_base`,`k`] >> strip_tac >>
          qpat_assum `!id q k. a.cs_next_id <= id /\ id < c.cs_next_id /\ _ ==> _`
            (qspecl_then [`id`,`slot_base`,`k`] mp_tac) >>
          impl_tac >- (rpt (conj_tac >- decide_tac) >> first_assum ACCEPT_TAC) >>
          disch_then ACCEPT_TAC) >>
      gen_tac >> strip_tac >>
      qpat_assum `!x. not_fresh_at a x ==> lookup_var x r = _ /\ _`
        (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  qx_genl_tac [`id`,`slot_base`,`k`] >> strip_tac >>
  qpat_assum `!id q k. a.cs_next_id <= id /\ id < c.cs_next_id /\ _ ==> _`
    (qspecl_then [`id`,`slot_base`,`k`] mp_tac) >>
  impl_tac >- (rpt (conj_tac >- decide_tac) >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* The destination root is kept live while the suffix moves its cursor. *)
Theorem finite_member_live_frame[local]:
  (^member_frame) a b ctx fn site limit lo s G tn d sz t H u sc /\
  (^member_live) a src (Var root) root s p root_addr G tn extent /\
  a.cs_next_var <= b.cs_next_var /\
  FLOOKUP s.vs_allocas oid = SOME (owner,cap) /\
  (oid < a.cs_next_id \/ b.cs_next_id <= oid) ==>
  (^member_live) b src (Var root) root t p root_addr H u extent /\
  FLOOKUP t.vs_allocas oid = SOME (owner,cap) /\ t.vs_call_ctx = s.vs_call_ctx
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_fresh_at a root /\ (!q. src = Var q ==> not_fresh_at a q)` by
    metis_tac[calldata_operand_live_not_fresh] >>
  `eval_operand src t = SOME p /\ lookup_var root t = lookup_var root s` by
    metis_tac[eval_operand_def] >>
  `ptr_covers H u root t extent` by
    metis_tac[assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame] >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >|
     [simp[NoAsms, ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def],
        rename1 `op_taint u (Var x) = _` >>
        `not_fresh_at a x` by
          (qpat_assum `!q. Var x = Var q ==> _` (qspec_then `x` mp_tac) >>
           simp[NoAsms]) >>
        qpat_assum `!name. not_fresh_at a name ==> FLOOKUP H name = _ /\ _`
          (qspec_then `x` (drule_then mp_tac)) >>
        qpat_assum `op_prov G (Var x) = NONE` mp_tac >>
        qpat_assum `op_taint tn (Var x) = {}` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[ptrDisciplineTheory.op_prov_def] >> metis_tac[],
      simp[NoAsms, ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def]]) >>
  `FLOOKUP t.vs_allocas oid = SOME (owner,cap)` by metis_tac[] >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `abi_decode_footprint_frame _ s t` mp_tac >>
     simp[NoAsms, abiDecoderFrameTheory.abi_decode_footprint_frame_def]) >>
  `abi_decoder_operand_live b.cs_next_var src /\ abi_decoder_operand_live b.cs_next_var (Var root)` by
    (conj_tac >> irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists `a.cs_next_var` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[eval_operand_def]
QED

(* Starting history is needed only when a member is revisited.  The prefix
   cannot alter allocations belonging to a subsequent member. *)
Theorem finite_member_resources_tail[local]:
  (^member_resources) a c ctx fn site limit lo s /\
  (^member_frame) a b ctx fn site limit lo s G tn d n t H u sc /\
  a.cs_next_id <= b.cs_next_id ==>
  (^member_resources) b c ctx fn site limit lo t
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`id`,`q`,`k`] >> strip_tac >>
  `FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (qpat_assum `!id. id < a.cs_next_id \/ b.cs_next_id <= id ==> _`
       (qspec_then `id` mp_tac) >> strip_tac >> metis_tac[]) >>
  `FLOOKUP s.vs_allocas id = SOME (q,k)` by metis_tac[] >>
  qpat_assum `!id q k. a.cs_next_id <= id /\ id < c.cs_next_id /\
             FLOOKUP s.vs_allocas id = SOME (q,k) ==> _`
    (qspecl_then [`id`,`q`,`k`] mp_tac) >>
  impl_tac >- (rpt (conj_tac >- decide_tac) >> first_assum ACCEPT_TAC) >>
  strip_tac >> asm_rewrite_tac[] >> conj_tac >- decide_tac >>
  qexists `ins` >> asm_rewrite_tac[]
QED

Theorem none_finite_members_paths:
  !tys tvs a c ao vo s G tn.
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (^member_child) ctx fn site limit lo PG (type_to_abi_dec_info sf ce ty) tv) tys tvs /\
  compile_abi_decode_complex_elems (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
      (abi_decoder_member_infos sf ce tys) ao vo a = ((),c) /\
  fn_has_code a c fn /\ (^member_exit) a c fn /\ ~ctx_has_dalloca ctx /\
  c.cs_next_var <= limit.cs_next_var /\
  (^member_resources) a c ctx fn site limit lo s /\
  (^member_live) a src (Var root) root s p d G tn extent /\
  vo + SUM (MAP type_memory_size tvs) <= extent /\
  (^member_owner) a c s oid owner cap (d+vo) (SUM (MAP type_memory_size tvs)) ==>
  (^member_abort) lo ctx fn PG s G tn \/
  ?t H u sc. IS_SOME (cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) ao) /\
    (^member_path) lo ctx fn PG s G tn (OK t) H u /\
    (^member_frame) a c ctx fn site limit lo s G tn (d+vo) (SUM (MAP type_memory_size tvs)) t H u sc
Proof
  BETA_TAC >> Induct_on `tys` >> gen_tac >> Cases_on `tvs` >>
  rewrite_tac[listTheory.LIST_REL_def]
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`
        (mp_tac o REWRITE_RULE [abiDecoderMemberInfosTheory.abi_decoder_member_infos_def,
            listTheory.MAP, Once abiEncoderTheory.compile_abi_decode_to_buf_def,
            compileEnvTheory.comp_return_def, pairTheory.PAIR_EQ]) >>
      disch_then SUBST_ALL_TAC >>
      disj2_tac >> qexistsl [`s`,`G`,`tn`,`[]`] >>
      rewrite_tac[listTheory.MAP,listTheory.SUM,Once cd_decode_def,IS_SOME_DEF] >> conj_tac
      >- (rpt gen_tac >> irule (cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules) >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[LESS_EQ_REFL, listTheory.MEM, pred_setTheory.SUBSET_REFL,
          abiDecoderFrameTheory.abi_decode_footprint_frame_refl]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_cons_code >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `abi_decode_member_setup _ _ _ _ _ _ ao vo a = (ops,b)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ (type_to_abi_dec_info sf ce ty) b = ((),e)` >>
  rename1 `LIST_REL _ tys tvs` >>
  rename1 `SUM (MAP type_memory_size (tv::tvs))` >>
  qpat_x_assum `(\ty tv. _) _ _` (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  rule_assum_tac (REWRITE_RULE[listTheory.MAP,listTheory.SUM]) >>
  `fn_has_code a b fn /\ fn_has_code b e fn` by
    (mp_tac (Q.SPECL [`a`,`b`,`e`,`fn`] fragExecTheory.fn_has_code_split) >> asm_rewrite_tac[]) >>
  drule_all abiDecoderMemberCodeTheory.abi_decode_member_setup_shape >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(^member_exit) b e fn` by (BETA_TAC >> drule_all abi_decoder_members_child_phi >> disch_then ACCEPT_TAC) >>
  `(^member_exit) e c fn` by (BETA_TAC >> drule_all abi_decoder_members_tail_phi >> disch_then ACCEPT_TAC) >>
  rule_assum_tac BETA_RULE >>
  `vo + type_memory_size tv <= extent /\ d + vo < dimword (:256) /\
   b.cs_next_var <= limit.cs_next_var /\ e.cs_next_var <= limit.cs_next_var /\
   b.cs_next_id <= c.cs_next_id` by
    (conj_tac
     >- (qpat_assum `vo + (_ + _) <= extent` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     conj_tac
     >- (qpat_assum `d + vo + _ < dimword (:256)` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rpt conj_tac >> simp[]) >>
  drule_all (BETA_RULE (Q.INST [`sz` |-> `type_memory_size tv`] finite_member_setup)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `SND ops = Var q` >>
  rename1 `r.vs_allocas = s.vs_allocas` >>
  qabbrev_tac `p1 = if dec_info_needs_offset (type_to_abi_dec_info sf ce ty)
                    then p + abi_decode_load CALLDATALOAD (p + n2w ao) s
                    else p + n2w ao` >>
  (Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC) `oid < b.cs_next_id \/ e.cs_next_id <= oid`
   >- (qpat_assum `oid < a.cs_next_id \/ c.cs_next_id <= oid` mp_tac >>
     qpat_assum `a.cs_next_id < b.cs_next_id` mp_tac >>
     qpat_assum `e.cs_next_id <= c.cs_next_id` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
  qpat_x_assum `!mid en q src s p d oid base cap G tn. _`
    (qspecl_then [`b`,`e`,`q`,`FST ops`,`r`,`p1`,`d+vo`,`oid`,`owner`,`cap`,`H`,`u`] mp_tac) >>
  (impl_tac >-
    (qunabbrev_tac `p1` >>
     `compile_abi_decode_to_buf (Var q) (FST ops) CALLDATALOAD (Lit 0w) (Lit 0w)
           (type_to_abi_dec_info sf ce ty) b = ((),e)` by
       (qpat_assum `compile_abi_decode_to_buf (SND ops) _ _ _ _ _ b = _` mp_tac >>
        qpat_assum `SND ops = Var q` (fn th => rewrite_tac[th])) >>
     `FLOOKUP r.vs_allocas oid = SOME (owner,cap)` by
       (qpat_assum `r.vs_allocas = s.vs_allocas` (fn th => rewrite_tac[th]) >>
        first_assum ACCEPT_TAC) >>
     `d + vo + type_memory_size tv <= owner + cap` by
       (qpat_assum `d + vo + _ <= owner + cap` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `d + vo + type_memory_size tv < dimword (:256)` by
       (qpat_assum `d + vo + _ < dimword (:256)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qx_genl_tac [`id`,`slot_base`,`k`] >> strip_tac >>
     qpat_assum `!id q k. b.cs_next_id <= id /\ id < c.cs_next_id /\ FLOOKUP r.vs_allocas id = SOME (q,k) ==> _`
       (qspecl_then [`id`,`slot_base`,`k`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
       qpat_assum `id < e.cs_next_id` mp_tac >>
       qpat_assum `e.cs_next_id <= c.cs_next_id` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
     disch_then ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `z` (qx_choose_then `gh` (qx_choose_then `w` strip_assume_tac)))
    (qx_choose_then `t1` (qx_choose_then `J` (qx_choose_then `v`
      (qx_choose_then `sc1` (map_every assume_tac o CONJUNCTS))))))
  >- (disj1_tac >> qexistsl [`z`,`gh`,`w`] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl [`H`,`r`,`u`] >> simp[]) >>
  `(^member_path) lo ctx fn PG s G tn (OK t1) J v` by
    (BETA_TAC >> rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl [`H`,`r`,`u`] >> simp[]) >>
  `a.cs_next_id <= b.cs_next_id` by (irule LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC) >>
  (Q_TAC (fn t => SUBGOAL_THEN t (mk_asm "prefix_frame" o BETA_RULE))
    `(^member_frame) a e ctx fn site limit lo s G tn (d+vo) (type_memory_size tv) t1 J v sc1`
   >- (BETA_TAC >>
       mp_tac (REWRITE_RULE [ADD_CLAUSES,listTheory.APPEND] (BETA_RULE
         (Q.INST [`b` |-> `b`, `c` |-> `e`, `d` |-> `d+vo`, `n` |-> `0`,
           `m` |-> `type_memory_size tv`, `t` |-> `t1`, `sc` |-> `[]`,
           `tc` |-> `sc1`] finite_member_frame_join))) >>
       (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC)) >>
  rule_assum_tac BETA_RULE >>
  `a.cs_next_id <= e.cs_next_id /\ a.cs_next_var <= e.cs_next_var` by
    (conj_tac
     >- (irule LESS_EQ_TRANS >> qexists `b.cs_next_id` >> conj_tac >> first_assum ACCEPT_TAC) >>
     irule LESS_EQ_TRANS >> qexists `b.cs_next_var` >> conj_tac >> first_assum ACCEPT_TAC) >>
  (Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC) `oid < a.cs_next_id \/ e.cs_next_id <= oid`
   >- (qpat_assum `oid < a.cs_next_id \/ c.cs_next_id <= oid` mp_tac >>
       qpat_assum `e.cs_next_id <= c.cs_next_id` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
  asm "prefix_frame" (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (Q.INST [`b` |-> `e`, `t` |-> `t1`, `H` |-> `J`, `u` |-> `v`,
    `d` |-> `d+vo`, `sz` |-> `type_memory_size tv`, `sc` |-> `sc1`,
    `root_addr` |-> `d`] finite_member_live_frame)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (Q.INST [`b` |-> `e`, `t` |-> `t1`, `H` |-> `J`, `u` |-> `v`,
    `d` |-> `d+vo`, `n` |-> `type_memory_size tv`, `sc` |-> `sc1`]
    finite_member_resources_tail)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv` by
    (drule calldata_coherent_embedded_size >> disch_then ACCEPT_TAC) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (drule abi_decoder_coherent_header >> simp[NoAsms, abi_decoder_header_def]) >>
  (Q_TAC (fn t => SUBGOAL_THEN t ASSUME_TAC) `oid < e.cs_next_id \/ c.cs_next_id <= oid`
   >- (qpat_assum `oid < a.cs_next_id \/ c.cs_next_id <= oid` mp_tac >>
       qpat_assum `a.cs_next_id <= e.cs_next_id` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)) >>
  `owner <= d + (vo + type_memory_size tv)` by
    (qpat_assum `owner <= d + vo` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `!tvs a c ao vo s G tn. _`
    (qspecl_then [`tvs`,`e`,`c`,`ao + tv_abi_size tv`,`vo + type_memory_size tv`,`t1`,`J`,`v`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rewrite_tac [ADD_ASSOC] >> TRY (first_assum (ACCEPT_TAC o REWRITE_RULE [ADD_ASSOC])) >>
     qpat_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ e = _` mp_tac >>
     qpat_assum `type_memory_bytes ce ty = type_memory_size tv` (fn th => rewrite_tac[th]) >>
     qpat_assum `abi_embedded_static_size ce.ce_struct_fields ty = tv_abi_size tv`
       (fn th => rewrite_tac[th]) >> disch_then ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `z` (qx_choose_then `gh` (qx_choose_then `w` strip_assume_tac)))
    (qx_choose_then `t2` (qx_choose_then `gh` (qx_choose_then `w`
      (qx_choose_then `sc2` (map_every assume_tac o CONJUNCTS))))))
  >- (disj1_tac >> qexistsl [`z`,`gh`,`w`] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl [`J`,`t1`,`v`] >> simp[]) >>
  disj2_tac >> qexistsl [`t2`,`gh`,`w`,`sc1 ++ sc2`] >>
  conj_tac
  >- ((`IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv
          (cd_member_ptr F s.vs_call_ctx.cc_calldata tv (w2n p) ao))` by
        (qpat_assum `IS_SOME (cd_decode F r.vs_call_ctx.cc_calldata tv (w2n p1))` mp_tac >>
         qunabbrev_tac `p1` >>
         qpat_assum `r.vs_call_ctx = s.vs_call_ctx` (fn th => rewrite_tac[th]) >>
         drule member_source_decode >> disch_then (fn th => rewrite_tac[th])) >>
      qpat_assum `IS_SOME (cd_decode_list F t1.vs_call_ctx.cc_calldata tvs _ _)`
        (mp_tac o REWRITE_RULE[IS_SOME_EXISTS]) >>
      qpat_assum `t1.vs_call_ctx = s.vs_call_ctx` (fn th => rewrite_tac[th]) >>
      strip_tac >>
      qpat_assum `IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (cd_member_ptr _ _ _ _ _))`
        (strip_assume_tac o REWRITE_RULE[IS_SOME_EXISTS]) >>
      rewrite_tac[Once cd_decode_def] >>
      qpat_assum `cd_decode F _ tv (cd_member_ptr _ _ _ _ _) = SOME _` (fn th => rewrite_tac[th]) >>
      qpat_assum `cd_decode_list F _ tvs _ _ = SOME _` (fn th => rewrite_tac[th]) >>
      rewrite_tac[IS_SOME_DEF] >> (simp[Once cd_decode_def, IS_SOME_DEF, member_source_decode]))) >>
  conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl [`J`,`t1`,`v`] >> simp[]) >>
  rewrite_tac[listTheory.MAP,listTheory.SUM] >>
  mp_tac (BETA_RULE (Q.INST [`b` |-> `e`, `r` |-> `t1`, `H` |-> `J`, `u` |-> `v`,
    `t` |-> `t2`, `J` |-> `gh`, `v` |-> `w`, `sc` |-> `sc1`, `tc` |-> `sc2`,
    `d` |-> `d+vo`, `n` |-> `type_memory_size tv`, `m` |-> `SUM (MAP type_memory_size tvs)`]
    finite_member_frame_join)) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rewrite_tac [ADD_ASSOC] >> first_assum (ACCEPT_TAC o REWRITE_RULE [ADD_ASSOC]))) >>
  disch_then ACCEPT_TAC
QED
