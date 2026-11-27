(* Readiness geometry at the selected linked packing endpoint. *)
Theory bodyExtRequestPackedBufferMods
Ancestors
  bodyFullIntCallReturnFrame exprSimPrecompiles wordArgsPtr stateRelProj
  exprLoweringProps localPtrsProps loweringStateRelDefs
  venomInst venomState compileEnv words finite_map arithmetic list

Theorem packed_buffer_subregions[local]:
  regions_disjoint p n b sz /\ cap <= n /\ k <= sz ==>
  regions_disjoint p cap b k
Proof
  simp[regions_disjoint_def] >> decide_tac
QED

(* The active-module component of the reached state relation covers this
   exact constructor ALLOCA, not an arbitrary allocation with the same size. *)
Theorem packed_buffer_immutable[local]:
  stmt_state_rel H ctx func ce cx ee t /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n) /\ cap <= n ==>
  regions_disjoint p cap off (type_memory_size tv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (mp_tac o CONJUNCT2 o REWRITE_RULE [immutable_alloca_sep_def])
    return_stmt_immutable_sep >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (drule_all_then strip_assume_tac) >>
  qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz`
    (qspecl_then [`inst`,`p`,`n`] mp_tac) >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem ext_request_packed_buffer_mods:
  buf_op = Var root /\ lookup_var root t = SOME (n2w p) /\
  MEM (mk_inst s5.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  FLOOKUP t.vs_allocas s5.cs_next_id = SOME (p,n) /\ p+n < dimword (:256) /\
  sa.cs_next_id <= s5.cs_next_id /\ s5.cs_next_id < sp.cs_next_id /\ cap <= n /\
  stmt_state_rel H0 ctx func ce cx es s0 /\ stmt_state_rel H1 ctx func ce cx ee t /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ wb_frame ce es ee sa s0 t /\
  (!d w tv. default_opt = SOME d /\ ~is_word_type default_ty /\
     eval_operand default_op t = SOME w /\
     evaluate_type (get_tenv cx) default_ty = SOME tv ==>
     ?aid. aid < s5.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
       val_footprint tv d <= type_memory_size tv) ==>
  (?ro. eval_operand buf_op t = SOME ro /\ w2n ro + cap < dimword (:256) /\
     (?live buf_size. sa.cs_next_id <= live /\ live < sp.cs_next_id /\ cap <= buf_size /\
        FLOOKUP t.vs_allocas live = SOME (w2n ro,buf_size)) /\
     (!name b sz. local_region ce ee.scopes t name b sz ==> regions_disjoint (w2n ro) cap b sz) /\
     (!name b sz. local_region ce es.scopes s0 name b sz ==> regions_disjoint (w2n ro) cap b sz) /\
     (!aid b sz. aid < sa.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n ro) cap b sz) /\
     (ce.ce_is_ctor ==> !name tv v off.
        FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
        regions_disjoint (w2n ro) cap off (type_memory_size tv)) /\
     (!d w tv. default_opt = SOME d /\ ~is_word_type default_ty /\
        eval_operand default_op t = SOME w /\
        evaluate_type (get_tenv cx) default_ty = SOME tv ==>
        regions_disjoint (w2n ro) cap (w2n w) (val_footprint tv d))) /\
  buf_op = Var root /\ eval_operand buf_op t = SOME (n2w p) /\
  MEM (mk_inst s5.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func) /\
  (mk_inst s5.cs_next_id ALLOCA [Lit (n2w n)] [root]).inst_opcode = ALLOCA /\
  (mk_inst s5.cs_next_id ALLOCA [Lit (n2w n)] [root]).inst_id = s5.cs_next_id /\
  (mk_inst s5.cs_next_id ALLOCA [Lit (n2w n)] [root]).inst_outputs = [root] /\
  FLOOKUP t.vs_allocas s5.cs_next_id = SOME (w2n (n2w p : bytes32),n) /\ cap <= n
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p < dimword (:256) /\ p+cap < dimword (:256)` by decide_tac >>
  `w2n (n2w p : bytes32) = p` by simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `eval_operand buf_op t = SOME (n2w p)` by simp[eval_operand_def] >>
  reverse conj_tac >- simp[mk_inst_def] >>
  qexists `n2w p` >> asm_rewrite_tac[] >>
  conj_tac >- (qexistsl [`s5.cs_next_id`,`n`] >> asm_rewrite_tac[]) >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_id = s5.cs_next_id /\ inst.inst_outputs = [root]`
    by simp[Abbr `inst`,mk_inst_def] >>
  qpat_assum `stmt_state_rel H1 _ _ _ _ ee t`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `!name b sz. local_region ce ee.scopes t name b sz ==> regions_disjoint p cap b sz` by
    (rpt gen_tac >> disch_tac >>
     `regions_disjoint p n b sz` by
       (irule local_ptrs_rel_alloca_disjoint >>
        qpat_assum `local_ptrs_rel func ce ee.scopes t` (irule_at Any) >>
        qpat_assum `local_region ce ee.scopes t name b sz` (irule_at Any) >>
        qpat_assum `MEM inst (fn_insts func)` (irule_at Any) >>
        qexists `root` >> simp[]) >>
     drule_then (irule_at Any) packed_buffer_subregions >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt gen_tac >> disch_tac >>
     drule_all wb_frame_local_regions >> strip_tac >>
     `local_region ce ee.scopes t name b sz` by
       (qpat_assum `!n b sz. local_region _ _ s0 n b sz <=> _`
          (drule_then ACCEPT_TAC o iffLR o SPEC_ALL)) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `!aid b sz. aid < s5.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint p n b sz` by
    (rpt gen_tac >> strip_tac >>
     `s5.cs_next_id <> aid` by decide_tac >>
     drule_all_then ACCEPT_TAC state_allocations_disjoint) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `aid < s5.cs_next_id` by decide_tac >>
     `regions_disjoint p n b sz` by
       (qpat_assum `!aid b sz. aid < s5.cs_next_id /\ _ ==> _`
          (drule_all_then ACCEPT_TAC)) >>
     drule_then (irule_at Any) packed_buffer_subregions >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n)` by simp[] >>
     drule_all_then ACCEPT_TAC packed_buffer_immutable) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!d w tv. _ ==> ?aid. _` (drule_all_then strip_assume_tac) >>
  `regions_disjoint p n (w2n w) (type_memory_size tv)` by
    first_assum (drule_all_then ACCEPT_TAC) >>
  drule_then (irule_at Any) packed_buffer_subregions >> simp[]
QED
