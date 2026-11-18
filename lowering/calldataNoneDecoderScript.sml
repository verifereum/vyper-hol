(* The installed decoder either reverts or can continue only after source decoding succeeds. *)
Theory calldataNoneDecoder
Ancestors
  calldataNoneDecodeLeaves calldataNoneFiniteMembers calldataNoneArrayFold
  calldataRecursiveProducers ptrSafetyTransportEndpoint assignTuplePtrCopyLen
  abiDecoderSourceFacts calldataDecodePtr decoderBlockGrowth valueEncodingProofs
  fragGasOriginPtr fragExec abiDecoderFrame calldataSourceSize
  abiDecoderMemberInfos abiDecoderComplexGuard abiDecoderBulk abiDecoderArrayHeader
  abiDecoderDynarrayPrefix abiDecoderContract compileEnv emitHelper
  vyperCalldata ptrDiscipline abiDecoderCoherence words venomState
  rich_list list option arithmetic pred_set

val decode_history = ``\st last fn s.
  !id q k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]``;
val decode_exit = ``\st last fn. st.cs_blocks = last.cs_blocks \/
  !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0``;
val decode_input = ``\di sz st last limit ctx fn site src child s p d oid base cap G tn lo.
  compile_abi_decode_to_buf (Var child) src CALLDATALOAD (Lit 0w) (Lit 0w) di st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
  last.cs_next_var <= limit.cs_next_var /\ unit_alloca_budget ctx < dimword (:256) /\
  (^decode_exit) st last fn /\
  eval_operand src s = SOME p /\ eval_operand (Var child) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var child) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ (^decode_history) st last fn s /\
  FLOOKUP s.vs_allocas oid = SOME (base,cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base <= d /\ d+sz <= base+cap /\ d+sz < dimword (:256) /\
  ptr_covers G tn child s sz /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts``;
val decode_outcome = ``\accepted sz st last limit ctx fn site child s d G tn lo PG.
  (?z H u. z.vs_returndata = [] /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u))) \/
  ?v sc H u. accepted /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\
    v.vs_inst_idx = LENGTH last.cs_current_insts /\
    v.vs_call_ctx = s.vs_call_ctx /\ v.vs_data_section = s.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (^decode_history) st last fn v /\
    s.vs_alloca_next <= v.vs_alloca_next /\
    (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==> FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
      FLOOKUP v.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op v = eval_operand op s) /\
    abi_decode_footprint_frame ((d,sz)::sc) s v /\
    (!q k. MEM (q,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP v.vs_allocas id = SOME (q,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers H u child v sz /\
    (!name. not_fresh_at st name ==> FLOOKUP H name = FLOOKUP G name /\
      op_taint u (Var name) = op_taint tn (Var name)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,H,u))``;
val coherent_paths = ``\ce (env:(num option # string) |-> type_args)
  (sf:string |-> (string # type # num) list) ty tv.
  !st last limit ctx fn site src child s p d oid base cap G tn lo PG.
  (^decode_input) (type_to_abi_dec_info sf ce ty) (type_memory_size tv)
    st last limit ctx fn site src child s p d oid base cap G tn lo ==>
  (^decode_outcome) (IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p)))
    (type_memory_size tv) st last limit ctx fn site child s d G tn lo PG``;

Theorem decode_path_endpoint_floor[local]:
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,H,u)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  disch_then (CONJUNCTS_THEN2 (mp_tac o SPEC_ALL) strip_assume_tac) >>
  disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >>
  disch_then (mp_tac o MATCH_MP gas_path_ptr_ok_allocas_from o CONJUNCT2) >>
  disch_then (qspecl_then [`lo`,`t`] mp_tac) >> simp[]
QED

Theorem decode_fixed_source[local]:
  !n i. cd_decode_list F cd (REPLICATE n tv) p (i * tv_abi_size tv) =
        cd_decode_elems F cd tv p i n
Proof
  Induct_on `n` >> simp[REPLICATE, Once cd_decode_def] >> gen_tac >>
  once_rewrite_tac[cd_decode_def] >>
  Cases_on `cd_decode F cd tv (cd_member_ptr F cd tv p (i * tv_abi_size tv))` >>
  simp[] >>
  first_x_assum (qspec_then `i + 1` mp_tac) >>
  simp[RIGHT_ADD_DISTRIB, ADD_COMM]
QED

(* At a finite aggregate, the unbounded head guard emits no code. *)
Theorem decode_finite_paths[local]:
  LIST_REL (\ty tv. abi_decoder_coherent ce env sf ty tv /\
    (^coherent_paths) ce env sf ty tv) tys tvs /\
  (^decode_input) (DecComplex dyn (abi_decoder_member_infos sf ce tys))
    (SUM (MAP type_memory_size tvs)) st last limit ctx fn site src child s p d oid owner_base cap G tn lo ==>
  (^decode_outcome) (IS_SOME (cd_decode_list F s.vs_call_ctx.cc_calldata tvs (w2n p) 0))
    (SUM (MAP type_memory_size tvs)) st last limit ctx fn site child s d G tn lo PG
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE std_ss [Once abiEncoderTheory.compile_abi_decode_to_buf_def, LET_THM]) >>
  drule_at (Pat `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _`)
    (BETA_RULE calldataNoneFiniteMembersTheory.none_finite_members_paths) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (mp_tac o Q.INST [`env` |-> `env`, `PG` |-> `PG`,
    `tvs'` |-> `tvs`, `p` |-> `p`] o SPEC_ALL) >>
  rewrite_tac[ADD_CLAUSES, LESS_EQ_REFL] >> impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `LIST_REL _ _ _` mp_tac >> ho_match_mp_tac LIST_REL_mono >>
      rpt gen_tac >> strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      map_every qx_gen_tac [`mid`,`en`,`q`,`sop`,`r`,`pw`,`e`,`rid`,`rb`,`child_cap`,`A`,`ta`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `(^decode_input) (type_to_abi_dec_info sf ce ty) (type_memory_size tv)
        mid en limit ctx fn site sop q r pw e rid rb child_cap A ta lo` by
        (BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      pop_assum (fn input =>
        qpat_x_assum `!st last limit ctx fn site src child s p d oid base cap G tn lo PG. _`
          (mp_tac o C MATCH_MP (BETA_RULE input))) >>
      disch_then (qspec_then `PG` (DISJ_CASES_THEN2
        (qx_choose_then `z` (qx_choose_then `H` (qx_choose_then `u` strip_assume_tac)))
        (qx_choose_then `v` (qx_choose_then `sc` (qx_choose_then `H`
          (qx_choose_then `u` strip_assume_tac))))))
      >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
      `allocas_from lo v /\ lo <= v.vs_alloca_next` by
        (irule decode_path_endpoint_floor >>
         qexistsl [`A`,`H`,`PG`,`ctx`,`fn`,`r`,`ta`,`u`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disj2_tac >> qexistsl [`v`,`H`,`u`,`sc`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> disch_then (fn th =>
        POP_ASSUM_LIST (K ALL_TAC) >> mp_tac (CONJUNCT1 th) >> mp_tac (cj 2 th)) >>
      simp[arithmeticTheory.NOT_LESS]) >>
  strip_tac
  >- (disj1_tac >> qexistsl [`z`,`H`,`u`] >> asm_rewrite_tac[]) >>
  disj2_tac >> qexistsl [`t`,`sc`,`H`,`u`] >>
  `t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section` by
    (qpat_assum `abi_decode_footprint_frame _ _ _`
       (mp_tac o REWRITE_RULE [abi_decode_footprint_frame_def]) >> simp[NoAsms]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule ptr_covers_lookup_frame >> qexistsl [`G`,`s`,`tn`] >>
  `not_fresh_at st child` by
    (rewrite_tac[GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `!name. not_fresh_at st name ==> _` (drule_all_then strip_assume_tac) >>
  `lookup_var child t = lookup_var child s` by
    (qpat_assum `!op. abi_decoder_operand_live _ op ==> _`
       (qspec_then `Var child` mp_tac) >>
     disch_then (drule_then mp_tac) >> simp[NoAsms, eval_operand_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
