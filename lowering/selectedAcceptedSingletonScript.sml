(* Assemble one positional slot using its actual calldata decoder. *)
Theory selectedAcceptedSingleton
Ancestors
  selectedAcceptedInterfaces entryPtrSeamRegister dispatchedDecoderTrace
  abiDecoderAppend abiDecoderCounters abiDecoderCode calldataRegistrationExec
  actualAllocExec venomInstIdsProps emitHelperProps exprSimProps
  calldataClampPtr calldataDynOwned venomMemDefs fragExec compileEnv arithmetic
  venomState words list venomInst finite_map fragGasPathFrameMem fragGasPathMem

Theorem selected_register_one:
  !ce env sf ty tv.
    selected_decoder_accepts ce env sf ty tv ==>
    selected_slot_accepts ce env sf ty tv
Proof
  rewrite_tac[selected_slot_accepts_def] >> rpt gen_tac >> disch_tac >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `compile_register_positional_args ce [(name,F,dyn,sz,di)] (4+ofs) st = (ce',last)` by
    (Cases_on `prim` >> gvs[registration_primitive_as_aggregate]) >>
  drule_all registration_aggregate_phases >> strip_tac >>
  `cs_extends st a /\ cs_extends a mid /\ cs_extends first last` by
    metis_tac[cs_appends_abi_alloc_buffer, cs_appends_abi_member_pointer,
      cs_appends_abi_decode_mutual, cs_appends_def] >>
  `cs_extends mid first /\ mid.cs_next_var <= first.cs_next_var /\
    mid.cs_next_id <= first.cs_next_id` by
    (Cases_on `dyn` >> fs[cs_extends_refl] >>
     drule registration_ptr_guard_code >> strip_tac >>
     metis_tac[registration_ptr_guard_extends, LESS_EQ_ADD]) >>
  `cs_extends a first` by metis_tac[cs_extends_trans] >>
  `fn_has_code st a fn /\ fn_has_code a first fn /\ fn_has_code first last fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!entry. FLOOKUP s.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    metis_tac[venomInstIdsPropsTheory.fn_inst_ids_distinct_all_distinct] >>
  `dyn ==> abi_decode_load CALLDATALOAD (n2w (4+ofs) : bytes32) s = n2w delta /\
    4+delta < dimword (:256)` by simp[] >>
  drule_all registration_argument_prepare_counted >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  rename1 `lookup_var q ready = SOME (n2w p)` >>
  drule_all registration_preparation_forward_slots >> strip_tac >>
  `st.cs_next_id < mid.cs_next_id` by
    (first_assum irule >> qexists_tac `(p,n)` >> simp[]) >>
  `st.cs_next_id < first.cs_next_id` by decide_tac >>
  `first.cs_next_id <= last.cs_next_id` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     mp_tac (CONJUNCT1 abi_decoder_code_mutual) >>
     disch_then (qspecl_then [`buf.buf_operand`, `src`, `CALLDATALOAD`,
       `Lit 0w`, `Lit 0w`, `di`] mp_tac) >> simp[] >>
     disch_then (qspec_then `first` mp_tac) >> simp[abi_decoder_code_def]) >>
  `st.cs_next_id < last.cs_next_id` by decide_tac >>
  `first.cs_next_var <= last.cs_next_var` by
    metis_tac[abi_decoder_vars_mono_mutual, abi_decoder_vars_mono_def, pairTheory.SND] >>
  `st.cs_next_var <= first.cs_next_var` by
    metis_tac[abi_decoder_vars_mono_abi_alloc_buffer,
      abi_decoder_vars_mono_abi_member_pointer, abi_decoder_vars_mono_def,
      pairTheory.SND, LESS_EQ_TRANS] >>
  `fresh_vars_wrt last ready` by
    (irule fresh_vars_wrt_mono >> qexists_tac `first` >> simp[]) >>
  `lo <= ready.vs_alloca_next` by decide_tac >>
  `srcpos < dimword (:256)` by (Cases_on `dyn` >> fs[]) >>
  `eval_operand src ready = SOME (n2w srcpos)` by metis_tac[] >>
  `w2n (n2w srcpos : bytes32) = srcpos` by
    (rewrite_tac[w2n_n2w] >> irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  `cd_decode F ready.vs_call_ctx.cc_calldata tv (w2n (n2w srcpos : bytes32)) = SOME x` by
    metis_tac[] >>
  `compile_abi_decode_to_buf (Var q) src CALLDATALOAD (Lit 0w) (Lit 0w)
     (type_to_abi_dec_info sf ce ty) first = ((),last)` by metis_tac[] >>
  qpat_x_assum `selected_decoder_accepts ce env sf ty tv`
    (mp_tac o REWRITE_RULE [selected_decoder_accepts_def]) >>
  disch_then (qspecl_then [`first`, `last`, `last`, `ctx`, `fn`, `site`, `src`, `q`,
    `ready`, `n2w srcpos`, `p`, `st.cs_next_id`, `p`, `n`, `H`, `u`, `lo`, `PG`, `x`] mp_tac) >>
  (impl_tac >-
    (asm_rewrite_tac[eval_operand_def, LESS_EQ_REFL] >>
     rpt strip_tac >> TRY decide_tac >>
     TRY (qpat_assum `!id. mid.cs_next_id <= id ==> FLOOKUP ready.vs_allocas id = NONE`
       (qspec_then `id` mp_tac)) >> gvs[eval_operand_def])) >>
  disch_then (qx_choose_then `t` (qx_choose_then `scratch`
    (qx_choose_then `Ht` (qx_choose_then `ut` strip_assume_tac)))) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK t,Ht,ut)` by
    (rpt gen_tac >> irule dispatched_decoder_joint_then >>
     qexistsl_tac [`H`, `ready`, `u`] >> simp[]) >>
  `ready.vs_code = s.vs_code` by
    (`gas_path_mem ctx fn s 0 (OK ready)` by
       metis_tac[selected_zero_path_mem] >>
     drule (cj 1 gas_path_mem_exec) >> disch_then (mp_tac o MATCH_MP gas_path_code_labels) >>
     simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn)` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
     `q = STRING #"%" (toString st.cs_next_var)` by metis_tac[operand_11] >>
     drule_all actual_alloc_buffer_site >> asm_rewrite_tac[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live first.cs_next_var op` by
       (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >>
     metis_tac[]) >>
  `!id entry. FLOOKUP ready.vs_allocas id = SOME entry ==>
    FLOOKUP t.vs_allocas id = SOME entry` by
    (rpt strip_tac >> PairCases_on `entry` >> metis_tac[]) >>
  `!id entry. FLOOKUP t.vs_allocas id = SOME entry ==> id < last.cs_next_id` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `last.cs_next_id <= id /\ mid.cs_next_id <= id` by decide_tac >>
     metis_tac[optionTheory.NOT_SOME_NONE]) >>
  `lookup_var q t = SOME (n2w p)` by
    (qpat_assum `!op. abi_decoder_operand_live first.cs_next_var op ==>
                     eval_operand op t = eval_operand op ready`
       (qspec_then `Var q` mp_tac) >>
     rewrite_tac[eval_operand_def] >> metis_tac[]) >>
  `fresh_vars_wrt limit t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `last` >> simp[]) >>
  `val_footprint tv x <= n` by metis_tac[val_footprint_le] >>
  `s.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
    FLOOKUP t.vs_allocas id = SOME entry` by metis_tac[] >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,n)` by
    (qpat_assum `!id entry. FLOOKUP ready.vs_allocas id = SOME entry ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `n = type_memory_size tv` SUBST_ALL_TAC >>
  qexistsl_tac [`t`, `Ht`, `ut`, `q`, `p`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- suspend "old_local") >>
  suspend "allocation_size"
QED

Resume selected_register_one[old_local]:
  rpt gen_tac >> strip_tac >>
  `old < first.cs_next_id /\ old < last.cs_next_id /\ old <> st.cs_next_id` by
    decide_tac >>
  `FLOOKUP t.vs_allocas old = SOME (p0,n0)` by
    (qpat_assum `!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
                            FLOOKUP t.vs_allocas id = SOME entry` irule >>
     first_assum ACCEPT_TAC) >>
  `ptr_covers H u q0 ready n0` by metis_tac[] >>
  `p0 + n0 <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >>
     rewrite_tac[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem ready.vs_memory mem ==>
         val_in_memory tv0 v0 p0 mem` by
    (qpat_assum `!tv0 v0 p0. val_wf tv0 v0 /\ _ ==> _`
       (qspecl_then [`tv0`, `v0`, `p0`] mp_tac) >>
     (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  `not_fresh_at st q0` by
    (`eval_operand (Var q0) s = SOME (n2w p0)` by asm_rewrite_tac[eval_operand_def] >>
     qspecl_then [`st`, `s`, `Var q0`, `n2w p0`]
       mp_tac exprSimWordBuiltinsTheory.fresh_vars_wrt_not_fresh_at >> simp[]) >>
  `abi_decoder_operand_live st.cs_next_var (Var q0)` by
    asm_rewrite_tac[calldata_operand_live_not_fresh] >>
  `abi_decoder_operand_live first.cs_next_var (Var q0)` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_rewrite_tac[]) >>
  `not_fresh_at first q0` by
    metis_tac[calldata_operand_live_not_fresh] >>
  `lookup_var q0 t = SOME (n2w p0) /\ lookup_var q0 ready = SOME (n2w p0)` by
    (qpat_assum `!op. abi_decoder_operand_live st.cs_next_var op ==>
                     eval_operand op t = eval_operand op s`
       (qspec_then `Var q0` mp_tac) >>
     qpat_assum `!op. abi_decoder_operand_live first.cs_next_var op ==>
                     eval_operand op t = eval_operand op ready`
       (qspec_then `Var q0` mp_tac) >>
     rewrite_tac[eval_operand_def] >> metis_tac[]) >>
  `FLOOKUP Ht q0 = FLOOKUP H q0 /\
   op_taint ut (Var q0) = op_taint u (Var q0)` by
    (qpat_assum `!name. not_fresh_at first name ==> _`
       (qspec_then `q0` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  drule_at (Pat `abi_decode_footprint_frame`) registration_owned_local_frame >>
  disch_then (drule_at (Pat `val_wf`)) >>
  disch_then (drule_at (Pat `ptr_covers`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,_)`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = op_taint _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = FLOOKUP _ _`)) >>
  disch_then (drule_at (Pat `!mem. mem_agree_outside tm memory mem ==> val_in_memory tv v p mem`)) >>
  disch_then (qspec_then `st.cs_next_id` mp_tac) >>
  disch_then (qspecl_then
    [`last.cs_next_id`, `type_memory_size tv`, `first.cs_next_id`, `p`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  strip_tac >> asm_rewrite_tac[]
QED

Resume selected_register_one[allocation_size]:
  rpt strip_tac >>
  Cases_on `first.cs_next_id <= inst.inst_id /\ inst.inst_id < last.cs_next_id`
  >- (qpat_x_assum `!id q k. first.cs_next_id <= id /\ _ ==> _`
        (qspecl_then [`inst.inst_id`, `b`, `k`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
      `inst = ins` by metis_tac[fn_inst_ids_distinct_inj] >>
      `[Lit w] = [Lit 32w]` by metis_tac[] >>
      pop_assum mp_tac >> simp[dimword_def]) >>
  `FLOOKUP ready.vs_allocas inst.inst_id = SOME (b,k)` by
    (qpat_assum `!id. id < first.cs_next_id \/ last.cs_next_id <= id ==> _`
       (qspec_then `inst.inst_id` mp_tac) >>
     (impl_tac >- decide_tac) >> disch_tac >> metis_tac[]) >>
  Cases_on `inst.inst_id = st.cs_next_id`
  >- (`inst = mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))] [q]` by
        (irule fn_inst_ids_distinct_inj >>
         (conj_tac >- asm_simp_tac (srw_ss()) [venomInstTheory.mk_inst_def]) >>
         qexists_tac `fn` >> asm_rewrite_tac[]) >>
      `inst.inst_operands = [Lit (n2w (type_memory_size tv))]` by
        (pop_assum SUBST1_TAC >> simp[venomInstTheory.mk_inst_def]) >>
      `k = type_memory_size tv` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
      `[Lit w] = [Lit (n2w (type_memory_size tv))]` by metis_tac[] >>
      pop_assum mp_tac >> rewrite_tac[CONS_11, operand_11] >>
      disch_then SUBST1_TAC >> asm_rewrite_tac[w2n_n2w] >>
      sym_tac >> irule LESS_MOD >> first_assum ACCEPT_TAC) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k)` by metis_tac[] >>
  qpat_x_assum `!inst w b k. MEM inst _ /\ _ ==> k = w2n w`
    (qspecl_then [`inst`, `w`, `b`, `k`] mp_tac) >> asm_rewrite_tac[]
QED

Finalise selected_register_one
