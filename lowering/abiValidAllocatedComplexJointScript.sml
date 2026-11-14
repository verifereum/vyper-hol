(* The complex guard enters member traversal with one operational/ghost endpoint. *)
Theory abiValidAllocatedComplexJoint
Ancestors
  abiValidAllocatedComplex abiDecodePtrComplexGuardJoint abiValidAllocatedMembers
  abiMalformedRecursiveInterface abiDecoderComplexExecute abiDecoderComplexGuard
  abiDecoderComplexHead abiDecoderMemberInfos abiDecoderCoherence abiDecoderReentry
  abiDecodePtrMemberFrame decoderGhostFramePtr entryDecoderHistoryFrame
  abiDecoderContract abiEncoder compileEnv loweringStateRelDefs exprLoweringProps
  emitHelperProps bodyPtrDefs ptrDiscipline venomState venomExecSemantics
  finite_map words list rich_list arithmetic

Theorem abi_valid_allocated_complex_members_entry_joint:
  abi_decode_complex_head_guard src hi H st = ((),middle) /\
  compile_abi_decode_complex_elems (Var output) src MLOAD (Var source) hi
    (abi_decoder_member_infos sf ce tys) 0 0 middle = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry HZ ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live
    (Var source) hi src (Var output) B L xs p d n s /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  type_memory_size_list tvs <= n /\ p + H <= L /\
  p + SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= L /\
  vyper_decode_valid_enc_tuple (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs) /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) (DROP p xs) (DROP p xs)) = SOME vs /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~ctx_has_dalloca ctx /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s n /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn src = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
  ?t G' tn'. abi_decode_sim ctx func s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s t /\
    abi_valid_allocated_members_entry HZ ce env sf tys tvs vs ctx func cenv cx es
      middle en (Var source) hi src (Var output) B L xs p d n 0 0 dstid live ceiling t /\
    run_inst_seq (emitted_insts st middle) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ptr_covers G' tn' output t n /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_allocated_complex_members_entry_run >> strip_tac >>
  `t.vs_inst_idx = LENGTH middle.cs_current_insts` by
    fs[abi_valid_allocated_members_entry_def] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_complex_code >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `not_fresh_at st source /\ not_fresh_at st output` by
    fs[EVERY_DEF, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >>
  mp_tac (abi_decode_complex_guard_success_joint |> Q.INST
    [`sa` |-> `st`, `sb` |-> `middle`, `pos` |-> `src`, `n` |-> `H`,
     `u` |-> `t with vs_inst_idx := s.vs_inst_idx`]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `t with vs_inst_idx := _ = s with vs_vars := _` kall_tac >>
  `t with vs_inst_idx := LENGTH middle.cs_current_insts = t` by
    simp[venom_state_component_equality] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ _ _ _`
       (qspecl_then [`D`, `explicit`] mp_tac) >>
     qpat_assum `t with vs_inst_idx := LENGTH middle.cs_current_insts = t`
       (fn th => simp_tac (srw_ss()) [th])) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st middle)` by
    fs[EVERY_MEM] >>
  `alloca_history func t` by
    (drule_all entry_straight_line_alloca_history >> simp[]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     simp_tac (srw_ss()) [lookup_var_def] >>
     qpat_assum `!x. not_fresh_at st x ==> _ /\ _ /\ _`
       (fn th => ACCEPT_TAC
         (SIMP_RULE (srw_ss()) [lookup_var_def] (UNDISCH (Q.SPEC `x` th))))) >>
  `ptr_covers G' tn' output t n` by
    (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `abi_decode_ptr_window G' tn' t source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `allocas_from lo t` by (fs[allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> asm_simp_tac bool_ss []
QED
