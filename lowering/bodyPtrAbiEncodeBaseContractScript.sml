(* Same-endpoint finite encoder contracts. *)
Theory bodyPtrAbiEncodeBaseContract
Ancestors
  bodyPtrAbiEncodeCleanCopy bodyPtrAbiEncodePrimitive abiEncoderWindowLeaves abiEncoderWindowContract
  abiEncoderWindow abiEncoderExtendSim abiEncoderRegisteredEffect
  fragGasPathPtr bodyPtrDefs compileEnv exprLoweringProps ptrDiscipline
  venomState venomExecSemantics valueEncodingProofs valueEncoding valueEncodingProps
  abiEncoder abiEncoderInput abiEncoderOpenInput contractABI
  abiEncoderLeaves abiEncoderPrimitiveEffect
  fragExecPtr typedCopyPtr ghostPcTransportPtr fragGasSeqPtr
  emitHelperProps emitHelper fragExec venomInst
  words finite_map pred_set list arithmetic

Theorem abi_encode_empty_strong_endpoint:
  !B K D.
  compile_abi_encode_to_buf dst src (AbiComplex []) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en dst src (AbiComplex []) at av B K D s ==>
  en = st /\ out = Lit 0w /\ enc at av = [] /\
  window_strong_result ctx fn st en out at av D s s
Proof
  rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites fn (frag_ids st en) /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  gvs[Once compile_abi_encode_child_def, comp_return_def] >>
  `enc at av = []` by
    (fs[abi_encoder_window_complex_iff, abi_encoder_tuple_type_def,
        abi_encoder_member_span_def, enc_def, LET_THM, REV_DEF]) >>
  simp[window_strong_result_def, abi_encoder_window_result_def,
       mem_bytes_at_def, eval_operand_def, abi_encoder_registered_effect_refl,
       abi_encoder_extend_sim_refl, abi_encoder_extend_sim_sim,
       window_alloca_growth_def] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* Stronger than the proposed empty P-to-R instance: only the semantic entry,
   common freshness and retained coverage are needed for this no-step case. *)
Theorem abi_encode_empty_resource_contract:
  !B K D C.
  compile_abi_encode_to_buf (Var dst) src (AbiComplex []) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) src (AbiComplex []) at av B K D s /\
  fresh_vars_wrt limit s /\ (0 < C ==> ptr_covers G tn dst s C) ==>
  ?t H un.
    window_strong_result ctx fn st en out at av D s t /\
    gas_path_ptr gasD 0 ctx fn PG G tn s 0 H un (OK t) /\
    op_taint un out = {} /\
    (!q. out = Var q ==> not_fresh_at en q) /\ fresh_vars_wrt limit t /\
    (!q. not_fresh_at st q ==>
       lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
       op_taint un (Var q) = op_taint tn (Var q)) /\
    (0 < C ==> ptr_covers H un dst t C) /\
    (!i. D <= i /\ i < D+LENGTH(enc at av) ==> i NOTIN un.t_mem) /\
    mem_agree_outside
      ({i | D <= i /\ i < D+LENGTH(enc at av)} UNION
       {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n})
      s.vs_memory t.vs_memory /\
    (!i. i NOTIN
      ({i | D <= i /\ i < D+LENGTH(enc at av)} UNION
       {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n}) ==>
      (i IN un.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all abi_encode_empty_strong_endpoint >> strip_tac >>
  `~s.vs_halted` by fs[abi_encoder_window_pre_def] >>
  qexistsl_tac [`s`, `G`, `tn`] >>
  simp[gas_path_ptr_rules, op_taint_def, mem_agree_outside_def]
QED

Theorem abi_encode_copy_strong_endpoint:
  !B K D.
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en dst src (AbiCopy sz) at av B K D s ==>
  window_strong_result ctx fn st en out at av D s
    ((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites fn (frag_ids st en) /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >>
  pop_assum (mk_asm "sizes") >>
  drule abi_encode_copy_code >> strip_tac >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_copy_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = sz` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
  `B < dimword(:256) /\ D < dimword(:256) /\ sz < dimword(:256)` by decide_tac >>
  `eval_operand (Lit (n2w sz)) s = SOME (n2w sz)` by simp[eval_operand_def] >>
  drule_all window_emit_copy_run >> strip_tac >>
  `abi_encoder_extend_sim ctx fn s
    ((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites fn (frag_ids st en))
    [(D,sz)] s ((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `mcopy D B sz s` >>
     simp[abi_encoder_registered_output_copy, abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st en) [(D,sz)] s
    ((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites fn (frag_ids st en)`, `[(D,sz)]`] >>
     simp[window_alloca_sites_subset]) >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, mcopy_mem_bytes_at_same, abi_encoder_extend_sim_sim] >>
  drule_all window_copy_state_resources >>
  disch_then (qspecl_then [`B`, `sz`, `LENGTH en.cs_current_insts`, `D`] mp_tac) >>
  simp[] >> strip_tac >> conj_tac >- asm "sizes" ACCEPT_TAC >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

(* The semantic read capacity, rather than the encoded size, owns the source. *)
Theorem abi_encode_copy_entry_check:
  !B cap D C.
  abi_encoder_window_pre ctx fn st en (Var dst) src (AbiCopy sz) at av B cap D s /\
  ~ctx_has_dalloca ctx /\ op_taint tn src = {} /\
  op_taint tn (Var dst) = {} /\
  LENGTH (enc at av) <= C /\ sz < dimword(:256) /\
  (0 < C ==> ptr_covers G tn dst s C) /\
  (0 < cap ==> ?q. src = Var q /\ ptr_covers G tn q s cap) ==>
  ptr_inst_ok gasD 0 fuel ctx fn G tn
    (mk_inst id MCOPY [Var dst;src;Lit (n2w sz)] []) s
Proof
  rpt gen_tac >> strip_tac >>
  `sz <= cap /\ LENGTH (enc at av) = sz /\
   eval_operand src s = SOME (n2w B) /\
   eval_operand (Var dst) s = SOME (n2w D)` by
    (fs[abi_encoder_window_pre_def, abi_encoder_window_copy_iff] >>
     metis_tac[LENGTH_mem_bytes_at_proof]) >>
  Cases_on `sz = 0`
  >- (gvs[] >> irule ptr_inst_ok_mcopy_zero >> metis_tac[]) >>
  `0 < cap /\ 0 < C` by decide_tac >>
  `?q. src = Var q /\ ptr_covers G tn q s cap` by metis_tac[] >>
  `ptr_covers G tn dst s sz /\ ptr_covers G tn q s sz` by
    (fs[ptr_covers_def] >> rpt conj_tac >>
     rpt (first_assum $ irule_at Any) >> decide_tac) >>
  gvs[] >> irule ptr_inst_ok_mcopy >> simp[w2n_n2w, LESS_MOD]
QED

Theorem abi_encode_copy_fetch:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,en) /\
  fn_has_code st en fn ==>
  en.cs_current_bb = st.cs_current_bb /\
  LENGTH en.cs_current_insts = SUC (LENGTH st.cs_current_insts) /\
  ?bb. lookup_block st.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH st.cs_current_insts) =
      SOME (mk_inst st.cs_next_id MCOPY [dst;src;Lit (n2w sz)] [])
Proof
  strip_tac >> drule abi_encode_copy_code >> strip_tac >>
  `en.cs_current_bb = st.cs_current_bb /\
   en.cs_current_insts = st.cs_current_insts ++
     [mk_inst st.cs_next_id MCOPY [dst;src;Lit (n2w sz)] []]` by
    gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  simp[] >> drule_all fn_has_code_same_block >> strip_tac >>
  qexists_tac `bb` >> simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem abi_encode_copy_counted_endpoint:
  !B cap D.
  compile_abi_encode_to_buf (Var dst) src (AbiCopy sz) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) src (AbiCopy sz) at av B cap D s /\
  B < dimword(:256) /\ D < dimword(:256) /\ sz < dimword(:256) /\
  ptr_inst_ok gasD 0 0 ctx fn G tn
    (mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] []) s ==>
  gas_path_ptr gasD 0 ctx fn PG G tn s 0 G
    (step_taint (mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] [])
      s (mcopy D B sz s) tn)
    (OK ((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  `fn_has_code st en fn /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\
   s.vs_inst_idx = LENGTH st.cs_current_insts /\
   eval_operand src s = SOME (n2w B) /\
   eval_operand (Var dst) s = SOME (n2w D)` by
    fs[abi_encoder_window_pre_def] >>
  drule_all abi_encode_copy_fetch >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id MCOPY
     [Var dst;src;Lit (n2w sz)] []) s = OK (mcopy D B sz s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def, w2n_n2w]) >>
  `step_prov PG G (mk_inst st.cs_next_id MCOPY
     [Var dst;src;Lit (n2w sz)] []) (mcopy D B sz s) = G` by
    simp[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
         DRESTRICT_UNIV] >>
  `gas_path_ptr_edge gasD 0 ctx fn PG G tn s 0 G
    (step_taint (mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] [])
      s (mcopy D B sz s) tn)
    (OK ((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts))` by
    (`(mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] []).inst_opcode <> INVOKE /\
      ~is_terminator (mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] []).inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME
        (mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] [])` by simp[] >>
     drule_all straight_line_ptr_edge >>
     disch_then (qspec_then `PG` mp_tac) >>
     asm_rewrite_tac[] >> simp[mk_inst_def]) >>
  `~((mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts).vs_halted` by
    simp[mcopy_def, write_memory_with_expansion_def] >>
  metis_tac[gas_path_ptr_rules, ADD_CLAUSES]
QED

Theorem abi_encode_copy_taint_endpoint:
  !B D sz.
  eval_operand dst s = SOME (n2w D) /\ eval_operand src s = SOME (n2w B) /\
  B < dimword(:256) /\ D < dimword(:256) /\ sz < dimword(:256) /\
  (!i. B <= i /\ i < B+sz ==> i NOTIN tn.t_mem) ==>
  (step_taint (mk_inst id MCOPY [dst;src;Lit (n2w sz)] [])
    s (mcopy D B sz s) tn).t_var = tn.t_var /\
  (step_taint (mk_inst id MCOPY [dst;src;Lit (n2w sz)] [])
    s (mcopy D B sz s) tn).t_mem =
      tn.t_mem DIFF {i | D <= i /\ i < D+sz}
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Lit (n2w sz)) s = SOME (n2w sz:bytes32)` by
    simp[eval_operand_def] >>
  qpat_assum `eval_operand dst s = _`
    (mp_then (Pos hd) mp_tac mcopy_operand_ghost_frame) >>
  disch_then (fn th => qpat_assum `eval_operand src s = _`
    (mp_then (Pos hd) mp_tac th)) >>
  disch_then (fn th => qpat_assum `eval_operand (Lit _) s = _`
    (mp_then (Pos hd) mp_tac th)) >>
  simp[w2n_n2w] >> strip_tac >> simp[] >>
  `{D+i | i < sz /\ B+i IN tn.t_mem} = {}` by
    (simp[EXTENSION] >> rpt strip_tac >>
     first_x_assum (qspec_then `B+i` mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[UNION_EMPTY]
QED

Theorem abi_encode_copy_resource_contract:
  !B cap D C.
  compile_abi_encode_to_buf (Var dst) src (AbiCopy sz) st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) src (AbiCopy sz) at av B cap D s /\
  fresh_vars_wrt limit s /\ ~ctx_has_dalloca ctx /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  B < dimword(:256) /\ D < dimword(:256) /\
  LENGTH (enc at av) <= C /\ LENGTH (enc at av) < dimword(:256) /\
  (0 < C ==> ptr_covers G tn dst s C) /\
  (0 < cap ==> ?q. src = Var q /\ ptr_covers G tn q s cap) /\
  (!i. B <= i /\ i < B+cap ==> i NOTIN tn.t_mem) ==>
  ?t H un.
    window_strong_result ctx fn st en out at av D s t /\
    gas_path_ptr gasD 0 ctx fn PG G tn s 0 H un (OK t) /\
    op_taint un out = {} /\
    (!q. out = Var q ==> not_fresh_at en q) /\ fresh_vars_wrt limit t /\
    (!q. not_fresh_at st q ==>
       lookup_var q t = lookup_var q s /\ FLOOKUP H q = FLOOKUP G q /\
       op_taint un (Var q) = op_taint tn (Var q)) /\
    (0 < C ==> ptr_covers H un dst t C) /\
    (!i. D <= i /\ i < D+LENGTH(enc at av) ==> i NOTIN un.t_mem) /\
    mem_agree_outside
      ({i | D <= i /\ i < D+LENGTH(enc at av)} UNION
       {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n})
      s.vs_memory t.vs_memory /\
    (!i. i NOTIN
      ({i | D <= i /\ i < D+LENGTH(enc at av)} UNION
       {i | ?id b n. id IN window_alloca_sites fn (frag_ids st en) /\
          FLOOKUP t.vs_allocas id = SOME(b,n) /\ b <= i /\ i < b+n}) ==>
      (i IN un.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `sz <= cap /\ LENGTH (enc at av) = sz /\
   eval_operand src s = SOME (n2w B) /\
   eval_operand (Var dst) s = SOME (n2w D)` by
    (fs[abi_encoder_window_pre_def, abi_encoder_window_copy_iff] >>
     metis_tac[LENGTH_mem_bytes_at_proof]) >>
  `sz < dimword(:256)` by metis_tac[] >>
  drule_all abi_encode_copy_entry_check >>
  disch_then (qspecl_then [`st.cs_next_id`, `gasD`, `0`] assume_tac) >>
  drule_all abi_encode_copy_counted_endpoint >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule_all abi_encode_copy_strong_endpoint >> strip_tac >>
  `!i. B <= i /\ i < B+sz ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> qpat_x_assum `!i. B <= i /\ i < B+cap ==> _`
       (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  drule_all abi_encode_copy_taint_endpoint >>
  disch_then (qspec_then `st.cs_next_id` strip_assume_tac) >>
  drule abi_encode_copy_code >> strip_tac >>
  `mem_agree_outside {i | D <= i /\ i < D+sz} s.vs_memory (mcopy D B sz s).vs_memory` by
    (simp[mem_agree_outside_def] >> rpt strip_tac >> sym_tac >>
     irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
  qexistsl_tac [`(mcopy D B sz s) with vs_inst_idx := LENGTH en.cs_current_insts`,
    `G`, `step_taint (mk_inst st.cs_next_id MCOPY [Var dst;src;Lit (n2w sz)] [])
       s (mcopy D B sz s) tn`] >>
  simp[op_taint_def] >>
  conj_tac >- metis_tac[abi_encode_clean_copy_fresh] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- (strip_tac >> fs[ptr_covers_def, op_taint_def, lookup_var_def] >>
      simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def]) >>
  fs[mem_agree_outside_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED
