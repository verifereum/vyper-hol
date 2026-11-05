(* Exact semantic endpoint for the primitive word encoder. *)
Theory bodyPtrAbiEncodeWordContract
Ancestors
  bodyPtrDefs ptrDiscipline fragExecPtr abiEncoderReentryLeaves abiEncoderAdmissible
  bodyPtrAbiEncodeWordChecks fragExec fragGasSeqPtr fragGasPathPtr
  bodyPtrAbiEncodeBaseContract abiEncoderWindowLeaves abiEncoderWindowContract
  abiEncoderWindow abiEncoderExtendSim abiEncoderRegisteredEffect
  abiEncoderMemory abiEncoderInput abiEncoderOpenInput abiEncoder abiEncoderPrimitiveEffect
  abiEncoderLeaves contractABI valueEncoding valueEncodingProps valueEncodingProofs
  emitHelperProps exprLoweringProps compileEnv emitHelper venomState
  venomExecSemantics venomInst words finite_map pred_set list arithmetic

Theorem abi_encode_word_strong_endpoint:
  !B cap D.
  compile_abi_encode_to_buf dst src AbiPrimWord st = (out,en) /\
  abi_encoder_window_pre ctx fn st en dst src AbiPrimWord at av B cap D s ==>
  window_strong_result ctx fn st en out at av D s
    ((mstore D (mload B s)
      (update_var (STRING #"%" (toString st.cs_next_var)) (mload B s) s))
      with vs_inst_idx := LENGTH en.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >>
  `!i b n. i IN window_alloca_sites fn (frag_ids st en) /\
     FLOOKUP s.vs_allocas i = SOME (b,n) ==> n = 32` by
    metis_tac[window_pre_sites] >> pop_assum (mk_asm "sizes") >>
  qpat_x_assum `abi_encoder_window_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [abi_encoder_window_pre_def]) >>
  fs[abi_encoder_window_word_iff] >>
  qpat_x_assum `!inst b sz. _ ==> _` kall_tac >>
  `LENGTH (enc at av) = 32` by metis_tac[LENGTH_mem_bytes_at_proof] >>
  `s.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
  `B < dimword(:256) /\ D < dimword(:256)` by decide_tac >>
  `!x. dst = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all window_word_run >> strip_tac >>
  `abi_encoder_extend_sim ctx fn s
    (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_run_sequence_extend_sim >>
     (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_encoder_registered_effect (window_alloca_sites fn (frag_ids st en))
    [(D,32)] s (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `t` >>
     (conj_tac >-
       (irule abi_encoder_registered_effect_trans >>
        qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (mload B s) s` >>
        simp[abi_encoder_registered_update_var, abi_encoder_output_store])) >>
     simp[abi_encoder_registered_inst_idx]) >>
  `abi_encoder_registered_effect (frag_ids st en) [(D,32)] s
    (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`window_alloca_sites fn (frag_ids st en)`, `[(D,32)]`] >>
     simp[window_alloca_sites_subset]) >>
  drule abi_encoder_extend_sim_sim >> strip_tac >>
  simp_tac bool_ss [window_strong_result_def, abi_encoder_window_result_def] >>
  simp[eval_operand_def, abi_encoder_extend_sim_sim] >>
  drule_all window_word_state_resources >>
  disch_then (qspecl_then [`mload B s`, `st`, `LENGTH en.cs_current_insts`, `D`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[abi_encoder_word_window, mstore_mem_word_at_same, update_var_def,
    GSYM mem_word_at_eq_mload, mstore_def, write_memory_with_expansion_def] >>
  asm "sizes" ACCEPT_TAC
QED

Theorem abi_encode_word_counted_endpoint:
  !B cap D.
  compile_abi_encode_to_buf (Var dst) (Var src) AbiPrimWord st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) (Var src) AbiPrimWord at av B cap D s /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  B < dimword(:256) /\ D < dimword(:256) /\
  (!i. B <= i /\ i < B+32 ==> i NOTIN tn.t_mem) /\ ~ctx_has_dalloca ctx ==>
  ?H un.
    gas_path_ptr gasD 0 ctx fn PG G tn s 0 H un
      (OK ((mstore D (mload B s)
        (update_var (STRING #"%" (toString st.cs_next_var)) (mload B s) s))
        with vs_inst_idx := LENGTH en.cs_current_insts)) /\
    un.t_mem = tn.t_mem DIFF {i | D <= i /\ i < D+32} /\
    (!q. not_fresh_at st q ==> FLOOKUP H q = FLOOKUP G q /\
       op_taint un (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var src) s = SOME (n2w B) /\
   eval_operand (Var dst) s = SOME (n2w D) /\ not_fresh_at st dst /\
   fn_has_code st en fn /\ ~s.vs_halted /\
   s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts` by
    (fs[abi_encoder_window_pre_def] >> metis_tac[]) >>
  `!x. Var dst = Var x ==> not_fresh_at st x` by simp[] >>
  drule_all window_word_run >> strip_tac >>
  `lookup_var src s = SOME (n2w B) /\ lookup_var dst s = SOME (n2w D)` by
    fs[eval_operand_def] >>
  `!i. w2n (n2w B:bytes32) <= i /\ i < w2n (n2w B:bytes32)+32 ==>
       i NOTIN tn.t_mem` by simp[w2n_n2w] >>
  drule_all abi_encode_word_emitted_checks >>
  disch_then (qspecl_then [`fn`, `PG`, `gasD`] strip_assume_tac) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, inst_extends_def] >>
     qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp_tac bool_ss [rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `l` >>
     pure_asm_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
  drule_all run_inst_seq_gas_path_ptr >>
  drule abi_encode_word_emitted_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st en) = LENGTH en.cs_current_insts` by
    fs[inst_extends_def] >>
  simp[mk_inst_def, w2n_n2w] >> strip_tac >>
  qexistsl_tac [`Gf`, `tnf`] >> simp[w2n_n2w]
QED

Theorem abi_encode_word_resource_contract:
  !B cap D C.
  compile_abi_encode_to_buf (Var dst) src AbiPrimWord st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) src AbiPrimWord at av B cap D s /\
  en.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  ~ctx_has_dalloca ctx /\ not_fresh_at st dst /\
  B < dimword(:256) /\ D < dimword(:256) /\ LENGTH (enc at av) <= C /\
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
  `32 <= cap /\ LENGTH (enc at av) = 32 /\ alloca_inv s /\ alloca_room ctx fn s` by
    (fs[abi_encoder_window_pre_def, abi_encoder_window_word_iff] >>
     metis_tac[LENGTH_mem_bytes_at_proof]) >>
  `0 < C /\ 0 < cap` by decide_tac >>
  `?q. src = Var q /\ ptr_covers G tn q s cap` by metis_tac[] >> gvs[] >>
  `ptr_covers G tn q s 32 /\ ptr_covers G tn dst s 32` by
    (fs[ptr_covers_def] >> rpt conj_tac >>
     rpt (first_assum $ irule_at Any) >> decide_tac) >>
  `!i. B <= i /\ i < B+32 ==> i NOTIN tn.t_mem` by
    (rpt strip_tac >> qpat_x_assum `!i. B <= i /\ i < B+cap ==> _`
      (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
  drule_all abi_encode_word_counted_endpoint >>
  disch_then (qspecl_then [`gasD`, `PG`] strip_assume_tac) >>
  drule_all abi_encode_word_strong_endpoint >> strip_tac >>
  drule abi_encode_word_trace >> strip_tac >>
  `st.cs_next_var < limit.cs_next_var` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `window_strong_result ctx fn st en out at av D s t` >>
  `fresh_vars_wrt limit t` by
    fs[Abbr `t`, fresh_vars_wrt_def] >>
  `!q. not_fresh_at st q ==> lookup_var q t = lookup_var q s` by
    (simp[Abbr `t`] >> drule_all window_word_state_resources >> metis_tac[]) >>
  `mem_agree_outside {i | D <= i /\ i < D+32} s.vs_memory t.vs_memory` by
    (simp[Abbr `t`, mem_agree_outside_def] >> rpt strip_tac >>
     `s.vs_memory = (update_var (STRING #"%" (toString st.cs_next_var)) (mload B s) s).vs_memory` by
       simp[update_var_def] >>
     pop_assum SUBST1_TAC >> sym_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[op_taint_def] >>
  conj_tac
  >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  fs[mem_agree_outside_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* One static-info boundary covers all admissible nonrecursive descriptors. *)
Theorem abi_encode_static_leaf_resource_contract:
  !B cap D C.
  abi_encoder_static_leaf ei /\
  compile_abi_encode_static_info (Var dst) src ei st = (out,en) /\
  abi_encoder_window_pre ctx fn st en (Var dst) src ei at av B cap D s /\
  en.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  ~ctx_has_dalloca ctx /\ op_taint tn src = {} /\
  op_taint tn (Var dst) = {} /\ not_fresh_at st dst /\
  B < dimword(:256) /\ D < dimword(:256) /\
  B+cap <= dimword(:256) /\ D+C <= dimword(:256) /\
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
  `compile_abi_encode_to_buf (Var dst) src ei st = (out,en)` by
    metis_tac[abi_encode_static_info_agrees] >>
  fs[abi_encoder_static_leaf_def]
  >- (gvs[] >> drule_all abi_encode_word_resource_contract >>
      disch_then (qspecl_then [`gasD`, `PG`] mp_tac) >> simp[]) 
  >- (gvs[] >> drule_all abi_encode_copy_resource_contract >>
      disch_then (qspecl_then [`gasD`, `PG`] mp_tac) >> simp[]) >>
  gvs[] >> drule_all abi_encode_empty_resource_contract >>
  disch_then (qspecl_then [`gasD`, `PG`] mp_tac) >> simp[]
QED
