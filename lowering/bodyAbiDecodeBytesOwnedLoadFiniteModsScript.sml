Theory bodyAbiDecodeBytesOwnedLoadFiniteMods
Ancestors
  bodyFullAbiDecodeGuardReadObserved bodyFullAbiDecodeFiniteObserved
  bodyFullAbiDecodeRelativeLoadExact[qualified]
  abiDecodePtrRead fragGasSeqPtr instSeqPtrLo fragGasOriginPtrLoop
  fragExecMem instMemFrontier memSafeRun abiDecodeStaticProps
  abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  venomState venomExecSemantics venomInst venomInstProofs fragExec
  gasOriginPtrLabels ptrDiscipline unitTransformDefs freshWrites
  fragGasOriginPtr fragGasPath stateFrame words arithmetic list rich_list
  finite_map pred_set pair relation

local
  fun close tm = list_mk_forall (free_vars_lr tm, tm)
  val emit_tm = ``
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
      (t with vs_inst_idx := LENGTH sb.cs_current_insts,G',tn')``
  val (pre, post) = dest_imp (concl abi_decode_bytes_owned_load_frame_joint_observed)
  val (results, body) = strip_exists post
  val os = #1 (strip_comb (find_term (fn tm =>
    let val (head,args) = strip_comb tm
    in is_abs head andalso length args = 4 end) body))
  val finite = ``!D. RELPOW (\(u,Gu,tu) (v,Gv,tv).
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
    (LENGTH sc.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn) (t,Gf,tnf)``
  fun append_field tm =
    if is_conj tm then
      let val (l,r) = dest_conj tm in mk_conj (l, append_field r) end
    else mk_conj (tm,finite)
  val load_tm = mk_imp (pre, list_mk_exists (results, append_field body))
  fun normalize tm = rhs (concl (DEPTH_CONV BETA_CONV tm))
in
  val emitted_finite_input = close emit_tm
  val load_finite_contract = close (normalize load_tm)
  val owned_decoder_state = os
end

(* Use one ADD/MLOAD execution for the load, both ghost maps, and every fetch. *)
Theorem bytes_owned_load_finite:
  ^emitted_finite_input ==> ^load_finite_contract
Proof
  disch_then (mk_asm "emit_finite") >> rpt gen_tac >> strip_tac >>
  `abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
   lo <= s.vs_alloca_next /\
   w2n input_word+LENGTH input_bytes <= s.vs_alloca_next /\
   alloca_history fn s` by fs[] >>
  drule_all (abiDecodePtrReadTheory.abi_decode_ptr_relative_load |>
    Q.INST [`D` |-> `ARB`, `PG` |-> `PG`]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `!D. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G' tn'` by
    (gen_tac >>
     drule_all (abiDecodePtrReadTheory.abi_decode_ptr_relative_load |>
       Q.INST [`D` |-> `D`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
     qpat_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac fragGasSeqPtrTheory.inst_seq_ptr_ghost_unique) >>
     disch_then drule >> simp[] >> strip_tac >> gvs[]) >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sc) s G' tn'` by
    (gen_tac >> irule instSeqPtrLoTheory.inst_seq_ptr_zero_to_lo >>
     simp[] >> qexists_tac `D` >> simp[]) >>
  `emit_op ADD [Var input;pos] sa = (addr,sb)` by
    gvs[compile_abi_dec_addr_def] >>
  `inst_extends sa sb /\ inst_extends sb sc /\ inst_extends sa sc` by
    metis_tac[inst_extends_emit_op, inst_extends_trans] >>
  `sc.cs_current_bb = sa.cs_current_bb` by gvs[inst_extends_def] >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS) (emitted_insts sa sc)` by
    simp[mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    suspend "load_memory" >>
  `ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sc = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> dalloca_no_wrap i u` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sc)` by
       (qpat_assum `emitted_insts sa sc = pre ++ i::post`
          (fn th => pure_rewrite_tac[th]) >> simp[MEM_APPEND]) >>
     pop_assum mp_tac >>
     qpat_assum `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc`
       (fn th => pure_rewrite_tac[th]) >>
     simp[mk_inst_def] >> strip_tac >> simp[]) >>
  `((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sc.cs_current_insts) = t` by
    simp[venom_state_component_equality] >>
  suspend "load_finite"
QED

Resume bytes_owned_load_finite[load_memory]:
  `lookup_var input s = SOME input_word` by
    gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
  asm_rewrite_tac[] >>
  simp[fragExecMemTheory.run_inst_seq_mem_ok_def] >>
  conj_tac
  >- (irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [Var input;pos]
    [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      (input_word+n2w p) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  simp[] >>
  simp[instMemFrontierTheory.below_frontier_MLOAD, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (`w2n (input_word+n2w p) = w2n input_word+p` by
        (irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
      decide_tac) >>
  BasicProvers.TOP_CASE_TAC >> simp[]
QED

Resume bytes_owned_load_finite[load_finite]:
  `!D. RELPOW (\(u,Gu,tu) (v,Gv,tv).
      gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (u,Gu,tu) [] (OK v,Gv,tv))
      (LENGTH sc.cs_current_insts - LENGTH sa.cs_current_insts) (s,G,tn)
      (t,G',tn')` by
    (gen_tac >>
     qpat_assum `(_ with vs_inst_idx := _) = t`
       (fn th => pure_once_rewrite_tac [GSYM th]) >>
     asm "emit_finite" (irule o SPEC_ALL) >>
     asm_rewrite_tac[] >> simp[mk_inst_def,is_terminator_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
     (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >>
     qpat_x_assum `inst_seq_ptr ARB _ _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D 0 _ _ _ _ _ _ _ _ _` kall_tac >>
     qpat_x_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
       (qspec_then `D` assume_tac) >>
     drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >> asm_rewrite_tac[]) >>
  `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t)` by
    (qsuff_tac `!obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0
       (OK ((t with vs_inst_idx := s.vs_inst_idx) with
         vs_inst_idx := LENGTH sc.cs_current_insts))`
     >- asm_rewrite_tac[] >>
     rpt strip_tac >> irule abi_decode_finite_success_observed >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`emitted_insts sa sc`, `sa`] >>
     gvs[inst_extends_def, mk_inst_def, is_terminator_def,
         LENGTH_NIL, FILTER_EQ_NIL, EVERY_CONJ]) >>
  `isPREFIX sa.cs_current_insts sc.cs_current_insts` by
    metis_tac[inst_extends_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sa sc)` by
    simp[mk_inst_def] >>
  `alloca_history fn t` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >> metis_tac[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by simp[] >>
  `(^owned_decoder_state) sc t G' tn'` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> BETA_TAC >> asm_rewrite_tac[] >>
     qexists_tac `inst` >> asm_rewrite_tac[]) >>
  `allocas_from lo t` by
    (fs[allocas_from_def, stateFrameTheory.state_frame_def] >> metis_tac[]) >>
  `eval_operand v t = SOME (mload (w2n input_word+p) s)` by
    (qpat_assum `v = Var out` (fn th => pure_once_rewrite_tac[th]) >>
     pure_rewrite_tac[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(^owned_decoder_state) sc t G' tn'` (assume_tac o BETA_RULE) >>
  qexistsl_tac [`out`, `ap`, `t`, `G'`, `tn'`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Finalise bytes_owned_load_finite
