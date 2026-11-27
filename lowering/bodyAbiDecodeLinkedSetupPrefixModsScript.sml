(* The decoder's covered length load and payload-address calculation. *)
Theory bodyAbiDecodeLinkedSetupPrefixMods
Ancestors
  abiDecodePtrRead abiDecodePtrMemberFrame abiDecoderReentry abiEncoder
  bodyPtrIfExpBytesCounted assignTuplePtrCopyLen emitHelperProps loweringShapeRules
  freshWrites exprLoweringProps loweringStateRelDefs compileEnv exprSimAccounts
  decoderGhostFramePtr unitTransformDefs pred_set
  fragExec fragExecMem instMemFrontier instSeqPtrLo fragGasSeq fragGasSeqPtr fragGasOriginPtrLoop
  fragGasOriginPtrDead bodyFullAbiDecodeRelativeLoadExact allocasBelowFmpUpdatesProps
  stateFrame allocaHistory ptrDiscipline bodyPtrDefs
  venomExecSemantics venomInst venomState words arithmetic finite_map list rich_list

Theorem abi_decode_linked_setup_prefix_mods:
  emit_op MLOAD [data] start = (len,sa) /\
  emit_op ADD [data; Lit 32w] sa = (src,sb) /\
  fn_has_code start sb fn /\ fn_inst_ids_distinct fn /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  alloca_history fn s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  data = Var p /\ eval_operand data s = SOME (n2w b) /\
  op_taint tn data = {} /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_decode_ptr_window G tn s p (n2w b) (32 + LENGTH bs) /\
  mload b s = n2w (LENGTH bs) /\
  b + 32 + LENGTH bs <= s.vs_alloca_next /\
  b + 32 + LENGTH bs < dimword (:256) ==>
  ?u Gp tnp.
    (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK u,Gp,tnp)) /\
    (!obs. fn_has_code start sb obs ==> gas_path ctx obs s 0 (OK u)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (?input. src = Var input /\
      abi_decode_ptr_window Gp tnp u input (n2w (b+32)) (LENGTH bs)) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    op_prov Gp len = NONE /\ op_taint tnp len = {} /\ op_taint tnp src = {} /\
    abi_decoder_operand_live sb.cs_next_var len /\
    abi_decoder_operand_live sb.cs_next_var src /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
    tnp.t_mem = tn.t_mem /\ tnp.t_stor = tn.t_stor /\
    tnp.t_trans = tn.t_trans /\ tnp.t_imm = tn.t_imm /\ alloca_history fn u /\
    (!x. not_fresh_at start x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends start sa /\ cs_extends sa sb /\
   start.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[emit_op_extends_next_var] >>
  `fn_has_code sa sb fn` by (irule fn_has_code_mid >> simp[] >> qexistsl [`sb`,`start`] >> simp[cs_extends_refl]) >>
  `?lv. len = Var lv` by metis_tac[emitted_insts_emit_op] >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn p s 32 /\ lookup_var p s = SOME (n2w b) /\
   (!i. w2n (n2w b:256 word) <= i /\ i < w2n (n2w b:256 word)+32 ==>
      i NOTIN tn.t_mem)` by
    (gvs[abi_decode_ptr_window_def, ptr_covers_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> decide_tac) >>
  qpat_x_assum `data = Var p` SUBST_ALL_TAC >>
  qpat_x_assum `len = Var lv` SUBST_ALL_TAC >>
  qabbrev_tac `D0 = <|d_stor := K (K {}); d_trans := K (K {});
                       d_imm := K {}; d_ret := K {}|>` >>
  drule_all (Q.SPECL [`D0`, `ctx`, `fn`, `PG`] emit_mload_clean_seq_ptr) >>
  disch_then (qspecl_then [`fn`, `PG`, `D0`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts start sa) s = OK raw_load` >>
  rename1 `inst_seq_ptr D0 0 ctx fn PG G tn (emitted_insts start sa) s Gl tnl` >>
  `not_fresh_at start p` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  qabbrev_tac `mid = raw_load with vs_inst_idx := LENGTH sa.cs_current_insts` >>
  `~mid.vs_halted /\ mid.vs_current_bb = start.cs_current_bb /\
   mid.vs_inst_idx = LENGTH sa.cs_current_insts` by
    (qpat_assum `(raw_load with vs_vars := _) = s` mp_tac >>
     simp[Abbr `mid`, venom_state_component_equality]) >>
  `abi_decode_ptr_window Gl tnl mid p (n2w b) (32+LENGTH bs)` by
    (qpat_assum `abi_decode_ptr_window G tn s p _ _`
       (mp_then (Pat `abi_decode_ptr_window _ _ _ _ _ _`) irule abi_decode_ptr_window_frame) >>
     qpat_assum `!p. not_fresh_at start p ==> lookup_var p raw_load = _`
       (qspec_then `p` assume_tac) >>
     qpat_assum `!p. not_fresh_at start p ==> FLOOKUP Gl p = _ /\ _`
       (qspec_then `p` assume_tac) >>
     fs[Abbr `mid`, lookup_var_def]) >>
  `sa.cs_current_bb = start.cs_current_bb /\ sb.cs_current_bb = start.cs_current_bb` by
    metis_tac[emit_op_facts] >>
  `compile_abi_dec_addr (Var p) (Lit 32w) sa = (src,sb)` by
    simp[compile_abi_dec_addr_def] >>
  `eval_operand (Lit 32w) mid = SOME (n2w 32) /\
   op_taint tnl (Lit 32w) = {} /\ 32 <= 32+LENGTH bs /\
   w2n (n2w b:256 word) + (32+LENGTH bs) < dimword (:256)` by
    (simp[eval_operand_def, op_taint_def, LESS_MOD] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp mid` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     qpat_assum `(raw_load with vs_vars := _) = s` (SUBST1_TAC o SYM) >>
     simp[NoAsms, Abbr `mid`, allocas_below_fmp_updates]) >>
  drule abi_decode_ptr_address >>
  disch_then (qspecl_then [`tnl`, `mid`, `32`, `32+LENGTH bs`, `fn`, `ctx`, `n2w b`,
      `PG`, `Gl`, `D0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) mid = OK (t with vs_inst_idx := mid.vs_inst_idx)` >>
  rename1 `inst_seq_ptr D0 0 ctx fn PG Gl tnl (emitted_insts sa sb) mid Gp tnp` >>
  suspend "join"
QED

Resume abi_decode_linked_setup_prefix_mods[join]:
  qabbrev_tac `il = mk_inst start.cs_next_id MLOAD [Var p]
    [STRING #"%" (toString start.cs_next_var)]` >>
  qabbrev_tac `ia = mk_inst sa.cs_next_id ADD [Var p; Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `emitted_insts start sa = [il] /\ emitted_insts sa sb = [ia] /\
   sa.cs_current_insts = start.cs_current_insts ++ emitted_insts start sa /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (qpat_assum `emit_op MLOAD _ start = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD _ sa = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[Abbr `il`, Abbr `ia`]) >>
  `run_inst_seq (emitted_insts start sa) s = OK (mid with vs_inst_idx := s.vs_inst_idx)` by
    (qpat_assum `(raw_load with vs_vars := _) = s`
       (mp_tac o AP_TERM ``venom_state_vs_inst_idx``) >>
     simp[Abbr `mid`] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts start sa) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[Abbr `il`, Abbr `ia`, mk_inst_def, is_terminator_def] >>
  drule_all emitted_insts_join_normalized_ptr >> strip_tac >>
  `emitted_insts start sb = [il;ia]` by metis_tac[emitted_insts_append, APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
       i.inst_opcode <> GAS) (emitted_insts start sb)` by
    simp[Abbr `il`, Abbr `ia`, mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`t`, `Gp`, `tnp`] >>
  conj_tac >- suspend "origin" >>
  conj_tac >- suspend "observer" >>
  suspend "frame"
QED

Resume abi_decode_linked_setup_prefix_mods[origin]:
  `run_inst_seq_mem_ok (emitted_insts start sb) s` by
    (`run_inst_seq_mem_ok [il] s` by
       (simp[run_inst_seq_mem_ok_last, Abbr `il`, below_frontier_MLOAD,
             LESS_MOD, memSafeRunTheory.inst_dload_in_section_other, mk_inst_def] >>
        decide_tac) >>
     `!v. run_inst_seq_mem_ok [ia] v` by
       simp[run_inst_seq_mem_ok_last, Abbr `ia`, mk_inst_def,
            memSafeRunTheory.inst_dload_in_section_other, below_frontier_no_ranges] >>
     `emitted_insts start sb = [il] ++ [ia]` by simp[] >>
     pure_once_asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[]) >>
  `ctx_has_dalloca ctx ==>
   !pre i post v. emitted_insts start sb = pre ++ i::post /\
     run_inst_seq pre s = OK v ==> dalloca_no_wrap i v` by
    (rpt strip_tac >> `MEM i (emitted_insts start sb)` by simp[MEM_APPEND] >>
     qpat_x_assum `MEM i (emitted_insts start sb)` mp_tac >>
     qpat_assum `emitted_insts start sb = [il;ia]` (fn th => simp[NoAsms, th]) >>
     disch_then (DISJ_CASES_THEN SUBST1_TAC) >>
     simp[Abbr `il`, Abbr `ia`, mk_inst_def, unitTransformDefsTheory.dalloca_no_wrap_def]) >>
  `inst_extends start sb` by metis_tac[inst_extends_emit_op, inst_extends_trans] >>
  `!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts start sb) s Gp tnp` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists `D0` >>
     simp[Abbr `D0`] >>
     qpat_assum `emitted_insts start sb = [il;ia]` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  gen_tac >> strip_tac >>
  qpat_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _` (qspec_then `DF H` assume_tac) >>
  drule_all fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts`
    (fn th => simp[GSYM th, NoAsms])
QED

Resume abi_decode_linked_setup_prefix_mods[observer]:
  qx_gen_tac `obs` >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb obs.fn_blocks = SOME bb /\
        isPREFIX sb.cs_current_insts bb.bb_instructions` by
    (qpat_x_assum `fn_has_code start sb obs` mp_tac >> simp[fn_has_code_def]) >>
  `isPREFIX (emitted_insts start sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX sb.cs_current_insts _` mp_tac >>
     qpat_assum `sb.cs_current_insts = start.cs_current_insts ++ emitted_insts start sb`
       (fn th => rewrite_tac[th, IS_PREFIX_APPEND]) >>
     disch_then (qx_choose_then `rest` (fn th =>
       qexists_tac `rest` >> once_rewrite_tac[th])) >>
     qpat_assum `s.vs_inst_idx = LENGTH start.cs_current_insts`
       (fn th => pure_rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     rewrite_tac[DROP_LENGTH_APPEND]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts start sb) = t.vs_inst_idx` by simp[] >>
  `((t with vs_inst_idx := s.vs_inst_idx) with
      vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts start sb)) = t` by
    (qpat_assum `s.vs_inst_idx + LENGTH (emitted_insts start sb) = t.vs_inst_idx`
       (fn th => simp[th, NoAsms])) >>
  qpat_assum `run_inst_seq (emitted_insts start sb) s = OK (t with vs_inst_idx := _)`
    (mp_then (Pat `run_inst_seq _ _ = OK _`) mp_tac fragGasSeqTheory.tuple_run_inst_seq_gas_path) >>
  disch_then (qspecl_then [`ctx`, `obs`, `bb`] mp_tac) >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  simp[Abbr `il`, Abbr `ia`, mk_inst_def, is_terminator_def]
QED

Resume abi_decode_linked_setup_prefix_mods[frame]:
  `step_inst_base il s = OK raw_load` by
    (qpat_assum `run_inst_seq (emitted_insts start sa) s = OK raw_load` mp_tac >>
     qpat_assum `emitted_insts start sa = [il]`
       (fn th => simp[NoAsms, th, run_inst_seq_def, AllCaseEqs()])) >>
  `step_taint il s raw_load tn = tnl` by
    (qpat_assum `inst_seq_ptr D0 0 ctx fn PG G tn (emitted_insts start sa) _ _ _` mp_tac >>
     qpat_assum `emitted_insts start sa = [il]` (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `step_inst_base il s = OK raw_load`
       (fn th => simp[NoAsms, inst_seq_ptr_def, th])) >>
  `tnl.t_imm = tn.t_imm` by
    (qpat_assum `step_taint il s raw_load tn = tnl`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     simp[step_taint_nonmemory_frame, Abbr `il`, mk_inst_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_assum `(raw_load with vs_vars := _) = s` mp_tac >>
     simp[Abbr `mid`, venom_state_component_equality]) >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx)` by
    (qpat_assum `state_frame t = state_frame (mid with vs_inst_idx := _)`
       (fn th => pure_once_rewrite_tac[th]) >>
     qpat_assum `(raw_load with vs_vars := _) = s`
       (mp_tac o AP_TERM ``\z:venom_state. state_frame (z with vs_inst_idx := t.vs_inst_idx)``) >>
     simp[Abbr `mid`, state_frame_def, venom_state_component_equality, NoAsms]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `state_frame t = state_frame (s with vs_inst_idx := _)`
       (mp_tac o AP_TERM ``venom_state_vs_alloca_next``) >> simp[state_frame_def, NoAsms]) >>
  `!x. not_fresh_at start x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gp x = FLOOKUP G x /\ op_taint tnp (Var x) = op_taint tn (Var x)` by
    (qx_gen_tac `x` >> strip_tac >>
     `not_fresh_at sa x` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sa x ==> _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!p. not_fresh_at start p ==> lookup_var p raw_load = _`
       (qspec_then `x` (drule_then assume_tac)) >>
     qpat_assum `!p. not_fresh_at start p ==> FLOOKUP Gl p = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     fs[Abbr `mid`, lookup_var_def]) >>
  `alloca_history fn t` by
    (irule abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl [`s`, `start`, `sb`] >>
     simp[IS_PREFIX_APPEND, Abbr `il`, Abbr `ia`, mk_inst_def]) >>
  `abi_decoder_operand_live sa.cs_next_var (Var lv)` by
    metis_tac[abi_decoder_operand_live_emit] >>
  `not_fresh_at sa lv` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `lv` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `n2w b + 32w = (n2w (b+32):256 word)` by simp[word_add_n2w] >>
  `op_taint tnp src = {}` by fs[abi_decode_ptr_window_def, ptr_covers_def] >>
  `lookup_var lv mid = lookup_var lv raw_load` by simp[Abbr `mid`, lookup_var_def, NoAsms] >>
  `abi_decoder_operand_live sb.cs_next_var (Var lv) /\
   abi_decoder_operand_live sb.cs_next_var src` by
    metis_tac[abi_decoder_operand_live_emit, abi_decoder_operand_live_mono] >>
  fs[eval_operand_def, op_prov_def, LESS_MOD]
QED
Finalise abi_decode_linked_setup_prefix_mods
