(* Accumulate the linked effect over exactly the observed loop witnesses. *)
Theory bodyAbiDecodeGuardedLoopAccumulationMods
Ancestors
  bodyAbiDecodeGuardedEffectBaseMods
  bodyFullAbiDecodeOwnedStateProps[qualified,ignore_grammar]
  fragExec[qualified,ignore_grammar] venomInst[qualified,ignore_grammar]
  rich_list[qualified,ignore_grammar]
  bodyFullAbiDecodeRuntimeLoopBoundary bodyFullAbiDecodeRuntimeLoopHeaderFrame
  bodyFullAbiDecodeAge[qualified]
  bodyFullAbiDecodeLoopObservedSyntax bodyFullAbiDecodeLoopIterateObserved
  bodyFullAbiDecodeLoopPhasesObserved bodyFullAbiDecodeLoopHeaderBridge bodyFullAbiDecodeLoopLayout
  abiDecoderRecursiveLoopEntry abiDecoderRecursiveLoopLayout abiDecoderContract fragGasOriginPtrLoop
  freshWrites exprLoweringProps loweringStateRelDefs
  abiDecoderExecution abiDecoderReentry fragGasPath venomExecSemantics venomState
Libs
  bodyFullAbiDecodeRuntimeLoopSyntaxLib bodyFullAbiDecodeLoopObservedSyntaxLib
  bodyFullAbiDecodeRuntimeLoopLengthObservedLib bodyAbiDecodeGuardedEffectSyntaxLib

(* Close the checked header interface after extending only its normal packet. *)
val observed_header_effect =
  let
    val old = beta (concl abi_decode_loop_header_observed)
    val (entry, rest) = dest_imp old
    val (origin, post) = dest_imp rest
    val [t,Gf,tnf] = fst (strip_exists post)
    val vars = free_vars old
    val result = list_mk_exists ([t,Gf,tnf], mk_conj (snd (strip_exists post),
      effect (param vars "s") (param vars "tn") t tnf))
  in
    close_statement (checked "loop header" old (mk_imp (entry,mk_imp (origin,result))))
  end;

Theorem abi_decode_guarded_loop_split_entry_from_header_mods:
  ^observed_header_effect ==> ^(guarded_effect_length_body_typed ()) ==>
  ^(guarded_effect_length_split_entry ())
Proof
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (mk_asm "header_contract") >> disch_then (mk_asm "body") >>
  rpt gen_tac >> disch_then (mk_asm "child_ih") >>
  map_every qx_gen_tac [`env`,`sf`,`ty`,`tv`,`live`,`protected`,`start`,
    `final_st`,`sin`,`Gin`,`tnin`,`d`,`aid`,`counter`,`cell`,`n`,`j`,`srcbase`,`srcoff`,`h`] >>
  disch_then (fn th =>
    mk_asm "entry" (CONJUNCT1 th) >> map_every assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `opc = MLOAD` SUBST_ALL_TAC >>
  qpat_x_assum `base_op = Var input` SUBST_ALL_TAC >>
  qpat_x_assum `ip = Var counter` SUBST_ALL_TAC >>
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `dst_name` strip_assume_tac) >>
  qpat_x_assum `dst = Var dst_name` SUBST_ALL_TAC >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dyn_loop_layout >> strip_tac >>
  PairCases_on `ops` >>
  rename1 `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ loop_body =
    ((idx,child_src,child_dst),child)` >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  `?iv. idx = Var iv` by simp[] >>
  qpat_x_assum `idx = Var iv` SUBST_ALL_TAC >>
  `cs_extends returned final_st` by
    drule_then ACCEPT_TAC abiDecoderLoopCodeTheory.abi_decoder_loop_suffix_extends >>
  `cs_extends start loop_body` by
    drule_then ACCEPT_TAC abiDecoderLoopCodeTheory.abi_decoder_loop_prefix_extends >>
  `cs_extends loop_body final_st` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `returned` >> simp[]) >>
  `fn_has_code start loop_body fn` by
    (drule_all fragExecTheory.fn_has_code_split >> simp[]) >>
  drule_all abi_decode_prefix_header_tail_phases >>
  disch_then (qx_choose_then `sa` (qx_choose_then `sb` (qx_choose_then `sc`
    (qx_choose_then `sd` (qx_choose_then `se` (qx_choose_then `header_sf`
      (qx_choose_then `sg` (qx_choose_then `header_idx` strip_assume_tac)))))))) >>
  `cs_extends sa final_st` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `loop_body` >> simp[]) >>
  `cs_extends sg final_st` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `loop_body` >> simp[]) >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
  rename1 `compile_abi_decode_dyn_loop (Var dst_name) src MLOAD (Var input) hi ei asz msz
    (Var counter) cnt start = ((),final_st)` >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  `start.cs_next_var <= loop_body.cs_next_var /\ start.cs_next_id <= loop_body.cs_next_id` by decide_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  drule_all abiDecoderCodeTheory.abi_decoder_dyn_loop_code >>
  simp_tac bool_ss [abiDecoderCodeTheory.abi_decoder_code_def] >>
  disch_then (assume_tac o CONJUNCT1) >>
  `start.cs_next_var <= final_st.cs_next_var` by decide_tac >>
  `phi_prefix_length (abi_decode_position_header_insts (start.cs_next_id+1)
    (Var counter) src MLOAD (Var input) start.cs_next_var
    (FST (SND labels)) (SND (SND labels))) = 0` by
    simp[abi_decode_position_header_insts_def, abi_decode_header_insts_def,
         phi_prefix_length_def, venomInstTheory.mk_inst_def] >>
  qabbrev_tac `hdr = FST labels` >>
  qpat_x_assum `lookup_block hdr fn.fn_blocks = SOME _` (assume_tac o GSYM) >>
  `local_ptrs_reserved ce sa` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `origin` >> simp[]) >>
  mp_tac (abi_decode_loop_entry_jump_joint |> SPEC_ALL |>
          Q.INST [`dst` |-> `dst_name`, `opc` |-> `MLOAD`,
                  `base_op` |-> `Var input`, `ip` |-> `Var counter`] |> BETA_RULE) >>
  (impl_tac >- (BETA_TAC >> asm "entry" assume_tac >> asm_rewrite_tac[])) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "initial_path") (mk_asm "initial_inv")) >>
  asm_x "entry" kall_tac >>
  `!obs. fn_has_code start final_st obs ==>
    lookup_block start.cs_current_bb obs.fn_blocks = SOME
      <|bb_label := start.cs_current_bb;
        bb_instructions := start.cs_current_insts ++ [mk_inst start.cs_next_id JMP [Label hdr] []]|>` by
    (rpt strip_tac >>
     qpat_assum `Abbrev (hdr = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule (REWRITE_RULE [pairTheory.FST,pairTheory.SND]
       (Q.INST [`ops` |-> `(Var iv,child_src,child_dst)`] (SPEC_ALL abi_decoder_loop_phase_entry))) >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`asz`,`Var input`,`child_dst`,`child_src`,`ei`,`Var dst_name`,
       `returned`,`hi`,`Var counter`,`iv`,`child`,`msz`,`MLOAD`,`src`,`loop_body`] >>
     qpat_assum `Abbrev (hdr = _)` (ONCE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     asm_rewrite_tac[]) >>
  `!obs. fn_has_code start final_st obs ==> gas_path ctx obs sin 0 (OK (jump_to hdr sin))` by
    (rpt strip_tac >> irule gas_path_jump >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`<|bb_label := start.cs_current_bb;
       bb_instructions := start.cs_current_insts ++ [mk_inst start.cs_next_id JMP [Label hdr] []]|>`,
       `start.cs_next_id`,`start.cs_current_insts`] >>
     simp[venomInstTheory.basic_block_accessors]) >>
  pop_assum (mk_asm "initial_observer") >>
  rename1 `abi_decode_array_element_setup (Var counter) src (Var dst) MLOAD (Var input)
    hi ei asz msz loop_body = ((Var iv,child_src,child_dst),child)` >>
  qabbrev_tac `Inv = \k s G tn. (^loop_inv) start hdr sin Gin tnin k s G tn /\
    (^input_origin) s /\ (^taint_decreases) tnin tn /\ j <= k /\
    (^completed_robust_typed) j k s tn /\
    mem_word_at d s.vs_memory = mem_word_at d sin.vs_memory /\
    abi_decode_guarded_effect_core sin tnin s tn` >>
  `Inv j (jump_to hdr sin) Gin tnin` by
    (simp_tac bool_ss [Abbr `Inv`] >> conj_tac >- asm "initial_inv" (ACCEPT_TAC o SIMP_RULE bool_ss []) >>
     reverse conj_tac >- simp[NoAsms,jump_to_def,abi_decode_guarded_effect_core_def] >>
     irule bodyFullAbiDecodeInputOriginTheory.abi_decode_input_origin_transport >> qexistsl_tac [`sin`,`start`] >>
     asm_rewrite_tac[typedMemoryCopyTheory.typed_copy_lookup_var_jump] >> simp[jump_to_def]) >>
  `!p. not_fresh_at sa p = not_fresh_at start p` by simp[not_fresh_at_def] >>
  `not_fresh_at sa input /\ not_fresh_at sa counter /\
   not_fresh_at start counter /\ not_fresh_at start dst /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. hi = Var x ==> not_fresh_at sa x)` by
    (let
       fun live_var th =
         ACCEPT_TAC (SRULE [abi_decoder_operand_live_def, abi_decoder_older_vars_def,
                            GSYM not_fresh_at_def] th)
       fun live_op th = gen_tac >> disch_then (fn eq => live_var (REWRITE_RULE [eq] th))
     in
       asm_rewrite_tac[] >>
       conj_tac >- qpat_assum `abi_decoder_operand_live start.cs_next_var (Var input)` live_var >>
       conj_tac >- qpat_assum `abi_decoder_operand_live start.cs_next_var (Var counter)` live_var >>
       conj_tac >- qpat_assum `abi_decoder_operand_live start.cs_next_var (Var counter)` live_var >>
       conj_tac >- qpat_assum `abi_decoder_operand_live start.cs_next_var (Var dst)` live_var >>
       conj_tac >- qpat_assum `abi_decoder_operand_live start.cs_next_var src` live_op >>
       qpat_assum `abi_decoder_operand_live start.cs_next_var hi` live_op
     end) >>
  `!k s G tn. Inv k s G tn ==>
    ?u Gu tnu.
      (!H. V H ==> gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK u,Gu,tnu)) /\
      (!obs. fn_has_code sa sg obs ==> gas_path ctx obs s 0 (OK u)) /\
      (^loop_resource) start k u Gu tnu /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
      u.vs_current_bb = (if k = n then final_st.cs_current_bb else loop_body.cs_current_bb) /\
      (^frame) start s G tn u Gu tnu /\ (^input_origin) u /\
      (^taint_decreases) tnin tnu /\ (^completed_robust_typed) j k u tnu /\
      mem_word_at d u.vs_memory = mem_word_at d sin.vs_memory /\
      abi_decode_guarded_effect_core sin tnin u tnu` by
    suspend "header" >>
  pop_assum (mk_asm "header") >> asm_x "header_contract" kall_tac >>
  suspend "iterate"
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[header]:
  asm_x "body" kall_tac >> asm_x "child_ih" kall_tac >>
  qpat_x_assum `msz = type_memory_size tv` kall_tac >>
  map_every qx_gen_tac [`k`,`s`,`G`,`tn`] >>
  simp_tac bool_ss [Abbr `Inv`] >>
  disch_then (fn th => assume_tac (CONJUNCT1 (CONJUNCT1 th)) >>
    assume_tac (CONJUNCT1 (CONJUNCT1 (CONJUNCT1 th))) >>
    map_every assume_tac (CONJUNCTS th)) >>
  `cell < dimword (:256)` by
    (qsuff_tac `s.vs_alloca_next < dimword (:256)` >- (simp[]) >>
     qpat_x_assum `?H. V H` strip_assume_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
       (drule_then (assume_tac o CONJUNCT1)) >>
     drule_then assume_tac stateRelProjTheory.stmt_state_rel_alloca_room >>
     drule_then ACCEPT_TAC alloca_room_next_lt) >>
  `(^owned_decoder_state) live protected sa s G tn` by
    (BETA_TAC >> MATCH_MP_TAC (BETA_RULE abi_decode_loop_header_anchor_owned_lift |>
      SPEC_ALL |> Q.INST [`anchor` |-> `start`]) >>
     conj_tac >- qpat_assum `sa.cs_next_var = start.cs_next_var` (ACCEPT_TAC o SYM) >>
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  pop_assum (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `s.vs_current_bb = sa.cs_current_bb` by
    (qpat_assum `sa.cs_current_bb = hdr` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `?H. V H` mp_tac >>
     qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[bodyFullAbiDecodeOwnedStatePropsTheory.owned_decoder_allocas_below_fmp]) >>
  asm_x "header_contract" (fn th => mp_tac (th |> SPEC_ALL |>
    Q.INST [`j` |-> `k`, `idx` |-> `header_idx`, `sf` |-> `header_sf`,
            `exit_lbl` |-> `SND (SND (labels:string # string # string))`,
            `body_lbl` |-> `FST (SND (labels:string # string # string))`])) >>
  (impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> asm_rewrite_tac[])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
    (fn th => assume_tac th >> map_every assume_tac (CONJUNCTS th))))) >>
  `(^frame) start s G tn u Gu tnu` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     qpat_assum `!p. not_fresh_at sa p ==> _` MATCH_MP_TAC >> asm_rewrite_tac[]) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `(^loop_resource) start k u Gu tnu` by
    (BETA_TAC >> MATCH_MP_TAC (BETA_RULE abi_decode_loop_header_anchor_resource_frame |>
      SPEC_ALL |> Q.INST [`anchor` |-> `start`]) >>
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  pop_assum (assume_tac o BETA_RULE) >>
  `abi_decode_guarded_effect_core sin tnin u tnu` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl_tac [`tn`,`s`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`u`,`Gu`,`tnu`] >> BETA_TAC >>
  qpat_assum `final_st.cs_current_bb = SND (SND labels)` SUBST1_TAC >>
  qpat_assum `loop_body.cs_current_bb = FST (SND labels)` SUBST1_TAC >>
  asm_rewrite_tac[] >> simp[]
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[iterate]:
  `!obs. fn_has_code start final_st obs ==> fn_has_code sa final_st obs` by
    (rpt strip_tac >>
     drule_all_then (ACCEPT_TAC o CONJUNCT2)
       (Q.SPECL [`start`,`sa`,`final_st`] fragExecTheory.fn_has_code_split)) >>
  `!obs. fn_has_code sa final_st obs ==> fn_has_code sa sg obs` by
    (rpt strip_tac >>
     drule_all_then (ACCEPT_TAC o CONJUNCT1)
       (Q.SPECL [`sa`,`sg`,`final_st`] fragExecTheory.fn_has_code_split)) >>
  `cs_extends loop_body child` by
    (drule_all abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_shape >>
     strip_tac >> irule compileEnvTheory.cs_extends_same_block >> simp[]) >>
  `cs_extends child returned` by
    drule_then ACCEPT_TAC abiDecoderAppendTheory.cs_extends_abi_decode >>
  `cs_extends child final_st /\ cs_extends sa returned /\ cs_extends sa child` by
    (conj_tac
     >- (irule compileEnvTheory.cs_extends_trans >> qexists_tac `returned` >> simp[]) >>
     conj_tac >> irule compileEnvTheory.cs_extends_trans >> qexists_tac `loop_body` >> simp[]) >>
  `!obs. fn_has_code sa final_st obs ==>
      fn_has_code loop_body child obs /\ fn_has_code child returned obs /\
      lookup_block returned.cs_current_bb obs.fn_blocks = SOME
        <|bb_label := returned.cs_current_bb; bb_instructions := returned.cs_current_insts ++
          abi_decode_backedge_insts returned.cs_next_id iv
            (STRING #"%" (toString returned.cs_next_var)) (Var counter) hdr|>` by
    (asm_x "body" kall_tac >> asm_x "child_ih" kall_tac >> qx_gen_tac `obs` >> disch_tac >>
     conj_tac >-
       (drule_all_then ACCEPT_TAC
          (Q.SPECL [`sa`,`loop_body`,`child`,`final_st`] fragExecTheory.fn_has_code_mid)) >>
     conj_tac >-
       (drule_all_then ACCEPT_TAC
          (Q.SPECL [`sa`,`child`,`returned`,`final_st`] fragExecTheory.fn_has_code_mid)) >>
     `fn_has_code returned final_st obs` by
       (drule_all_then (ACCEPT_TAC o CONJUNCT2)
          (Q.SPECL [`sa`,`returned`,`final_st`] fragExecTheory.fn_has_code_split)) >>
     qmatch_goalsub_abbrev_tac `SOME bb` >>
     `final_st.cs_blocks = [bb] ++ returned.cs_blocks` by simp[Abbr `bb`] >>
     `fragExec$emitted_blocks returned final_st = [bb]` by
       (irule fragExecTheory.emitted_blocks_append >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `fn_has_code returned final_st obs` mp_tac >>
     simp[fragExecTheory.fn_has_code_def, Abbr `bb`]) >>
  `!obs. fn_has_code (start with cs_blocks := sa.cs_blocks) final_st obs =
          fn_has_code sa final_st obs` by
    simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  pop_assum (mk_asm "anchor_observer") >>
  `local_ptrs_reserved ce (start with cs_blocks := sa.cs_blocks) =
     local_ptrs_reserved ce start` by
    simp[NoAsms, local_ptrs_reserved_def, not_fresh_at_def] >>
  pop_assum (mk_asm "anchor_locals") >>
  `!x. not_fresh_at (start with cs_blocks := sa.cs_blocks) x = not_fresh_at start x` by
    simp[not_fresh_at_def] >>
  pop_assum (mk_asm "anchor_fresh") >>
  asm_x "child_ih" mp_tac >>
  disch_then (qspecl_then [`dec_info_needs_offset ei`,`child_dst`,`child_src`] mp_tac) >>
  rewrite_tac[] >> disch_then (mk_asm "child_packet") >>
  qabbrev_tac `Exit = \t Gf tnf. (^loop_resource) start n t Gf tnf /\
    (^frame) start sin Gin tnin t Gf tnf /\ ~t.vs_halted /\
    t.vs_current_bb = final_st.cs_current_bb /\ t.vs_inst_idx = 0 /\
    (^input_origin) t /\ (^taint_decreases) tnin tnf /\ (^completed_robust_typed) j n t tnf /\
    mem_word_at d t.vs_memory = mem_word_at d sin.vs_memory /\
    abi_decode_guarded_effect_core sin tnin t tnf` >>
  mp_tac (abi_decode_loop_iterate_observed |>
    INST_TYPE [Type.alpha |-> ``:(bool # 'a word # type_value) list # num list``] |>
    SPEC_ALL |> Q.INST [`Q` |-> `Exit`, `Obs` |-> `fn_has_code sa final_st`] |> BETA_RULE) >>
  (impl_tac >- (conj_tac >- suspend "terminal" >> suspend "successor")) >>
  suspend "composition"
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[terminal]:
  asm_x "body" kall_tac >> asm_x "child_packet" kall_tac >>
  map_every qx_gen_tac [`s`,`G`,`tn`] >> disch_tac >>
  asm "header" (qspecl_then [`n`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
    (map_every (assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV)) o CONJUNCTS)))) >>
  qexistsl_tac [`u`,`Gu`,`tnu`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `obs` >> disch_tac >>
     qpat_assum `!obs. fn_has_code sa sg obs ==> gas_path ctx obs s 0 (OK u)`
       (qspec_then `obs` MATCH_MP_TAC) >>
     qpat_assum `!obs. fn_has_code sa final_st obs ==> fn_has_code sa sg obs`
       (qspec_then `obs` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `Inv n s G tn` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >>
  disch_then (fn th =>
    mk_asm "cumulative" (List.last (CONJUNCTS (CONJUNCT1 th)))) >>
  qpat_assum `Abbrev (Exit = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  BETA_TAC >>
  qpat_x_assum `u.vs_current_bb = (if n = n then _ else _)`
    (assume_tac o REWRITE_RULE []) >>
  conj_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  conj_tac >-
    (qx_gen_tac `x` >> disch_tac >>
     asm "cumulative" (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = lookup_var x s /\ _`
       (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[successor]:
  map_every qx_gen_tac [`k`,`s`,`G`,`tn`] >> strip_tac >>
  asm "header" (qspecl_then [`k`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `u` (qx_choose_then `Gu` (qx_choose_then `tnu`
    (map_every (assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV)) o CONJUNCTS)))) >>
  `k <> n` by decide_tac >>
  qpat_x_assum `u.vs_current_bb = (if k = n then _ else _)` mp_tac >>
  qpat_assum `k <> n` (fn th => simp_tac bool_ss [th]) >> disch_tac >>
  qpat_x_assum `Inv k s G tn` mp_tac >>
  simp_tac bool_ss [Abbr `Inv`] >>
  disch_then (fn th =>
    mk_asm "cumulative" (List.last (CONJUNCTS (CONJUNCT1 th))) >>
    map_every assume_tac (CONJUNCTS (CONJUNCT2 th))) >>
  `!obs. fn_has_code sa final_st obs ==> gas_path ctx obs s 0 (OK u)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qpat_assum `!obs. fn_has_code sa sg obs ==> gas_path ctx obs s 0 (OK u)`
       (qspec_then `obs` MATCH_MP_TAC) >>
     qpat_assum `!obs. fn_has_code sa final_st obs ==> fn_has_code sa sg obs`
       (qspec_then `obs` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  rename1 `abi_decode_loop_prefix _ _ _ _ _ = (loop_labels,loop_body)` >>
  `~not_fresh_at returned (STRING #"%" (toString returned.cs_next_var))` by
    simp[NoAsms,not_fresh_at_def] >>
  (* Change the observer slice without changing the resource age. *)
  asm_x "anchor_observer" (fn obs_eq =>
  asm_x "anchor_locals" (fn locals_eq =>
  asm_x "anchor_fresh" (fn fresh_eq =>
  asm_x "body" (qspec_then `final_st` (fn th => mp_tac (th |> SPEC_ALL |>
    Q.INST [`anchor` |-> `start with cs_blocks := sa.cs_blocks`,
      `j0` |-> `j`, `w` |-> `mem_word_at d sin.vs_memory`,
      `k` |-> `k`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tnu`, `idx` |-> `Var iv`,
      `nv` |-> `STRING #"%" (toString returned.cs_next_var)`,
      `hdr_bb` |-> `<|bb_label := hdr; bb_instructions :=
        abi_decode_position_header_insts (start.cs_next_id + 1) (Var counter) src MLOAD
          (Var input) start.cs_next_var loop_body.cs_current_bb
          (SND (SND (loop_labels:string # string # string)))|>`] |>
    REWRITE_RULE [compileEnvTheory.compile_state_accfupds, obs_eq, locals_eq, fresh_eq])))))) >>
  impl_tac >- suspend "body_pre" >>
  suspend "body_post"
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[body_pre]:
  let
    val norm = [arithmeticTheory.SUB_EQUAL_0, arithmeticTheory.ADD_CLAUSES,
                arithmeticTheory.LESS_EQ_REFL,
                AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
  in
    asm_x "child_packet" (assume_tac o SIMP_RULE bool_ss norm) >>
    rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
    SIMP_TAC bool_ss norm >>
    rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
  end
  >- (qpat_assum `Var iv = Var _` (SUBST1_TAC o SRULE []) >> first_assum ACCEPT_TAC)
  >- (sym_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `loop_body.cs_current_insts = []` SUBST1_TAC >>
  rewrite_tac[listTheory.LENGTH] >> simp[]
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[body_post]:
  disch_then (DISJ_CASES_THEN
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS o CONV_RULE (REDEPTH_CONV BETA_CONV))))))
  >- (disj1_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >>
      conj_tac >-
        (qx_gen_tac `H` >> disch_tac >> irule gas_origin_ptr_path_trans >>
         qexistsl_tac [`Gu`,`u`,`tnu`] >>
         conj_tac >> first_assum (qspec_then `H` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
      qx_gen_tac `obs` >> disch_tac >>
      `gas_path ctx obs s (0 + 0) (Abort Revert_abort t)` suffices_by simp[NoAsms] >>
      irule gas_path_then >> qexists_tac `u` >>
      conj_tac >> first_assum (qspec_then `obs` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl_tac [`t`,`Gf`,`tnf`] >>
  conj_tac >-
    (qx_gen_tac `H` >> disch_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >>
     conj_tac >> first_assum (qspec_then `H` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qx_gen_tac `obs` >> disch_tac >>
     `gas_path ctx obs s (0 + 0) (OK t)` suffices_by simp[NoAsms] >>
     irule gas_path_then >> qexists_tac `u` >>
     conj_tac >> first_assum (qspec_then `obs` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
  `j <= SUC k` by simp[] >>
  `abi_decode_guarded_effect_core sin tnin t tnf` by
    (irule abi_decode_guarded_effect_compose_core >> qexistsl_tac [`tnu`,`u`] >> asm_rewrite_tac[]) >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
  >- (qx_gen_tac `x` >> disch_tac >>
      asm "cumulative" (qspec_then `x` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `!x. not_fresh_at start x ==> lookup_var x u = lookup_var x s /\ _`
        (qspec_then `x` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `!x. not_fresh_at start x ==> lookup_var x t = lookup_var x u /\ _`
        (qspec_then `x` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qx_gen_tac `i` >> strip_tac >>
  qpat_assum `!i. _ /\ _ /\ i IN tnu.t_mem ==> i IN tnin.t_mem`
    (qspec_then `i` MATCH_MP_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!i. _ /\ _ /\ i IN tnf.t_mem ==> i IN tnu.t_mem`
    (qspec_then `i` MATCH_MP_TAC) >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
QED

Resume abi_decode_guarded_loop_split_entry_from_header_mods[composition]:
  asm_x "body" kall_tac >> asm_x "child_packet" kall_tac >> asm_x "header" kall_tac >>
  disch_then (qspecl_then [`j`,`jump_to hdr sin`,`Gin`,`tnin`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  let
    val take_result = qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
      (map_every assume_tac o CONJUNCTS)))
    val physical = qx_gen_tac `H` >> disch_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gin`,`jump_to hdr sin`,`tnin`] >>
      conj_tac >- (asm "initial_path" (qspec_then `H` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
      first_assum (qspec_then `H` MATCH_MP_TAC) >> first_assum ACCEPT_TAC
    fun observer result = qx_gen_tac `obs` >> disch_tac >>
      `gas_path ctx obs sin (0 + 0) (^result)` suffices_by simp[NoAsms] >>
      irule gas_path_then >> qexists_tac `jump_to hdr sin` >>
      conj_tac >- (asm "initial_observer" (qspec_then `obs` MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
      first_assum (qspec_then `obs` MATCH_MP_TAC) >>
      first_assum (qspec_then `obs` MATCH_MP_TAC) >> first_assum ACCEPT_TAC
    val select_header = qexists_tac `sa` >>
      ntac 5 (conj_tac >- first_assum ACCEPT_TAC)
    val tail = qpat_assum `sa.cs_current_bb = hdr` SUBST1_TAC >> first_assum ACCEPT_TAC
  in
    disch_then (DISJ_CASES_THEN take_result)
    >- (select_header >> qexistsl_tac [`Abort Revert_abort t`,`Gf`,`tnf`] >>
        conj_tac >- physical >> conj_tac >- observer ``Abort Revert_abort t`` >>
        conj_tac >- tail >> disj2_tac >> qexists_tac `t` >> REFL_TAC) >>
    select_header >> qexistsl_tac [`OK t`,`Gf`,`tnf`] >> conj_tac >- physical >>
    conj_tac >- observer ``OK t`` >> conj_tac >- tail
  end >>
  qpat_x_assum `Exit t Gf tnf` mp_tac >>
  simp_tac bool_ss [Abbr `Exit`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disj1_tac >> qexists_tac `t` >>
  qpat_assum `final_st.cs_current_insts = []` SUBST1_TAC >>
  rewrite_tac[listTheory.LENGTH] >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
  >- (qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) /\ _) live`
        (mp_tac o REWRITE_RULE [listTheory.EVERY_MEM,pairTheory.FORALL_PROD]) >>
      simp[listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >>
      disch_then (fn th => rpt gen_tac >> disch_then (mp_tac o MATCH_MP (SPEC_ALL th))) >>
      simp[] >> decide_tac)
  >- (qpat_assum `output_id < start.cs_next_id` mp_tac >>
      qpat_assum `start.cs_next_id <= final_st.cs_next_id` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)
  >- (irule not_fresh_at_mono >> qexists_tac `start` >> asm_rewrite_tac[])
  >- (qpat_assum `origin.cs_next_var <= start.cs_next_var` mp_tac >>
      qpat_assum `start.cs_next_var <= final_st.cs_next_var` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac)
  >- (irule bodyFullAbiDecodeAgeTheory.abi_decode_live_age_mono >>
      qexists_tac `start` >> asm_rewrite_tac[]) >>
  qx_gen_tac `x` >> disch_tac >>
  qpat_assum `!y. not_fresh_at start y ==> lookup_var y t = lookup_var y sin /\ _`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (ACCEPT_TAC o CONJUNCT1)
QED

Finalise abi_decode_guarded_loop_split_entry_from_header_mods
