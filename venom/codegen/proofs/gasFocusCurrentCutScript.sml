Theory gasFocusCurrentCut
Ancestors
  gasFocusCurrentCursor dftFinitePacketReachability dftGasInvForwardActive
  dftFinitePacket dftRunRel dftGasInvCrossingProbe dftGasFromListTraceDefs
  memSafeRun unitMemInv o1SafeUpto stepWriteFootprintBase contextRawReachable contextCodegenRel codegenSymRel
  frameJointTransition frameJointTrace venomExecSemantics venomExecProps
  venomState venomWf venomInst asmOptimizer gasEvents dftDefs venomEffects
  finite_map list rich_list words arithmetic

Theorem focus_current_visit_cut:
  dft_focus_packet_rel N ((stage:num -> venom_context) 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  (!raw sf src_inst u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
    raw_reachable (root_entry with vs_gas_readings := raw ++ [0w])
      (stage 7) sf src_inst u /\
    gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w])))
      (root_entry with vs_gas_readings := raw ++ [0w]) u ==>
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7))) ==>
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ((inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
          (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
          EL q xs = inst8 /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst8.inst_opcode ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `dft_focus_packet_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [dft_focus_packet_rel_def]) >>
  strip_tac >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac [joint_config_11] >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  rename1 `FLOOKUP acts p = SOME (sf,fn8,inc,entry,live_order,NONE,NONE)` >>
  rename1 `FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,in_state,h0,body_opt,done,OK s8,F,NONE)` >>
  rename1 `get_instruction bt s8.vs_inst_idx = SOME inst8` >>
  qexistsl [`sf`,`inc`,`entry`,`live_order`,`NONE`,`NONE`,`bb`,`bt`,`ps`,`xs`,
    `ys`,`sched`,`in_state`,`h0`,`body_opt`,`done`,`OK s8`,`F`,`NONE`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mk_asm "current_guard") >>
  qpat_assum `FLOOKUP acts p = SOME (sf,fn8,inc,entry,live_order,NONE,NONE)`
    (fn activation =>
      qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
        (fn th => qpat_assum `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,sched,in_state,h0,body_opt,done,OK s8,F,NONE)`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [activation] o MATCH_MP th))) >>
  qpat_assum `!a sf tf inc entry order res nrest. _ ==> MEM sf _ /\ _`
    (fn th => qpat_assum `FLOOKUP acts p = SOME (sf,fn8,inc,entry,live_order,NONE,NONE)`
      (strip_assume_tac o MATCH_MP th)) >>
  namedCases_on `body_opt` ["", "body_pair"]
  >- (qpat_x_assum `case NONE of
        NONE => phi_prefix_length _ <= s8.vs_inst_idx /\ _ | SOME v => _`
        (strip_assume_tac o SRULE []) >>
      `is_pseudo inst8.inst_opcode` by
        (`s8.vs_inst_idx < LENGTH ps + LENGTH ys` by decide_tac >>
         qpat_assum `get_instruction bt _ = SOME inst8` mp_tac >>
         qpat_assum `bt.bb_instructions = ps ++ ys`
           (fn layout => qpat_assum `s8.vs_inst_idx < LENGTH ps + LENGTH ys`
             (fn h => qpat_assum `s8.vs_inst_idx < LENGTH ps`
               (fn h' => simp[NoAsms,get_instruction_def,EL_APPEND_EQN,layout,h,h']))) >>
         disch_then (SUBST1_TAC o SYM) >>
         qpat_assum `EVERY _ ps` (mp_tac o SRULE [EVERY_EL]) >>
         disch_then irule >> first_assum ACCEPT_TAC) >>
      asm "current_guard" mp_tac >>
      qpat_assum `is_pseudo inst8.inst_opcode` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> Cases_on `inst8.inst_opcode` >>
      simp[is_pseudo_def,is_terminator_def,dftGasInvCrossingProbeTheory.inv_memory_observation_def,
           dftDefsTheory.is_fallible_def,venomEffectsTheory.opcode_fail_class_def]) >>
  PairCases_on `body_pair` >>
  rename1 `FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,sched,in_state,h0,SOME (be,hbe),done,OK s8,F,NONE)` >>
  qpat_x_assum `case SOME (_,_) of
    NONE => phi_prefix_length _ <= s8.vs_inst_idx /\ _ | SOME v => _`
    (strip_assume_tac o SRULE []) >>
  qabbrev_tac `q = EL done sched` >>
  `q = EL done sched` by simp[Abbr `q`] >>
  `LENGTH ps <= s8.vs_inst_idx /\ s8.vs_inst_idx - LENGTH ps = done` by simp[] >>
  `done < LENGTH sched /\ q < LENGTH xs /\ EL q xs = inst8 /\
   EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
   (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE done sched))` by
    (asm "current_guard" assume_tac >>
     drule_all focus_current_guard_schedule >> disch_then ACCEPT_TAC) >>
  qabbrev_tac `z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` >>
  `z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` by simp[Abbr `z`] >>
  `EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst8` by
    (drule_all dft_packet_cut_instruction >> disch_then SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum
    `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
       body_entry count front closed brest q z. _`
    (qspecl_then [`p`,`d`,`sf`,`fn8`,`inc`,`entry`,`live_order`,`NONE`,`NONE`,
      `bb`,`bt`,`ps`,`xs`,`ys`,`sched`,`in_state`,`h0`,`SOME (be,hbe)`,`done`,
      `OK s8`,`F`,`NONE`,`q`,`z`] mp_tac) >>
  (impl_tac >-
    (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     disj1_tac >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qexistsl [`q`,`z`,`inst8`,`cuts`,`levels`,`Mcut`,`Ecut`,`Kcut`,`mr`,`er`,`kr`] >>
  conj_tac >- (sym_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (disj1_tac >>
     qpat_assum `s8.vs_inst_idx - LENGTH ps = done` SUBST1_TAC >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms])) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `!i ai ds ei qi zi. _` mp_tac >>
      pure_rewrite_tac [pairTheory.pair_CASE_def] >> simp_tac bool_ss []) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  `raw_slots = Mcut ++ mr` by
    (qpat_assum `raw_slots = AM []` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `sites = AE []` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qpat_assum `AK [] = Kcut ++ kr` mp_tac >>
     qpat_assum `AK = _` (fn th => pure_rewrite_tac [th]) >>
     simp_tac bool_ss []) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  `!fuel gs tail events u.
      N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
      rooted_eval fuel (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
        (events,OK u) ==>
      raw_reachable (root_entry with vs_gas_readings := gs ++ tail) (stage 7) sf inst8 u /\
      u.vs_gas_readings = tail /\
      (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
      (inv_memory_observation inst8.inst_opcode ==>
        (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
        u.vs_initial_fmp = s8.vs_initial_fmp)` by
    (map_every qx_gen_tac [`fuel`,`gs`,`tail`,`events`,`u`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
       (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `rooted_eval fuel _ _ _ = (events,OK u)`
       (fn th => pure_rewrite_tac [th]) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     `MEM ((p,d,inst8.inst_id),sf,inst8,u)
        (trace_blocks [] 0 fuel (stage 7) root_sf
          (root_entry with vs_gas_readings := gs ++ tail))` by
       (qpat_assum `trace_blocks [] 0 fuel _ _ _ = _` SUBST1_TAC >>
        qpat_assum `EL (LENGTH z) _ = inst8` SUBST1_TAC >>
        simp[NoAsms]) >>
     `raw_reachable (root_entry with vs_gas_readings := gs ++ tail) (stage 7) sf inst8 u` by
       (irule dftFinitePacketReachabilityTheory.dft_packet_trace_raw_reachable >>
        qpat_assum `MEM ((p,d,inst8.inst_id),sf,inst8,u) _` (irule_at Any) >>
        qexistsl [`nm`,`lbl`] >> simp[]) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (strip_tac >>
        `active_inst sf inst8 u` by
          (qpat_assum `raw_reachable _ (stage 7) sf inst8 u` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[raw_reachable_active]) >>
        `wf_function sf` by
          (qpat_assum `dft_fn_rel sf fn8` mp_tac >> simp[NoAsms,dftRunRelTheory.dft_fn_rel_def]) >>
        `MEM inst8 bb.bb_instructions` by
          (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
           qpat_assum `EL q xs = inst8` (SUBST1_TAC o SYM) >>
           simp[NoAsms,MEM_APPEND] >> disj2_tac >> irule EL_MEM >> first_assum ACCEPT_TAC) >>
        `u.vs_current_bb = bb.bb_label` by
          (irule dft_packet_active_block >>
           qpat_assum `lookup_block bb.bb_label sf.fn_blocks = SOME bb` (irule_at Any) >>
           qpat_assum `active_inst sf inst8 u` (irule_at Any) >> simp[]) >>
        qpat_assum `lookup_block s8.vs_current_bb fn8.fn_blocks = SOME bt`
          (strip_assume_tac o MATCH_MP simplifyCfgDefsTheory.lookup_block_member_label) >>
        `active_inst fn8 inst8 s8` by
          (simp[NoAsms,active_inst_def] >> qexists_tac `bt` >>
           ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
           qpat_assum `get_instruction bt _ = SOME inst8`
             (mp_tac o SIMP_RULE (srw_ss()) [get_instruction_def]) >>
           simp_tac bool_ss [AllCaseEqs()]) >>
        strip_tac >>
        `in_revert_forward fn8 s8` suffices_by simp[] >>
        qpat_assum `fn8 = dft_fn sf` SUBST_ALL_TAC >>
        irule dftGasInvForwardActiveTheory.inv_forward_active >>
        rpt (first_assum (irule_at Any)) >>
        qpat_assum `u.vs_current_bb = bb.bb_label` SUBST1_TAC >>
        qpat_assum `bt.bb_label = bb.bb_label` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC) >>
     disch_tac >>
     qpat_assum `inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==> _`
       (fn th => MATCH_MP_TAC th) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac [`fuel`,`gs`,`tail`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!F gs tail. _ ==> levels_ok _ _ _ _ _ _ _ _ _ /\ _`
        (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (CONJUNCTS_THEN2 (K all_tac) ACCEPT_TAC)) >>
  conj_tac
  >- (map_every qx_gen_tac [`fuel`,`gs`,`tail`,`n`,`u`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!F gs tail events u. _` (drule_all_then strip_assume_tac) >>
      conj_tac
      >- (`LENGTH gs = LENGTH Mcut` by
             (qpat_assum `LIST_REL _ Mcut gs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
              simp[NoAsms]) >>
          `gas_cut n (root_entry with vs_gas_readings := gs ++ tail) u` by
            (simp[NoAsms,gas_cut_def] >>
             qpat_assum `u.vs_gas_readings = tail` SUBST1_TAC >>
             qpat_assum `LENGTH gs = LENGTH Mcut` SUBST1_TAC >>
             simp[NoAsms] >> first_assum ACCEPT_TAC) >>
          qpat_x_assum `mem_inv _ _ _`
            (strip_assume_tac o SIMP_RULE bool_ss [mem_inv_raw_reachable]) >>
          first_x_assum irule >> conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`raw`,`fuel`,`u`] >> ntac 2 strip_tac >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut (TAKE (LENGTH Mcut) raw)` by
    (qpat_assum `LIST_REL _ raw_slots raw`
       (qspec_then `LENGTH Mcut` mp_tac o MATCH_MP EVERY2_TAKE) >>
     qpat_assum `raw_slots = Mcut ++ mr` SUBST1_TAC >> simp[NoAsms,TAKE_LENGTH_APPEND]) >>
  qabbrev_tac `gs = TAKE (LENGTH Mcut) raw` >>
  qabbrev_tac `tail = DROP (LENGTH Mcut) raw ++ [0w]` >>
  qpat_assum `!F gs tail events u. _`
    (qspecl_then [`fuel`,`gs`,`tail`,`Ecut`,`u`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `LENGTH gs = LENGTH Mcut` by
    (qpat_assum `LIST_REL _ Mcut gs` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[NoAsms]) >>
  qabbrev_tac `n = MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))` >>
  `gas_cut n (root_entry with vs_gas_readings := gs ++ tail) u` by
    (simp[NoAsms,gas_cut_def] >>
     qpat_assum `u.vs_gas_readings = tail` SUBST1_TAC >>
     qpat_assum `LENGTH gs = LENGTH Mcut` SUBST1_TAC >>
     simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  `gs ++ tail = raw ++ [0w]` by
    simp[NoAsms,Abbr `gs`,Abbr `tail`,GSYM APPEND_ASSOC,TAKE_DROP] >>
  qpat_assum `!raw sf src_inst u. _`
    (qspecl_then [`raw`,`sf`,`inst8`,`u`] mp_tac) >>
  qpat_assum `Abbrev (n = _)`
    (fn th => PURE_ONCE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `gs ++ tail = raw ++ [0w]` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >> simp[]
QED
