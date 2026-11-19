Theory dftPacketPreterminalNativeAgreement
Ancestors
  dftPacketPreterminalAgreement dftPacketPreterminalGeometry
  dftPacketPreterminalRows dftPacketSuccessfulPrefixTrace
  dftPacketPreterminalOracle dftPacketRetainedOracle
  dftPacketNativeSupplierReplay dftPacketNativePrefixBoundary
  dftGasFromListTraceNames dftStructural dftDefs venomEffects passSharedDefs
  dftGasFromListReadings dftIndexedExec finite_map list rich_list sorting arithmetic dftContractGas o1PassContract venomWf dftWf

Theorem preterminal_source_gas_observed[local]:
  !q.
  xs = ordered ++ [term] /\ ys = executed ++ [term] /\
  LENGTH ordered = LENGTH executed /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) schedule ys /\
  (!r. r < LENGTH ordered ==> MEM r (TAKE (LENGTH executed) schedule)) /\
  bt.bb_instructions = ps ++ ys /\ be.vs_inst_idx = LENGTH ps /\
  EVERY (\i. ~is_terminator i.inst_opcode) executed /\
  FOLDR (dft_exec_cons fuel C) OK executed be = OK st /\
  EVERY (\kw. MEM kw obs) (trace_gas (trace_block a e fuel C tf
    (bt with bb_instructions := TAKE (LENGTH ps + LENGTH executed) bt.bb_instructions) be)) /\
  q < LENGTH ordered /\ (EL q xs).inst_opcode = GAS ==>
  ?w. MEM ((a,e,(EL q xs).inst_id),w) obs
Proof
  rpt gen_tac >> strip_tac >>
  `MEM q (TAKE (LENGTH executed) schedule)` by metis_tac[] >>
  `?k. k < LENGTH executed /\ k < LENGTH schedule /\ EL k schedule = q` by
    (qpat_x_assum `MEM q (TAKE _ _)`
       (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     `n < LENGTH executed /\ n < LENGTH schedule` by
       (Cases_on `LENGTH executed <= LENGTH schedule` >> fs[LENGTH_TAKE_EQ] >> decide_tac) >>
     qexists_tac `n` >> gvs[EL_TAKE]) >>
  `EL k ys = EL q xs` by
    (qpat_x_assum `LIST_REL _ _ _` (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
     strip_tac >> gvs[from_block_def, is_flippable_def,
       is_commutative_def, is_comparator_def]) >>
  `MEM (EL q xs) executed` by
    (simp[MEM_EL] >> qexists_tac `k` >>
     qpat_x_assum `EL k ys = _` mp_tac >> simp[EL_APPEND1]) >>
  `?w. MEM ((a,e,(EL q xs).inst_id),w)
    (trace_gas (trace_block a e fuel C tf
      (bt with bb_instructions := TAKE (LENGTH ps + LENGTH executed) bt.bb_instructions) be))` by
    (qpat_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
     irule dft_packet_successful_prefix_gas_keys >>
     simp[DROP_APPEND, TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >> metis_tac[]) >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem dft_packet_preterminal_native_agreement:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    N C7 C8 root_tf root_entry j hbe a e sf tf bb bt ps xs ys schedule
    count inst be st ms ess ks obs AM AK ms_tab es_tab ks_tab.
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  o1_ctx_shape C8 /\ MEM root_tf C8.ctx_functions /\
  dft_fn_rel sf tf /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb_well_formed bb /\ bb_well_formed bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  LENGTH xs = LENGTH ys /\ PERM schedule (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) schedule ys /\
  count < LENGTH ys /\ inst = EL count ys /\ is_terminator inst.inst_opcode /\
  be.vs_inst_idx = LENGTH ps /\
  lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
  get_instruction bt st.vs_inst_idx = SOME inst /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE count ys) be = OK st) /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\ hbe <= j /\
  EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) =
    ((a,e,inst.inst_id),tf,inst,st) /\
  obs = trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM ks_tab /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (!e. MEM e order <=> (a,e) IN FDOM blocks) /\
    (res = NONE <=> nrest = NONE) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret.
        FLOOKUP calls (parent,e,cid) = SOME (q,h,b0,done_at_call,entry,ret))) /\
  (!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) ==>
    (?sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order) /\
    (body_entry = NONE ==>
      FLOOKUP ms_tab (a,e) = SOME [] /\ FLOOKUP ks_tab (a,e) = SOME [])) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
    FLOOKUP ks_tab (a,e) = SOME ks ==>
    LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
    ALL_DISTINCT (FLAT ks) /\
    (!q. q < LENGTH xs ==>
      ((EL q xs).inst_opcode = GAS ==>
        EL q ms = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
        EL q ks = [(a,e,(EL q xs).inst_id)]) /\
      ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
        EL q ms = [] /\ EL q ks = []) /\
      ((EL q xs).inst_opcode = INVOKE ==>
        (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
          NONE => EL q ms = [] /\ EL q ks = []
        | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
            EL q ks = AK ((e,(EL q xs).inst_id)::a))))) /\
  FDOM blocks = FDOM es_tab /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    (?bb bt ps xs ys rho in_state h0 be hbe count front closed brest c.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE) /\
    (?csf ctf child_order child_res child_rest.
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      (!ir child_out caller_post. ret = SOME (ir,child_out,caller_post) ==>
        child_res = SOME (IntRet ir child_out)))) /\
  (!a sf tf inc entry order r8 u0.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
    !v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (AM a)) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
    ?h b0 done_at_call child_entry ir child_out caller_post.
      FLOOKUP calls (a,e,(EL q xs).inst_id) =
        SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (AK []) /\
  LENGTH (AM []) = LENGTH (AK []) /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs /\
  (?in_state h0. FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,schedule,in_state,h0,SOME (be,hbe),count,OK st,F,NONE)) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP es_tab (a,e) = SOME ess /\
  FLOOKUP ks_tab (a,e) = SOME ks /\
  (!F k kgss tail u.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count schedule)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    gas_events_block (F-e) C7 sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
      (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess)) /\
  (!F q kgss tail u.
    N <= F /\ q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\
    MEM q (TAKE count schedule) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
    (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count schedule)) /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms kgss /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
    (?extra. EL q ks = MAP FST (trace_gas
      (trace_step a e (F-e) C7 sf (EL q xs) u)) ++ extra) /\
    (!v. step_inst (F-e) C7 (EL q xs) u = OK v ==>
      EL q ks = MAP FST (trace_gas (trace_step a e (F-e) C7 sf (EL q xs) u)))) ==>
  ?ordered executed.
    xs = ordered ++ [inst] /\ ys = executed ++ [inst] /\
    count = LENGTH executed /\ LENGTH ordered = LENGTH executed /\
    EVERY IS_SOME (FLAT (TAKE (LENGTH ordered) ms)) /\
    (!F kgss tail.
      N <= F /\ LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
        (TAKE (LENGTH ordered) ms) kgss ==>
      FOLDR (dft_exec_cons (F-e) C7) OK ordered
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK (st with vs_gas_readings := tail) /\
      gas_events_block (F-e) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ ordered|>
        (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE (LENGTH ordered) ess) /\
      trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + LENGTH ordered) bb.bb_instructions)
        (be with vs_gas_readings := FLAT kgss ++ tail)) =
        ZIP (FLAT (TAKE (LENGTH ordered) ks),FLAT kgss))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_preterminal_geometry >> strip_tac >>
  qpat_x_assum `ps = FILTER _ _` (mk_asm "pseudo") >>
  qpat_x_assum `inst = EL _ ys` (mk_asm "cursor") >>
  `!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK executed be = OK st` by
    (qx_gen_tac `fuel` >> strip_tac >>
     qpat_x_assum `!F. N <= F ==> _` (qspec_then `fuel` mp_tac) >> simp[TAKE_APPEND]) >>
  `EVERY (\kw. MEM kw obs) (trace_gas (trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + LENGTH executed) bt.bb_instructions) be))`
    by suspend "observations" >>
  `!q. q < LENGTH ordered /\ (EL q xs).inst_opcode = GAS ==>
    ?w. MEM ((a,e,(EL q xs).inst_id),w) obs`
    by (rpt strip_tac >>
      `FOLDR (dft_exec_cons (N-e) C8) OK executed be = OK st` by metis_tac[LESS_EQ_REFL] >>
      `!r. r < LENGTH ordered ==> MEM r (TAKE (LENGTH executed) schedule)` by metis_tac[] >>
      drule_all preterminal_source_gas_observed >> simp[]) >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks. _`
    (drule_all_then strip_assume_tac) >>
  `EVERY IS_SOME (FLAT (TAKE (LENGTH ordered) ms))` by suspend "some" >>
  `!q. LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE q ks)) (FLAT (TAKE q ms))` by suspend "lookup" >>
  qexistsl [`ordered`,`executed`] >> simp[] >>
  rpt gen_tac >> strip_tac >> suspend "replay"
QED

Resume dft_packet_preterminal_native_agreement[observations]:
  `EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C8.ctx_functions` by
    (drule o1_ctx_shape_wf_functions >>
     simp[EVERY_MEM] >> metis_tac[wf_fn_block_inst_ids_distinct]) >>
  `ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry))` by
    (irule (cj 3 trace_names_distinct) >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `obs = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  irule dft_packet_preterminal_prefix_observations >>
  simp[TAKE_APPEND, DROP_APPEND] >>
  metis_tac[LESS_EQ_REFL]
QED
Resume dft_packet_preterminal_native_agreement[some]:
  qpat_x_assum `AM = _` kall_tac >>
  qpat_x_assum `AK = _` kall_tac >>
  qpat_x_assum `obs = _` kall_tac >>
  irule dft_packet_preterminal_rows_some >>
  qexistsl [`AM`,`a`,`acts`,`calls`,`e`,`obs`,`inst`,`xs`] >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _` drule >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret. FLOOKUP calls (a,e,cid) = _ ==> _`
       (drule_then strip_assume_tac) >> gvs[] >> metis_tac[]) >>
  conj_tac >-
    (qpat_assum `xs = _` (fn th => rewrite_tac[GSYM th]) >>
     rpt strip_tac >>
     `q < LENGTH xs /\ MEM q (TAKE count' schedule)` by (simp[] >> metis_tac[]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> !q. _`
       (drule_then (qspec_then `q` mp_tac)) >> simp[]) >>
  qpat_assum `xs = _` (fn th => rewrite_tac[GSYM th]) >>
  rpt strip_tac >>
  qpat_x_assum `!q. _ ==> ((_ ==> _) /\ (_ ==> _) /\ (_ ==> _))`
    (qspec_then `q` mp_tac) >>
  `q < LENGTH xs` by fs[] >>
  disch_then (drule_then mp_tac o cj 3) >>
  disch_then drule >>
  Cases_on `FLOOKUP calls (a,e,(EL q xs).inst_id)` >>
  pure_asm_rewrite_tac[] >> simp[]
QED
Resume dft_packet_preterminal_native_agreement[lookup]:
  irule dft_packet_preterminal_row_lookup >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`AK`,`AM`,`a`,`acts`,`blocks`,`calls`,`e`,`ks_tab`,`ms_tab`] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (drule_then strip_assume_tac) >> conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `?ess. FLOOKUP es_tab (a',e') = SOME ess` by
       (fs[FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
       FLOOKUP blocks (a,e) = _ /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `!q. _ ==> ((_ ==> _) /\ (_ ==> _) /\ (_ ==> _))`
       (qspec_then `q` (drule_then mp_tac o cj 3)) >>
     disch_then drule >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!a e cid q h b0 done_at_call child_entry ret.
       FLOOKUP calls (a,e,cid) = _ ==> _` (drule_then (mp_tac o cj 1)) >> simp[]) >>
  asm_rewrite_tac [] >>
  qpat_x_assum `FDOM blocks = FDOM es_tab` (fn th => rewrite_tac[GSYM th]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
Resume dft_packet_preterminal_native_agreement[replay]:
  qpat_x_assum `AM = _` kall_tac >>
  qpat_x_assum `AK = _` kall_tac >>
  qpat_x_assum `obs = _` kall_tac >>
  qpat_x_assum `LENGTH ordered = LENGTH executed` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> pure_rewrite_tac[GSYM th]) >>
  `ALL_DISTINCT (FLAT (TAKE (LENGTH ordered) ks))` by
    (qpat_x_assum `ALL_DISTINCT (FLAT ks)` mp_tac >>
     qspecl_then [`LENGTH ordered`,`ks`] (fn th =>
       GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) empty_rewrites [GSYM th])
       TAKE_DROP >> simp[FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (FLAT (TAKE (LENGTH ordered) ms)) (FLAT kgss)` by
    (`!(mss : bytes32 option list list) gss. LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) mss gss ==>
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT mss) (FLAT gss)` by
       (Induct >> Cases_on `gss` >> simp[] >> rpt strip_tac >>
        irule LIST_REL_APPEND_suff >> simp[]) >>
     qpat_x_assum `!mss gss. _` (qspecl_then [`TAKE (LENGTH ordered) ms`,`kgss`] mp_tac) >>
     disch_then drule >> simp[]) >>
  qabbrev_tac `orc = (\key. case ALOOKUP
    (obs ++ ZIP (FLAT (TAKE (LENGTH ordered) ks),FLAT kgss)) key of
    NONE => 0w | SOME w => w)` >>
  `LIST_REL (\key slot. slot = ALOOKUP obs key)
    (FLAT (TAKE (LENGTH ordered) ks)) (FLAT (TAKE (LENGTH ordered) ms))` by
    (qpat_x_assum `!q. LIST_REL _ _ _` (qspec_then `LENGTH ordered` ACCEPT_TAC)) >>
  drule_all dft_packet_retained_oracle_alignment >>
  simp[NoAsms, LET_THM] >>
  disch_then (qspec_then `tail` strip_assume_tac) >>
  `LENGTH ordered = LENGTH executed` by
    (qpat_x_assum `LENGTH xs = LENGTH ys` mp_tac >> simp[]) >>
  `trace_block a e (F'-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + LENGTH ordered) bt.bb_instructions) be =
   trace_block a e (N-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + LENGTH ordered) bt.bb_instructions) be` by
    (qpat_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
     irule dft_packet_successful_prefix_trace_stable >>
     simp[DROP_APPEND, TAKE_APPEND]) >>
  `trace_agrees orc (trace_block a e (F'-e) C8 tf
    (bt with bb_instructions := TAKE (LENGTH ps + LENGTH executed) bt.bb_instructions) be)` by
    (qpat_assum `LENGTH ordered = LENGTH executed` (fn th => pure_rewrite_tac[GSYM th]) >>
     simp[NoAsms, Abbr `orc`] >>
     qpat_x_assum `trace_block _ _ _ _ _ _ _ = _`
       mp_tac >> simp[NoAsms, ADD_COMM] >>
     disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `trace_agrees orc (trace_block a e (F'-e) C8 tf
    (bt with bb_instructions := TAKE (be.vs_inst_idx + LENGTH executed) bt.bb_instructions) be)` by
    (qpat_assum `be.vs_inst_idx = _` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `trace_agrees _ _`) dft_packet_native_prefix_trace >>
  simp[DROP_APPEND, TAKE_APPEND] >>
  disch_then (qspec_then `be.vs_gas_readings` (assume_tac o SRULE [])) >>
  `bb.bb_instructions = ps ++ ordered ++ [inst] /\
   bt.bb_instructions = ps ++ executed ++ [inst]` by simp[] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) ordered /\ ~is_pseudo inst.inst_opcode` by
    (qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs` mp_tac >> simp[]) >>
  asm_x "pseudo" assume_tac >>
  drule_all dft_packet_preterminal_oracle_reflect >>
  disch_then assume_tac >>
  qpat_x_assum `ps = FILTER _ _` (mk_asm "pseudo") >>
  qpat_x_assum `LENGTH ordered = LENGTH executed` (mk_asm "lengths") >>
  qpat_x_assum `LENGTH xs = LENGTH ys` (mk_asm "body_lengths") >>
  `EL (LENGTH ordered) ms = []` by
    (qpat_x_assum `!q. q < LENGTH xs ==> ((_ ==> _) /\ (_ ==> _) /\ (_ ==> _))`
       (qspec_then `LENGTH ordered` mp_tac) >> simp[EL_LENGTH_APPEND_0]) >>
  `LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) ms (kgss ++ [[]]) /\
   FLAT (kgss ++ [[]]) = FLAT kgss` by
    (irule (INST_TYPE [``:'b`` |-> ``:instruction``] dft_packet_preterminal_filling_extension) >>
     qexists_tac `ordered` >> simp[]) >>
  `LIST_REL (\i keys. if i.inst_opcode = GAS then keys = [(a,e,i.inst_id)]
    else if i.inst_opcode = INVOKE then T else keys = [])
    ordered (TAKE (LENGTH ordered) ks)` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `n < LENGTH xs` by simp[] >>
     Cases_on `(EL n ordered).inst_opcode = GAS`
     >- (qpat_x_assum `!q. q < LENGTH xs ==> ((_ ==> _) /\ (_ ==> _) /\ (_ ==> _))`
           (qspec_then `n` (mp_tac o cj 1)) >>
         disch_then (drule_then mp_tac) >>
         `EL n xs = EL n ordered` by
           (qpat_assum `xs = _` (fn th => pure_rewrite_tac[th]) >>
            simp[EL_APPEND_EQN]) >>
         qpat_assum `EL n xs = EL n ordered` (fn th => pure_rewrite_tac[th]) >>
         qpat_assum `(EL n ordered).inst_opcode = GAS`
           (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms] >> strip_tac >>
         qpat_assum `EL n ks = _` (fn th => simp[th, EL_TAKE])) >>
     Cases_on `(EL n ordered).inst_opcode = INVOKE` >- simp[] >>
     qpat_x_assum `!q. q < LENGTH xs ==> ((_ ==> _) /\ (_ ==> _) /\ (_ ==> _))`
       (qspec_then `n` (mp_tac o cj 2)) >>
     simp[EL_APPEND_EQN, EL_TAKE]) >>
  `LIST_REL (\keys gs. LENGTH keys = LENGTH gs) (TAKE (LENGTH ordered) ks) kgss` by
    (qpat_x_assum `LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks`
       (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     qpat_x_assum `LIST_REL (LIST_REL _) (TAKE (LENGTH ordered) ms) kgss`
       (mp_tac o SRULE [LIST_REL_EL_EQN]) >>
     simp[LIST_REL_EL_EQN, EL_TAKE] >> rpt strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >>
     simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  qpat_assum `inv_ev_trace orc a e (F'-e) C7 ordered be _`
    (mp_then (Pat `inv_ev_trace _ _ _ _ _ _ _ _`) mp_tac
      dft_packet_native_supplier_replay) >>
  disch_then (qspecl_then [`sf`, `TAKE (LENGTH ordered) ks`, `kgss`,
    `bb with bb_instructions := TAKE (LENGTH ps + LENGTH ordered) bb.bb_instructions`]
      (qspec_then `tail` mp_tac)) >>
  simp[NoAsms] >>
  (impl_tac >- suspend "native_inputs") >> strip_tac >>
  asm "lengths" (fn th => pure_rewrite_tac[GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >-
    (qpat_x_assum `trace_gas _ = ZIP _` mp_tac >> simp[TAKE_APPEND]) >>
  qpat_x_assum `!F k kgss tail u. _ ==> gas_events_block _ _ _ _ _ = _`
    (qspecl_then [`F'`, `LENGTH ordered`, `kgss`, `tail`]
      (qspec_then `st with vs_gas_readings := tail` mp_tac)) >>
  simp[TAKE_APPEND]
QED
Resume dft_packet_preterminal_native_agreement[native_inputs]:
  conj_tac >- simp[TAKE_APPEND, DROP_APPEND, TAKE_LENGTH_TOO_LONG] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `LIST_REL (\i keys. if _ then _ else _) ordered _` mp_tac >>
     simp[NoAsms]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[Abbr `orc`] >>
  rpt gen_tac >> strip_tac >>
  `q - LENGTH ordered = 0` by decide_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q ordered)` by
    (irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!F q kgss tail u. _ ==> (?extra. _) /\ _`
    (qspecl_then [`F'`, `q`, `kgss ++ [[]]`, `tail`]
      (qspec_then `u` mp_tac)) >>
  simp[TAKE_APPEND, EL_APPEND_EQN, EL_TAKE]
QED
Finalise dft_packet_preterminal_native_agreement
