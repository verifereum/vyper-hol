Theory dftPacketBlockEdgeClauses
Ancestors
  dftPacketBlockNativePrefix dftPacketBlockEntryDischarge dftPacketEntryReplay
  dftPacketBlockEdgeSplice dftPacketBlockReplayFrame dftPacketBlockHistoricalCuts
  dftPacketBlockRootedCertificate dftPacketBlockTerminatorCoverage
  dftPacketSuccessfulTerminalRow dftPacketBlockInitializedStructure
  dftPacketBlockInitializedReplay dftPacketBlockInitializedHistory
  dftPacketBlockInitializedFreshCut dftGasToListReplay stateEquiv
  dftIndexedExec dftRunRel venomExecProofs venomInst venomState list rich_list

(* At the source entry the same pseudo phase precedes the terminal body.
   Replaying it does not consume any of the body filling. *)
Theorem block_source_full_fold[local]:
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis hin bt.bb_instructions = OK sp /\
  FOLDR (dft_exec_cons f C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
  FOLDR (dft_exec_cons g C7) OK xs (be with vs_gas_readings := gs) = OK out ==>
  eval_phis hin bb.bb_instructions = OK sp /\
  FOLDR (dft_exec_cons g C7) OK
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
    ((sp with vs_gas_readings := gs) with
      vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK out
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. i.inst_opcode <> PHI) ys` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `eval_phis hin bb.bb_instructions = OK sp /\
   phi_prefix_length bb.bb_instructions = phi_prefix_length ps /\
   phi_prefix_length bt.bb_instructions = phi_prefix_length ps` by
    gvs[dft_phi_prefix_append,dft_eval_phis_append] >>
  `EVERY (\i. is_pseudo i.inst_opcode) (DROP (phi_prefix_length ps) ps)` by
    simp[EVERY_DROP] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP (phi_prefix_length ps) ps)` by
    (pop_assum mp_tac >> simp[EVERY_MEM] >>
     strip_tac >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `FOLDR (dft_exec_cons g C7) OK (DROP (phi_prefix_length ps) ps)
      ((sp with vs_gas_readings := gs) with vs_inst_idx := phi_prefix_length ps) =
    OK (be with vs_gas_readings := gs)` by
    (qpat_x_assum `FOLDR (dft_exec_cons f C8) OK _ _ = _` mp_tac >>
     simp[] >> strip_tac >> drule_all dft_packet_pseudo_fold_gas >>
     simp[venom_state_component_equality]) >>
  `phi_prefix_length ps - LENGTH ps = 0` by
    simp[arithmeticTheory.SUB_EQ_0,phi_prefix_length_le] >>
  simp[DROP_APPEND,FOLDR_APPEND,Once dft_exec_prefix_continue]
QED

(* Use the exact successful preterminal replay, not the conditional
   termination guard of a retained closed row. *)
Theorem block_source_terminal_fold[local]:
  xs = pre ++ [inst] /\ is_terminator inst.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  step_inst f C8 inst s = OK post /\ ~post.vs_halted /\
  FOLDR (dft_exec_cons g C7) OK pre
    (be with vs_gas_readings := gs ++ tail) = OK (s with vs_gas_readings := tail) ==>
  post.vs_gas_readings = s.vs_gas_readings /\
  FOLDR (dft_exec_cons g C7) OK xs
    (be with vs_gas_readings := gs ++ tail) = OK (post with vs_gas_readings := tail)
Proof
  strip_tac >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `gasOracleReplay$gas_replay_at 0 (step_inst_base inst) s` by
    simp[gasOracleReplayTheory.gas_base_non_gas] >>
  `step_inst_base inst s = OK post` by metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  qpat_x_assum `gasOracleReplay$gas_replay_at _ _ _` mp_tac >>
  simp[gasOracleReplayTheory.gas_replay_at_def,gasOracleReplayTheory.gas_prefix_def] >>
  disch_then (qspec_then `tail` mp_tac) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := tail)` >>
  simp[lift_result_def] >> strip_tac >>
  simp[FOLDR_APPEND] >>
  simp[Once dft_exec_prefix_continue] >>
  simp[dft_exec_cons_def,venomExecSemanticsTheory.step_inst_non_invoke]
QED

(* The exact preterminal replay gives both a source end state for entry
   initialization and the uniform full-row fold for the rooted append. *)
Theorem block_source_closed_fold[local]:
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  xs = pre ++ [inst] /\ EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  is_terminator inst.inst_opcode /\
  step_inst f C8 inst s = OK post /\ ~post.vs_halted /\
  eval_phis hin bt.bb_instructions = OK sp /\
  FOLDR (dft_exec_cons f C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
  (!F kgss tail. N <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE (LENGTH pre) ms) kgss ==>
    FOLDR (dft_exec_cons (F-d) C7) OK pre
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK (s with vs_gas_readings := tail)) ==>
  post.vs_gas_readings = s.vs_gas_readings /\
  eval_phis hin bb.bb_instructions = OK sp /\
  !F gs tail. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE (LENGTH pre) ms)) gs ==>
    FOLDR (dft_exec_cons (F-d) C7) OK xs
      (be with vs_gas_readings := gs ++ tail) = OK (post with vs_gas_readings := tail) /\
    FOLDR (dft_exec_cons (F-d) C7) OK
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
      ((sp with vs_gas_readings := gs ++ tail) with
        vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      OK (post with vs_gas_readings := tail)
Proof
  strip_tac >>
  `!F gs tail. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE (LENGTH pre) ms)) gs ==>
    FOLDR (dft_exec_cons (F-d) C7) OK pre
      (be with vs_gas_readings := gs ++ tail) = OK (s with vs_gas_readings := tail)` by
    (map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
     drule_then strip_assume_tac dftPacketFillingBoundaryTheory.dft_packet_flat_filling_split >>
     qpat_assum `!F kgss tail. _ ==> FOLDR _ _ pre (be with vs_gas_readings := FLAT kgss ++ tail) = _`
       (qspecl_then [`fuel`,`gss`,`tail`] mp_tac) >> simp[]) >>
  `!F gs tail. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE (LENGTH pre) ms)) gs ==>
    post.vs_gas_readings = s.vs_gas_readings /\ eval_phis hin bb.bb_instructions = OK sp /\
    FOLDR (dft_exec_cons (F-d) C7) OK xs
      (be with vs_gas_readings := gs ++ tail) = OK (post with vs_gas_readings := tail) /\
    FOLDR (dft_exec_cons (F-d) C7) OK
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
      ((sp with vs_gas_readings := gs ++ tail) with
        vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      OK (post with vs_gas_readings := tail)` by
    (map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
     `FOLDR (dft_exec_cons (fuel-d) C7) OK pre
        (be with vs_gas_readings := gs ++ tail) = OK (s with vs_gas_readings := tail)` by
       (qpat_assum `!F gs tail. _ ==> FOLDR _ _ pre (be with vs_gas_readings := gs ++ tail) = _`
          (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >> simp[]) >>
     drule_all_then strip_assume_tac block_source_terminal_fold >>
     drule_all_then strip_assume_tac block_source_full_fold >> simp[]) >>
  `!ss:bytes32 option list. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) ss (MAP THE ss)` by
    (Induct >> simp[] >> Cases_on `h` >> simp[]) >>
  conj_tac >-
    (qpat_assum `!F gs tail. _ ==> post.vs_gas_readings = _ /\ _`
       (qspecl_then [`N`,`MAP THE (FLAT (TAKE (LENGTH pre) ms))`,`[]`] mp_tac) >> simp[]) >>
  conj_tac >-
    (qpat_assum `!F gs tail. _ ==> post.vs_gas_readings = _ /\ _`
       (qspecl_then [`N`,`MAP THE (FLAT (TAKE (LENGTH pre) ms))`,`[]`] mp_tac) >> simp[]) >>
  map_every qx_gen_tac [`fuel`,`vals`,`rest`] >> strip_tac >>
  qpat_assum `!F gs tail. _ ==> post.vs_gas_readings = _ /\ _`
    (qspecl_then [`fuel`,`vals`,`rest`] mp_tac) >> simp[]
QED

(* Join the concrete edge to the source row's exact native replay.  The
   one filling used for availability does not restrict subsequent replay. *)
Theorem block_edge_initialized_visit[local]:
  FDOM blocks = FDOM m /\ FDOM blocks = FDOM es /\ FDOM blocks = FDOM ks /\
  FLOOKUP acts p = SOME (sf,tf,inc,entry:venom_state,order,NONE:exec_result option,NONE:bytes32 list option) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho0:num list,hin,h0:num,SOME (be,hbe:num),cnt0:num,OK s,F,NONE) /\
  LAST order = d /\
  (?rsf rtf rinc rentry rorder rres rrest.
    FLOOKUP acts [] = SOME (rsf,rtf,rinc,rentry,rorder,rres,rrest)) /\
  (!a f g ai ent ord r u.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==>
    ord <> [] /\ ord = GENLIST (\i. ai + SUC i) (LENGTH ord) /\
    (!e. MEM e ord <=> (a,e) IN FDOM blocks)) /\
  (!i. i < LENGTH p ==>
    ?a e cid f g ai ent ord q h b done child.
      a = DROP (SUC i) p /\ (e,cid) = EL i p /\
      FLOOKUP acts a = SOME (f,g,ai,ent,ord,NONE,NONE) /\ LAST ord = e /\
      FLOOKUP calls (a,e,cid) = SOME (q:num,h:num,b:venom_state,done:num list,child:venom_state,
        NONE:(internal_return # venom_state # venom_state) option)) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho0 hin h0 be hbe count front closed brest cf cg cord cr cu.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ (EL q xs).inst_id = cid /\
      FLOOKUP acts ((e,cid)::a) = SOME (cf,cg,e,child,cord,cr,cu)) /\
  (!a e bb bt ps xs ys rho0 hin h0 body count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho0,hin,h0,body,count,front,closed,brest) ==>
    body = NONE ==>
    FLOOKUP m (a,e) = SOME [] /\ FLOOKUP es (a,e) = SOME [] /\
    FLOOKUP ks (a,e) = SOME []) /\
  (!a e bb bt ps xs ys rho0 hin h0 be hbe count front closed brest mr er kr.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP m (a,e) = SOME mr /\ FLOOKUP es (a,e) = SOME er /\
    FLOOKUP ks (a,e) = SOME kr ==>
    LENGTH mr = LENGTH xs /\ LENGTH er = LENGTH mr /\ LENGTH kr = LENGTH mr /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr kr /\
    (!q. q < LENGTH xs ==>
      ((EL q xs).inst_opcode = GAS ==> EL q kr = [(a,e,(EL q xs).inst_id)]) /\
      ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
        EL q kr = []) /\
      ((EL q xs).inst_opcode = INVOKE ==>
        (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
           NONE => EL q kr = []
         | SOME call =>
             EL q mr = AM ((e,(EL q xs).inst_id)::a) /\
             EL q er = AE ((e,(EL q xs).inst_id)::a) /\
             EL q kr = AK ((e,(EL q xs).inst_id)::a))))) /\
  AM = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  ALL_DISTINCT (AK []) /\
  dft_fn_rel sf tf /\ tf = dft_fn sf /\
  o1_ctx_shape C7 /\ MEM sf C7.ctx_functions /\
  o1_ctx_shape C8 /\ LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
  strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
  ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  xs = pre ++ [inst] /\ EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  is_terminator inst.inst_opcode /\
  step_inst (N-d) C8 inst s = OK post /\ ~post.vs_halted /\
  eval_phis hin bt.bb_instructions = OK sp /\
  FOLDR (dft_exec_cons (N-d) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
  (!F kgss tail. N <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE (LENGTH pre) ms) kgss ==>
    FOLDR (dft_exec_cons (F-d) C7) OK pre
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK (s with vs_gas_readings := tail)) /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),tf,inst,s) /\
  active_inst tf inst s /\ enters_block tf post s1 /\ active_inst tf next s1 ==>
  ?N' bb1 bt1 sp1 ps1 xs1 ys1 rho1 body1 cm ce ck.
    N <= N' /\ SUC d <= N' /\
    SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry) /\
    TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      ((p,SUC d,next.inst_id),tf,next,s1) /\
    trace_gas (TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry)) =
      trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
    s1.vs_gas_readings = s.vs_gas_readings /\
    lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\
    lookup_block post.vs_current_bb tf.fn_blocks = SOME bt1 /\
    bt1.bb_label = bb1.bb_label /\ bb1.bb_label = post.vs_current_bb /\
    eval_phis post bt1.bb_instructions = OK sp1 /\
    s1 = sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions /\
    lookup_block s1.vs_current_bb tf.fn_blocks = SOME bt1 /\
    get_instruction bt1 s1.vs_inst_idx = SOME next /\
    bb1.bb_instructions = ps1 ++ xs1 /\ bt1.bb_instructions = ps1 ++ ys1 /\
    EVERY (\i. is_pseudo i.inst_opcode) ps1 /\
    EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\
    EVERY (\i. ~is_pseudo i.inst_opcode) ys1 /\
    EVERY inst_shape_ok bb1.bb_instructions /\
    EVERY inst_wf bb1.bb_instructions /\
    ALL_DISTINCT (MAP (\i. i.inst_id) xs1) /\
    LENGTH xs1 = LENGTH ys1 /\ PERM rho1 (COUNT_LIST (LENGTH xs1)) /\
    LIST_REL (\q y. q < LENGTH xs1 /\
      y.inst_id = (EL q xs1).inst_id /\ from_block [EL q xs1] y) rho1 ys1 /\
    strict_dom_vars_defined sf post /\ fn_reachable sf post.vs_current_bb /\
    ctx_labels_bound C7 post.vs_labels /\ ctx_labels_bound C8 post.vs_labels /\
    (s1.vs_inst_idx = LENGTH ps1 ==> dft_remaining_inv sf bb1 xs1 s1) /\
    phi_prefix_length bt1.bb_instructions <= s1.vs_inst_idx /\
    s1.vs_inst_idx <= LENGTH ps1 /\
    (?acts' blocks' calls' inds m' es' ks' AM' AE' AK'.
      acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
      blocks' = (blocks |+ ((p,d),
        (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
          SOME post.vs_gas_readings))) |+ ((p,SUC d),
        (bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body1,0,OK s1,F,NONE)) /\
      calls' = calls /\
      inds = GENLIST (\i. FST (THE (FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p) /\
      AM' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      AE' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      AK' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
      (p,SUC d) NOTIN FDOM blocks /\ FDOM acts' = FDOM acts /\
      order ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d])) /\
      (!e. MEM e (order ++ [SUC d]) <=> (p,e) IN FDOM blocks') /\
      FDOM blocks' = (p,SUC d) INSERT FDOM blocks /\
      FDOM blocks' = FDOM m' /\ FDOM blocks' = FDOM es' /\ FDOM blocks' = FDOM ks' /\
      FLOOKUP m' (p,SUC d) = SOME cm /\ FLOOKUP es' (p,SUC d) = SOME ce /\
      FLOOKUP ks' (p,SUC d) = SOME ck /\
      (!i. i < LENGTH p ==>
        ?h b done child.
          FLOOKUP calls' (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
            SOME (EL i inds,h,b,done,child,NONE)) /\
      (!i mr er kr. i < LENGTH p /\
        FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
        FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
        FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
        FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
        FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
        FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)) /\
      (!a e. (a,e) <> (p,SUC d) /\
        (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
        FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
        FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
        FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
      (!key mr er kr. FLOOKUP m' key = SOME mr /\ FLOOKUP es' key = SOME er /\
        FLOOKUP ks' key = SOME kr ==>
        LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
        LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
        LIST_REL (\x y. LENGTH x = LENGTH y) mr kr) /\
      LENGTH (AM' []) = LENGTH (AE' []) /\ LENGTH (AM' []) = LENGTH (AK' []) /\
      MAP THE (FILTER IS_SOME (AM' [])) = MAP THE (FILTER IS_SOME (AM [])) /\
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK' [],AM' []))) =
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM []))) /\
      ALL_DISTINCT (AK' [])) /\
    (if s1.vs_inst_idx < LENGTH ps1 then
       body1 = NONE /\ cm = [] /\ ce = [] /\ ck = [] /\
       (!f C. FOLDR (dft_exec_cons f C) OK
         (DROP (phi_prefix_length bt1.bb_instructions) (TAKE s1.vs_inst_idx ps1))
         (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1) /\
       (!F gs z R.
         N' <= F /\
         z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) /\
         R = (\entry. case eval_phis entry bb1.bb_instructions of
           OK sp =>
             (gas_events_block (F-SUC d) C7 sf.fn_name
               (bb1 with bb_instructions :=
                 TAKE (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions ++ z)
               (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions),
              FOLDR (dft_exec_cons (F-SUC d) C7) OK z
               (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
           | other => ([],other)) ==>
         R (post with vs_gas_readings := gs) =
           ([],OK (s1 with vs_gas_readings := gs)))
     else
       s1.vs_inst_idx = LENGTH ps1 /\ body1 = SOME (s1,SUC j) /\
       dft_remaining_inv sf bb1 xs1 s1 /\
       cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
       ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
       ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
       (!f C. FOLDR (dft_exec_cons f C) OK
         (DROP (phi_prefix_length bt1.bb_instructions) ps1)
         (sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions) = OK s1) /\
       LENGTH cm = LENGTH xs1 /\ LENGTH ce = LENGTH cm /\ LENGTH ck = LENGTH cm /\
       LIST_REL (\m es. LENGTH m = LENGTH es) cm ce /\
       LIST_REL (\m keys. LENGTH m = LENGTH keys) cm ck /\
       ALL_DISTINCT (FLAT ck) /\
       (!q. q < LENGTH xs1 ==>
         ((EL q xs1).inst_opcode = GAS ==>
           EL q cm = [NONE] /\ EL q ce = [(sf.fn_name,(EL q xs1).inst_id)] /\
           EL q ck = [(p,SUC d,(EL q xs1).inst_id)]) /\
         ((EL q xs1).inst_opcode <> GAS ==>
           EL q cm = [] /\ EL q ce = [] /\ EL q ck = [])) /\
       (!F k kgss tail.
         N' <= F /\ k <= LENGTH xs1 /\
         EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs1) /\
         (!q. q < k /\ (EL q xs1).inst_opcode = INVOKE ==> MEM q (TAKE 0 rho1)) /\
         LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
           (TAKE k cm) kgss ==>
         (?extra. FLAT (TAKE k ce) =
           gas_events_block (F-SUC d) C7 sf.fn_name
             <|bb_label := s1.vs_current_bb; bb_instructions :=
               REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
             (s1 with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
         (!u. FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
             (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
           gas_events_block (F-SUC d) C7 sf.fn_name
             <|bb_label := s1.vs_current_bb; bb_instructions :=
               REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
             (s1 with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ce) /\
           u.vs_gas_readings = tail /\
           trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
             (bb1 with bb_instructions := TAKE (LENGTH ps1 + k) bb1.bb_instructions)
             (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
               ZIP (FLAT (TAKE k ck),FLAT kgss) /\
           (!tail'.
             FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
               (s1 with vs_gas_readings := FLAT kgss ++ tail') =
                 OK (u with vs_gas_readings := tail') /\
             gas_events_block (F-SUC d) C7 sf.fn_name
               <|bb_label := s1.vs_current_bb; bb_instructions :=
                 REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
               (s1 with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ce)))) /\
       (!F q kgss tail z R.
         N' <= F /\ q < LENGTH xs1 /\
         EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs1) /\
         (!r. r < q /\ (EL r xs1).inst_opcode = INVOKE ==> MEM r (TAKE 0 rho1)) /\
         z = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q xs1 /\
         R = (\entry. case eval_phis entry bb1.bb_instructions of
           OK sp =>
             (gas_events_block (F-SUC d) C7 sf.fn_name
               (bb1 with bb_instructions :=
                 TAKE (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions ++ z)
               (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions),
              FOLDR (dft_exec_cons (F-SUC d) C7) OK z
               (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
           | other => ([],other)) /\
         LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss ==>
         SND (R (post with vs_gas_readings := FLAT kgss ++ tail)) =
           FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE q xs1)
             (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
         (?extra. FLAT (TAKE q ce) =
           FST (R (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
         (!events u. R (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
           events = FLAT (TAKE q ce) /\ u.vs_gas_readings = tail /\
           trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
             (bb1 with bb_instructions := TAKE (LENGTH ps1 + q) bb1.bb_instructions)
             (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
               ZIP (FLAT (TAKE q ck),FLAT kgss) /\
           !tail'. R (post with vs_gas_readings := FLAT kgss ++ tail') =
             (events,OK (u with vs_gas_readings := tail')))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM tf C8.ctx_functions` by
    (drule_all LIST_REL_MEM_IMP >> strip_tac >> gvs[]) >>
  `wf_function tf` by
    (drule dftContractGasTheory.o1_ctx_shape_wf_functions >> simp[EVERY_MEM]) >>
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (conj_tac >> disch_then (fn eq =>
       qpat_assum `is_terminator inst.inst_opcode` (mp_tac o REWRITE_RULE [eq])) >>
     simp[NoAsms,is_terminator_def]) >>
  drule_all_then (qx_choose_then `N'` (qx_choose_then `bt1` (qx_choose_then `sp1`
    (map_every assume_tac o CONJUNCTS)))) dft_packet_block_native_prefix >>
  drule_all_then (map_every assume_tac o CONJUNCTS) block_source_closed_fold >>
  `!ss:bytes32 option list. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) ss (MAP THE ss)` by
    (Induct >> simp[] >> Cases_on `h` >> simp[]) >>
  `FOLDR (dft_exec_cons (N-d) C7) OK
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
    ((sp with vs_gas_readings := MAP THE (FLAT (TAKE (LENGTH pre) ms))) with
      vs_inst_idx := phi_prefix_length bb.bb_instructions) =
    OK (post with vs_gas_readings := [])` by
    (qpat_assum `!F gs tail. _ ==> FOLDR _ _ xs _ = _ /\ _`
       (qspecl_then [`N`,`MAP THE (FLAT (TAKE (LENGTH pre) ms))`,`[]`] mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (ACCEPT_TAC o SRULE [APPEND_NIL] o CONJUNCT2)) >>
  `xs <> [] /\ is_terminator (LAST xs).inst_opcode` by simp[] >>
  drule_all_then (qx_choose_then `bb1` (qx_choose_then `ps1` (qx_choose_then `xs1`
    (qx_choose_then `ys1` (qx_choose_then `rho1` (map_every assume_tac o CONJUNCTS))))))
    dft_packet_block_entry_discharge >>
  qpat_assum `!a d j N'. ?body_entry ms ess ks count front closed brest. _`
    (qspecl_then [`p`,`d`,`j`,`N'`] strip_assume_tac) >>
  `sp1.vs_gas_readings = post.vs_gas_readings` by
    (qspecl_then [`bt1.bb_instructions`,`post`] mp_tac gasOracleReplayTheory.gas_eval_phis >>
     simp[gasOracleReplayTheory.gas_replay_at_def] >>
     disch_then (qspec_then `[]` mp_tac) >>
     Cases_on `eval_phis (post with vs_gas_readings := []) (ps1 ++ ys1)` >>
     simp[lift_result_def]) >>
  `sp1.vs_current_bb = post.vs_current_bb` by
    (qpat_assum `eval_phis post bt1.bb_instructions = OK sp1`
      (mp_then Any ACCEPT_TAC eval_phis_preserves_current_bb)) >>
  rename1 `(if s1.vs_inst_idx < LENGTH ps1 then body_entry = NONE /\ cm = [] /\ ce = [] /\ ck = [] /\ _ else _)` >>
  `(if s1.vs_inst_idx < LENGTH ps1 then cm = [] /\ ce = [] /\ ck = [] else
      cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE:bytes32 option] else []) (LENGTH xs1) /\
      ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
      ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1))` by
    (qpat_assum `(if s1.vs_inst_idx < LENGTH ps1 then body_entry = NONE /\ _ else _)` mp_tac >>
     Q_TAC ASM_CASES_TAC `s1.vs_inst_idx < LENGTH ps1` >>
     pop_assum (fn guard => simp[NoAsms,guard])) >>
  qexistsl [`N'`,`bb1`,`bt1`,`sp1`,`ps1`,`xs1`,`ys1`,`rho1`,`body_entry`,`cm`,`ce`,`ck`] >>
  qpat_x_assum `(if s1.vs_inst_idx < LENGTH ps1 then body_entry = NONE /\ _ else _)`
    (fn th => pure_once_rewrite_tac [EQT_INTRO th]) >>
  qpat_x_assum `!a d j N'. ?body_entry ms ess ks count front closed brest. _` kall_tac >>
  `s1.vs_gas_readings = s.vs_gas_readings` by simp[] >>
  `lookup_block s1.vs_current_bb tf.fn_blocks = SOME bt1` by
    (qpat_assum `s1 = sp1 with vs_inst_idx := _` (fn th => simp[NoAsms,th]) >>
     qpat_assum `sp1.vs_current_bb = post.vs_current_bb` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  ntac 33 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qabbrev_tac `newrow = (bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body_entry,
       0:num,OK s1,F,NONE:bytes32 list option)` >>
     qabbrev_tac `acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE))` >>
     qabbrev_tac `blocks' = (blocks |+ ((p,d),
       (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
         SOME post.vs_gas_readings))) |+ ((p,SUC d),newrow)` >>
     `acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
      blocks' = (blocks |+ ((p,d),
        (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
          SOME post.vs_gas_readings))) |+ ((p,SUC d),newrow)` by
       simp[Abbr `acts'`,Abbr `blocks'`] >>
     `!i. i < LENGTH p ==>
        ?f g ai ent ord q h b done child.
          FLOOKUP acts (DROP (SUC i) p) = SOME (f,g,ai,ent,ord,NONE,NONE) /\
          LAST ord = FST (EL i p) /\
          FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
            SOME (q,h,b,done,child,NONE)` by
       (qx_gen_tac `i` >> disch_tac >>
        qpat_assum `!i. i < LENGTH p ==> ?a e cid f g ai ent ord q h b done child. _`
          (drule_then (REPEAT_TCL CHOOSE_THEN STRIP_ASSUME_TAC)) >>
        rename1 `(e0,cid0) = EL i p` >>
        rename1 `a0 = DROP (SUC i) p` >>
        rename1 `FLOOKUP acts a0 = SOME (f0,g0,ai0,ent0,ord0,NONE,NONE)` >>
        rename1 `FLOOKUP calls (a0,e0,cid0) = SOME (q0,h0p,b0,done0,child0,NONE)` >>
        qpat_assum `(e0,cid0) = EL i p` (fn th =>
          assume_tac (SRULE [] (AP_TERM ``FST:num # num -> num`` th)) >>
          assume_tac (SRULE [] (AP_TERM ``SND:num # num -> num`` th))) >>
        qexistsl [`f0`,`g0`,`ai0`,`ent0`,`ord0`,`q0`,`h0p`,`b0`,`done0`,`child0`] >>
        pure_once_rewrite_tac [pairTheory.PAIR_EQ] >>
        gvs[]) >>
     Q_TAC (fn t => SUBGOAL_THEN t assume_tac)
       `((cm = [] /\ ce = [] /\ ck = []) \/
         (cm = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
          ce = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(sf.fn_name,(EL q xs1).inst_id)] else []) (LENGTH xs1) /\
          ck = GENLIST (\q. if (EL q xs1).inst_opcode = GAS then [(p,SUC d,(EL q xs1).inst_id)] else []) (LENGTH xs1)))` >-
       (qpat_assum `(if s1.vs_inst_idx < LENGTH ps1 then cm = [] /\ _ else _)` mp_tac >>
        Q_TAC ASM_CASES_TAC `s1.vs_inst_idx < LENGTH ps1` >>
        pop_assum (fn guard => simp[NoAsms,guard])) >>
     assume_tac (REFL ``calls:(gas_event,num # num # venom_state # num list # venom_state #
       (internal_return # venom_state # venom_state) option) fmap``) >>
     qspecl_then
       [`acts`,`blocks`,`calls`,`m`,`es`,`ks`,`p`,`d`,`sf`,`tf`,`inc`,`entry`,`order`,
        `bb`,`bt`,`ps`,`xs`,`ys`,`rho0`,`hin`,`h0`,`be`,`hbe`,`cnt0`,`s`,`post`,
        `newrow`,`acts'`,`blocks'`,`calls`,`xs1`,`cm`,`ce`,`ck`,`AM`,`AE`,`AK`]
       mp_tac dftPacketBlockPathUpdateTheory.dft_packet_block_path_update >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `inds` (qx_choose_then `orders` (qx_choose_then `m'`
       (qx_choose_then `es'` (qx_choose_then `ks'` (qx_choose_then `AM'`
         (qx_choose_then `AE'` (qx_choose_then `AK'` (map_every assume_tac o CONJUNCTS))))))))) >>
     qexistsl [`acts'`,`blocks'`,`calls`,`inds`,`m'`,`es'`,`ks'`,`AM'`,`AE'`,`AK'`] >>
     conj_tac >- REFL_TAC >>
     conj_tac >- REFL_TAC >>
     conj_tac >- REFL_TAC >>
     `!i mr er kr. i < LENGTH p /\
        FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
        FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
        FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
        FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
        FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
        FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!i mr er kr. _ ==> FLOOKUP m' _ = SOME (LUPDATE _ _ _) /\ _`
          (drule_all_then (fn th =>
            conj_tac >- ACCEPT_TAC (cj 1 th) >>
            conj_tac >- ACCEPT_TAC (cj 2 th) >> ACCEPT_TAC (cj 3 th)))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[NoAsms]
QED

fun choose_all names =
    List.foldr (fn (name, ttac) => qx_choose_then name ttac)
      (map_every assume_tac o CONJUNCTS) names;

(* The structural transport uses the same initialized rows as the native trace. *)
(* One initialized splice supplies both rooted-cut cases and every updated row. *)
Theorem dft_packet_block_edge_clauses:
  row_eval = (\F C owner (bb,e,z) s.
    case eval_phis s bb.bb_instructions of
      OK sp =>
       (gas_events_block (F-e) C owner
         (bb with bb_instructions :=
           TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
        FOLDR (dft_exec_cons (F-e) C) OK z
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    | other => ([],other)) /\
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row.
      case r of
        OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
      | other => (es,other)) ([],OK entry) plan) /\
  call_setup = (\C c s.
    case decode_invoke c of
      NONE => Error "invoke: bad operand format"
    | SOME (nm,ops) =>
      case lookup_function nm C.ctx_functions of
        NONE => Error "invoke: function not found"
      | SOME callee =>
        case eval_operands ops s of
          NONE => Error "invoke: undefined argument"
        | SOME args =>
          case setup_callee callee args s of
            NONE => Error "invoke: empty function"
          | SOME cs => OK cs) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller =>
              (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\ FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\ EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  FDOM blocks = FDOM (m:(((num # num) list # num),bytes32 option list list) fmap) /\
  FDOM blocks = FDOM (es:(((num # num) list # num),(string # num) list list) fmap) /\
  FDOM blocks = FDOM ks /\
  FLOOKUP acts p = SOME (sf,tf,inc,entry:venom_state,order,NONE:exec_result option,NONE:bytes32 list option) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho0:num list,hin,h0:num,SOME (be,hbe:num),cnt0:num,OK s,F,NONE) /\
  LAST order = d /\
  (?rsf rtf rinc rentry rorder rres rrest.
    FLOOKUP acts [] = SOME (rsf,rtf,rinc,rentry,rorder,rres,rrest)) /\
  (!a f g ai ent ord r u.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==>
    ord <> [] /\ ord = GENLIST (\i. ai + SUC i) (LENGTH ord) /\
    (!e. MEM e ord <=> (a,e) IN FDOM blocks)) /\
  (!i. i < LENGTH p ==>
    ?a e cid f g ai ent ord q h b done child.
      a = DROP (SUC i) p /\ (e,cid) = EL i p /\
      FLOOKUP acts a = SOME (f,g,ai,ent,ord,NONE,NONE) /\ LAST ord = e /\
      FLOOKUP calls (a,e,cid) = SOME (q:num,h:num,b:venom_state,done:num list,child:venom_state,
        NONE:(internal_return # venom_state # venom_state) option)) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho0 hin h0 be hbe count front closed brest cf cg cord cr cu.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ (EL q xs).inst_id = cid /\
      FLOOKUP acts ((e,cid)::a) = SOME (cf,cg,e,child,cord,cr,cu)) /\
  (!a e bb bt ps xs ys rho0 hin h0 body count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho0,hin,h0,body,count,front,closed,brest) ==>
    body = NONE ==>
    FLOOKUP m (a,e) = SOME [] /\ FLOOKUP es (a,e) = SOME [] /\
    FLOOKUP ks (a,e) = SOME []) /\
  (!a e bb bt ps xs ys rho0 hin h0 be hbe count front closed brest mr er kr.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP m (a,e) = SOME mr /\ FLOOKUP es (a,e) = SOME er /\
    FLOOKUP ks (a,e) = SOME kr ==>
    LENGTH mr = LENGTH xs /\ LENGTH er = LENGTH mr /\ LENGTH kr = LENGTH mr /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
    LIST_REL (\x y. LENGTH x = LENGTH y) mr kr /\
    (!q. q < LENGTH xs ==>
      ((EL q xs).inst_opcode = GAS ==> EL q kr = [(a,e,(EL q xs).inst_id)]) /\
      ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
        EL q kr = []) /\
      ((EL q xs).inst_opcode = INVOKE ==>
        (case FLOOKUP calls (a,e,(EL q xs).inst_id) of
           NONE => EL q kr = []
         | SOME call =>
             EL q mr = AM ((e,(EL q xs).inst_id)::a) /\
             EL q er = AE ((e,(EL q xs).inst_id)::a) /\
             EL q kr = AK ((e,(EL q xs).inst_id)::a))))) /\
  AM = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  ALL_DISTINCT (AK []) /\
  (!a e bb bt ps xs ys rho hin h0 be hbe cnt front closed brest mr er kr.
   FLOOKUP blocks (a,e) =
     SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),cnt,front,closed,brest) /\
   FLOOKUP m (a,e) = SOME mr /\ FLOOKUP es (a,e) = SOME er /\
   FLOOKUP ks (a,e) = SOME kr ==>
   LENGTH mr = LENGTH xs /\
   (!f g ai ent ord r u.
     FLOOKUP acts a = SOME (f,g,ai,ent,ord,r,u) ==>
     !q. q < LENGTH xs ==>
       ((EL q xs).inst_opcode = GAS ==>
         EL q mr = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
         EL q er = [(f.fn_name,(EL q xs).inst_id)] /\
         EL q kr = [(a,e,(EL q xs).inst_id)]) /\
       ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
         EL q mr = [] /\ EL q er = [] /\ EL q kr = []))) /\
  LENGTH (AK []) = LENGTH (AM []) /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM [])))) obs /\
  dft_fn_rel sf tf /\
  tf = dft_fn sf /\
  o1_ctx_shape C7 /\
  MEM sf C7.ctx_functions /\
  o1_ctx_shape C8 /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\
  strict_dom_vars_defined sf hin /\
  fn_reachable sf hin.vs_current_bb /\
  ctx_labels_bound C7 hin.vs_labels /\
  ctx_labels_bound C8 hin.vs_labels /\
  bb.bb_instructions = ps ++ xs /\
  bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  xs = pre ++ [inst] /\
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  is_terminator inst.inst_opcode /\
  step_inst (N-d) C8 inst s = OK post /\
  ~post.vs_halted /\
  eval_phis hin bt.bb_instructions = OK sp /\
  FOLDR (dft_exec_cons (N-d) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
  (!F kgss tail. N <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE (LENGTH pre) ms) kgss ==>
    FOLDR (dft_exec_cons (F-d) C7) OK pre
      (be with vs_gas_readings := FLAT kgss ++ tail) = OK (s with vs_gas_readings := tail)) /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),tf,inst,s) /\
  active_inst tf inst s /\
  enters_block tf post s1 /\
  active_inst tf next s1 /\
  (?seq. FLOOKUP acts [] = SOME (rsf,root_tf,0,root_entry,seq,NONE,NONE)) /\
  (!a f g ai ent seq r rest. FLOOKUP acts a = SOME (f,g,ai,ent,seq,r,rest) ==>
    MEM f C7.ctx_functions /\ g = dft_fn f /\ dft_fn_rel f g /\
    ai = (case a of [] => 0 | (e,cid)::parent => e) /\
    seq <> [] /\ seq = GENLIST (\i. ai + SUC i) (LENGTH seq) /\
    (!e. MEM e seq <=> (a,e) IN FDOM blocks) /\
    (r = NONE <=> rest = NONE) /\
    (r = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret. FLOOKUP calls (parent,e,cid) =
        SOME (q,h,b0,done_at_call,ent,ret))) /\
  (!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order /\ e <= N /\ h0 <= j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
      strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
      ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\ eval_phis hin bt.bb_instructions = OK sp /\
      EL h0 (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
        EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
        sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (a,e-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      cnt <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_ent of NONE => a = p /\ e = d /\ cnt = 0 /\ front = OK s /\
          FLOOKUP m (a,e) = SOME [] /\ FLOOKUP es (a,e) = SOME [] /\ FLOOKUP ks (a,e) = SOME []
        | SOME (be,hbe) => hbe <= j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\ EL hbe (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front) /\
          (closed ==> cnt = LENGTH ys /\ terminates front /\
            (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
      (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
  (!a f g ai ent ord r rest.
    FLOOKUP acts a = SOME (f,g,ai,ent,ord,SOME r,SOME rest) ==>
    run_blocks (N-ai) C8 g ent = r) /\
  (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    h < j /\ EL h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,cid),tf,c,b0) /\ LENGTH ps <= b0.vs_inst_idx /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
      (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
    done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done_at_call /\
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
    (case ret of
      NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME (ir,child_out,caller_post) =>
        child_res = SOME (IntRet ir child_out) /\
        bind_outputs c.inst_outputs ir.iret_values
          (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
        h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child_entry)) <= j /\
        MEM q (TAKE count sched))) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\ (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\ active_inst tf (EL k stk).cf_inst b0) /\
  (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
      done_at_call = TAKE count sched /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
  cnt0 < LENGTH ys /\
  inst = EL cnt0 ys /\
  (!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post) /\
  (!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hbe pos front closed rest.
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,rest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE pos rho))) /\
  (!a e bb bt ps xs ys rho hin h be hbe pos front closed rest.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,front,closed,rest) ==>
    ALL_DISTINCT (MAP (\x. x.inst_id) xs) /\
    LENGTH (THE (FLOOKUP m (a,e))) = LENGTH xs /\
    LENGTH (THE (FLOOKUP es (a,e))) = LENGTH xs /\
    LENGTH (THE (FLOOKUP ks (a,e))) = LENGTH xs) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    (res = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p))))) /\
  (!a e cid q h b done child ir child_out caller_post.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,SOME (ir,child_out,caller_post)) ==>
    ?csf ctf order rest. FLOOKUP acts ((e,cid)::a) =
      SOME (csf,ctf,e,child,order,SOME (IntRet ir child_out),rest)) /\
  (!a e bb bt ps xs ys rho hin h be hb cnt front closed brest ms ess keys
       sf tf inc entry order res nrest.
     FLOOKUP blocks (a,e) =
       SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
     FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\
     FLOOKUP ks (a,e) = SOME keys /\
     FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
     !F k kgss tail.
       N <= F /\ k <= LENGTH xs /\
       EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
       (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cnt rho)) /\
       LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
       (?extra. FLAT (TAKE k ess) = gas_events_block (F-e) C7 sf.fn_name
         <|bb_label := be.vs_current_bb; bb_instructions :=
           REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
         (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
       (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
         (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
         gas_events_block (F-e) C7 sf.fn_name
           <|bb_label := be.vs_current_bb; bb_instructions :=
             REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
           (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
         u.vs_gas_readings = tail /\
         trace_gas (trace_block a e (F-e) C7 sf
           (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
           (be with vs_gas_readings := FLAT kgss ++ tail)) =
           ZIP (FLAT (TAKE k keys),FLAT kgss) /\
         (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
             (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
           gas_events_block (F-e) C7 sf.fn_name
             <|bb_label := be.vs_current_bb; bb_instructions :=
               REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
             (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
  (!a e cid q h b0 done child ret bb bt ps xs ys rho hin hbe be hb cnt front closed brest ms.
     FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
     FLOOKUP blocks (a,e) =
       SOME (bb,bt,ps,xs,ys,rho,hin,hbe,SOME (be,hb),cnt,front,closed,brest) /\
     FLOOKUP m (a,e) = SOME ms ==>
     !F kgss tail u.
       N <= F /\ LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
       FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
         (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
       (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
       (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
         setup_callee callee args b0)) /\
  (!a e sf tf inc entry order res rest bb bt ps xs ys rho hin h be hb cnt r8 u0 ms ess keys.
     FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,rest) /\
     FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
     FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME keys ==>
     terminates r8 /\
     PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
     (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
     (!F. N <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
       (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
         (?extra. FLAT ess = gas_events_block (F-e) C7 sf.fn_name
           <|bb_label := be.vs_current_bb; bb_instructions :=
             REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
           (be with vs_gas_readings := gs ++ tail) ++ extra) /\
         ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
             (be with vs_gas_readings := gs ++ tail))) ==>
           terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
           dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
             (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
           (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
             gas_events_block (F-e) C7 sf.fn_name
               <|bb_label := be.vs_current_bb; bb_instructions :=
                 REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
               (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
             residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
               (be with vs_gas_readings := gs ++ tail)))) /\
         (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                 (be with vs_gas_readings := gs ++ tail) = OK v \/
               ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                 (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
           trace_gas (trace_block a e (F-e) C7 sf
               <|bb_label := be.vs_current_bb; bb_instructions :=
                 REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
               (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT keys,gs))))) /\
  (!a sf tf inc entry order r8 u0.
     FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
     terminates r8 /\ LENGTH (AM a) = LENGTH (AE a) /\ LENGTH (AM a) = LENGTH (AK a) /\
     PERM (MAP THE (FILTER IS_SOME (AM a)) ++ u0) entry.vs_gas_readings /\
     (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (AM a) /\ u0 = v.vs_gas_readings) /\
     (!F. N <= F ==> run_blocks (F-inc) C8 tf entry = r8 /\
       (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM a) gs ==>
         (?extra. AE a = gas_events_blocks (F-inc) C7 sf
           (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
         ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
           terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
           dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
             (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
           (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
             gas_events_blocks (F-inc) C7 sf
               (entry with vs_gas_readings := gs ++ tail) = AE a /\
             residual_result tail r8 (run_blocks (F-inc) C7 sf
               (entry with vs_gas_readings := gs ++ tail)))) /\
         (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
               ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
           trace_gas (trace_blocks a inc (F-inc) C7 sf
               (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK a,gs))))) /\
  (!a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
     FLOOKUP blocks (a,e) =
       SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) /\
     FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME keys ==>
     !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
       case FLOOKUP calls (a,e,(EL q xs).inst_id) of
         NONE => EL q ms = [] /\ EL q ess = [] /\ EL q keys = []
       | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
           EL q ess = AE ((e,(EL q xs).inst_id)::a) /\ EL q keys = AK ((e,(EL q xs).inst_id)::a)) /\
  (!a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
     FLOOKUP blocks (a,e) =
       SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) ==>
     !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE cnt rho) ==>
       ?ch b done child ir child_out caller_post.
         FLOOKUP calls (a,e,(EL q xs).inst_id) =
           SOME (q,ch,b,done,child,SOME (ir,child_out,caller_post))) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cnt0 rho0)) /\
  FLOOKUP m (p,d) = SOME ms /\
  FLOOKUP es (p,d) = SOME ess /\
  FLOOKUP ks (p,d) = SOME keys /\
  (terminates (OK post) /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ post.vs_gas_readings) be.vs_gas_readings /\
    (!v. (OK post = OK v \/ (?ir. OK post = IntRet ir v)) ==>
      EVERY IS_SOME (FLAT ms) /\ post.vs_gas_readings = v.vs_gas_readings) /\
    (!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post /\
      (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
        (?extra. FLAT ess = gas_events_block (F-d) C7 sf.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
          (be with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons (F-d) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-d) C7) OK xs
            (be with vs_gas_readings := gs ++ tail))) (restore_result [] (OK post)) /\
          (((?v. OK post = OK v) \/ (?ir v. OK post = IntRet ir v)) ==>
            gas_events_block (F-d) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
            residual_result tail (OK post) (FOLDR (dft_exec_cons (F-d) C7) OK xs
              (be with vs_gas_readings := gs ++ tail)))) /\
        (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = OK v \/
              ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs
                (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
          trace_gas (trace_block p d (F-d) C7 sf
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
              (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT keys,gs))))) /\
  (!a sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      tf = dft_fn sf /\ dft_fn_rel sf tf /\
      order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
      (!e. MEM e order <=> (a,e) IN FDOM blocks)) /\
  (!a e bb bt ps xs ys rho in_state h0 body_entry count front closed brest.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) ==>
      (?sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
        lookup_block bb.bb_label tf.fn_blocks = SOME bt) /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      (body_entry = NONE ==> (a,e) = (p,d))) /\
  (!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess row_keys.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,in_state,h0,SOME (be,hbe),count,front,closed,brest) /\
      FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\ FLOOKUP ks (a,e) = SOME row_keys ==>
      LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH row_keys = LENGTH ms /\
      (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
        case FLOOKUP calls (a,e,(EL q xs).inst_id) of
          NONE => EL q ms = [] /\ EL q ess = [] /\ EL q row_keys = []
        | SOME call => EL q ms = AM ((e,(EL q xs).inst_id)::a) /\
            EL q ess = AE ((e,(EL q xs).inst_id)::a) /\ EL q row_keys = AK ((e,(EL q xs).inst_id)::a))) /\
  (!a e cid q h b done_at_call child_entry ret.
      FLOOKUP calls (a,e,cid) = SOME (q,h,b,done_at_call,child_entry,ret) ==>
      ?bb bt ps xs ys rho hin h0 be hbe pos front closed brest.
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),pos,front,closed,brest) /\
        q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ (EL q xs).inst_id = cid /\
        (case ret of
          NONE => MEM ((e,cid)::a) (GENLIST (\k. DROP k p) (SUC (LENGTH p)))
        | SOME triple => MEM q (TAKE pos rho))) /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
          body_entry count front closed brest q z.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      ((IS_SOME body_entry /\ q < LENGTH xs /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho))) \/
       (body_entry = NONE /\ a = p /\ e = d /\ q = 0 /\
        z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s.vs_inst_idx ps))) ==>
      ?cuts levels Mcut Ecut Kcut mr er kr.
        MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
            EL i levels = (sfi,
              MAP (\f. case THE (FLOOKUP blocks (ai,f)) of
                (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                  (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++ [(bbi,ei,zi)],
              if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP m (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP m (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks (ai,ei))))) cuts) /\
        AM [] = Mcut ++ mr /\ AE [] = Ecut ++ er /\ AK [] = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
            (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
                (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
            rsf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
          (?extra. Ecut = FST (rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F C7 rsf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((a,e,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
                (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==> u with vs_gas_readings := s.vs_gas_readings = s) /\
              (a = p /\ e = d /\ IS_SOME body_entry /\
               inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
                u.vs_initial_fmp = s.vs_initial_fmp)
          | stopped =>
              run_blocks F C7 rsf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gasEvents$gas_events_blocks F C7 rsf (root_entry with vs_gas_readings := gs ++ tail) =
                FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))) ==>
  ?N' bb1 bt1 sp1 ps1 xs1 ys1 rho1 body1 cm ce ck acts' blocks' calls' inds m' es' ks' AM' AE' AK'.
    N <= N' /\
    SUC d <= N' /\
    SUC j < LENGTH (trace_blocks [] 0 N' C8 root_tf root_entry) /\
    TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      TAKE (SUC j) (trace_blocks [] 0 N C8 root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry) =
      ((p,SUC d,next.inst_id),tf,next,s1) /\
    trace_gas (TAKE (SUC j) (trace_blocks [] 0 N' C8 root_tf root_entry)) =
      trace_gas (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry)) /\
    eval_phis post bt1.bb_instructions = OK sp1 /\
    acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
    blocks' = (blocks |+ ((p,d),
        (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),LENGTH ys,OK post,T,
          SOME post.vs_gas_readings))) |+ ((p,SUC d),
        (bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body1,0,OK s1,F,NONE)) /\
    calls' = calls /\
    inds = GENLIST (\i. FST (THE (FLOOKUP calls
        (DROP (SUC i) p,FST (EL i p),SND (EL i p))))) (LENGTH p) /\
    AM' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    AE' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    AK' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (a,f))))
        (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
    (p,SUC d) NOTIN FDOM blocks /\
    FDOM acts' = FDOM acts /\
    order ++ [SUC d] = GENLIST (\i. inc + SUC i) (LENGTH (order ++ [SUC d])) /\
    (!e. MEM e (order ++ [SUC d]) <=> (p,e) IN FDOM blocks') /\
    FDOM blocks' = (p,SUC d) INSERT FDOM blocks /\
    FDOM blocks' = FDOM m' /\
    FDOM blocks' = FDOM es' /\
    FDOM blocks' = FDOM ks' /\
    FLOOKUP m' (p,SUC d) = SOME cm /\
    FLOOKUP es' (p,SUC d) = SOME ce /\
    FLOOKUP ks' (p,SUC d) = SOME ck /\
    (!i. i < LENGTH p ==>
        ?h b done child.
          FLOOKUP calls' (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
            SOME (EL i inds,h,b,done,child,NONE)) /\
    (!i mr er kr. i < LENGTH p /\
        FLOOKUP m (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
        FLOOKUP es (DROP (SUC i) p,FST (EL i p)) = SOME er /\
        FLOOKUP ks (DROP (SUC i) p,FST (EL i p)) = SOME kr ==>
        FLOOKUP m' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
        FLOOKUP es' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
        FLOOKUP ks' (DROP (SUC i) p,FST (EL i p)) =
          SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)) /\
    (!a e. (a,e) <> (p,SUC d) /\
        (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
        FLOOKUP m' (a,e) = FLOOKUP m (a,e) /\
        FLOOKUP es' (a,e) = FLOOKUP es (a,e) /\
        FLOOKUP ks' (a,e) = FLOOKUP ks (a,e)) /\
    s1.vs_gas_readings = s.vs_gas_readings /\
    LENGTH (AM' []) = LENGTH (AE' []) /\
    LENGTH (AM' []) = LENGTH (AK' []) /\
    MAP THE (FILTER IS_SOME (AM' [])) = MAP THE (FILTER IS_SOME (AM [])) /\
    MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK' [],AM' []))) =
      MAP (\(key,slot). (key,THE slot))
        (FILTER (\(key,slot). IS_SOME slot) (ZIP (AK [],AM []))) /\
    ALL_DISTINCT (AK' []) /\
    (?seq. FLOOKUP acts' [] = SOME (rsf,root_tf,0,root_entry,seq,NONE,NONE)) /\
    (!a f g ai ent seq r rest. FLOOKUP acts' a = SOME (f,g,ai,ent,seq,r,rest) ==>
    MEM f C7.ctx_functions /\ g = dft_fn f /\ dft_fn_rel f g /\
    ai = (case a of [] => 0 | (e,cid)::parent => e) /\
    seq <> [] /\ seq = GENLIST (\i. ai + SUC i) (LENGTH seq) /\
    (!e. MEM e seq <=> (a,e) IN FDOM blocks') /\
    (r = NONE <=> rest = NONE) /\
    (r = NONE <=> MEM a (GENLIST (\i. DROP i p) (SUC (LENGTH p)))) /\
    (!e cid parent. a = (e,cid)::parent ==>
      ?q h b0 done_at_call ret. FLOOKUP calls (parent,e,cid) =
        SOME (q,h,b0,done_at_call,ent,ret))) /\
    (!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks' (a,e) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,cnt,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) /\ MEM e order /\ e <= N' /\ h0 <= SUC j /\
      lookup_block bb.bb_label sf.fn_blocks = SOME bb /\ lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      lookup_block hin.vs_current_bb sf.fn_blocks = SOME bb /\ bt.bb_label = bb.bb_label /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      EVERY inst_shape_ok bb.bb_instructions /\ LENGTH xs = LENGTH ys /\
      PERM sched (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) sched ys /\
      strict_dom_vars_defined sf hin /\ fn_reachable sf hin.vs_current_bb /\
      ctx_labels_bound C7 hin.vs_labels /\ ctx_labels_bound C8 hin.vs_labels /\ eval_phis hin bt.bb_instructions = OK sp /\
      EL h0 (trace_blocks [] 0 N' C8 root_tf root_entry) = ((a,e,(EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions).inst_id),tf,
        EL (phi_prefix_length bt.bb_instructions) bt.bb_instructions,
        sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks' (a,e-1) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      cnt <= LENGTH ys /\ (closed <=> IS_SOME brest) /\
      (case body_ent of NONE => a = p /\ e = SUC d /\ cnt = 0 /\ front = OK s1 /\
          FLOOKUP m' (a,e) = SOME [] /\ FLOOKUP es' (a,e) = SOME [] /\ FLOOKUP ks' (a,e) = SOME []
        | SOME (be,hbe) => hbe <= SUC j /\ be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
          dft_remaining_inv sf bb xs be /\ EL hbe (trace_blocks [] 0 N' C8 root_tf root_entry) = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
          FOLDR (dft_exec_cons (N'-e) C8) OK (DROP (phi_prefix_length bt.bb_instructions) ps)
            (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
          (!F. N' <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK (TAKE cnt ys) be = front) /\
          (closed ==> cnt = LENGTH ys /\ terminates front /\
            (!v. (front = OK v \/ (?ir. front = IntRet ir v)) ==> brest = SOME v.vs_gas_readings))) /\
      (e <> LAST order ==> closed /\ ?post. front = OK post /\ ~post.vs_halted) /\
      (e = LAST order ==> res = (if closed then SOME front else NONE) /\ nrest = brest)) /\
    (?sf inc entry order bb bt ps xs ys sched hin h0 body_ent count.
    FLOOKUP acts' p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = SUC d /\
    FLOOKUP blocks' (p,SUC d) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,body_ent,count,OK s1,F,NONE) /\
    lookup_block s1.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt s1.vs_inst_idx = SOME next /\
    (case body_ent of NONE => phi_prefix_length bt.bb_instructions <= s1.vs_inst_idx /\
      s1.vs_inst_idx < LENGTH ps /\ count = 0 /\
      FOLDR (dft_exec_cons (N'-SUC d) C8) OK
        (DROP (phi_prefix_length bt.bb_instructions) (TAKE s1.vs_inst_idx ps))
        ((case eval_phis hin bt.bb_instructions of OK sp => sp | other => hin)
         with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK s1
    | SOME (be,hbe) => s1.vs_inst_idx = LENGTH ps + count /\ count < LENGTH ys /\ next = EL count ys)) /\
    (!a e cid q h b0 done_at_call child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
      be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    q < LENGTH xs /\ c = EL q xs /\ c.inst_id = cid /\ c.inst_opcode = INVOKE /\
    h < SUC j /\ EL h (trace_blocks [] 0 N' C8 root_tf root_entry) = ((a,e,cid),tf,c,b0) /\ LENGTH ps <= b0.vs_inst_idx /\
    get_instruction bt b0.vs_inst_idx = SOME c /\
    (!F. N' <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK
      (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0) /\
    done_at_call = TAKE (b0.vs_inst_idx - LENGTH ps) sched /\ ~MEM q done_at_call /\
    FLOOKUP acts' ((e,cid)::a) = SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
    decode_invoke c = SOME (nm,ops) /\ lookup_function nm C8.ctx_functions = SOME ctf /\
    eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
    (case ret of
      NONE => child_res = NONE /\ MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME (ir,child_out,caller_post) =>
        child_res = SOME (IntRet ir child_out) /\
        bind_outputs c.inst_outputs ir.iret_values
          (adopt_return_fmp ir (merge_callee_state b0 child_out)) = SOME caller_post /\
        h + SUC (LENGTH (trace_blocks ((e,cid)::a) e (N'-e) C8 ctf child_entry)) <= SUC j /\
        MEM q (TAKE count sched))) /\
    (!k. k < LENGTH p ==>
    ?sf tf inc entry order q call_h b0 done_at_call child_entry e cid a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,call_h,b0,done_at_call,child_entry,NONE) /\
      (EL k stk).cf_fn = tf /\ (EL k stk).cf_state = b0 /\ (EL k stk).cf_inst.inst_id = cid /\
      (EL k stk).cf_inst.inst_opcode = INVOKE /\ active_inst tf (EL k stk).cf_inst b0) /\
    (!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\
      FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK b0,F,NONE) /\
      FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done_at_call,child_entry,NONE) /\
      done_at_call = TAKE count sched /\ b0.vs_inst_idx = LENGTH ps + count /\
      get_instruction bt b0.vs_inst_idx = SOME (EL q xs)) /\
    (!a e bb bt ps xs ys sched hin h0 be hbe count front closed brest.
    FLOOKUP blocks' (a,e) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count sched) ==>
      ?h b0 done_at_call child_entry ir child_out caller_post.
        FLOOKUP calls (a,e,(EL q xs).inst_id) =
          SOME (q,h,b0,done_at_call,child_entry,SOME (ir,child_out,caller_post))) /\
    (!bb bt ps xs ys sched hin h0 be hbe count sf inc entry order.
    FLOOKUP acts' p = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
    FLOOKUP blocks' (p,SUC d) =
      SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,OK s1,F,NONE) /\
    inv_memory_observation next.inst_opcode ==>
    EL (EL count sched) xs = next /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (EL count sched) xs) /\
    (!q. q < EL count sched /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE count sched))) /\
    (!a e bb bt ps xs ys rho hin h be hb cnt front closed brest ms ess keys
         sf tf inc entry order res nrest.
       FLOOKUP blocks' (a,e) =
         SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,brest) /\
       FLOOKUP m' (a,e) = SOME ms /\ FLOOKUP es' (a,e) = SOME ess /\
       FLOOKUP ks' (a,e) = SOME keys /\
       FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
       !F k kgss tail.
         N' <= F /\ k <= LENGTH xs /\
         EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
         (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q (TAKE cnt rho)) /\
         LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
         (?extra. FLAT (TAKE k ess) = gas_events_block (F-e) C7 sf.fn_name
           <|bb_label := be.vs_current_bb; bb_instructions :=
             REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
           (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
         (!u. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
           (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
           gas_events_block (F-e) C7 sf.fn_name
             <|bb_label := be.vs_current_bb; bb_instructions :=
               REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
             (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
           u.vs_gas_readings = tail /\
           trace_gas (trace_block a e (F-e) C7 sf
             (bb with bb_instructions := TAKE (LENGTH ps + k) bb.bb_instructions)
             (be with vs_gas_readings := FLAT kgss ++ tail)) =
             ZIP (FLAT (TAKE k keys),FLAT kgss) /\
           (!tail'. FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
               (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
             gas_events_block (F-e) C7 sf.fn_name
               <|bb_label := be.vs_current_bb; bb_instructions :=
                 REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
               (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
    (!a e cid q h b0 done child ret bb bt ps xs ys rho hin hbe be hb cnt front closed brest ms.
       FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child,ret) /\
       FLOOKUP blocks' (a,e) =
         SOME (bb,bt,ps,xs,ys,rho,hin,hbe,SOME (be,hb),cnt,front,closed,brest) /\
       FLOOKUP m' (a,e) = SOME ms ==>
       !F kgss tail u.
         N' <= F /\ LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
         FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
           (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
         (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
         (!callee args. setup_callee callee args (u with vs_gas_readings := b0.vs_gas_readings) =
           setup_callee callee args b0)) /\
    (!a e sf tf inc entry order res rest bb bt ps xs ys rho hin h be hb cnt r8 u0 ms ess keys.
       FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,rest) /\
       FLOOKUP blocks' (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,r8,T,SOME u0) /\
       FLOOKUP m' (a,e) = SOME ms /\ FLOOKUP es' (a,e) = SOME ess /\ FLOOKUP ks' (a,e) = SOME keys ==>
       terminates r8 /\
       PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ u0) be.vs_gas_readings /\
       (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (FLAT ms) /\ u0 = v.vs_gas_readings) /\
       (!F. N' <= F ==> FOLDR (dft_exec_cons (F-e) C8) OK ys be = r8 /\
         (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
           (?extra. FLAT ess = gas_events_block (F-e) C7 sf.fn_name
             <|bb_label := be.vs_current_bb; bb_instructions :=
               REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
             (be with vs_gas_readings := gs ++ tail) ++ extra) /\
           ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
               (be with vs_gas_readings := gs ++ tail))) ==>
             terminates (FOLDR (dft_exec_cons (F-e) C7) OK xs (be with vs_gas_readings := gs ++ tail)) /\
             dft_res_rel (restore_result [] (FOLDR (dft_exec_cons (F-e) C7) OK xs
               (be with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
             (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
               gas_events_block (F-e) C7 sf.fn_name
                 <|bb_label := be.vs_current_bb; bb_instructions :=
                   REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                 (be with vs_gas_readings := gs ++ tail) = FLAT ess /\
               residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
                 (be with vs_gas_readings := gs ++ tail)))) /\
           (!v. (FOLDR (dft_exec_cons (F-e) C7) OK xs
                   (be with vs_gas_readings := gs ++ tail) = OK v \/
                 ?ir. FOLDR (dft_exec_cons (F-e) C7) OK xs
                   (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
             trace_gas (trace_block a e (F-e) C7 sf
                 <|bb_label := be.vs_current_bb; bb_instructions :=
                   REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
                 (be with vs_gas_readings := gs ++ tail)) = ZIP (FLAT keys,gs))))) /\
    (!a sf tf inc entry order r8 u0.
       FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,SOME r8,SOME u0) ==>
       terminates r8 /\ LENGTH (AM' a) = LENGTH (AE' a) /\ LENGTH (AM' a) = LENGTH (AK' a) /\
       PERM (MAP THE (FILTER IS_SOME (AM' a)) ++ u0) entry.vs_gas_readings /\
       (!v. (r8 = OK v \/ (?ir. r8 = IntRet ir v)) ==> EVERY IS_SOME (AM' a) /\ u0 = v.vs_gas_readings) /\
       (!F. N' <= F ==> run_blocks (F-inc) C8 tf entry = r8 /\
         (!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (AM' a) gs ==>
           (?extra. AE' a = gas_events_blocks (F-inc) C7 sf
             (entry with vs_gas_readings := gs ++ tail) ++ extra) /\
           ((?f. terminates (run_blocks f C7 sf (entry with vs_gas_readings := gs ++ tail))) ==>
             terminates (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail)) /\
             dft_res_rel (restore_result [] (run_blocks (F-inc) C7 sf
               (entry with vs_gas_readings := gs ++ tail))) (restore_result [] r8) /\
             (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
               gas_events_blocks (F-inc) C7 sf
                 (entry with vs_gas_readings := gs ++ tail) = AE' a /\
               residual_result tail r8 (run_blocks (F-inc) C7 sf
                 (entry with vs_gas_readings := gs ++ tail)))) /\
           (!v. (run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = OK v \/
                 ?ir. run_blocks (F-inc) C7 sf (entry with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
             trace_gas (trace_blocks a inc (F-inc) C7 sf
                 (entry with vs_gas_readings := gs ++ tail)) = ZIP (AK' a,gs))))) /\
    (!a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
       FLOOKUP blocks' (a,e) =
         SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) /\
       FLOOKUP m' (a,e) = SOME ms /\ FLOOKUP es' (a,e) = SOME ess /\ FLOOKUP ks' (a,e) = SOME keys ==>
       !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==>
         case FLOOKUP calls (a,e,(EL q xs).inst_id) of
           NONE => EL q ms = [] /\ EL q ess = [] /\ EL q keys = []
         | SOME call => EL q ms = AM' ((e,(EL q xs).inst_id)::a) /\
             EL q ess = AE' ((e,(EL q xs).inst_id)::a) /\ EL q keys = AK' ((e,(EL q xs).inst_id)::a)) /\
    (!a e bb bt ps xs ys rho hin h be hb cnt front closed rest.
       FLOOKUP blocks' (a,e) =
         SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hb),cnt,front,closed,rest) ==>
       !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE cnt rho) ==>
         ?ch b done child ir child_out caller_post.
           FLOOKUP calls (a,e,(EL q xs).inst_id) =
             SOME (q,ch,b,done,child,SOME (ir,child_out,caller_post))) /\
    (!key mr er kr. FLOOKUP m' key = SOME mr /\ FLOOKUP es' key = SOME er /\
      FLOOKUP ks' key = SOME kr ==>
      LENGTH mr = LENGTH er /\ LENGTH mr = LENGTH kr /\
      LIST_REL (\x y. LENGTH x = LENGTH y) mr er /\
      LIST_REL (\x y. LENGTH x = LENGTH y) mr kr) /\
    (!a e bb bt ps xs ys rho hin h0 be hbe cnt front closed brest mr er kr.
     FLOOKUP blocks' (a,e) =
       SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),cnt,front,closed,brest) /\
     FLOOKUP m' (a,e) = SOME mr /\ FLOOKUP es' (a,e) = SOME er /\
     FLOOKUP ks' (a,e) = SOME kr ==>
     LENGTH mr = LENGTH xs /\
     (!f g ai ent ord r u.
       FLOOKUP acts' a = SOME (f,g,ai,ent,ord,r,u) ==>
       !q. q < LENGTH xs ==>
         ((EL q xs).inst_opcode = GAS ==>
           EL q mr = [ALOOKUP obs (a,e,(EL q xs).inst_id)] /\
           EL q er = [(f.fn_name,(EL q xs).inst_id)] /\
           EL q kr = [(a,e,(EL q xs).inst_id)]) /\
         ((EL q xs).inst_opcode <> GAS /\ (EL q xs).inst_opcode <> INVOKE ==>
           EL q mr = [] /\ EL q er = [] /\ EL q kr = []))) /\
    (!a e kr. FLOOKUP ks' (a,e) = SOME kr ==> ALL_DISTINCT (FLAT kr)) /\
   (!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest q z.
    FLOOKUP acts' a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks' (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
    ((IS_SOME body_entry /\ q < LENGTH xs /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
        (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho))) \/
       (body_entry = NONE /\ a = p /\ e = SUC d /\ q = 0 /\
        z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s1.vs_inst_idx ps))) ==>
 ?cuts levels Mcut Ecut Kcut mr er kr. MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
      LENGTH cuts = LENGTH levels /\
      (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks' (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
            EL i levels = (sfi,
              MAP (\f. case THE (FLOOKUP blocks' (ai,f)) of
                (bf,btf,psf,xsf,ysf,rhof,inf,hf,bef,cf,rf,closedf,restf) =>
                  (bf,f,DROP (phi_prefix_length bf.bb_instructions) bf.bb_instructions)) ds ++ [(bbi,ei,zi)],
              if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
      Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP m' (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP m' (ai,ei))))) cuts) /\
      Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es' (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es' (ai,ei))))) cuts) /\
      Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks' (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks' (ai,ei))))) cuts) /\
      AM' [] = Mcut ++ mr /\
      AE' [] = Ecut ++ er /\
      AK' [] = Kcut ++ kr /\
      LENGTH Mcut = LENGTH Ecut /\
      LENGTH Mcut = LENGTH Kcut /\
      (!F gs tail.
          N' <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
            (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
                (sfi,tfi,inci,enti,orderi,resi,nresti) => inci) cuts)
            rsf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
          (?extra. Ecut = FST (rooted_eval F C7 levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F C7 rsf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((a,e,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
                (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==> u with vs_gas_readings := s1.vs_gas_readings = s1) /\
              (a = p /\ e = SUC d /\ IS_SOME body_entry /\
               inv_memory_observation next.inst_opcode /\ EL q xs = next ==>
                (!op. MEM op next.inst_operands ==> eval_operand op u = eval_operand op s1) /\
                u.vs_initial_fmp = s1.vs_initial_fmp)
          | stopped =>
              run_blocks F C7 rsf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gasEvents$gas_events_blocks F C7 rsf (root_entry with vs_gas_readings := gs ++ tail) =
                FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))))
Proof
  PURE_REWRITE_TAC [AND_CLAUSES] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac block_edge_initialized_visit >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (choose_all [`N'`,`bb1`,`bt1`,`sp1`,`ps1`,`xs1`,`ys1`,`rho1`,`body1`,`cm`,`ce`,`ck`]) >>
  qpat_x_assum `?acts' blocks' calls' inds m' es' ks' AM' AE' AK'. _`
    (choose_all [`acts'`,`blocks'`,`calls'`,`inds`,`m'`,`es'`,`ks'`,`AM'`,`AE'`,`AK'`]) >>
  `!F. N' <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post` by
    (qx_gen_tac `fuel` >> disch_tac >>
     qpat_assum `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post`
       (qspec_then `fuel` mp_tac) >>
     simp[] >> decide_tac) >>
  `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\
       FLOOKUP m' (p,SUC d) = SOME [] /\ FLOOKUP es' (p,SUC d) = SOME [] /\
       FLOOKUP ks' (p,SUC d) = SOME []
     else body1 = SOME (s1,SUC j) /\ dft_remaining_inv sf bb1 xs1 s1` by
    (Cases_on `s1.vs_inst_idx < LENGTH ps1` >>
     pop_assum (fn guard =>
       qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\ _ else _`
         (map_every assume_tac o CONJUNCTS o REWRITE_RULE [guard]) >>
       simp[guard])) >>
  mp_tac (Q.INST [`N1` |-> `N'`,
    `tf0` |-> `tf`,
    `sf0` |-> `sf`,
    `acts1` |-> `acts'`,
    `blocks1` |-> `blocks'`,
    `m1` |-> `m':(((num # num) list # num),bytes32 option list list) fmap`,
    `es1` |-> `es':(((num # num) list # num),(string # num) list list) fmap`,
    `ks1` |-> `ks':(((num # num) list # num),gas_event list list) fmap`,
    `inc0` |-> `inc`, `entry0` |-> `entry`, `ord0` |-> `order`,
    `bb0` |-> `bb`, `bt0` |-> `bt`, `ps0` |-> `ps`, `xs0` |-> `xs`, `ys0` |-> `ys`,
    `sch0` |-> `rho0`, `in0` |-> `hin`, `h00` |-> `h0`,
    `be0` |-> `be`, `hbe0` |-> `hbe`, `inst0` |-> `inst`, `sch1` |-> `rho1`,
    `rtf` |-> `root_tf`, `rentry` |-> `root_entry`,
    `tr` |-> `trace_blocks [] 0 N C8 root_tf root_entry`,
    `tr1` |-> `trace_blocks [] 0 N' C8 root_tf root_entry`]
    (let
       val th = block_initialized_structure
       val vars = free_vars (concl th)
       fun table_type name ty =
         let val var = valOf (List.find (fn v => fst (dest_var v) = name) vars)
         in match_type (type_of var) ty end
     in
       INST_TYPE (List.concat
         [table_type "m" ``:(((num # num) list # num),bytes32 option list list) fmap``,
          table_type "es" ``:(((num # num) list # num),(string # num) list list) fmap``,
          table_type "ks" ``:(((num # num) list # num),gas_event list list) fmap``,
          table_type "m1" ``:(((num # num) list # num),bytes32 option list list) fmap``,
          table_type "es1" ``:(((num # num) list # num),(string # num) list list) fmap``,
          table_type "ks1" ``:(((num # num) list # num),gas_event list list) fmap``]) th
     end)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>

  `(!i. i < LENGTH p ==>
    ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done child ch.
      FLOOKUP blocks (DROP (SUC i) p,FST (EL i p)) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h,SOME (be,hbe),pos,OK b0,F,NONE) /\
      FLOOKUP calls (DROP (SUC i) p,FST (EL i p),SND (EL i p)) =
        SOME (EL i inds,ch,b0,done,child,NONE) /\
      dft_fn_rel sf tf /\ lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
      lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
      bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
      EVERY (\x. is_pseudo x.inst_opcode) ps /\
      EVERY (\x. ~is_pseudo x.inst_opcode) xs /\ LENGTH xs = LENGTH ys /\
      PERM rho (COUNT_LIST (LENGTH xs)) /\
      LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
        from_block [EL q xs] y) rho ys /\
      EL i inds < LENGTH xs /\ (EL (EL i inds) xs).inst_opcode = INVOKE /\
      b0.vs_inst_idx = LENGTH ps + pos /\
      get_instruction bt b0.vs_inst_idx = SOME (EL (EL i inds) xs))` by suspend "replay_parent" >>
  `(body1 <> NONE ==> body1 = SOME (s1,SUC j) /\
    (!q. q < LENGTH xs1 /\ (EL q xs1).inst_opcode <> GAS ==>
       EL q cm = [] /\ EL q ce = [] /\ EL q ck = []) /\
    (!F k kgss tail.
       N' <= F /\ k <= LENGTH xs1 /\
       EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs1) /\
       (!q. q < k /\ (EL q xs1).inst_opcode = INVOKE ==> MEM q (TAKE 0 rho1)) /\
       LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k cm) kgss ==>
       (?extra. FLAT (TAKE k ce) = gas_events_block (F-SUC d) C7 sf.fn_name
         <|bb_label := s1.vs_current_bb; bb_instructions :=
           REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
         (s1 with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
       (!u. FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
         (s1 with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
         gas_events_block (F-SUC d) C7 sf.fn_name
           <|bb_label := s1.vs_current_bb; bb_instructions :=
             REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
           (s1 with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ce) /\
         u.vs_gas_readings = tail /\
         trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
           (bb1 with bb_instructions := TAKE (LENGTH ps1 + k) bb1.bb_instructions)
           (s1 with vs_gas_readings := FLAT kgss ++ tail)) =
           ZIP (FLAT (TAKE k ck),FLAT kgss) /\
         (!tail'. FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE k xs1)
             (s1 with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
           gas_events_block (F-SUC d) C7 sf.fn_name
             <|bb_label := s1.vs_current_bb; bb_instructions :=
               REPLICATE s1.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs1|>
             (s1 with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ce)))))` by suspend "replay_fresh" >>
  qspecl_then [
    `N`,`N'`,`C7`,`C8`,`p`,`d`,`inds`,`acts`,`acts'`,
    `blocks`,`blocks'`,`calls`,`m`,`es`,`ks`,`m'`,`es'`,`ks'`,
    `AM`,`AE`,`AK`,`AM'`,`AE'`,`AK'`,`sf`,`tf`,`inc`,
    `entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho0`,`hin`,
    `h0`,`be`,`hbe`,`cnt0`,`s`,`post`,`bb1`,`bt1`,`ps1`,
    `xs1`,`ys1`,`rho1`,`j`,`body1`,`s1`,`cm`,`ce`,`ck`,
    `ms`,`ess`,`keys`]
    (let
       fun discharge_binding th =
         let val (var,value) = dest_eq (fst (dest_imp (concl th)))
         in MP (INST [var |-> value] th) (REFL value) end
     in
       mp_tac o PURE_REWRITE_RULE [AND_CLAUSES] o
         CONV_RULE (REDEPTH_CONV BETA_CONV) o
         funpow 7 discharge_binding o SPEC_ALL
     end)
    block_initialized_replay >>
  (impl_tac >- (rpt conj_tac >>
    first_assum (fn th => FIRST [ACCEPT_TAC th, CONV_TAC SYM_CONV >> ACCEPT_TAC th]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>

  (* The history certificate uses fixed, unused root markers; its depth
     marker is typed as rat.  Supply the actual evaluator's []/0 markers. *)
  qspecl_then [
     `acts`,`blocks`,`calls`,`m`,`es`,`ks`,`acts'`,`blocks'`,`calls'`,
     `m'`,`es'`,`ks'`,`p`,`d`,`inds`,`sf`,`tf`,`inc`,
     `entry`,`order`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho0`,`hin`,
     `h0`,`be`,`hbe`,`cnt0`,`s`,`post`,`(bb1,bt1,ps1,xs1,ys1,rho1,post,SUC j,body1,0,OK s1,F,NONE)`,`inst`,`next`,
     `s1`,`AM`,`AE`,`AK`,`AM'`,`AE'`,`AK'`,`N`,`N'`,
     `C7`,`rsf`,`root_entry`,`rooted_eval`,
     `\fuel ctx lev paths deps owner ent (rp:unit list) (rd:rat).
       levels_ok fuel ctx lev paths deps owner ent ([]:(num # num) list) (0:num)`]
    (mp_tac o BETA_RULE) block_initialized_historical_cuts >>
  (impl_tac >- (rpt conj_tac >>
    first_assum (fn th => FIRST [ACCEPT_TAC th, CONV_TAC SYM_CONV >> ACCEPT_TAC th]))) >>
  disch_then assume_tac >>
  `(if s1.vs_inst_idx < LENGTH ps1 then
    body1 = NONE /\
    (!F gs z. N' <= F /\ z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) ==>
      row_eval F C7 sf.fn_name (bb1,SUC d,z) (post with vs_gas_readings := gs) =
        ([],OK (s1 with vs_gas_readings := gs)))
   else
    s1.vs_inst_idx = LENGTH ps1 /\ body1 = SOME (s1,SUC j) /\
    dft_remaining_inv sf bb1 xs1 s1 /\
    cm = GENLIST (\r. if (EL r xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
    ck = GENLIST (\r. if (EL r xs1).inst_opcode = GAS then [(p,SUC d,(EL r xs1).inst_id)] else []) (LENGTH xs1) /\
    LENGTH cm = LENGTH xs1 /\ LENGTH ce = LENGTH cm /\ LENGTH ck = LENGTH cm /\
    LIST_REL (\m es. LENGTH m = LENGTH es) cm ce /\ LIST_REL (\m keys. LENGTH m = LENGTH keys) cm ck /\
    (!F q kgss tail z. N' <= F /\ q < LENGTH xs1 /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs1) /\
      (!r. r < q /\ (EL r xs1).inst_opcode = INVOKE ==> MEM r (TAKE 0 rho1)) /\
      z = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q xs1 /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss ==>
      SND (row_eval F C7 sf.fn_name (bb1,SUC d,z) (post with vs_gas_readings := FLAT kgss ++ tail)) =
        FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE q xs1) (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
      (?extra. FLAT (TAKE q ce) = FST (row_eval F C7 sf.fn_name (bb1,SUC d,z)
        (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
      (!events u. row_eval F C7 sf.fn_name (bb1,SUC d,z) (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
        events = FLAT (TAKE q ce) /\ u.vs_gas_readings = tail /\
        trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
          (bb1 with bb_instructions := TAKE (LENGTH ps1 + q) bb1.bb_instructions)
          (s1 with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE q ck),FLAT kgss) /\
        !tail'. row_eval F C7 sf.fn_name (bb1,SUC d,z) (post with vs_gas_readings := FLAT kgss ++ tail') =
          (events,OK (u with vs_gas_readings := tail')))))` by suspend "fresh_row_eval" >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0
      body_entry count front closed brest q z.
      FLOOKUP acts a = SOME _ /\ FLOOKUP blocks (a,e) = SOME _ /\ _ ==>
      ?cuts levels Mcut Ecut Kcut mr er kr. _`
    (qspecl_then [`p`,`d`,`sf`,`tf`,`inc`,`entry`,`order`,`NONE`,`NONE`,
       `bb`,`bt`,`ps`,`xs`,`ys`,`rho0`,`hin`,`h0`,`SOME (be,hbe)`,`cnt0`,
       `OK s`,`F`,`NONE`,`0`,`DROP (phi_prefix_length bb.bb_instructions) ps`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `xs = pre ++ [inst]` (fn eq => simp[NoAsms,eq]))) >>
  disch_then (choose_all [`cuts0`,`levels0`,`M0`,`E0`,`K0`,`mr0`,`er0`,`kr0`]) >>
  qexistsl [`N'`,`bb1`,`bt1`,`sp1`,`ps1`,`xs1`,`ys1`,`rho1`,`body1`,`cm`,`ce`,`ck`,`acts'`,`blocks'`,`calls'`,`inds`,`m'`,`es'`,`ks'`,`AM'`,`AE'`,`AK'`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_asm1_tac >- suspend "row_shape" >>
  conj_tac >- suspend "row_distinct" >> suspend "rooted"
QED

Resume dft_packet_block_edge_clauses[rooted]:
  map_every qx_gen_tac [`a`,`e`,`f`,`g`,`i0`,`ent`,`ord`,`r0`,`u0`,
    `b`,`t`,`ps0`,`xs0`,`ys0`,`sch`,`in0`,`h00`,`cut_beopt`,`cnt`,`res`,`closed`,`rest`,`qc`,`zc`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(a,e) = (p,SUC d)`
  >- (qpat_assum `(a,e) = (p,SUC d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      qpat_x_assum `a = p` SUBST_ALL_TAC >>
      qpat_x_assum `e = SUC d` SUBST_ALL_TAC >>
      qpat_assum `FLOOKUP acts' p = SOME (f,g,i0,ent,ord,r0,u0)` mp_tac >>
      qpat_assum `FLOOKUP blocks' (p,SUC d) = SOME (b,t,ps0,xs0,ys0,sch,in0,h00,cut_beopt,cnt,res,closed,rest)` mp_tac >>
      qpat_assum `acts' = acts |+ _` (fn acteq =>
        qpat_assum `blocks' = blocks |+ _ |+ _` (fn blockeq =>
          simp_tac std_ss [acteq,blockeq,finite_mapTheory.FLOOKUP_UPDATE,pairTheory.PAIR_EQ,optionTheory.SOME_11])) >>
      rpt strip_tac >>
      rpt (first_x_assum (fn th => if is_eq (concl th) andalso
        is_var (rhs (concl th)) andalso
        List.exists (fn n => fst (dest_var (rhs (concl th))) = n)
          ["f","g","i0","ent","ord","r0","u0","b","t","ps0","xs0","ys0","sch","in0","h00","cut_beopt","cnt","res"]
        then SUBST_ALL_TAC (SYM th) else NO_TAC)) >>
      `be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label` by
        (qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
           FLOOKUP blocks (a,e) = SOME _ ==> ?sf tf inc entry order res nrest sp. _`
           (fn clause => qpat_assum
             `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,rho0,hin,h0,SOME (be,hbe),cnt0,OK s,F,NONE)`
             (choose_all [`sf0`,`tf0`,`inc0`,`entry0`,`order0`,`res0`,`rest0`,`sp0`] o MATCH_MP clause)) >>
         qpat_assum `(case SOME (be,hbe) of NONE => _ | SOME _ => _)`
           (mp_tac o SIMP_RULE (srw_ss()) []) >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)` by
        (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
         qpat_assum `xs = pre ++ [inst]` SUBST1_TAC >>
         simp[NoAsms,APPEND_ASSOC,FRONT_APPEND,FRONT_DEF,EVERY_APPEND] >>
         conj_tac >-
           (simp[NoAsms,EVERY_MEM] >> qx_gen_tac `ii` >> disch_tac >>
            qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps`
              (qspec_then `ii` mp_tac o SIMP_RULE std_ss [EVERY_MEM]) >>
            qpat_assum `MEM ii ps` (fn mem => simp_tac std_ss [mem]) >>
            Cases_on `ii.inst_opcode` >> simp[NoAsms,is_pseudo_def,is_terminator_def]) >>
         first_assum ACCEPT_TAC) >>
      `LENGTH (FLAT ms) = LENGTH (FLAT ess) /\
       LENGTH (FLAT ms) = LENGTH (FLAT keys)` by
        (qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr.
           FLOOKUP blocks (a,e) = SOME _ /\ FLOOKUP m (a,e) = SOME mr /\
           FLOOKUP es (a,e) = SOME er /\ FLOOKUP ks (a,e) = SOME kr ==>
           LENGTH mr = LENGTH xs /\ LENGTH er = LENGTH mr /\ LENGTH kr = LENGTH mr /\
           LIST_REL _ mr er /\ LIST_REL _ mr kr /\ _`
           (qspecl_then [`p`,`d`,`bb`,`bt`,`ps`,`xs`,`ys`,`rho0`,`hin`,`h0`,`be`,`hbe`,
                        `cnt0`,`OK s`,`F`,`NONE`,`ms`,`ess`,`keys`] mp_tac) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (map_every assume_tac o CONJUNCTS) >>
         conj_tac
         >- (qpat_assum `LIST_REL (\u v. LENGTH u = LENGTH v) ms ess` mp_tac >>
             POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `ess` >> qid_spec_tac `ms` >>
             Induct >- simp[] >> gen_tac >> Cases_on `ess` >> simp[] >>
             metis_tac [arithmeticTheory.ADD_SYM]) >>
         qpat_assum `LIST_REL (\u v. LENGTH u = LENGTH v) ms keys` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `keys` >> qid_spec_tac `ms` >>
         Induct >- simp[] >> gen_tac >> Cases_on `keys` >> simp[] >>
         metis_tac [arithmeticTheory.ADD_SYM]) >>
      `~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET]` by
        (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
         qpat_assum `xs = pre ++ [inst]` SUBST1_TAC >>
         simp[NoAsms,LAST_APPEND] >> rpt conj_tac >> disch_tac >>
         pop_assum (fn op_eq =>
           qpat_assum `step_inst (N-d) C8 inst s = OK post` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >>
           simp[op_eq,venomExecSemanticsTheory.step_inst_non_invoke,
             venomExecSemanticsTheory.step_inst_base_opcode_eqs, AllCaseEqs()] >>
           rpt strip_tac >> gvs[] >> pairarg_tac >> gvs[])) >>
      mp_tac (Q.INST [`root_sf` |-> `rsf`, `Nnew` |-> `N'`,
        `ms_tab` |-> `m`, `es_tab` |-> `es`, `ks_tab` |-> `ks`,
        `ms_tab'` |-> `m'`, `es_tab'` |-> `es'`, `ks_tab'` |-> `ks'`,
        `h1` |-> `SUC j`, `q` |-> `qc`, `z` |-> `zc`,
        `z0` |-> `DROP (phi_prefix_length bb.bb_instructions) ps`,
        `Z` |-> `DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions`,
        `Mb` |-> `FLAT ms`, `Eb` |-> `FLAT ess`, `Kb` |-> `FLAT keys`]
        block_initialized_fresh_cut) >>
      (impl_tac >-
        ((* Literal evaluators and retained activation/table facts. *)
         ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >- suspend "fresh_old_blocks" >>
         ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >- suspend "fresh_old_replay" >>
         conj_tac >- suspend "fresh_old_closed" >>
         conj_tac >- suspend "fresh_old_calls" >>
         conj_tac >- suspend "fresh_live_blocks" >>
         conj_tac >- first_assum ACCEPT_TAC >>
         ntac 2 (conj_tac >- REFL_TAC) >>
         ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >- suspend "fresh_anchor_cuts" >>
         ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >- suspend "fresh_anchor_replay" >>
         (* Completed source row. *)
         ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >-
           (qpat_assum `xs = pre ++ [inst]` (fn th => simp[NoAsms,th])) >>
         conj_tac >-
           (qpat_assum `xs = pre ++ [inst]` SUBST1_TAC >>
            simp_tac list_ss [LAST_APPEND] >> first_assum ACCEPT_TAC) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
            qpat_assum `xs = pre ++ [inst]` SUBST1_TAC >> simp[NoAsms]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qpat_assum `bb.bb_instructions = ps ++ xs` SUBST1_TAC >>
            qpat_assum `xs = pre ++ [inst]` SUBST1_TAC >>
            simp_tac list_ss [LAST_APPEND] >> first_assum ACCEPT_TAC) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qpat_assum `FLOOKUP m (p,d) = SOME ms` (fn th => simp[NoAsms,th])) >>
         conj_tac >-
           (qpat_assum `FLOOKUP es (p,d) = SOME ess` (fn th => simp[NoAsms,th])) >>
         conj_tac >-
           (qpat_assum `FLOOKUP ks (p,d) = SOME keys` (fn th => simp[NoAsms,th])) >>
         ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >-
           (map_every qx_gen_tac [`fuel`,`fill`,`tail0`] >>
            disch_then (map_every assume_tac o CONJUNCTS) >>
            qpat_assum `!F. N <= F ==> FOLDR (dft_exec_cons (F-d) C8) OK ys be = OK post /\ _`
              (qspec_then `fuel` (drule_then
                (qspec_then `fill` (drule_then (qspec_then `tail0`
                  (map_every assume_tac o CONJUNCTS))) o CONJUNCT2))) >>
            (conj_tac >- first_assum ACCEPT_TAC) >>
            (reverse conj_tac >- first_assum ACCEPT_TAC) >>
            disch_tac >>
            qpat_assum `(?f. terminates _) ==> terminates _ /\ dft_res_rel _ _ /\ _`
              (drule_then (mp_tac o cj 3)) >>
            (impl_tac >- (disj1_tac >> qexists `post` >> REFL_TAC)) >>
            disch_then ACCEPT_TAC) >>
         (* Initialized row and updates to the retained parent cells. *)
         ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >-
           (qpat_assum `bb1.bb_label = post.vs_current_bb` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         conj_tac >-
           (qpat_assum `bb1.bb_label = post.vs_current_bb` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
         conj_tac >-
           (qpat_assum `lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1`
              (ACCEPT_TAC o MATCH_MP lookup_block_MEM)) >>
         ntac 16 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >- suspend "fresh_parent_calls" >>
         ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
         conj_tac >- suspend "fresh_parent_tables" >>
         conj_tac >-
           (qpat_assum `(IS_SOME body1 /\ _ \/ body1 = NONE /\ _)`
              (ACCEPT_TAC o REWRITE_RULE [])) >>
         first_assum ACCEPT_TAC)) >>
      suspend "fresh_output") >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho in_state h0
    body_entry count front closed brest q z. (a,e) <> (p,SUC d) /\ _ ==> _`
    (qspecl_then [`a`,`e`,`f`,`g`,`i0`,`ent`,`ord`,`r0`,`u0`,
      `b`,`t`,`ps0`,`xs0`,`ys0`,`sch`,`in0`,`h00`,`cut_beopt`,`cnt`,`res`,`closed`,`rest`,`qc`,`zc`]
      (match_mp_tac o BETA_RULE)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[replay_fresh]:
  disch_tac >>
  Cases_on `s1.vs_inst_idx < LENGTH ps1`
  >- (pop_assum (fn guard =>
      qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\ cm = [] /\ _ else _`
        (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [guard,COND_CLAUSES])) >>
      qpat_assum `body1 = NONE` (fn none =>
        qpat_assum `body1 <> NONE` (CONTR_TAC o REWRITE_RULE [none]))) >>
  pop_assum (fn guard =>
    qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\ cm = [] /\ _ else _`
      (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [guard,COND_CLAUSES])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `idx` >> strip_tac >>
     qpat_assum `!q. q < LENGTH xs1 ==> _ /\ _`
       (drule_then (drule_then ACCEPT_TAC o CONJUNCT2))) >>
  first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[replay_parent]:
  qx_gen_tac `idx` >> disch_tac >>
  qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys sched hin h0
      be hbe count q h b0 done_at_call child_entry cid e a. _`
    (qspec_then `idx` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (choose_all [`src`,`tgt`,`incoming`,`ent`,`visits`,`src_bb`,`tgt_bb`,
    `pseudos`,`src_body`,`tgt_body`,`schedule`,`at_entry`,`visit_idx`,`at_body`,
    `body_idx`,`done_count`,`source_index`,`call_index`,`call_state`,`done`,
    `child_state`,`call_id`,`depth`,`path`]) >>
  qpat_assum `!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hbe count front closed brest cf cg cord cr cu.
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ (EL q xs).inst_id = cid /\
      FLOOKUP acts ((e,cid)::a) = SOME (cf,cg,e,child,cord,cr,cu)`
    (qspecl_then [`path`,`depth`,`call_id`] (drule_then
      (choose_all [`call_bb`,`call_bt`,`call_ps`,`call_xs`,`call_ys`,`call_rho`,
        `call_hin`,`call_h0`,`call_be`,`call_hbe`,`call_count`,`call_front`,
        `call_closed`,`call_rest`,`child_src`,`child_tgt`,`child_ord`,`child_res`,`child_gas`]))) >>
  `path <> p` by
    (qpat_assum `path = DROP (SUC idx) p` SUBST1_TAC >>
     strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH : (num # num) list -> num``) >>
     simp[LENGTH_DROP]) >>
  `FLOOKUP blocks' (path,depth) = FLOOKUP blocks (path,depth)` by
    (qpat_assum `path <> p` (fn different =>
       qpat_assum `blocks' = _ |+ _ |+ _` (fn update =>
         simp[NoAsms,different,update,finite_mapTheory.FLOOKUP_UPDATE,pairTheory.PAIR_EQ]))) >>
  `FLOOKUP blocks (path,depth) =
     SOME (src_bb,tgt_bb,pseudos,src_body,tgt_body,schedule,at_entry,visit_idx,
           SOME (at_body,body_idx),done_count,OK call_state,F,NONE)` by
    (qpat_assum `FLOOKUP blocks' (path,depth) = FLOOKUP blocks (path,depth)`
       (fn same =>
         qpat_assum `FLOOKUP blocks' (path,depth) =
           SOME (src_bb,tgt_bb,pseudos,src_body,_,_,_,_,_,_,_,_,_)`
           (ACCEPT_TAC o TRANS (SYM same)))) >>
  `call_xs = src_body` by
    (qpat_assum `FLOOKUP blocks (path,depth) = SOME (src_bb,tgt_bb,pseudos,src_body,_,_,_,_,_,_,_,_,_)`
      (fn th =>
        qpat_assum `FLOOKUP blocks (path,depth) = SOME (call_bb,_,_,_,_,_,_,_,_,_,_,_,_)`
          (mp_tac o REWRITE_RULE [th])) >>
     simp[NoAsms,optionTheory.SOME_11,pairTheory.PAIR_EQ]) >>
  qpat_x_assum `call_xs = src_body` SUBST_ALL_TAC >>
  qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME _ ==> ?sf tf inc entry order res nrest sp. _`
    (fn clauses =>
      qpat_assum `FLOOKUP blocks (path,depth) =
        SOME (src_bb,tgt_bb,pseudos,src_body,_,_,_,_,_,_,_,_,_)`
        (choose_all [`src0`,`tgt0`,`incoming0`,`ent0`,`visits0`,`res0`,`rest0`,`phi_state`] o
         MATCH_MP clauses)) >>
  `dft_fn_rel src0 tgt0` by
    (qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts a = _ ==> MEM _ _ /\ _`
       (fn clauses =>
         qpat_assum `FLOOKUP acts path = SOME (src0,tgt0,_,_,_,_,_)`
           (ACCEPT_TAC o cj 3 o MATCH_MP clauses))) >>
  `EL idx inds = source_index` by
    (qpat_assum `inds = GENLIST _ _` (fn def =>
       qpat_assum `idx < LENGTH p` (fn bound =>
         PURE_REWRITE_TAC [def,MATCH_MP EL_GENLIST bound])) >>
     CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     qpat_assum `(depth,call_id) = EL idx p` (fn th => PURE_REWRITE_TAC [SYM th]) >>
     qpat_assum `path = DROP (SUC idx) p` (fn th => PURE_REWRITE_TAC [SYM th]) >>
     qpat_assum `FLOOKUP calls (path,depth,call_id) =
       SOME (source_index,call_index,call_state,done,child_state,NONE)`
       (fn th => simp[NoAsms,th])) >>
  qexistsl [`src0`,`tgt0`,`src_bb`,`tgt_bb`,`pseudos`,`src_body`,`tgt_body`,
    `schedule`,`at_entry`,`visit_idx`,`at_body`,`body_idx`,`done_count`,`call_state`,
    `done`,`child_state`,`call_index`] >>
  qpat_assum `(depth,call_id) = EL idx p` (fn th => rewrite_tac [SYM th]) >>
  qpat_assum `path = DROP (SUC idx) p` (fn th => rewrite_tac [SYM th]) >>
  qpat_assum `EL idx inds = source_index` (fn th => rewrite_tac [th]) >>
  simp_tac std_ss [pairTheory.FST,pairTheory.SND] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_row_eval]:
  Cases_on `s1.vs_inst_idx < LENGTH ps1`
  >- (pop_assum (fn guard =>
       PURE_REWRITE_TAC [guard,COND_CLAUSES] >>
       qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\ cm = [] /\ _ else _`
         (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [guard,COND_CLAUSES])) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      map_every qx_gen_tac [`fuel`,`gs`,`z`] >>
      qpat_assum `!F gs z R. _ ==> R _ = _`
        (qspecl_then [`fuel`,`gs`,`z`,`row_eval fuel C7 sf.fn_name (bb1,SUC d,z)`] mp_tac) >>
      qpat_assum `row_eval = _` (fn eq => simp[NoAsms,eq])) >>
  pop_assum (fn guard =>
    PURE_REWRITE_TAC [guard,COND_CLAUSES] >>
    qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\ cm = [] /\ _ else _`
      (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [guard,COND_CLAUSES])) >>
  ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`fuel`,`q`,`kgss`,`tail`,`z`] >> strip_tac >>
  qpat_assum `!F q kgss tail z R. _ ==> SND (R _) = _ /\ _`
    (qspecl_then [`fuel`,`q`,`kgss`,`tail`,`z`,`row_eval fuel C7 sf.fn_name (bb1,SUC d,z)`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `row_eval = _` (fn eq => SIMP_TAC std_ss [eq])])) >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_old_closed]:
  map_every qx_gen_tac [`a`,`e`,`f`,`g`,`i0`,`ent`,`ord`,`res0`,`rest0`,
    `b`,`t`,`pref`,`src`,`tgt`,`sched`,`in0`,`at0`,`bdy`,`atb`,`pos`,`r8`,`u0`,`mr`,`er`,`kr`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qx_gen_tac `fuel` >> disch_tac >>
  map_every qx_gen_tac [`fill`,`tail0`] >> ntac 3 disch_tac >>
  qpat_assum `!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count
    r8 u0 mr er kr.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME _ /\ FLOOKUP m (a,e) = SOME mr /\
    FLOOKUP es (a,e) = SOME er /\ FLOOKUP ks (a,e) = SOME kr ==>
    terminates r8 /\ PERM _ _ /\ _`
    (qspecl_then [`a`,`e`,`f`,`g`,`i0`,`ent`,`ord`,`res0`,`rest0`,
      `b`,`t`,`pref`,`src`,`tgt`,`sched`,`in0`,`at0`,`bdy`,`atb`,`pos`,`r8`,`u0`,`mr`,`er`,`kr`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspec_then `fuel` mp_tac o cj 4) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`fill`,`tail0`] mp_tac o CONJUNCT2) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o cj 2) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (mp_tac o cj 3) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[NoAsms]
QED

Resume dft_packet_block_edge_clauses[fresh_old_replay]:
  map_every qx_gen_tac [`a`,`e`,`b`,`t`,`pref`,`src`,`tgt`,`sched`,`in0`,
    `at0`,`bdy`,`atb`,`pos`,`front`,`closed`,`rest0`,`mr`,`er`,`kr`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  (conj_tac >-
    (qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr.
       FLOOKUP blocks (a,e) = SOME _ /\ FLOOKUP m (a,e) = SOME mr /\
       FLOOKUP es (a,e) = SOME er /\ FLOOKUP ks (a,e) = SOME kr ==>
       LENGTH mr = LENGTH xs /\ LENGTH er = LENGTH mr /\ LENGTH kr = LENGTH mr /\
       LIST_REL _ mr er /\ LIST_REL _ mr kr /\ _`
      (qspecl_then [`a`,`e`,`b`,`t`,`pref`,`src`,`tgt`,`sched`,`in0`,
        `at0`,`bdy`,`atb`,`pos`,`front`,`closed`,`rest0`,`mr`,`er`,`kr`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1))) >>
  map_every qx_gen_tac [`f`,`g`,`i0`,`ent`,`ord`,`res0`,`nrest0`] >> disch_tac >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr sf tf inc entry order res nrest.
    _ ==> !F k kgss tail. _ ==> _`
    (qspecl_then [`a`,`e`,`b`,`t`,`pref`,`src`,`tgt`,`sched`,`in0`,
       `at0`,`bdy`,`atb`,`pos`,`front`,`closed`,`rest0`,`mr`,`er`,`kr`,
       `f`,`g`,`i0`,`ent`,`ord`,`res0`,`nrest0`] match_mp_tac) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_old_calls]:
  map_every qx_gen_tac [`a`,`e`,`cid`,`q`,`h`,`b0`,`done`,`child`,`ret`] >> disch_tac >>
  qpat_assum `!a e cid q h b0 done child ret.
    FLOOKUP calls (a,e,cid) = SOME _ ==> ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0
    be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ _`
    (qspecl_then [`a`,`e`,`cid`,`q`,`h`,`b0`,`done`,`child`,`ret`] (drule_then
      (choose_all [`call_sf`,`call_tf`,`call_inc`,`call_ent`,`call_ord`,`call_r`,`call_rest`,
        `call_bb`,`call_bt`,`call_ps`,`call_xs`,`call_ys`,`call_rho`,`call_in`,
        `call_h0`,`call_be`,`call_hbe`,`call_count`,`call_front`,`call_closed`,`call_brest`,
        `child_sf`,`child_tf`,`child_ord`,`child_r`,`child_rest`,`call_inst`,`call_nm`,`call_ops`,`call_args`]))) >>
  `(case ret of
      NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
    | SOME triple => MEM q (TAKE call_count call_rho))` by
    (qpat_assum `(case ret of NONE => _ | SOME _ => _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `ret` >>
     simp[NoAsms,pairTheory.pair_CASE_UNCURRY,pairTheory.ELIM_UNCURRY,combinTheory.C_THM]) >>
  qexistsl [`call_sf`,`call_tf`,`call_inc`,`call_ent`,`call_ord`,`call_r`,`call_rest`,
    `call_bb`,`call_bt`,`call_ps`,`call_xs`,`call_ys`,`call_rho`,`call_in`,
    `call_h0`,`call_be`,`call_hbe`,`call_count`,`call_front`,`call_closed`,`call_brest`,
    `child_sf`,`child_tf`,`child_ord`,`child_r`,`child_rest`,`call_nm`,`call_ops`,`call_args`] >>
  ntac 12 (conj_tac >-
    (qpat_assum `call_inst = EL q call_xs` (fn th =>
        once_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC)) >>
  first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_old_blocks]:
  map_every qx_gen_tac [`a`,`e`,`b`,`t`,`pref`,`src`,`tgt`,`sched`,
    `in0`,`at0`,`old_body_opt`,`pos`,`front`,`closed`,`rest0`] >> disch_tac >>
  qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks (a,e) = SOME _ ==> ?sf tf inc entry order res nrest sp.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\ _`
    (qspecl_then [`a`,`e`,`b`,`t`,`pref`,`src`,`tgt`,`sched`,`in0`,`at0`,`old_body_opt`,`pos`,`front`,`closed`,`rest0`]
      (drule_then (choose_all [`blk_sf`,`blk_tf`,`blk_inc`,`blk_ent`,`blk_ord`,`blk_r`,`blk_u`,`blk_phi`]))) >>
  qexistsl [`blk_sf`,`blk_tf`,`blk_inc`,`blk_ent`,`blk_ord`,`blk_r`,`blk_u`,`blk_phi`] >>
  ntac 10 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `(case old_body_opt of NONE => _ | SOME _ => _)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> Cases_on `old_body_opt` >>
      simp[NoAsms,pairTheory.pair_CASE_UNCURRY,pairTheory.ELIM_UNCURRY,combinTheory.C_THM]) >>
  qpat_assum `e <> LAST blk_ord ==> closed /\ _` (ACCEPT_TAC o cj 1)
QED

Resume dft_packet_block_edge_clauses[fresh_live_blocks]:
  qx_gen_tac `ix` >> disch_tac >>
  qpat_assum `!k. k < LENGTH p ==>
    ?sf tf inc entry order bb bt ps xs ys sched hin h0 be hbe count
      q h b0 done_at_call child_entry cid e a.
      a = DROP (SUC k) p /\ (e,cid) = EL k p /\
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\ LAST order = e /\ _`
    (qspec_then `ix` (drule_then (choose_all
      [`lsf`,`ltf`,`linc`,`lent`,`lord`,`lbb`,`lbt`,`lps`,`lxs`,`lys`,`lrho`,
       `lin`,`lh0`,`lbe`,`lhbe`,`lcnt`,`lq`,`lh`,`lb0`,`ldone`,`lchild`,`lcid`,`le`,`la`]))) >>
  qexistsl [`lbb`,`lbt`,`lps`,`lxs`,`lys`,`lrho`,`lin`,`lh0`,`lbe`,`lhbe`,
    `lcnt`,`lq`,`lh`,`lb0`,`ldone`,`lchild`,`lcid`,`le`,`la`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_anchor_cuts]:
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = _ ==> _` mp_tac >>
  simp[NoAsms,pairTheory.pair_CASE_UNCURRY,pairTheory.ELIM_UNCURRY,combinTheory.C_THM]
QED

Resume dft_packet_block_edge_clauses[fresh_anchor_replay]:
  map_every qx_gen_tac [`fuel`,`fill`,`tail0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!F gs tail. N <= F /\ _ ==> levels_ok F C7 levels0 _ _ _ _ [] 0 /\ _`
    (qspecl_then [`fuel`,`fill`,`tail0`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  pop_assum mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `SND (rooted_eval fuel C7 levels0 (root_entry with vs_gas_readings := fill ++ tail0))` >>
  simp[NoAsms]
QED

Resume dft_packet_block_edge_clauses[fresh_parent_tables]:
  qx_gen_tac `idx` >> disch_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done child ch.
      FLOOKUP blocks _ = SOME _ /\ FLOOKUP calls _ = SOME (EL i inds,_,_,_,_) /\ _`
    (qspec_then `idx` (fn th => mp_tac th)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (choose_all [`par_sf`,`par_tf`,`par_bb`,`par_bt`,`par_ps`,`par_xs`,
    `par_ys`,`par_rho`,`par_hin`,`par_h`,`par_be`,`par_hbe`,`par_pos`,
    `par_b0`,`par_done`,`par_child`,`par_ch`]) >>
  `((DROP (SUC idx) p,FST (EL idx p)) IN FDOM blocks)` by
    (simp[NoAsms,FDOM_FLOOKUP] >> goal_assum (drule_at Any)) >>
  `?mr. FLOOKUP m (DROP (SUC idx) p,FST (EL idx p)) = SOME mr` by
    (rewrite_tac[GSYM FDOM_FLOOKUP] >>
     qpat_assum `FDOM blocks = FDOM m` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `?er. FLOOKUP es (DROP (SUC idx) p,FST (EL idx p)) = SOME er` by
    (rewrite_tac[GSYM FDOM_FLOOKUP] >>
     qpat_assum `FDOM blocks = FDOM es` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `?kr. FLOOKUP ks (DROP (SUC idx) p,FST (EL idx p)) = SOME kr` by
    (rewrite_tac[GSYM FDOM_FLOOKUP] >>
     qpat_assum `FDOM blocks = FDOM ks` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH mr = LENGTH par_xs /\ LENGTH er = LENGTH mr /\ LENGTH kr = LENGTH mr` by
    (qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks0.
        FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME _,_,_,_,_) /\
        FLOOKUP m (a,e) = SOME ms /\ FLOOKUP es (a,e) = SOME ess /\
        FLOOKUP ks (a,e) = SOME ks0 ==> LENGTH ms = LENGTH xs /\ _`
       (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!i mr er kr. i < LENGTH p /\ FLOOKUP m _ = SOME mr /\
      FLOOKUP es _ = SOME er /\ FLOOKUP ks _ = SOME kr ==> FLOOKUP m' _ = _ /\ _`
    (qspecl_then [`idx`,`mr`,`er`,`kr`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL idx inds < LENGTH mr /\ EL idx inds < LENGTH er /\ EL idx inds < LENGTH kr` by
    (qpat_assum `LENGTH mr = LENGTH par_xs` (fn mlen =>
       qpat_assum `LENGTH er = LENGTH mr` (fn elen =>
         qpat_assum `LENGTH kr = LENGTH mr` (fn klen =>
           qpat_assum `EL idx inds < LENGTH par_xs` (fn bound =>
             simp[NoAsms,mlen,elen,klen,bound]))))) >>
  qexistsl [`mr`,`er`,`kr`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_parent_calls]:
  qx_gen_tac `idx` >> disch_tac >>
  qpat_assum `!i. i < LENGTH p ==> ?a e cid f g ai ent ord q h b done child.
    a = DROP (SUC i) p /\ (e,cid) = EL i p /\ FLOOKUP acts a = SOME _ /\
    LAST ord = e /\ FLOOKUP calls (a,e,cid) = SOME _`
    (qspec_then `idx` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (choose_all [`path`,`dep`,`cid0`,`par_sf`,`par_tf`,`par_inc`,`par_ent`,
    `par_ord`,`par_q`,`par_h`,`par_b`,`par_done`,`child_ent`]) >>
  qpat_assum `!i. i < LENGTH p ==> ?h b done child.
    FLOOKUP calls' (DROP (SUC i) p,FST (EL i p),SND (EL i p)) = SOME (EL i inds,h,b,done,child,NONE)`
    (qspec_then `idx` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `calls' = calls` (fn same => rewrite_tac[same]) >>
  disch_then (choose_all [`h1`,`b1`,`done1`,`child1`]) >>
  qexistsl [`h1`,`b1`,`done1`,`child1`,`par_ord`,`par_sf`,`par_tf`,`par_inc`,`par_ent`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `(dep,cid0) = EL idx p` (fn paths =>
    qpat_assum `path = DROP (SUC idx) p` (fn drop =>
      simp[NoAsms,GSYM paths,GSYM drop,pairTheory.FST])) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_block_edge_clauses[fresh_output]:
  disch_then (choose_all [`cuts1`,`levels1`,`M1`,`E1`,`K1`,`mr1`,`er1`,`kr1`]) >>
  qexistsl [`cuts1`,`levels1`,`mr1`,`er1`,`kr1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "fresh_output_geometry" >>
  rpt (conj_tac >- (qpat_assum `M1 = _` (fn mm =>
    qpat_assum `E1 = _` (fn ee => qpat_assum `K1 = _` (fn kk =>
      PURE_REWRITE_TAC [SYM mm,SYM ee,SYM kk]))) >> first_assum ACCEPT_TAC)) >>
  suspend "fresh_output_semantics"
QED

Resume dft_packet_block_edge_clauses[fresh_output_geometry]:
  map_every qx_gen_tac [`cut_idx`,`cut_path`,`cut_prior`,`cut_depth`,`cut_q`,`cut_z`] >>
  disch_tac >>
  qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts1 /\ EL i cuts1 = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later.
        FLOOKUP acts' ai = SOME _ /\ _`
    (qspecl_then [`cut_idx`,`cut_path`,`cut_prior`,`cut_depth`,`cut_q`,`cut_z`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (choose_all [`cut_sf`,`cut_tf`,`cut_inc`,`cut_entry`,`cut_order`,`cut_res`,
    `cut_rest`,`cut_bb`,`cut_bt`,`cut_ps`,`cut_xs`,`cut_ys`,`cut_rho`,`cut_in`,`cut_h`,
    `cut_body`,`cut_count`,`cut_front`,`cut_closed`,`cut_brest`,`cut_later`]) >>
  qexistsl [`cut_sf`,`cut_tf`,`cut_inc`,`cut_entry`,`cut_res`,`cut_rest`,
    `cut_bb`,`cut_bt`,`cut_ps`,`cut_xs`,`cut_ys`,`cut_rho`,`cut_in`,`cut_h`,
    `cut_body`,`cut_count`,`cut_front`,`cut_closed`,`cut_brest`,`cut_later`] >>
  qpat_assum `cut_order = cut_prior ++ cut_depth::cut_later`
    (fn th => PURE_REWRITE_TAC [SYM th]) >>
  conj_tac
  >- ((qpat_assum `FLOOKUP acts' cut_path = SOME _` mp_tac >>
      qpat_assum `acts' = _ |+ _` (fn th =>
        simp[NoAsms,th,finite_mapTheory.FLOOKUP_UPDATE]) >> (simp[]))) >>
  conj_tac
  >- (qpat_assum `FLOOKUP blocks' (cut_path,cut_depth) = SOME _` mp_tac >>
      qpat_assum `blocks' = _ |+ _ |+ _` (fn th =>
        simp[NoAsms,th,finite_mapTheory.FLOOKUP_UPDATE,pairTheory.PAIR_EQ]) >>
      simp[]) >>
  reverse conj_tac
  >- (qpat_assum `EL cut_idx levels1 = _` mp_tac >>
      qpat_assum `blocks' = _ |+ _ |+ _` (fn th =>
        simp[NoAsms,th,finite_mapTheory.FLOOKUP_UPDATE,pairTheory.PAIR_EQ,
          pairTheory.pair_CASE_UNCURRY,pairTheory.ELIM_UNCURRY,combinTheory.C_THM]) >>
      simp[]) >>
  qpat_assum `if SUC cut_idx = LENGTH cuts1 then cut_path = p /\ _ else _` mp_tac >>
  qpat_assum `calls' = calls` (fn th => rewrite_tac[th]) >>
  POP_ASSUM_LIST (K all_tac) >>
  Cases_on `SUC cut_idx = LENGTH cuts1` >> simp[NoAsms]
QED

Resume dft_packet_block_edge_clauses[fresh_output_semantics]:
  qpat_assum `M1 = _` (fn mm =>
    qpat_assum `E1 = _` (fn ee => qpat_assum `K1 = _` (fn kk =>
      PURE_REWRITE_TAC [SYM mm,SYM ee,SYM kk]))) >>
  qpat_assum `!F gs tail. N' <= F /\ LIST_REL _ M1 gs ==> levels_ok _ _ levels1 _ _ _ _ [] 0 /\ _`
    mp_tac >>
  qpat_assum `acts' = _ |+ _` (fn th =>
    qpat_assum `NONE = rest` (fn same =>
      simp[NoAsms,GSYM same,th,finite_mapTheory.FLOOKUP_UPDATE]))
QED

Resume dft_packet_block_edge_clauses[row_shape]:
  map_every qx_gen_tac [`a`,`e`,`rb`,`rt`,`rps`,`rxs`,`rys`,`rsched`,`rin`,`rh`,
    `rbe`,`rhb`,`rcnt`,`rr`,`rclosed`,`rrest`,`mr`,`er`,`kr`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(a,e) = (p,SUC d)`
  >- (qpat_assum `(a,e) = (p,SUC d)` (strip_assume_tac o REWRITE_RULE [pairTheory.PAIR_EQ]) >>
      qpat_x_assum `a = p` SUBST_ALL_TAC >> qpat_x_assum `e = SUC d` SUBST_ALL_TAC >>
      suspend "shape_fresh") >>
  suspend "shape_old"
QED

Resume dft_packet_block_edge_clauses[shape_fresh]:
  `!cid. ALOOKUP obs (p,SUC d,cid) = NONE` by suspend "fresh_obs_absent" >>
  qpat_assum `FLOOKUP blocks' (p,SUC d) = SOME (rb,rt,rps,rxs,rys,rsched,rin,rh,SOME (rbe,rhb),rcnt,rr,rclosed,rrest)` mp_tac >>
  qpat_assum `blocks' = _ |+ _ |+ _` (fn eq =>
    simp[NoAsms,eq,finite_mapTheory.FLOOKUP_UPDATE,pairTheory.PAIR_EQ]) >>
  strip_tac >>
  `body1 <> NONE` by (qpat_assum `body1 = SOME _` (fn eq => simp[NoAsms,eq])) >>
  Cases_on `s1.vs_inst_idx < LENGTH ps1` >>
  pop_assum (fn guard =>
    qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then body1 = NONE /\ cm = [] /\ _ else _`
      (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [guard,COND_CLAUSES]))
  >- (qpat_assum `body1 = NONE` (fn eq =>
      qpat_assum `body1 <> NONE` (CONTR_TAC o REWRITE_RULE [eq]))) >>
  `mr = cm /\ er = ce /\ kr = ck` by
    (map_every (fn (canonical,actual) =>
       qpat_assum canonical (fn eq =>
         qpat_assum actual (mp_tac o REWRITE_RULE [eq])) )
      [(`FLOOKUP m' (p,SUC d) = SOME cm`,`FLOOKUP m' (p,SUC d) = SOME mr`),
       (`FLOOKUP es' (p,SUC d) = SOME ce`,`FLOOKUP es' (p,SUC d) = SOME er`),
       (`FLOOKUP ks' (p,SUC d) = SOME ck`,`FLOOKUP ks' (p,SUC d) = SOME kr`)] >>
     simp[NoAsms,Once EQ_SYM_EQ]) >>
  conj_tac >- (qpat_assum `LENGTH cm = LENGTH xs1` mp_tac >>
    qpat_assum `mr = cm` (fn m => qpat_assum `xs1 = rxs` (fn x => simp[NoAsms,m,x]))) >>
  map_every qx_gen_tac [`rf`,`rg`,`ri`,`rent`,`rord`,`rres`,`ru`] >>
  qpat_assum `acts' = _ |+ _` (fn eq =>
    simp[NoAsms,eq,finite_mapTheory.FLOOKUP_UPDATE,pairTheory.PAIR_EQ]) >>
  strip_tac >> qx_gen_tac `idx` >> strip_tac >>
  qpat_assum `!q. q < LENGTH xs1 ==> _ /\ _` (qspec_then `idx` mp_tac) >>
  qpat_assum `idx < LENGTH rxs` (fn bound =>
    qpat_assum `xs1 = rxs` (fn x =>
    qpat_assum `mr = cm` (fn m => qpat_assum `er = ce` (fn es =>
    qpat_assum `kr = ck` (fn ks => qpat_assum `sf = rf` (fn f =>
    qpat_assum `!cid. ALOOKUP obs (p,SUC d,cid) = NONE` (fn absent =>
      simp[NoAsms,bound,x,m,es,ks,f,absent])))))))
QED

Resume dft_packet_block_edge_clauses[fresh_obs_absent]:
  `!cid. ~MEM (p,SUC d,cid) (AK [])` by suspend "fresh_key_absent" >>
  qpat_assum `PERM _ obs` (strip_assume_tac o MATCH_MP sortingTheory.PERM_MEM_EQ) >>
  qpat_assum `LENGTH (AK []) = LENGTH (AM [])` mp_tac >>
  qpat_assum `!cid. ~MEM (p,SUC d,cid) (AK [])` mp_tac >>
  qpat_assum `!x. MEM x _ <=> MEM x obs` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[alistTheory.ALOOKUP_NONE,MEM_MAP,MEM_FILTER,pairTheory.EXISTS_PROD] >>
  rpt strip_tac >>
  rename1 `MEM ((p,SUC d,cid),w) obs` >>
  `?slot. MEM ((p,SUC d,cid),slot) (ZIP (AK [],AM []))` by metis_tac[pairTheory.PAIR_EQ] >>
  qspecl_then [`AK []`,`AM []`,`((p,SUC d,cid),slot)`] mp_tac listTheory.MEM_ZIP >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (drule_then (qx_choose_then `i` strip_assume_tac) o iffLR) >>
  qpat_assum `!cid. ~MEM (p,SUC d,cid) (AK [])` (qspec_then `cid` mp_tac) >>
  qpat_assum `((p,SUC d,cid),slot) = _` (fn eq =>
    mp_tac (AP_TERM ``FST : gas_event # bytes32 option -> gas_event`` eq)) >>
  qpat_assum `i < LENGTH (AK [])` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[] >> metis_tac[MEM_EL]
QED

Resume dft_packet_block_edge_clauses[fresh_key_absent]:
  mp_tac (Q.SPECL [`acts`,`blocks`,`calls`,`ks`,`AK`]
    dftPacketPseudoKeyFreshnessTheory.dft_packet_retained_key_origin_clauses) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> conj_tac >-
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!a f g ai ent ord r u. FLOOKUP acts a = SOME _ ==> ord <> [] /\ _`
       (drule_then (fn th => mp_tac (cj 3 th))) >>
     disch_then (drule_then ACCEPT_TAC o iffLR)) >>
    suspend "fresh_origin_rows")) >>
  qpat_assum `?rsf rtf rinc rentry rorder rres rrest. FLOOKUP acts [] = SOME _`
    (choose_all [`base_sf`,`base_tf`,`base_inc`,`base_entry`,`base_ord`,`base_r`,`base_rest`]) >>
  disch_then (qspecl_then [`[]`,`base_sf`,`base_tf`,`base_inc`,`base_entry`,
    `base_ord`,`base_r`,`base_rest`,`p`,`SUC d`] assume_tac) >>
  qpat_assum `FLOOKUP acts [] = SOME (base_sf,base_tf,base_inc,base_entry,base_ord,base_r,base_rest)` mp_tac >>
  qpat_assum `(p,SUC d) NOTIN FDOM blocks` mp_tac >>
  qpat_assum `!cid. FLOOKUP acts [] = SOME (base_sf,base_tf,_,_,_,_,_) /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[finite_mapTheory.flookup_thm,optionTheory.NOT_NONE_SOME]
QED

Resume dft_packet_block_edge_clauses[fresh_origin_rows]:
  rpt gen_tac >> disch_tac >>
  rename1 `FLOOKUP blocks (a,f) = SOME (_,_,_,src,_,_,_,_,row_entry,_,_,_,_)` >>
  namedCases_on `row_entry` ["", "be_pair"]
  >- (qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest.
        FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,body,_,_,_,_) ==> body = NONE ==> _`
        (qspecl_then [`a`,`f`] (drule_then (fn th => simp[NoAsms,th])))) >>
  PairCases_on `be_pair` >>
  `(a,f) IN FDOM blocks` by
    (qpat_assum `FLOOKUP blocks (a,f) = SOME _`
      (mp_tac o REWRITE_RULE [finite_mapTheory.flookup_thm]) >> simp[NoAsms]) >>
  `?mr er kr. FLOOKUP m (a,f) = SOME mr /\ FLOOKUP es (a,f) = SOME er /\
       FLOOKUP ks (a,f) = SOME kr` by
    (qexistsl [`m ' (a,f)`,`es ' (a,f)`,`ks ' (a,f)`] >>
     simp[NoAsms,finite_mapTheory.flookup_thm] >>
     map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
       [`FDOM blocks = FDOM m`,`FDOM blocks = FDOM es`,`FDOM blocks = FDOM ks`] >>
     qpat_assum `(a,f) IN FDOM blocks` (fn th => simp[NoAsms,th])) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest mr er kr.
    FLOOKUP blocks (a,e) = SOME _ /\ _ ==> LENGTH mr = LENGTH xs /\ _ /\ _ /\ _ /\ _ /\ _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  rename1 `FLOOKUP ks (a,f) = SOME old_keys` >>
  rename1 `FLOOKUP m (a,f) = SOME old_slots` >>
  qpat_assum `FLOOKUP ks (a,f) = SOME old_keys` (fn lookup =>
    qpat_assum `LENGTH old_keys = LENGTH old_slots` (fn kl =>
      qpat_assum `LENGTH old_slots = LENGTH src` (fn ml =>
        simp[NoAsms,lookup,kl,ml]))) >>
  qx_gen_tac `idx` >> disch_tac >>
  qpat_assum `!q. q < LENGTH src ==> _ /\ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_assum `(EL idx src).inst_opcode = INVOKE ==> _`
    (drule_then (fn th =>
      Cases_on `FLOOKUP calls (a,f,(EL idx src).inst_id)` >>
      simp[NoAsms] >>
      pop_assum (fn lookup =>
        assume_tac lookup >>
        map_every assume_tac (CONJUNCTS (SIMP_RULE (srw_ss()) [lookup] th)))))
  >- first_assum ACCEPT_TAC >>
  rename1 `FLOOKUP calls (a,f,(EL idx src).inst_id) = SOME call_record` >>
  PairCases_on `call_record` >>
  qpat_assum `!a e cid q h b done child ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b,done,child,ret) ==>
    ?bb bt ps xs ys rho hin h0 be hbe count front closed brest cf cg cord cr cu.
      FLOOKUP blocks (a,e) = SOME _ /\ _ /\ _ /\ _ /\
      FLOOKUP acts ((e,cid)::a) = SOME _`
    (drule_then strip_assume_tac) >>
  qpat_assum `FLOOKUP acts ((f,(EL idx src).inst_id)::a) = SOME _`
    (fn child => simp[NoAsms,child] >>
      qpat_assum `EL idx old_keys = AK ((f,(EL idx src).inst_id)::a)`
        (fn cell => qpat_assum `AK = _`
          (fn agg => ACCEPT_TAC (SIMP_RULE (srw_ss()) [agg,child] cell))))
QED

Resume dft_packet_block_edge_clauses[shape_old]:
  `?oc orr ocl ou. FLOOKUP blocks (a,e) =
    SOME (rb,rt,rps,rxs,rys,rsched,rin,rh,SOME (rbe,rhb),oc,orr,ocl,ou)` by
    (`~(p = a /\ SUC d = e)` by
       (qpat_assum `(a,e) <> (p,SUC d)` mp_tac >> simp[NoAsms,EQ_SYM_EQ]) >>
     qpat_assum `FLOOKUP blocks' (a,e) = SOME _` mp_tac >>
     qpat_assum `blocks' = _ |+ _ |+ _` (fn eq =>
       qpat_assum `~(p = a /\ SUC d = e)` (fn fresh =>
         simp[NoAsms,eq,finite_mapTheory.FLOOKUP_UPDATE,fresh])) >>
     Cases_on `p = a /\ d = e`
     >- (pop_assum strip_assume_tac >>
         qpat_x_assum `p = a` (SUBST_ALL_TAC o SYM) >>
         qpat_x_assum `d = e` (SUBST_ALL_TAC o SYM) >>
         qpat_assum `FLOOKUP blocks (p,d) = SOME _` (fn old => simp[NoAsms,old])) >>
     pop_assum (fn th => simp[NoAsms,th]) >>
     disch_tac >> goal_assum (drule_at Any)) >>
  `(a,e) IN FDOM blocks` by
    (qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (mp_tac o REWRITE_RULE [finite_mapTheory.flookup_thm]) >> simp[NoAsms]) >>
  `?omr oer okr. FLOOKUP m (a,e) = SOME omr /\ FLOOKUP es (a,e) = SOME oer /\
       FLOOKUP ks (a,e) = SOME okr` by
    (qexistsl [`m ' (a,e)`,`es ' (a,e)`,`ks ' (a,e)`] >>
     simp[NoAsms,finite_mapTheory.flookup_thm] >>
     map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
       [`FDOM blocks = FDOM m`,`FDOM blocks = FDOM es`,`FDOM blocks = FDOM ks`] >>
     qpat_assum `(a,e) IN FDOM blocks` (fn th => simp[NoAsms,th])) >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe cnt front closed brest mr er kr.
    _ ==> LENGTH mr = LENGTH xs /\ !f g ai ent ord r u. FLOOKUP acts a = SOME _ ==> _`
    (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
  `LENGTH mr = LENGTH rxs /\ !q. q < LENGTH rxs /\ (EL q rxs).inst_opcode <> INVOKE ==>
    EL q mr = EL q omr /\ EL q er = EL q oer /\ EL q kr = EL q okr` by
    suspend "shape_old_cells" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "shape_old_owner"
QED

Resume dft_packet_block_edge_clauses[shape_old_cells]:
  Cases_on `?i. i < LENGTH p /\ (a,e) = (DROP (SUC i) p,FST (EL i p))`
  >- (pop_assum (qx_choose_then `idx` strip_assume_tac) >>
      `a = DROP (SUC idx) p /\ e = FST (EL idx p)` by
        (pop_assum mp_tac >> simp[NoAsms]) >>
      qpat_x_assum `a = DROP (SUC idx) p` SUBST_ALL_TAC >>
      qpat_x_assum `e = FST (EL idx p)` SUBST_ALL_TAC >>
      suspend "shape_old_parent") >>
  qpat_assum `!a e. (a,e) <> (p,SUC d) /\ _ ==> FLOOKUP m' (a,e) = _ /\ _`
    (qspecl_then [`a`,`e`] mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `~(?i. i < LENGTH p /\ (a,e) = _)` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[])) >>
  qpat_assum `FLOOKUP m' (a,e) = SOME mr` (fn n =>
  qpat_assum `FLOOKUP m (a,e) = SOME omr` (fn o0 =>
  qpat_assum `FLOOKUP es' (a,e) = SOME er` (fn ne =>
  qpat_assum `FLOOKUP es (a,e) = SOME oer` (fn oe =>
  qpat_assum `FLOOKUP ks' (a,e) = SOME kr` (fn nk =>
  qpat_assum `FLOOKUP ks (a,e) = SOME okr` (fn ok =>
  qpat_assum `LENGTH omr = LENGTH rxs` (fn len =>
    simp[NoAsms,n,o0,ne,oe,nk,ok,len,SF CONJ_ss])))))))
QED

Resume dft_packet_block_edge_clauses[shape_old_parent]:
  qpat_assum `!i mr er kr. _ ==> FLOOKUP m' _ = SOME (LUPDATE _ _ _) /\ _`
    (qspecl_then [`idx`,`omr`,`oer`,`okr`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(EL (EL idx inds) rxs).inst_opcode = INVOKE` by
    (qpat_assum `!i. i < LENGTH p ==> ?sf tf bb bt ps xs ys rho hin h be hbe pos b0 done child ch. _ /\ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (DROP (SUC idx) p,FST (EL idx p)) = SOME (rb,rt,rps,rxs,rys,rsched,rin,rh,SOME (rbe,rhb),oc,orr,ocl,ou)`
       (fn old => qpat_assum `FLOOKUP blocks (DROP (SUC idx) p,FST (EL idx p)) = SOME (_,_,_,_,_,_,_,_,SOME _,_,OK _,F,NONE)`
         (mp_tac o REWRITE_RULE [old])) >>
     simp[NoAsms] >> disch_then (fn th =>
       simp[NoAsms,cj 4 th] >> first_assum ACCEPT_TAC)) >>
  `mr = LUPDATE (AM' (DROP idx p)) (EL idx inds) omr /\
   er = LUPDATE (AE' (DROP idx p)) (EL idx inds) oer /\
   kr = LUPDATE (AK' (DROP idx p)) (EL idx inds) okr` by
    (map_every (fn (lookup, updated) =>
       qpat_assum lookup (fn old => qpat_assum updated
         (mp_tac o REWRITE_RULE [old])))
       [(`FLOOKUP m' _ = SOME mr`,`FLOOKUP m' _ = SOME (LUPDATE _ _ _)`),
        (`FLOOKUP es' _ = SOME er`,`FLOOKUP es' _ = SOME (LUPDATE _ _ _)`),
        (`FLOOKUP ks' _ = SOME kr`,`FLOOKUP ks' _ = SOME (LUPDATE _ _ _)`)] >>
     simp[NoAsms]) >>
  map_every (fn pat => qpat_assum pat SUBST1_TAC)
    [`mr = LUPDATE _ _ _`,`er = LUPDATE _ _ _`,`kr = LUPDATE _ _ _`] >>
  conj_tac >- (simp[NoAsms,LENGTH_LUPDATE] >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  `q <> EL idx inds` by
    (disch_then (fn eq => qpat_assum `(EL q rxs).inst_opcode <> INVOKE`
       (mp_tac o REWRITE_RULE [eq])) >>
     qpat_assum `(EL (EL idx inds) rxs).inst_opcode = INVOKE`
       (fn op_eq => simp[NoAsms,op_eq])) >>
  qpat_assum `q <> EL idx inds` (fn neq => simp[NoAsms,EL_LUPDATE,neq])
QED

Resume dft_packet_block_edge_clauses[shape_old_owner]:
  map_every qx_gen_tac [`rf`,`rg`,`ri`,`rent`,`rord`,`rres`,`ru`] >>
  disch_tac >>
  `?old_ord. FLOOKUP acts a = SOME (rf,rg,ri,rent,old_ord,rres,ru)` by
    (qpat_assum `FLOOKUP acts' a = SOME _` mp_tac >>
     qpat_assum `acts' = _ |+ _` (fn upd => simp[NoAsms,upd,finite_mapTheory.FLOOKUP_UPDATE]) >>
     Cases_on `p = a`
     >- (qpat_x_assum `p = a` (SUBST_ALL_TAC o SYM) >>
         qpat_assum `FLOOKUP acts p = SOME _` (fn old => simp[NoAsms,old])) >>
     pop_assum (fn neq => simp[NoAsms,neq]) >> disch_tac >> goal_assum (drule_at Any)) >>
  qx_gen_tac `idx` >> disch_tac >>
  qpat_assum `!f g ai ent ord r u. FLOOKUP acts a = SOME _ ==> !q. q < LENGTH rxs ==> _`
    (drule_then (drule_then (map_every assume_tac o CONJUNCTS))) >>
  conj_tac >> strip_tac
  >- (`(EL idx rxs).inst_opcode <> INVOKE` by
        (qpat_assum `(EL idx rxs).inst_opcode = GAS` (fn op_eq => simp[NoAsms,op_eq])) >>
      suspend "shape_old_cell_results") >>
  suspend "shape_old_cell_results"
QED

Resume dft_packet_block_edge_clauses[shape_old_cell_results]:
  markerLib.RESUME_TAC >>
  qpat_assum `!q. q < LENGTH rxs /\ (EL q rxs).inst_opcode <> INVOKE ==> _`
    (qspec_then `idx` mp_tac) >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
    first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `EL idx mr = EL idx omr` (fn m_eq =>
  qpat_assum `EL idx er = EL idx oer` (fn e_eq =>
  qpat_assum `EL idx kr = EL idx okr` (fn k_eq =>
    PURE_REWRITE_TAC [m_eq,e_eq,k_eq]))) >>
  first_assum (fn th =>
    if boolSyntax.is_imp (concl th) then
      (irule th >> rpt conj_tac >> first_assum ACCEPT_TAC)
    else NO_TAC)
QED

Resume dft_packet_block_edge_clauses[row_distinct]:
  `!a e kr. ALL_DISTINCT (AK' a) /\ FLOOKUP ks' (a,e) = SOME kr ==>
    ALL_DISTINCT (FLAT kr)` by suspend "distinct_row_piece" >>
  `!a. FLOOKUP acts' a <> NONE ==> ALL_DISTINCT (AK' a)` by
    suspend "distinct_activation" >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!a e kr. ALL_DISTINCT (AK' a) /\ _ ==> _` irule >>
  goal_assum (drule_at Any) >>
  qpat_assum `!a. FLOOKUP acts' a <> NONE ==> _` irule >>
  `(a,e) IN FDOM blocks'` by
    (qpat_assum `FLOOKUP ks' (a,e) = SOME kr`
       (mp_tac o REWRITE_RULE [finite_mapTheory.flookup_thm]) >>
     qpat_assum `FDOM blocks' = FDOM ks'` (fn eq => simp[NoAsms,eq])) >>
  `FLOOKUP blocks' (a,e) <> NONE` by simp[finite_mapTheory.FLOOKUP_DEF] >>
  qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
    FLOOKUP blocks' (a,e) = SOME _ ==> ?sf tf inc entry order res nrest sp. _`
    (qspecl_then [`a`,`e`] mp_tac) >>
  qpat_assum `FLOOKUP blocks' (a,e) <> NONE` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `FLOOKUP blocks' (a,e)` >> simp[] >>
  PairCases_on `x` >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Resume dft_packet_block_edge_clauses[distinct_row_piece]:
  rpt strip_tac >>
  `(a,e) IN FDOM blocks'` by
    (qpat_assum `FLOOKUP ks' (a,e) = SOME kr`
       (mp_tac o REWRITE_RULE [finite_mapTheory.flookup_thm]) >>
     qpat_assum `FDOM blocks' = FDOM ks'` (fn eq => simp[NoAsms,eq])) >>
  `FLOOKUP blocks' (a,e) <> NONE` by simp[finite_mapTheory.FLOOKUP_DEF] >>
  `?f g ai ent ord r u. FLOOKUP acts' a = SOME (f,g,ai,ent,ord,r,u) /\ MEM e ord` by
    (qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
       FLOOKUP blocks' (a,e) = SOME _ ==> ?sf tf inc entry order res nrest sp. _`
       (qspecl_then [`a`,`e`] mp_tac) >>
     qpat_assum `FLOOKUP blocks' (a,e) <> NONE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `FLOOKUP blocks' (a,e)` >> simp[] >>
     PairCases_on `x` >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (THE (FLOOKUP ks' (a,e))))` suffices_by
    (qpat_assum `FLOOKUP ks' (a,e) = SOME kr` (fn eq => simp[NoAsms,eq])) >>
  irule venomFnInstsProofsTheory.all_distinct_flat_mem >>
  qexists `MAP (\v. FLAT (THE (FLOOKUP ks' (a,v)))) ord` >>
  conj_tac >-
    (qpat_assum `ALL_DISTINCT (AK' a)` mp_tac >>
     qpat_assum `AK' = _` (fn agg =>
       qpat_assum `FLOOKUP acts' a = SOME (f,g,ai,ent,ord,r,u)`
         (fn lk => simp[NoAsms,agg,lk]))) >>
  simp[NoAsms,MEM_MAP] >> qexists `e` >> simp[]
QED

Resume dft_packet_block_edge_clauses[distinct_activation]:
  Induct >- (simp[NoAsms] >> disch_tac >> first_assum ACCEPT_TAC) >>
  PairCases >> rename1 `(ep,cid)::a` >> strip_tac >>
  suspend "distinct_invoke_cell"
QED

Resume dft_packet_block_edge_clauses[distinct_invoke_cell]:
  `?f g ai ent ord r u. FLOOKUP acts' ((ep,cid)::a) = SOME (f,g,ai,ent,ord,r,u)` by
    (qpat_assum `FLOOKUP acts' ((ep,cid)::a) <> NONE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `FLOOKUP acts' ((ep,cid)::a)` >> simp[] >> PairCases_on `x` >> simp[]) >>
  `?q h b0 done ret. FLOOKUP calls (a,ep,cid) = SOME (q,h,b0,done,ent,ret)` by
    (qpat_assum `!a f g ai ent seq r rest. FLOOKUP acts' a = SOME _ ==>
       MEM f C7.ctx_functions /\ _`
       (qspec_then `(ep,cid)::a` mp_tac) >>
     qpat_assum `FLOOKUP acts' ((ep,cid)::a) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `?bb bt ps xs ys sched hin h0 be hbe count front closed brest.
     FLOOKUP blocks' (a,ep) = SOME (bb,bt,ps,xs,ys,sched,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
     q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE` by
    (qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
       FLOOKUP calls (a,e,cid) = SOME _ ==> ?sf tf inc entry order res nrest bb bt ps xs ys sched hin h0 be hbe count front closed brest csf ctf child_order child_res child_rest c nm ops args. _`
       (qspecl_then [`a`,`ep`,`cid`] mp_tac) >>
     qpat_assum `FLOOKUP calls (a,ep,cid) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >>
     goal_assum (drule_at Any) >> simp[]) >>
  suspend "distinct_invoke_lookup"
QED

Resume dft_packet_block_edge_clauses[distinct_invoke_lookup]:
  rename1 `FLOOKUP calls (a,ep,cid) = SOME (iq,_,_,_,_,_)` >>
  rename1 `FLOOKUP blocks' (a,ep) = SOME (_,_,_,ixs,_,_,_,_,SOME _,_,_,_,_)` >>
  `(a,ep) IN FDOM blocks'` by
    (qpat_assum `FLOOKUP blocks' (a,ep) = SOME _` mp_tac >>
     simp[NoAsms,finite_mapTheory.flookup_thm]) >>
  `?im ie ik. FLOOKUP m' (a,ep) = SOME im /\ FLOOKUP es' (a,ep) = SOME ie /\
      FLOOKUP ks' (a,ep) = SOME ik` by
    (qpat_assum `FDOM blocks' = FDOM m'` mp_tac >>
     qpat_assum `FDOM blocks' = FDOM es'` mp_tac >>
     qpat_assum `FDOM blocks' = FDOM ks'` mp_tac >>
     qpat_assum `(a,ep) IN FDOM blocks'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]) >>
  `EL iq ik = AK' ((ep,cid)::a)` by suspend "distinct_cell_eq" >>
  `ALL_DISTINCT (AK' a)` by
    (qpat_assum `FLOOKUP acts' a <> NONE ==> ALL_DISTINCT (AK' a)` irule >>
     qpat_assum `!a e bb bt ps xs ys sched hin h0 body_ent cnt front closed brest.
       FLOOKUP blocks' (a,e) = SOME _ ==> ?sf tf inc entry order res nrest sp. _`
       (qspecl_then [`a`,`ep`] mp_tac) >>
     qpat_assum `FLOOKUP blocks' (a,ep) = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `ALL_DISTINCT (FLAT ik)` by
    (qpat_assum `!a e kr. ALL_DISTINCT (AK' a) /\ _ ==> _` irule >>
     goal_assum (drule_at Any) >> qexists `ep` >> first_assum ACCEPT_TAC) >>
  qpat_assum `EL iq ik = AK' ((ep,cid)::a)` (SUBST1_TAC o SYM) >>
  irule venomFnInstsProofsTheory.all_distinct_flat_mem >>
  qexists `ik` >> conj_tac >- first_assum ACCEPT_TAC >>
  suspend "distinct_cell_in_bounds"
QED

Resume dft_packet_block_edge_clauses[distinct_cell_eq]:
  qpat_assum `!a e bb bt ps xs ys rho hin h be hb cnt front closed rest ms ess keys.
    FLOOKUP blocks' (a,e) = SOME _ /\ FLOOKUP m' (a,e) = SOME _ /\
    FLOOKUP es' (a,e) = SOME _ /\ FLOOKUP ks' (a,e) = SOME _ ==>
    !q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE ==> _`
    (qspecl_then [`a`,`ep`] mp_tac) >>
  qpat_assum `FLOOKUP blocks' (a,ep) = SOME _` mp_tac >>
  qpat_assum `FLOOKUP m' (a,ep) = SOME im` mp_tac >>
  qpat_assum `FLOOKUP es' (a,ep) = SOME ie` mp_tac >>
  qpat_assum `FLOOKUP ks' (a,ep) = SOME ik` mp_tac >>
  qpat_assum `iq < LENGTH ixs` mp_tac >>
  qpat_assum `(EL iq ixs).inst_opcode = INVOKE` mp_tac >>
  qpat_assum `(EL iq ixs).inst_id = cid` mp_tac >>
  qpat_assum `FLOOKUP calls (a,ep,cid) = SOME _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 8 disch_tac >> simp[] >>
  disch_then (qspec_then `iq` mp_tac) >> simp[]
QED

Resume dft_packet_block_edge_clauses[distinct_cell_in_bounds]:
  rewrite_tac [MEM_EL] >> qexists `iq` >> simp[NoAsms] >>
  qpat_assum `!a e bb bt ps xs ys rho hin h0 be hbe cnt front closed brest mr er kr.
    FLOOKUP blocks' (a,e) = SOME _ /\ FLOOKUP m' (a,e) = SOME mr /\
    FLOOKUP es' (a,e) = SOME er /\ FLOOKUP ks' (a,e) = SOME kr ==>
    LENGTH mr = LENGTH xs /\ _` (qspecl_then [`a`,`ep`] mp_tac) >>
  qpat_assum `!key mr er kr. FLOOKUP m' key = SOME mr /\ _ ==>
    LENGTH mr = LENGTH er /\ _` (qspec_then `(a,ep)` mp_tac) >>
  qpat_assum `FLOOKUP blocks' (a,ep) = SOME _` mp_tac >>
  qpat_assum `FLOOKUP m' (a,ep) = SOME im` mp_tac >>
  qpat_assum `FLOOKUP es' (a,ep) = SOME ie` mp_tac >>
  qpat_assum `FLOOKUP ks' (a,ep) = SOME ik` mp_tac >>
  qpat_assum `iq < LENGTH ixs` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 5 disch_tac >> simp[]
QED

Finalise dft_packet_block_edge_clauses
