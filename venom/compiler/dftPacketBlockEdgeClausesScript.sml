Theory dftPacketBlockEdgeClauses
Ancestors
  dftPacketBlockNativePrefix dftPacketBlockEntryDischarge dftPacketEntryReplay
  dftPacketBlockEdgeSplice dftPacketBlockReplayFrame dftPacketBlockHistoricalCuts
  dftPacketBlockRootedCertificate dftPacketBlockTerminatorCoverage
  dftPacketSuccessfulTerminalRow dftGasToListReplay stateEquiv
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
  conj_tac >- (MATCH_MP_TAC dft_block_splice_initialized_path >>
    qexistsl [`cnt0`,`s`,`AE`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[NoAsms]
QED
