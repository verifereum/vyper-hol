Theory dftPacketBlockInitializedFreshCut
Ancestors
  dftPacketBlockRootedCertificate dftPacketReturnAnchorState
  dftPacketBlockHistoryRootPrefix dftPacketBlockHistorySelectedFrame
  dftPacketFreshBodyObservation dftPacketFillingBoundary
  finite_map list rich_list arithmetic venomInst

(* The initialized body is at index LENGTH ps, hence its current instruction
   is exactly the first scheduled body instruction. *)
Theorem block_initialized_head[local]:
  bt.bb_instructions = ps ++ ys /\
  s.vs_inst_idx = LENGTH ps /\ get_instruction bt s.vs_inst_idx = SOME next ==>
  ys <> [] /\ next = HD ys
Proof
  Cases_on `ys` >> simp[get_instruction_def] >> strip_tac >>
  gvs[EL_APPEND2]
  >> (MATCH_ACCEPT_TAC listTheory.el_append3)
QED

(* Observation replay at the fresh source prefix is obtained from the
   initializer's successful row fold and its native ZIP certificate. *)
Theorem block_initialized_observation[local]:
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  dft_fn_rel sf tf /\ MEM bb sf.fn_blocks /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv sf bb xs s /\ s.vs_inst_idx = LENGTH ps /\
  get_instruction bt s.vs_inst_idx = SOME next /\
  q < LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  cm = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
  ck = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(p,e,(EL r xs).inst_id)] else []) (LENGTH xs) /\
  (!F kgss tail. Nnew <= F /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss ==>
    SND (R F (post with vs_gas_readings := FLAT kgss ++ tail)) =
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (s with vs_gas_readings := FLAT kgss ++ tail) /\
    (!events u. R F (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
      trace_gas (trace_block p e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
        (s with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE q ck),FLAT kgss))) ==>
  !F gs tail events u.
    Nnew <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q cm)) gs /\
    R F (post with vs_gas_readings := gs ++ tail) = (events,OK u) /\
    inv_memory_observation next.inst_opcode /\ EL q xs = next ==>
    (!op. MEM op next.inst_operands ==> eval_operand op u = eval_operand op s) /\
    u.vs_initial_fmp = s.vs_initial_fmp
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac block_initialized_head >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`,`events`,`u`] >> strip_tac >>
  qpat_assum `LIST_REL _ (FLAT (TAKE q cm)) gs`
    (mp_then Any (qx_choose_then `kgss` strip_assume_tac) dft_packet_flat_filling_split) >>
  qpat_assum `!F kgss tail. _ ==> _` (qspecl_then [`fuel`,`kgss`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  qpat_assum `gs = FLAT kgss` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `R fuel _ = (events,OK u)` (fn th => rewrite_tac[th,pairTheory.SND]) >>
  disch_then (CONJUNCTS_THEN2 (assume_tac o SYM)
    (qspecl_then [`events`,`u`] (assume_tac o REWRITE_RULE [TRUTH]))) >>
  drule_all dft_packet_fresh_body_observation >> simp[NoAsms]
QED

(* Discharge the append observation premise in both initialization cases. *)
Theorem block_initialized_append_observation[local]:
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  dft_fn_rel sf tf /\ MEM bb sf.fn_blocks /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\
  get_instruction bt s.vs_inst_idx = SOME next /\
  mcut = FLAT (TAKE q cm) /\
  (s.vs_inst_idx < LENGTH ps \/
    (s.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
     EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
     dft_remaining_inv sf bb xs s /\
     cm = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [NONE] else []) (LENGTH xs) /\
     ck = GENLIST (\r. if (EL r xs).inst_opcode = GAS then [(p,e,(EL r xs).inst_id)] else []) (LENGTH xs) /\
     (!F kgss tail. Nnew <= F /\
       LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss ==>
       SND (R F (post with vs_gas_readings := FLAT kgss ++ tail)) =
         FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
           (s with vs_gas_readings := FLAT kgss ++ tail) /\
       (!events u. R F (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
         trace_gas (trace_block p e (F-e) C7 sf
           (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
           (s with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE q ck),FLAT kgss))))) ==>
  (!F gs tail (events:(string # num) list) u.
    Nnew <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) mcut gs /\
    R F (post with vs_gas_readings := gs ++ tail) = (events,OK u) /\
    inv_memory_observation next.inst_opcode /\ EL q xs = next ==>
    (!op. MEM op next.inst_operands ==> eval_operand op u = eval_operand op s) /\
    u.vs_initial_fmp = s.vs_initial_fmp)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `s.vs_inst_idx < LENGTH ps \/ _` STRIP_ASSUME_TAC
  >- (rpt gen_tac >> strip_tac >>
      `next = EL s.vs_inst_idx ps` by (fs[get_instruction_def,EL_APPEND1] >> (gvs[get_instruction_def, EL_APPEND1])) >>
      `is_pseudo next.inst_opcode` by
        (qpat_assum `EVERY _ ps` (mp_tac o REWRITE_RULE [EVERY_EL]) >>
         disch_then (qspec_then `s.vs_inst_idx` mp_tac) >> simp[]) >>
      metis_tac[dftGasInvMemoryObservationTheory.inv_memory_observation_nonpseudo]) >>
  qpat_assum `mcut = FLAT _` SUBST1_TAC >>
  rpt gen_tac >> strip_tac >>
  drule_all block_initialized_observation >> simp[NoAsms]
QED

(* The non-final cuts are the suspended live call chain, in reverse stack
   order. The adjacent path determines the very same call key. *)
Theorem block_anchor_live_edge[local]:
  paths = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  SUC i < LENGTH paths /\ EL i paths = ai /\
  EL (SUC i) paths = (e,cid)::ai ==>
  ?k. k < LENGTH p /\ ai = DROP (SUC k) p /\ (e,cid) = EL k p /\ ai <> p
Proof
  strip_tac >>
  `i < SUC (LENGTH p) /\ SUC i < SUC (LENGTH p)` by gvs[] >>
  qabbrev_tac `k = LENGTH p - SUC i` >>
  `k < LENGTH p /\ PRE (SUC (LENGTH p) - i) = SUC k /\
    PRE (SUC (LENGTH p) - SUC i) = k` by (simp[Abbr `k`] >> decide_tac) >>
  qexists `k` >>
  qpat_x_assum `EL i paths = ai` mp_tac >>
  qpat_x_assum `EL (SUC i) paths = _` mp_tac >>
  simp[EL_REVERSE,EL_GENLIST] >> rpt strip_tac >>
  fs[]
  >- (`PRE (LENGTH p - i) = k` by (simp[Abbr `k`] >> decide_tac) >>
      pop_assum (fn th => qpat_x_assum `DROP (PRE _) p = _` (mp_tac o PURE_REWRITE_RULE [th])) >>
      simp[DROP_BY_DROP_SUC]) >>
  `LENGTH (DROP (SUC k) p) = LENGTH p` by metis_tac[] >>
  fs[LENGTH_DROP] >> decide_tac
QED

(* A selected parent index and its position in the stack are unique. *)
Theorem block_anchor_pending_index[local]:
  paths = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  SUC i < LENGTH paths /\ EL i paths = ai /\ EL (SUC i) paths = (e,cid)::ai /\
  FLOOKUP calls (ai,e,cid) = SOME (q,h,b,done,ent,ret) /\
  (!k. k < LENGTH p ==>
    ?h b done ent. FLOOKUP calls (DROP (SUC k) p,FST (EL k p),SND (EL k p)) =
      SOME (EL k inds,h,b,done,ent,NONE)) ==>
  ai <> p /\
  (!k. k < LENGTH p /\ DROP (SUC k) p = ai ==> FST (EL k p) = e /\ EL k inds = q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac block_anchor_live_edge >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `l` >> strip_tac >>
  `LENGTH (DROP (SUC k) p) = LENGTH (DROP (SUC l) p)` by metis_tac[] >>
  `k = l` by (fs[LENGTH_DROP] >> decide_tac) >>
  qpat_x_assum `k = l` (SUBST_ALL_TAC o SYM) >>
  qpat_assum `!k. k < LENGTH p ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `(e,cid) = EL k p` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `ai = DROP (SUC k) p` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `FLOOKUP calls (_,FST (e,cid),SND (e,cid)) = _` mp_tac >>
  qpat_assum `FLOOKUP calls (ai,e,cid) = _` (fn th => simp[NoAsms,th])
QED

(* Earlier row visits have smaller indices than the last retained visit. *)
Theorem block_anchor_last_order[local]:
  order = ds ++ [d] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) ==>
  ALL_DISTINCT order /\ ~MEM d ds /\ ~MEM (SUC d) ds
Proof
  strip_tac >>
  `ALL_DISTINCT order` by
    (qpat_assum `order = GENLIST _ _` (fn th => pure_once_rewrite_tac[th]) >>
     simp[ALL_DISTINCT_GENLIST]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `order = ds ++ [d]` (fn th =>
       qpat_assum `ALL_DISTINCT order` (mp_tac o PURE_REWRITE_RULE [th])) >>
     simp[NoAsms,ALL_DISTINCT_APPEND]) >>
  `LAST order = d /\ order <> []` by
    (qpat_assum `order = ds ++ [d]` (fn th => simp[NoAsms,th])) >>
  `LENGTH order = SUC (LENGTH ds)` by
    (qpat_assum `order = ds ++ [d]` (fn th => simp[NoAsms,th])) >>
  `d = inc + LENGTH order` by
    (qpat_assum `order = GENLIST _ _` (mp_tac o Q.AP_TERM `LAST`) >>
     qpat_assum `LENGTH order = SUC _` (fn len =>
       qpat_assum `LAST order = d` (fn last => simp[NoAsms,len,last,GENLIST_LAST]))) >>
  strip_tac >>
  `MEM (SUC d) order` by
    (qpat_assum `order = ds ++ [d]` (fn th => simp[NoAsms,th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `order = GENLIST _ _` (fn th =>
    qpat_x_assum `MEM (SUC d) order` (mp_tac o PURE_ONCE_REWRITE_RULE [th])) >>
  simp[NoAsms,MEM_GENLIST] >> strip_tac >> decide_tac
QED

(* Earlier visits and the part before the live INVOKE are unaffected by the
   update at that very INVOKE. This works for each of the three row tables. *)
Theorem block_anchor_prefix_frame[local]:
  !(calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap).
  MAP (\(ai,ds,ei,qi,zi). ai) (prior ++ [(p,ds0,d,0,z0:instruction list)]) =
    REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  (!i ai ds ei qi zi. i < LENGTH prior /\ EL i prior = (ai,ds,ei,qi,zi) ==>
    ?cid h b done ent ret ord later.
      EL (SUC i) (MAP (\(ai,ds,ei,qi,zi). ai) (prior ++ [(p,ds0,d,0,z0)])) = (ei,cid)::ai /\
      FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret) /\
      ord = ds ++ ei::later /\ ALL_DISTINCT ord /\ LAST ord = ei) /\
  (!k. k < LENGTH p ==>
    ?h b done ent. FLOOKUP calls (DROP (SUC k) p,FST (EL k p),SND (EL k p)) =
      SOME (EL k inds,h,b,done,ent,NONE)) /\
  (!a e. (a,e) <> (p,SUC d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP out (a,e) = FLOOKUP tab (a,e)) /\
  (!i. i < LENGTH p ==>
    ?row v. FLOOKUP tab (DROP (SUC i) p,FST (EL i p)) = SOME row /\
      FLOOKUP out (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE v (EL i inds) row)) ==>
  !ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) prior ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP out (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP out (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))
Proof
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  map_every qx_gen_tac [`ai`,`ds`,`ei`,`qi`,`zi`] >>
  simp[NoAsms,MEM_EL] >> disch_then (qx_choose_then `i` strip_assume_tac) >>
  first_x_assum (qspecl_then [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] mp_tac) >>
  (impl_tac >- (conj_tac >> (simp[]))) >>
  strip_tac >>
  qabbrev_tac `paths = MAP (\(a,ds,e,q,z). a) (prior ++ [(p,ds0,d,0,z0)])` >>
  `SUC i < LENGTH paths /\ EL i paths = ai` by
    (conj_tac >- (simp[Abbr `paths`] >> decide_tac) >>
     simp[Abbr `paths`,EL_MAP,EL_APPEND1] >>
     qpat_assum `(ai,ds,ei,qi,zi) = EL i prior` (fn th =>
       simp[NoAsms,GSYM th])) >>
  drule_all_then strip_assume_tac block_anchor_pending_index >>
  `~MEM ei ds` by
    (qpat_assum `ord = _` (fn eq =>
       qpat_assum `ALL_DISTINCT ord`
         (strip_assume_tac o REWRITE_RULE [eq,ALL_DISTINCT_APPEND])) >>
     qpat_assum `!x. MEM x ds ==> _`
       (qspec_then `ei` (ACCEPT_TAC o SIMP_RULE (srw_ss()) []))) >>
  `!f. MEM f ds ==> FLOOKUP out (ai,f) = FLOOKUP tab (ai,f)` by
    (qx_gen_tac `f` >> disch_tac >>
     qpat_assum `!a e. _ ==> FLOOKUP out (a,e) = _` irule >>
     conj_tac >-
       (qx_gen_tac `k` >> strip_tac >>
        qpat_assum `!k. _ ==> FST (EL k p) = ei /\ _` (qspec_then `k` mp_tac) >>
        simp[NoAsms,pairTheory.PAIR_EQ] >> metis_tac[]) >>
     simp[pairTheory.PAIR_EQ]) >>
  `TAKE qi (THE (FLOOKUP out (ai,ei))) = TAKE qi (THE (FLOOKUP tab (ai,ei)))` by
    (drule_all_then strip_assume_tac block_anchor_live_edge >>
     qpat_assum `!i. _ ==> ?row v. _` (qspec_then `k` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `!k. _ ==> FST (EL k p) = ei /\ _`
       (qspec_then `k` (fn th =>
          `EL k inds = qi` by (mp_tac th >> metis_tac[]))) >>
     qpat_x_assum `(ei,cid) = EL k p` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `ai = DROP (SUC k) p` (SUBST_ALL_TAC o SYM) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     simp[dftPacketTableSpliceTheory.dft_packet_row_prefix_splice]) >>
  simp[] >> AP_TERM_TAC >> irule MAP_CONG >> simp[]
QED

(* At a non-final cut the activation is a strict suffix of p, so neither
   block update touches it.  The final cut changes only the last level. *)
Theorem block_fresh_cut_geometry[local]:
  FLOOKUP acts p = SOME (sf,tf,inc,entry,order,NONE:exec_result option,NONE:bytes32 list option) /\
  FLOOKUP blocks (p,d) = SOME (bb,bt:basic_block,ps:instruction list,xs:instruction list,ys:instruction list,rho0:num list,
    hin:venom_state,h0:num,SOME(be:venom_state,hbe:num),cnt0:num,OK s,F,NONE:bytes32 list option) /\
  order = ds0 ++ [d] /\ ~MEM (SUC d) ds0 /\ ~MEM d ds0 /\
  acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
  blocks' = (blocks |+ ((p,d),(bb,bt,ps,xs,ys,rho0,hin,h0,SOME(be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings))) |+
    ((p,SUC d),(bb1,bt1,ps1,xs1,ys1,rho1,post,h1,body1,0,OK s1,F,NONE)) /\
  rows = (\a ds. MAP (\f.
    (FST (THE (FLOOKUP blocks (a,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
       (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds) /\
  rows' = (\a ds. MAP (\f.
    (FST (THE (FLOOKUP blocks' (a,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (a,f)))).bb_instructions)
       (FST (THE (FLOOKUP blocks' (a,f)))).bb_instructions)) ds) /\
  cuts0 = prior ++ [(p,ds0,d,0,z0)] /\
  cuts = prior ++ [(p,ds0 ++ [d],SUC d,q,z)] /\
  levels = pre ++ [(sf,rows p ds0 ++
    [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z)],NONE)] /\
  LENGTH pre = LENGTH prior /\
  paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts0 /\
  paths = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  (!i ai ds ei qi zi. i < LENGTH prior /\ EL i prior = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later cid h b0 done child ret.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      EL (SUC i) paths = (ei,cid)::ai /\
      FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child,ret) /\
      qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
      zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
      EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
      (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done) /\
      EL i pre = (sfi,rows ai ds ++ [(bbi,ei,zi)],SOME (EL qi xsi))) ==>
  MAP (\(ai,ds,ei,qi,zi). ai) cuts = paths /\ LENGTH cuts = LENGTH levels /\
  MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts =
    MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts0 /\
  (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks' (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then ai = p /\ ei = SUC d /\ qi = q /\ zi = z
       else ?cid h b0 done child ret.
         EL (SUC i) paths = (ei,cid)::ai /\
         FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child,ret) /\
         qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
         (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
      EL i levels = (sfi,rows' ai ds ++ [(bbi,ei,zi)],
        if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- fs[MAP_APPEND] >>
  conj_tac >- simp[] >>
  `!a. a <> p ==> FLOOKUP acts' a = FLOOKUP acts a /\
    (!e. FLOOKUP blocks' (a,e) = FLOOKUP blocks (a,e)) /\
    (!ds. rows' a ds = rows a ds)` by simp[FLOOKUP_UPDATE,pairTheory.PAIR_EQ] >>
  `!i. i < LENGTH prior ==> EL i paths = FST (EL i prior) /\ SUC i < LENGTH paths` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_assum `paths = MAP _ cuts0` (fn th => pure_once_rewrite_tac[th]) >>
     `?a ds e q z. EL i prior = (a,ds,e,q,z)` by metis_tac[pairTheory.PAIR] >>
     simp[EL_MAP,EL_APPEND1] >> decide_tac) >>
  `!i ai ds ei qi zi. i < LENGTH prior /\ EL i prior = (ai,ds,ei,qi,zi) ==> ai <> p` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later cid h b0 done child ret. _`
       (drule_all_then strip_assume_tac) >>
     `EL i paths = ai /\ SUC i < LENGTH paths` by
       (qpat_assum `!i. i < LENGTH prior ==> _` (drule_then mp_tac) >>
        qpat_assum `EL i prior = (ai,ds,ei,qi,zi)` (fn th => simp[NoAsms,th])) >>
     drule_all block_anchor_live_edge >> metis_tac[]) >>
  conj_tac
  >- (simp[MAP_APPEND,FLOOKUP_UPDATE] >> irule MAP_CONG >> simp[MEM_EL] >>
      rpt strip_tac >> PairCases_on `x` >>
      `x0 <> p` by metis_tac[] >> simp[FLOOKUP_UPDATE]) >>
  map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
  Cases_on `i < LENGTH prior`
  >- (`~(SUC i = LENGTH cuts) /\ EL i prior = (ai,ds,ei,qi,zi) /\ EL i levels = EL i pre` by
        (`EL i cuts = EL i prior` by
           (simp[EL_APPEND1,IgnAsm `EL i cuts = _`]) >>
         conj_tac >- (simp[] >> decide_tac) >>
         conj_tac >- metis_tac[] >> simp[EL_APPEND1]) >>
      `ai <> p` by metis_tac[] >>
      qpat_assum `!i ai ds ei qi zi. _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later cid h b0 done child ret. _`
        (drule_all_then strip_assume_tac) >>
      qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,
        `ini`,`hi`,`bei`,`counti`,`fronti`,`closedi`,`resti`,`later`] >>
      simp[IgnAsm `rows = _`,IgnAsm `rows' = _`] >> metis_tac[]) >>
  `i = LENGTH prior /\ i = LENGTH pre` by
    gvs[] >>
  `ai = p /\ ds = ds0 ++ [d] /\ ei = SUC d /\ qi = q /\ zi = z` by
    gvs[EL_APPEND2] >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,`order ++ [SUC d]`,`NONE`,`NONE`,`bb1`,`bt1`,`ps1`,`xs1`,`ys1`,
    `rho1`,`post`,`h1`,`body1`,`0`,`OK s1`,`F`,`NONE`,`[]`] >>
  `rows' p ds0 = rows p ds0` by
    (simp[] >> irule MAP_CONG >> simp[FLOOKUP_UPDATE,pairTheory.PAIR_EQ] >> metis_tac[]) >>
  `rows' p (ds0 ++ [d]) = rows p ds0 ++
    [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)]` by
    (qpat_assum `rows' = _` (fn th => CONV_TAC (LHS_CONV (REWR_CONV (Q.AP_THM (Q.AP_THM th `p`) `ds0 ++ [d]`)))) >>
     simp[MAP_APPEND,FLOOKUP_UPDATE] >>
     irule MAP_CONG >> simp[] >>
     qx_gen_tac `f` >> strip_tac >> `f <> d /\ f <> SUC d` by metis_tac[] >>
     simp[FLOOKUP_UPDATE]) >>
  gvs[EL_APPEND2,FLOOKUP_UPDATE,APPEND_ASSOC]
QED

(* Identify the terminal selected row of the zero-body cut. *)
Theorem block_anchor_decompose[local]:
  FLOOKUP acts p = SOME (sf,tf:ir_function,inc:num,entry:venom_state,order:num list,
    NONE:exec_result option,NONE:bytes32 list option) /\
  FLOOKUP blocks (p,d) = SOME (bb,bt:basic_block,ps:instruction list,xs:instruction list,
    ys:instruction list,rho0:num list,hin:venom_state,h0:num,SOME(be:venom_state,hbe:num),
    cnt0:num,OK s,F,NONE:bytes32 list option) /\
  LAST order = d /\
  order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts0 = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH levels0 = LENGTH cuts0 /\
  (!i ai ds ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==>
     ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
       ini hi bei counti fronti closedi resti later.
       FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
       FLOOKUP blocks (ai,ei) =
         SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
       orderi = ds ++ ei::later /\
       (SUC i = LENGTH cuts0 ==> ai = p /\ ei = d /\ qi = 0 /\ zi = z0 /\
          EL i levels0 = (sfi,rows ai ds ++ [(bbi,ei,zi)],NONE))) ==>
  ?prior pre ds0. cuts0 = prior ++ [(p,ds0,d,(0:num),z0)] /\
    levels0 = pre ++ [(sf,rows p ds0 ++ [(bb,d,z0)],NONE)] /\
    LENGTH pre = LENGTH prior /\ order = ds0 ++ [d] /\
    ~MEM d ds0 /\ ~MEM (SUC d) ds0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cuts0 <> []` by
    (qpat_assum `MAP _ cuts0 = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[NoAsms] >> Cases_on `cuts0` >> simp[]) >>
  `levels0 <> []` by (strip_tac >> gvs[]) >>
  qabbrev_tac `i = PRE (LENGTH cuts0)` >>
  `i < LENGTH cuts0 /\ SUC i = LENGTH cuts0` by
    (Cases_on `cuts0` >> gvs[Abbr `i`]) >>
  qabbrev_tac `lastcut = EL i cuts0` >> PairCases_on `lastcut` >>
  qpat_assum `!i ai ds ei qi zi. _`
    (qspecl_then [`i`,`lastcut0`,`lastcut1`,`lastcut2`,`lastcut3`,`lastcut4`] mp_tac) >>
  (impl_tac >- (metis_tac[Abbr `lastcut`])) >>
  disch_then strip_assume_tac >>
  qpat_x_assum `SUC i = LENGTH cuts0 ==> _` (drule_then strip_assume_tac) >>
  `ALL_DISTINCT order` by
    (qpat_assum `order = GENLIST _ _` (fn th => pure_once_rewrite_tac[th]) >>
     simp[ALL_DISTINCT_GENLIST]) >>
  `later = [] /\ order = lastcut1 ++ [d]` by
    (qpat_assum `FLOOKUP acts lastcut0 = _` mp_tac >>
     qpat_assum `FLOOKUP acts p = _` mp_tac >>
     qpat_assum `orderi = _` mp_tac >>
     qpat_assum `LAST order = d` mp_tac >>
     qpat_assum `lastcut0 = p` mp_tac >>
     qpat_assum `lastcut2 = d` mp_tac >>
     qpat_assum `ALL_DISTINCT order` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> ntac 7 (disch_then assume_tac) >>
     `order = lastcut1 ++ lastcut2::later` by gvs[] >>
     `~MEM lastcut2 later` by
       (qpat_assum `order = _` (fn th => fs[th,ALL_DISTINCT_APPEND])) >>
     Cases_on `later` >- gvs[] >>
     `LAST (h::t) = lastcut2` by gvs[LAST_APPEND] >>
     metis_tac[MEM_LAST,NOT_CONS_NIL]) >>
  drule_all_then strip_assume_tac block_anchor_last_order >>
  `LAST cuts0 = (p,lastcut1,d,0,z0)` by
    (qpat_assum `Abbrev (lastcut = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[LAST_EL,Abbr `i`]) >>
  `LAST levels0 = (sf,rows p lastcut1 ++ [(bb,d,z0)],NONE)` by
    (qpat_assum `EL i levels0 = _` mp_tac >>
     qpat_assum `FLOOKUP acts lastcut0 = _` mp_tac >>
     qpat_assum `FLOOKUP blocks (lastcut0,lastcut2) = _` mp_tac >>
     simp[LAST_EL,Abbr `i`] >> gvs[]) >>
  qexistsl [`FRONT cuts0`,`FRONT levels0`,`lastcut1`] >>
  `cuts0 = FRONT cuts0 ++ [LAST cuts0] /\ levels0 = FRONT levels0 ++ [LAST levels0]` by
    metis_tac[APPEND_FRONT_LAST] >>
  `LENGTH (FRONT levels0) = LENGTH (FRONT cuts0)` by
    (ntac 2 (pop_assum (mp_tac o Q.AP_TERM `LENGTH`)) >> simp[]) >>
  metis_tac[]
QED

(* The initializer's per-entry replay is independent of the enclosing plan. *)
Theorem block_initialized_row_replay[local]:
  FLOOKUP m' (p,SUC d) = SOME cm /\
  FLOOKUP es' (p,SUC d) = SOME (ce:(string # num) list list) /\
  FLOOKUP ks' (p,SUC d) = SOME ck /\
  M1 = FLAT (TAKE q (THE (FLOOKUP m' (p,SUC d)))) /\
  E1 = FLAT (TAKE q (THE (FLOOKUP es' (p,SUC d)))) /\
  K1 = FLAT (TAKE q (THE (FLOOKUP ks' (p,SUC d)))) /\
  ((IS_SOME body1 /\ q < LENGTH xs1 /\
    z = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q xs1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs1) /\
    (!r. r < q /\ (EL r xs1).inst_opcode = INVOKE ==> MEM r (TAKE 0 rho1))) \/
   (body1 = NONE /\ q = 0 /\
    z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1))) /\
  (if s1.vs_inst_idx < LENGTH ps1 then
    body1 = NONE /\
    (!F gs. Nnew <= F ==> R F (post with vs_gas_readings := gs) =
      ([],OK (s1 with vs_gas_readings := gs)))
   else
    s1.vs_inst_idx = LENGTH ps1 /\ body1 = SOME (s1,h1:num) /\
    LENGTH cm = LENGTH xs1 /\ LENGTH ce = LENGTH cm /\ LENGTH ck = LENGTH cm /\
    LIST_REL (\m es. LENGTH m = LENGTH es) cm ce /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) cm ck /\
    (!F kgss tail. Nnew <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss ==>
      SND (R F (post with vs_gas_readings := FLAT kgss ++ tail)) =
        FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE q xs1)
          (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
      (?extra. FLAT (TAKE q ce) =
        FST (R F (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
      (!events u. R F (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
        events = FLAT (TAKE q ce) /\ u.vs_gas_readings = tail /\
        trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
          (bb1 with bb_instructions := TAKE (LENGTH ps1 + q) bb1.bb_instructions)
          (s1 with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE q ck),FLAT kgss) /\
        !tail'. R F (post with vs_gas_readings := FLAT kgss ++ tail') =
          (events,OK (u with vs_gas_readings := tail'))))) ==>
  ((q = 0 /\ s1.vs_inst_idx < LENGTH ps1 /\
    z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) /\
    M1 = [] /\ E1 = [] /\ K1 = [] /\
    (!F t. Nnew <= F ==> R F (post with vs_gas_readings := t) =
      ([],OK (s1 with vs_gas_readings := t)))) \/
   (s1.vs_inst_idx = LENGTH ps1 /\ q < LENGTH xs1 /\
    z = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q xs1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs1) /\
    (!r. r < q ==> (EL r xs1).inst_opcode <> INVOKE) /\
    LENGTH cm = LENGTH xs1 /\ LENGTH ce = LENGTH cm /\ LENGTH ck = LENGTH cm /\
    LIST_REL (\m es. LENGTH m = LENGTH es) cm ce /\
    LIST_REL (\m keys. LENGTH m = LENGTH keys) cm ck /\
    M1 = FLAT (TAKE q cm) /\ E1 = FLAT (TAKE q ce) /\ K1 = FLAT (TAKE q ck) /\
    (!F kgss tail. Nnew <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q cm) kgss ==>
      SND (R F (post with vs_gas_readings := FLAT kgss ++ tail)) =
        FOLDR (dft_exec_cons (F-SUC d) C7) OK (TAKE q xs1)
          (s1 with vs_gas_readings := FLAT kgss ++ tail) /\
      (?extra. E1 = FST (R F (post with vs_gas_readings := FLAT kgss ++ tail)) ++ extra) /\
      (!events u. R F (post with vs_gas_readings := FLAT kgss ++ tail) = (events,OK u) ==>
        events = E1 /\ u.vs_gas_readings = tail /\
        trace_gas (trace_block p (SUC d) (F-SUC d) C7 sf
          (bb1 with bb_instructions := TAKE (LENGTH ps1 + q) bb1.bb_instructions)
          (s1 with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (K1,FLAT kgss) /\
        !tail'. R F (post with vs_gas_readings := FLAT kgss ++ tail') =
          (events,OK (u with vs_gas_readings := tail'))))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `s1.vs_inst_idx < LENGTH ps1` >> gvs[] >> metis_tac[]
QED

(* With the final call-cell property, nesting gives the remainder in the
   final root aggregate.  No equality to an old remainder is required. *)
Theorem block_fresh_cut_root_suffix[local]:
  paths = MAP (\(ai,ds,ei,qi,zi:instruction list). ai) cuts /\
  paths = REVERSE (GENLIST (\i. DROP i (p:(num # num) list)) (SUC (LENGTH p))) /\
  agg = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  FLOOKUP tab (p,SUC d) = SOME fresh /\ q <= LENGTH fresh /\
  (!k. k < LENGTH p ==>
    ?row. EL k inds < LENGTH row /\
      FLOOKUP tab (DROP (SUC k) p,FST (EL k p)) =
        SOME (LUPDATE (agg (DROP k p)) (EL k inds) row)) /\
  (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sf tf inc entry order res nrest later.
      FLOOKUP acts ai = SOME (sf:ir_function,tf:ir_function,inc:num,entry:venom_state,order,
        res:exec_result option,nrest:bytes32 list option) /\
      order = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then ai = p /\ ei = SUC d /\ qi = q
       else
         ?k. k < LENGTH p /\ ai = DROP (SUC k) p /\ ei = FST (EL k p) /\
           qi = EL k inds /\ FST (EL (SUC i) cuts) = DROP k p)) ==>
  ?rest. agg [] = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cuts) ++ rest
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `GENLIST (\i. DROP i p) (SUC (LENGTH p)) <> []` by
    (strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `cuts <> [] /\ FST (HD cuts) = []` by
    (qpat_assum `paths = MAP _ cuts` (fn eq =>
       qpat_assum `paths = REVERSE _` (mp_tac o REWRITE_RULE [eq])) >>
     Cases_on `cuts`
     >- (simp[] >> strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
     PairCases_on `h` >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_REVERSE,GENLIST_LAST,DROP_LENGTH_TOO_LONG]) >>
  irule dftPacketSelectedCutTransportTheory.dft_packet_selected_cut_prefix >>
  rpt (first_assum (irule_at Any)) >>
  map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
  qpat_assum `!i ai ds ei qi zi. _ ==> _` (drule_all_then strip_assume_tac) >>
  Cases_on `SUC i = LENGTH cuts`
  >- (qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >> simp[] >>
      disch_then strip_assume_tac >>
      `~(SUC i < LENGTH cuts)` by decide_tac >>
      qexistsl [`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,`later`,`fresh`] >>
      asm_rewrite_tac[optionTheory.THE_DEF]) >>
  qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >> asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  qpat_assum `!k. k < LENGTH p ==> ?row. _` (drule_then strip_assume_tac) >>
  `SUC i < LENGTH cuts` by decide_tac >>
  qexistsl [`sf`,`tf`,`inc`,`entry`,`order`,`res`,`nrest`,`later`,
    `LUPDATE (agg (DROP k p)) (EL k inds) row`] >>
  simp[EL_LUPDATE]
QED

Theorem block_activation_incoming[local]:
  (case (a:'a # 'b # 'c # 'd # 'e # 'f # 'g) of
     (_,_,inc,_,_,_,_) => inc) = FST (SND (SND a))
Proof
  PairCases_on `a` >> simp[]
QED

(* The old q=0 cut seeds the same-level append. Its selected ancestor rows
   are unchanged; the completed row and initialized row are added only at
   the final level. The final table aggregates, not the old remainders,
   determine the new suffix witnesses. *)
Theorem block_initialized_fresh_cut:
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
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  (?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,
    NONE:exec_result option,NONE:bytes32 list option)) /\
  (!a sf tf inc entry order res nrest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
    order <> [] /\ order = GENLIST (\i. inc + SUC i) (LENGTH order) /\
    (!e. MEM e order <=> (a,e) IN FDOM blocks)) /\
  (!a e bb bt ps xs ys rho hin h0 body count front closed brest.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) ==>
    ?sf tf inc entry order res nrest sp.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      MEM e order /\ bb.bb_instructions = ps ++ xs /\
      bt.bb_instructions = ps ++ ys /\
      EVERY (\i. is_pseudo i.inst_opcode) ps /\
      EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
      EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
      eval_phis hin bt.bb_instructions = OK sp /\
      (if e = SUC inc then hin = entry else
        ?pb pt pps pxs pys prho pin ph pbe pc pu.
          FLOOKUP blocks (a,e-1) =
            SOME (pb,pt,pps,pxs,pys,prho,pin,ph,pbe,pc,OK hin,T,SOME pu) /\
          ~hin.vs_halted) /\
      (closed <=> IS_SOME brest) /\
      (case body of NONE => a = p /\ e = d
       | SOME (be,hbe) =>
           FOLDR (dft_exec_cons (N-e) C8) OK
             (DROP (phi_prefix_length bt.bb_instructions) ps)
             (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be) /\
      (e <> LAST order ==> closed)) /\
  FLOOKUP acts (p:(num # num) list) = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,rho0,hin,(h0:num),SOME (be,(hbe:num)),cnt0,OK s,F,NONE) /\
  LAST order = d /\
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\ FDOM blocks = FDOM ks_tab /\
  (!a e bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ess ks.
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
    LENGTH ms = LENGTH xs /\
    (!sf tf inc entry order res nrest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
      !F k kgss tail.
        N <= F /\ k <= LENGTH xs /\
        EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
        (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
        LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE k ms) kgss ==>
        (?extra. FLAT (TAKE k ess) =
          gas_events_block (F-e) C7 sf.fn_name
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
            (be with vs_gas_readings := FLAT kgss ++ tail)) = ZIP (FLAT (TAKE k ks),FLAT kgss) /\
          (!tail'.
            FOLDR (dft_exec_cons (F-e) C7) OK (TAKE k xs)
              (be with vs_gas_readings := FLAT kgss ++ tail') = OK (u with vs_gas_readings := tail') /\
            gas_events_block (F-e) C7 sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
              (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))))) /\
  (!a e sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count r8 u0 ms ess ks.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,r8,T,SOME u0) /\
    FLOOKUP ms_tab (a,e) = SOME ms /\
    FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks ==>
    !F. N <= F ==> !gs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT ms) gs ==>
      (?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
        (be with vs_gas_readings := gs ++ tail))) ==>
      (((?v. r8 = OK v) \/ (?ir v. r8 = IntRet ir v)) ==>
        residual_result tail r8 (FOLDR (dft_exec_cons (F-e) C7) OK xs
          (be with vs_gas_readings := gs ++ tail)))) /\
  (!a e cid q h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) ==>
    ?sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 be hbe count front closed brest
      csf ctf child_order child_res child_rest nm ops args.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) =
        SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
      q < LENGTH xs /\ (EL q xs).inst_id = cid /\ (EL q xs).inst_opcode = INVOKE /\
      done = TAKE (b0.vs_inst_idx - LENGTH ps) rho /\ ~MEM q done /\
      FLOOKUP acts ((e,cid)::a) =
        SOME (csf,ctf,e,child_entry,child_order,child_res,child_rest) /\
      decode_invoke (EL q xs) = SOME (nm,ops) /\
      lookup_function nm C8.ctx_functions = SOME ctf /\
      eval_operands ops b0 = SOME args /\ setup_callee ctf args b0 = SOME child_entry /\
      (case ret of NONE => MEM ((e,cid)::a) (GENLIST (\i. DROP i p) (SUC (LENGTH p)))
       | SOME triple => MEM q (TAKE count rho))) /\
  (!k. k < LENGTH p ==>
    ?bb' bt' ps' xs' ys' rho' hin' h0' be' hbe' cnt'
      q' h' b0' done' child_entry' cid' e' a'.
      a' = DROP (SUC k) p /\ (e',cid') = EL k p /\
      FLOOKUP blocks (a',e') =
        SOME (bb',bt',ps',xs',ys',rho',hin',h0',SOME (be',hbe'),cnt',OK b0',F,NONE) /\
      FLOOKUP calls (a',e',cid') = SOME (q',h',b0',done',child_entry',NONE) /\
      done' = TAKE cnt' rho') /\
  (!a e cid q h b0 done child_entry ret bb bt ps xs ys rho hin h0 be hbe count front closed brest ms.
    FLOOKUP calls (a,e,cid) = SOME (q,h,b0,done,child_entry,ret) /\
    FLOOKUP blocks (a,e) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
    FLOOKUP ms_tab (a,e) = SOME ms ==>
    !F kgss tail u.
      N <= F /\
      LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w)) (TAKE q ms) kgss /\
      FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      (!op. MEM op (EL q xs).inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee argv. setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
        setup_callee callee argv b0)) /\
  z0 = DROP (phi_prefix_length bb.bb_instructions) ps /\
  Z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts0 = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH cuts0 = LENGTH levels0 /\
  (!i ai ds ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts0 then ai = p /\ ei = d /\ qi = 0 /\ zi = z0
       else ?cid h b0 done child_entry ret.
         EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts0) = (ei,cid)::ai /\
         FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
         qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
         (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
      EL i levels0 =
        (sfi,MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
         if SUC i = LENGTH cuts0 then NONE else SOME (EL qi xsi))) /\
  M0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts0) /\
  E0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts0) /\
  K0 = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts0) /\
  LENGTH M0 = LENGTH E0 /\ LENGTH M0 = LENGTH K0 /\
  (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs ==>
    levels_ok F C7 levels0 (MAP (\(ai,ds,ei,qi,zi). ai) cuts0)
      (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts ai) of
        (sf,tf,inc,ent,order,res,nrest) => inc) cuts0) root_sf
      (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E0 = FST (rooted_eval F C7 levels0
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u => FST (rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail)) = E0 /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((p,d,(EL (LENGTH z0) Z).inst_id),sf,EL (LENGTH z0) Z,u)] ++ after /\
          trace_gas before = ZIP (K0,gs)) /\
        (!tail'. rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail') =
          (E0,OK (u with vs_gas_readings := tail')))
    | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail)))) /\
  bb.bb_instructions = ps ++ xs /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  be.vs_inst_idx = LENGTH ps /\ be.vs_current_bb = bb.bb_label /\
  xs <> [] /\ is_terminator (LAST xs).inst_opcode /\ ~post.vs_halted /\
  bb.bb_instructions <> [] /\ EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
  is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
  Mb = FLAT (THE (FLOOKUP ms_tab (p,d))) /\
  Eb = FLAT (THE (FLOOKUP es_tab (p,d))) /\
  Kb = FLAT (THE (FLOOKUP ks_tab (p,d))) /\
  LENGTH Mb = LENGTH Eb /\ LENGTH Mb = LENGTH Kb /\
  (!F gs tail. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mb gs ==>
    (?extra. Eb = gas_events_block (F-d) C7 sf.fn_name
      <|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
      (be with vs_gas_readings := gs ++ tail) ++ extra) /\
    ((?f. terminates (FOLDR (dft_exec_cons f C7) OK xs
        (be with vs_gas_readings := gs ++ tail))) ==>
      gas_events_block (F-d) C7 sf.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail) = Eb /\
      residual_result tail (OK post)
        (FOLDR (dft_exec_cons (F-d) C7) OK xs (be with vs_gas_readings := gs ++ tail))) /\
    (!v. (FOLDR (dft_exec_cons (F-d) C7) OK xs (be with vs_gas_readings := gs ++ tail) = OK v \/
          ?ir. FOLDR (dft_exec_cons (F-d) C7) OK xs (be with vs_gas_readings := gs ++ tail) = IntRet ir v) ==>
      trace_gas (trace_block p d (F-d) C7 sf
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
        (be with vs_gas_readings := gs ++ tail)) = ZIP (Kb,gs))) /\
  N <= Nnew /\ SUC d <= Nnew /\
  dft_fn_rel sf tf /\ lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\
  lookup_block bb1.bb_label sf.fn_blocks = SOME bb1 /\
  lookup_block bb1.bb_label tf.fn_blocks = SOME bt1 /\ MEM bb1 sf.fn_blocks /\
  bb1.bb_instructions = ps1 ++ xs1 /\ bt1.bb_instructions = ps1 ++ ys1 /\ bt1.bb_label = bb1.bb_label /\
  EVERY (\i. is_pseudo i.inst_opcode) ps1 /\ EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys1 /\ LENGTH xs1 = LENGTH ys1 /\
  EVERY inst_shape_ok bb1.bb_instructions /\
  eval_phis post bt1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bt1.bb_instructions /\
  get_instruction bt1 s1.vs_inst_idx = SOME next /\
  acts' = acts |+ (p,(sf,tf,inc,entry,order ++ [SUC d],NONE,NONE)) /\
  blocks' = (blocks |+ ((p,d),(bb,bt,ps,xs,ys,rho0,hin,h0,SOME(be,hbe),LENGTH ys,OK post,T,SOME post.vs_gas_readings))) |+
    ((p,SUC d),(bb1,bt1,ps1,xs1,ys1,rho1,post,h1,body1,0,OK s1,F,NONE)) /\
  FLOOKUP ms_tab' (p,SUC d) = SOME cm /\ FLOOKUP es_tab' (p,SUC d) = SOME ce /\
  FLOOKUP ks_tab' (p,SUC d) = SOME ck /\
  (!k. k < LENGTH p ==>
    ?h b done ent ord rsf rtf rinc rent.
      FLOOKUP calls (DROP (SUC k) p,FST (EL k p),SND (EL k p)) =
        SOME (EL k inds,(h:num),b,done,ent,NONE:(internal_return # venom_state # venom_state) option) /\
      FLOOKUP acts (DROP (SUC k) p) = SOME (rsf,rtf,rinc,rent,ord,NONE,NONE) /\
      LAST ord = FST (EL k p)) /\
  (!a e. (a,e) <> (p,SUC d) /\
    (!i. i < LENGTH p ==> (a,e) <> (DROP (SUC i) p,FST (EL i p))) ==>
    FLOOKUP ms_tab' (a,e) = FLOOKUP ms_tab (a,e) /\
    FLOOKUP es_tab' (a,e) = FLOOKUP es_tab (a,e) /\
    FLOOKUP ks_tab' (a,e) = FLOOKUP ks_tab (a,e)) /\
  AM' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  AE' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  AK' = (\a. FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (a,f))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts' a))))))))) /\
  (!i. i < LENGTH p ==>
    ?mr er kr.
      FLOOKUP ms_tab (DROP (SUC i) p,FST (EL i p)) = SOME mr /\
      FLOOKUP es_tab (DROP (SUC i) p,FST (EL i p)) = SOME er /\
      FLOOKUP ks_tab (DROP (SUC i) p,FST (EL i p)) = SOME kr /\
      EL i inds < LENGTH mr /\ EL i inds < LENGTH er /\ EL i inds < LENGTH kr /\
      FLOOKUP ms_tab' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AM' (DROP i p)) (EL i inds) mr) /\
      FLOOKUP es_tab' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AE' (DROP i p)) (EL i inds) er) /\
      FLOOKUP ks_tab' (DROP (SUC i) p,FST (EL i p)) = SOME (LUPDATE (AK' (DROP i p)) (EL i inds) kr)) /\
  ((IS_SOME body1 /\ q < LENGTH xs1 /\
    z = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q xs1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs1) /\
    (!r. r < q /\ (EL r xs1).inst_opcode = INVOKE ==> MEM r (TAKE 0 rho1))) \/
   (body1 = NONE /\ q = 0 /\ z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1))) /\
  (if s1.vs_inst_idx < LENGTH ps1 then
    body1 = NONE /\
    (!F gs z. Nnew <= F /\ z = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) ==>
      row_eval F C7 sf.fn_name (bb1,SUC d,z) (post with vs_gas_readings := gs) =
        ([],OK (s1 with vs_gas_readings := gs)))
   else
    s1.vs_inst_idx = LENGTH ps1 /\ body1 = SOME (s1,h1) /\
    dft_remaining_inv sf bb1 xs1 s1 /\
    cm = GENLIST (\r. if (EL r xs1).inst_opcode = GAS then [NONE] else []) (LENGTH xs1) /\
    ck = GENLIST (\r. if (EL r xs1).inst_opcode = GAS then [(p,SUC d,(EL r xs1).inst_id)] else []) (LENGTH xs1) /\
    LENGTH cm = LENGTH xs1 /\ LENGTH ce = LENGTH cm /\ LENGTH ck = LENGTH cm /\
    LIST_REL (\m es. LENGTH m = LENGTH es) cm ce /\ LIST_REL (\m keys. LENGTH m = LENGTH keys) cm ck /\
    (!F q kgss tail z. Nnew <= F /\ q < LENGTH xs1 /\
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
          (events,OK (u with vs_gas_readings := tail'))))) ==>
  ?cuts levels Mcut Ecut Kcut mr er kr.
    MAP (\(ai,ds,ei,qi,zi). ai) cuts = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then ai = p /\ ei = SUC d /\ qi = q /\ zi = z
         else ?cid h b0 done child_entry ret.
           EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
           FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
           qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
           zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
           EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
           (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
        EL i levels =
          (sfi,MAP (\f. (FST (THE (FLOOKUP blocks' (ai,f))),f,
            DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)
              (FST (THE (FLOOKUP blocks' (ai,f)))).bb_instructions)) ds ++ [(bbi,ei,zi)],
           if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
    Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei))))) cuts) /\
    AM' [] = Mcut ++ mr /\ AE' [] = Ecut ++ er /\ AK' [] = Kcut ++ kr /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail. Nnew <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      levels_ok F C7 levels (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
        (MAP (\(ai,ds,ei,qi,zi). case THE (FLOOKUP acts' ai) of
          (sf,tf,inc,ent,order,res,nrest) => inc) cuts)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((p,SUC d,(EL (LENGTH z)
                (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions),u)] ++ after /\
            trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail'))) /\
          (body1 = NONE ==> u with vs_gas_readings := s1.vs_gas_readings = s1) /\
          (IS_SOME body1 /\ inv_memory_observation next.inst_opcode /\ EL q xs1 = next ==>
            (!op. MEM op next.inst_operands ==> eval_operand op u = eval_operand op s1) /\
            u.vs_initial_fmp = s1.vs_initial_fmp)
      | stopped => run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!F gs tail ev u. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
    rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
    u = (be with vs_gas_readings := tail)` by suspend "anchor" >>
  suspend "compose"
QED

Resume block_initialized_fresh_cut[anchor]:
  map_every qx_gen_tac [`fuel`,`gs`,`tail`,`ev`,`u`] >> strip_tac >>
  `!F gs tail ev u. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
    rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
    ev = E0` by
    (map_every qx_gen_tac [`F'`,`gs'`,`tail'`,`ev'`,`u'`] >> strip_tac >>
     qpat_assum `!F gs tail. N <= F /\ _ ==> levels_ok F C7 levels0 _ _ _ _ [] 0 /\ _`
       (qspecl_then [`F'`,`gs'`,`tail'`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `rooted_eval F' _ _ _ = (ev',OK u')` (fn th => simp[NoAsms,th])) >>
  `0 < LENGTH xs` by
    (qpat_assum `xs <> []` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `xs` >> simp[]) >>
  `FDOM ks_tab = FDOM ms_tab /\ FDOM ks_tab = FDOM es_tab` by
    (qpat_assum `FDOM blocks = FDOM ks_tab` (fn hk =>
     qpat_assum `FDOM blocks = FDOM ms_tab` (fn hm =>
     qpat_assum `FDOM blocks = FDOM es_tab` (fn he =>
       rewrite_tac[GSYM hk,GSYM hm,GSYM he])))) >>
  irule (cj 2 dft_packet_return_anchor_state) >>
  qexistsl [`C7`,`C8`,`E0`,`fuel`,`M0`,`N`,`p`,`acts`,`bb`,`blocks`,`NONE`,`bt`,`call_setup`,`calls`,
    `bb`,`SOME (be,hbe)`,`cnt0`,`h0`,`hin`,`F`,`cnt0`,`ps`,`rho0`,`bt`,`cuts0`,`xs`,`ys`,`d`,`d`,
    `es_tab`,`ev`,`OK s`,`gs`,`h0`,`hbe`,`hin`,`ks_tab`,`levels0`,`ms_tab`,`p`,`plan_eval`,`ps`,
    `rho0`,`root_entry`,`root_sf`,`root_tf`,`rooted_eval`,`row_eval`,`s`,`xs`,`ys`,`z0`] >>
  asm_rewrite_tac[] >>
  qpat_assum `FDOM blocks = FDOM ms_tab` (fn hm =>
  qpat_assum `FDOM blocks = FDOM es_tab` (fn he => rewrite_tac[GSYM hm,GSYM he]))
QED

Resume block_initialized_fresh_cut[compose]:
  qabbrev_tac `rows = \a ds. MAP (\f.
    (FST (THE (FLOOKUP blocks (a,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
       (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds` >>
  `order = GENLIST (\i. inc + SUC i) (LENGTH order)` by
    (qpat_assum `!a sf tf inc entry order res nrest. _ ==> _`
       (drule_then (ACCEPT_TAC o cj 2))) >>
  `?prior pre ds0. cuts0 = prior ++ [(p,ds0,d,(0:num),z0)] /\
    levels0 = pre ++ [(sf,rows p ds0 ++ [(bb,d,z0)],NONE)] /\
    LENGTH pre = LENGTH prior /\ order = ds0 ++ [d] /\
    ~MEM d ds0 /\ ~MEM (SUC d) ds0` by
    (`LENGTH levels0 = LENGTH cuts0` by (sym_tac >> first_assum ACCEPT_TAC) >>
     irule block_anchor_decompose >>
     rpt (first_assum (irule_at Any)) >>
     map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. _ ==> _` (drule_all_then strip_assume_tac) >>
     qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,
       `ini`,`hi`,`bei`,`counti`,`fronti`,`closedi`,`resti`,`later`] >>
     ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _` mp_tac >>
     qpat_x_assum `EL i levels0 = _` mp_tac >>
     qpat_assum `SUC i = LENGTH cuts0` (fn th => simp[NoAsms,th,Abbr `rows`])) >>
  qabbrev_tac `paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts0` >>
  qabbrev_tac `incoming = MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts0` >>
  qabbrev_tac `cuts = prior ++ [(p,ds0 ++ [d],SUC d,q,z)]` >>
  qabbrev_tac `levels = pre ++ [(sf,rows p ds0 ++ [(bb,d,Z);(bb1,SUC d,z)],NONE)]` >>
  qabbrev_tac `rows' = \a ds. MAP (\f.
    (FST (THE (FLOOKUP blocks' (a,f))),f,
     DROP (phi_prefix_length (FST (THE (FLOOKUP blocks' (a,f)))).bb_instructions)
       (FST (THE (FLOOKUP blocks' (a,f)))).bb_instructions)) ds` >>
  `!i ai ds ei qi zi. i < LENGTH prior /\ EL i prior = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later cid h b0 done child ret.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      EL (SUC i) paths = (ei,cid)::ai /\
      FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child,ret) /\
      qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
      zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
      EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
      (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done) /\
      EL i pre = (sfi,rows ai ds ++ [(bbi,ei,zi)],SOME (EL qi xsi))` by
    (map_every qx_gen_tac [`i`,`ai`,`ds`,`ei`,`qi`,`zi`] >> strip_tac >>
     `i < LENGTH cuts0 /\ ~(SUC i = LENGTH cuts0) /\ i < LENGTH pre` by
       (qpat_assum `cuts0 = prior ++ _` (fn th => simp[th]) >> decide_tac) >>
     `EL i cuts0 = (ai,ds,ei,qi,zi) /\ EL i levels0 = EL i pre` by
       (qpat_assum `cuts0 = _` (fn th => rewrite_tac[th]) >>
        qpat_assum `levels0 = _` (fn th => rewrite_tac[th]) >> simp[EL_APPEND1]) >>
     qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts0 /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `~(SUC i = LENGTH cuts0)` (fn th =>
       qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _`
         (strip_assume_tac o REWRITE_RULE[th]) >>
       qpat_x_assum `EL i levels0 = (sfi,_,_)`
         (assume_tac o REWRITE_RULE[th])) >>
     qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`bbi`,`bti`,`psi`,`xsi`,`ysi`,`rhoi`,
       `ini`,`hi`,`bei`,`counti`,`fronti`,`closedi`,`resti`,`later`,`cid`,`h`,`b0`,`done`,`child_entry`,`ret`] >>
     qpat_assum `EL i levels0 = (sfi,_,_)` (fn th =>
       qpat_assum `EL i levels0 = EL i pre` (fn eq => assume_tac (REWRITE_RULE [eq] th))) >>
     simp[Abbr `rows`,Abbr `paths`]) >>
  `MAP (\(ai,ds,ei,qi,zi). ai) cuts = paths /\ LENGTH cuts = LENGTH levels /\
   MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts = incoming /\
   (!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks' (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then ai = p /\ ei = SUC d /\ qi = q /\ zi = z
       else ?cid h b0 done child ret.
         EL (SUC i) paths = (ei,cid)::ai /\
         FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done,child,ret) /\
         qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
         zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
         EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
         (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done)) /\
      EL i levels = (sfi,rows' ai ds ++ [(bbi,ei,zi)],
        if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi)))` by
    (qpat_assum `Abbrev (incoming = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     irule block_fresh_cut_geometry >>
     rpt (first_assum (irule_at Any)) >>
     qexists `rows` >>
     conj_tac >- simp[Abbr `rows'`] >>
     conj_tac >- simp[Abbr `paths`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[Abbr `rows`] >>
     conj_tac >-
       (qpat_assum `Z = DROP _ _` (fn th => simp[NoAsms,Abbr `levels`,th])) >>
     simp[Abbr `cuts`]) >>
  `paths = REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    simp[Abbr `paths`] >>
  `!i ai ds ei qi zi. i < LENGTH prior /\ EL i prior = (ai,ds,ei,qi,zi) ==>
    ?cid k. k < LENGTH p /\ ai = DROP (SUC k) p /\ (ei,cid) = EL k p /\
      EL (SUC i) paths = (ei,cid)::ai /\ FST (EL (SUC i) cuts) = DROP k p /\ qi = EL k inds` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. i < LENGTH prior /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     `SUC i < LENGTH paths /\ EL i paths = ai` by
       (simp[Abbr `paths`,EL_MAP,EL_APPEND1] >> decide_tac) >>
     drule_all_then strip_assume_tac block_anchor_live_edge >>
     qexistsl [`cid`,`k`] >>
     `FST (EL (SUC i) cuts) = EL (SUC i) paths` by
       (qpat_assum `MAP _ cuts = paths` (fn th => pure_once_rewrite_tac[GSYM th]) >>
        `SUC i < LENGTH cuts` by
          (qpat_assum `i < LENGTH prior` mp_tac >>
           simp[NoAsms,Abbr `cuts`] >> decide_tac) >>
        qpat_assum `SUC i < LENGTH cuts` (fn th => simp[NoAsms,EL_MAP,th]) >>
        qabbrev_tac `t = EL (SUC i) cuts` >> PairCases_on `t` >> simp[NoAsms]) >>
     `DROP k p = (ei,cid)::ai` by
       (qpat_assum `(ei,cid) = EL k p` (fn th => rewrite_tac[th]) >>
        qpat_assum `ai = DROP (SUC k) p` (fn th => rewrite_tac[th]) >>
        metis_tac[DROP_BY_DROP_SUC]) >>
     `!j. j < LENGTH p ==>
      ?h b done ent. FLOOKUP calls (DROP (SUC j) p,FST (EL j p),SND (EL j p)) =
        SOME (EL j inds,h,b,done,ent,NONE)` by
       (rpt gen_tac >> strip_tac >> qpat_assum `!k. k < LENGTH p ==> ?h b done ent ord rsf rtf rinc rent. _`
          (drule_then strip_assume_tac) >> goal_assum (drule_at Any)) >>
     drule_all_then strip_assume_tac block_anchor_pending_index >>
     `EL k inds = qi` by
       (qpat_assum `!k. _ ==> FST (EL k p) = ei /\ _` (qspec_then `k` mp_tac) >> simp[]) >>
     simp[]) >>
  `!i ai ds ei qi zi. i < LENGTH prior /\ EL i prior = (ai,ds,ei,qi,zi) ==>
    ?cid h b done ent ret ord later.
      EL (SUC i) (MAP (\(ai,ds,ei,qi,zi). ai) (prior ++ [(p,ds0,d,0,z0)])) = (ei,cid)::ai /\
      FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b,done,ent,ret) /\
      ord = ds ++ ei::later /\ ALL_DISTINCT ord /\ LAST ord = ei` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. i < LENGTH prior /\ _ ==> ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi ini hi bei counti fronti closedi resti later cid h b0 done child ret. _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?cid k. k < LENGTH p /\ ai = DROP (SUC k) p /\ _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `!k. k < LENGTH p ==> ?h b done ent ord rsf rtf rinc rent. _`
       (drule_then strip_assume_tac) >>
     `ord = orderi /\ FST (EL k p) = ei` by
       (qpat_assum `FLOOKUP acts (DROP (SUC k) p) = _` mp_tac >>
        qpat_assum `FLOOKUP acts ai = _` mp_tac >>
        qpat_assum `(ei,cid') = EL k p` (mp_tac o Q.AP_TERM `FST`) >>
        qpat_assum `ai = DROP (SUC k) p` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> ntac 4 (disch_then assume_tac) >> gvs[]) >>
     qexistsl [`cid`,`h`,`b0`,`done`,`child`,`ret`,`orderi`,`later`] >>
     conj_tac >- (qpat_assum `Abbrev (paths = _)` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
                  qpat_assum `cuts0 = prior ++ _` (fn th => rewrite_tac[th]) >>
                  disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (`orderi = GENLIST (\j. inci + SUC j) (LENGTH orderi)` by
          (qpat_assum `!a sf tf inc entry order res nrest. _ ==> _`
             (qspecl_then [`ai`,`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`]
               (drule_then (ACCEPT_TAC o cj 2)))) >>
        pop_assum (fn th => pure_once_rewrite_tac[th]) >>
        simp[NoAsms,ALL_DISTINCT_GENLIST]) >>
     qpat_assum `ord = orderi` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     qpat_assum `FST (EL k p) = ei` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `!k. k < LENGTH p ==>
      ?h b done ent. FLOOKUP calls (DROP (SUC k) p,FST (EL k p),SND (EL k p)) =
        SOME (EL k inds,h,b,done,ent,NONE)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!k. k < LENGTH p ==> ?h b done ent ord rsf rtf rinc rent. _`
       (drule_then strip_assume_tac) >> goal_assum (drule_at Any)) >>
  `MAP (\(ai,ds,ei,qi,zi). ai) (prior ++ [(p,ds0,d,0,z0)]) =
    REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p)))` by
    (qpat_assum `cuts0 = prior ++ _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     (simp[])) >>
  `!f. f <> SUC d ==> FLOOKUP ms_tab' (p,f) = FLOOKUP ms_tab (p,f) /\
      FLOOKUP es_tab' (p,f) = FLOOKUP es_tab (p,f) /\
      FLOOKUP ks_tab' (p,f) = FLOOKUP ks_tab (p,f)` by
    (gen_tac >> disch_tac >>
     `!i. i < LENGTH p ==> p <> DROP (SUC i) p` by
       (rpt strip_tac >>
        qpat_assum `p = DROP (SUC i) p` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[NoAsms,LENGTH_DROP] >> decide_tac) >>
     qpat_assum `!a e. _ ==> FLOOKUP ms_tab' (a,e) = _ /\ _`
       (qspecl_then [`p`,`f`] irule) >> simp[pairTheory.PAIR_EQ]) >>
  `!ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) prior ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei)))) /\
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab' (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab' (ai,ei)))) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))` by
    (rpt gen_tac >> disch_tac >> rpt conj_tac >>
     irule block_anchor_prefix_frame >>
     qexistsl [`calls`,`d`,`ds0`,`inds`,`p`,`prior`,`z0`,`zi`] >>
     asm_rewrite_tac[] >>
     conj_tac >-
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!a e. _ ==> FLOOKUP ms_tab' (a,e) = _ /\ _`
          (drule_all_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     gen_tac >> strip_tac >>> NTH_GOAL (simp[]) 2 >>> NTH_GOAL (simp[]) 3 >>
     qpat_assum `!i. i < LENGTH p ==> ?mr er kr. FLOOKUP ms_tab _ = SOME mr /\ _`
       (drule_then strip_assume_tac) >>
     FIRST [qmatch_goalsub_abbrev_tac `FLOOKUP ms_tab' key` >>
              qexistsl [`mr`,`AM' (DROP i p)`],
            qmatch_goalsub_abbrev_tac `FLOOKUP es_tab' key` >>
              qexistsl [`er`,`AE' (DROP i p)`],
            qmatch_goalsub_abbrev_tac `FLOOKUP ks_tab' key` >>
              qexistsl [`kr`,`AK' (DROP i p)`]] >>
     simp[Abbr `key`]) >>
  `!i ai ds ei qi zi. i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti later.
      FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then ai = p /\ ei = SUC d /\ qi = q
       else ?k. k < LENGTH p /\ ai = DROP (SUC k) p /\ ei = FST (EL k p) /\
         qi = EL k inds /\ FST (EL (SUC i) cuts) = DROP k p)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> _`
       (drule_all_then strip_assume_tac) >>
     qexistsl [`sfi`,`tfi`,`inci`,`enti`,`orderi`,`resi`,`nresti`,`later`] >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     Cases_on `SUC i = LENGTH cuts`
     >- (qpat_x_assum `if SUC i = LENGTH cuts then _ else _` mp_tac >> simp[]) >>
     qpat_assum `SUC i <> LENGTH cuts` (fn th => simp[NoAsms,th]) >>
     `i < LENGTH prior` by
       (qpat_assum `i < LENGTH cuts` mp_tac >>
        qpat_assum `SUC i <> LENGTH cuts` mp_tac >>
        simp[NoAsms,Abbr `cuts`] >> decide_tac) >>
     `EL i prior = (ai,ds,ei,qi,zi)` by
       (qpat_assum `EL i cuts = _` mp_tac >>
        qpat_assum `i < LENGTH prior` (fn th =>
          simp[NoAsms,Abbr `cuts`,EL_APPEND1,th])) >>
     qpat_assum `!i ai ds ei qi zi. _ ==> ?cid k. k < LENGTH p /\ ai = DROP (SUC k) p /\ _`
       (drule_all_then strip_assume_tac) >>
     qexists `k` >>
     qpat_assum `(ei,cid) = EL k p` (assume_tac o Q.AP_TERM `FST`) >> simp[]) >>
  suspend "replay"
QED

Resume block_initialized_fresh_cut[replay]:
  qabbrev_tac `M1 = FLAT (TAKE q (THE (FLOOKUP ms_tab' (p,SUC d))))` >>
  qabbrev_tac `E1 = FLAT (TAKE q (THE (FLOOKUP es_tab' (p,SUC d))))` >>
  qabbrev_tac `K1 = FLAT (TAKE q (THE (FLOOKUP ks_tab' (p,SUC d))))` >>
  qabbrev_tac `R = \fuel. row_eval fuel C7 sf.fn_name (bb1,SUC d,z)` >>
  `M1 = FLAT (TAKE q cm) /\ E1 = FLAT (TAKE q ce) /\ K1 = FLAT (TAKE q ck)` by
    simp[Abbr `M1`,Abbr `E1`,Abbr `K1`] >>
  mp_tac (Q.INST [`m'` |-> `ms_tab'`, `es'` |-> `es_tab'`, `ks'` |-> `ks_tab'`]
    block_initialized_row_replay) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[Abbr `M1`] >>
     conj_tac >- simp[Abbr `E1`] >>
     conj_tac >- simp[Abbr `K1`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     Cases_on `s1.vs_inst_idx < LENGTH ps1`
     >- (qpat_assum `s1.vs_inst_idx < LENGTH ps1` (fn th =>
           qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then _ else _`
             (strip_assume_tac o PURE_REWRITE_RULE [th,COND_CLAUSES]) >>
           pure_rewrite_tac[th,COND_CLAUSES]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `body1 = NONE` (fn th =>
           qpat_assum `IS_SOME body1 /\ _ \/ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [th])) >>
         map_every qx_gen_tac [`fuel`,`gs`] >> strip_tac >>
         qpat_assum `!F gs z. _ ==> row_eval _ _ _ _ _ = _`
           (qspecl_then [`fuel`,`gs`,`z`] mp_tac) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
         simp[NoAsms,Abbr `R`]) >>
     qpat_assum `~(s1.vs_inst_idx < LENGTH ps1)` (fn th =>
       qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then _ else _`
         (strip_assume_tac o PURE_REWRITE_RULE [th,COND_CLAUSES]) >>
       pure_rewrite_tac[th,COND_CLAUSES]) >>
     qpat_assum `body1 = SOME (s1,h1)` (fn th =>
       qpat_assum `IS_SOME body1 /\ _ \/ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [th])) >>
     ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
     map_every qx_gen_tac [`fuel`,`kgss`,`tail`] >> strip_tac >>
     qpat_assum `!F q kgss tail z. _ ==> _`
       (qspecl_then [`fuel`,`q`,`kgss`,`tail`,`z`] mp_tac) >>
     (impl_tac >- simp[]) >>
     simp[NoAsms,Abbr `R`])) >>
  disch_then assume_tac >>
  mp_tac (Q.INST [
    `bb` |-> `bb1`, `bt` |-> `bt1`, `ps` |-> `ps1`, `xs` |-> `xs1`, `ys` |-> `ys1`,
    `s` |-> `s1`, `e` |-> `SUC d`, `mcut` |-> `M1`]
    block_initialized_append_observation) >>
  (impl_tac >-
    (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     Cases_on `s1.vs_inst_idx < LENGTH ps1`
     >- (disj1_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >>
     qpat_assum `~(s1.vs_inst_idx < LENGTH ps1)` (fn th =>
       qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then _ else _`
         (strip_assume_tac o REWRITE_RULE [th])) >>
     qpat_assum `body1 = SOME (s1,h1)` (fn th =>
       qpat_assum `IS_SOME body1 /\ _ \/ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [th])) >>
     ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
     map_every qx_gen_tac [`fuel`,`kgss`,`tail`] >> strip_tac >>
     qpat_assum `!F q kgss tail z. _ ==> _`
       (qspecl_then [`fuel`,`q`,`kgss`,`tail`,`z`] mp_tac) >>
     (impl_tac >- simp[]) >>
     qpat_assum `Abbrev (R = _)` (fn th =>
       pure_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     BETA_TAC >>
     disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 kall_tac assume_tac)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     map_every qx_gen_tac [`events`,`u`] >> strip_tac >>
     qpat_assum `!events u. row_eval _ _ _ _ _ = _ ==> _`
       (qspecl_then [`events`,`u`] (drule_then (ACCEPT_TAC o cj 3))))) >>
  disch_then assume_tac >>
  suspend "append"
QED

Resume block_initialized_fresh_cut[append]:
  qabbrev_tac `base_rows = rows p ds0` >>
  `levels0 = pre ++ [(sf,base_rows ++ [(bb,d,z0)],NONE)]` by
    (simp[NoAsms,Abbr `base_rows`] >> first_assum ACCEPT_TAC) >>
  `levels = pre ++ [(sf,base_rows ++ [(bb,d,Z);(bb1,SUC d,z)],NONE)]` by
    simp[NoAsms,Abbr `levels`,Abbr `base_rows`] >>
  `cuts = prior ++ [(p,ds0 ++ [d],SUC d,q,z)]` by simp[NoAsms,Abbr `cuts`] >>
  `paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts0` by simp[NoAsms,Abbr `paths`] >>
  `!f. MEM f ds0 ==> FLOOKUP ms_tab' (p,f) = FLOOKUP ms_tab (p,f) /\
      FLOOKUP es_tab' (p,f) = FLOOKUP es_tab (p,f) /\
      FLOOKUP ks_tab' (p,f) = FLOOKUP ks_tab (p,f)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!f. f <> SUC d ==> FLOOKUP ms_tab' (p,f) = _ /\ _` irule >>
     strip_tac >>
     qpat_assum `f = SUC d` (fn th =>
       qpat_assum `~MEM (SUC d) ds0` (mp_tac o REWRITE_RULE [GSYM th])) >>
     qpat_assum `MEM f ds0` (fn th => simp[NoAsms,th])) >>
  `Mb = FLAT (THE (FLOOKUP ms_tab' (p,d))) /\
    Eb = FLAT (THE (FLOOKUP es_tab' (p,d))) /\
    Kb = FLAT (THE (FLOOKUP ks_tab' (p,d)))` by
    (`d <> SUC d` by decide_tac >>
     qpat_assum `d <> SUC d` (fn neq =>
       qpat_assum `!f. f <> SUC d ==> FLOOKUP ms_tab' (p,f) = _ /\ _`
         (qspec_then `d` (fn th => pure_rewrite_tac (CONJUNCTS (MP th neq))))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!F gs tail. N <= F /\ _ ==> levels_ok F C7 levels0 _ _ _ _ [] 0 /\ _`
    (fn th =>
       qpat_assum `Abbrev (paths = _)` (fn peq =>
       qpat_assum `Abbrev (incoming = _)` (fn ieq =>
         assume_tac (REWRITE_RULE (block_activation_incoming ::
           map (GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) [peq,ieq]) th)))) >>
  qpat_assum `Abbrev (R = _)` (fn eq =>
    let val expand = BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq]
    in
      qpat_assum `q = 0 /\ _ \/ s1.vs_inst_idx = LENGTH ps1 /\ _`
        (assume_tac o expand) >>
      qpat_assum `!F gs tail events u. _ /\ _ /\ R F _ = _ /\ _ ==> _`
        (assume_tac o expand)
    end) >>
  (* The append theorem takes the observation predicate as a free parameter. *)
  mp_tac (Q.INST [
    `oldlevels` |-> `levels0`, `newlevels` |-> `levels`,
    `oldcuts` |-> `cuts0`, `newcuts` |-> `cuts`,
    `priorcuts` |-> `prior`, `ds` |-> `ds0`, `rows` |-> `base_rows`,
    `q1` |-> `q`, `z1` |-> `z`, `next1` |-> `next`, `focus` |-> `next`,
    `obs_state` |-> `s1`, `ms1` |-> `cm`, `ess1` |-> `ce`, `ks1` |-> `ck`]
    (INST [mk_var ("inv_memory_observation", ``:opcode -> bool``) |->
      ``dftGasInvCrossingProbe$inv_memory_observation``] dft_packet_block_rooted_append)) >>
  (impl_tac >-
    (rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, simp[NoAsms,Abbr `M1`,Abbr `E1`,Abbr `K1`]])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `q <= LENGTH cm /\ q <= LENGTH ce /\ q <= LENGTH ck` by
    (qpat_assum `q = 0 /\ _ \/ s1.vs_inst_idx = LENGTH ps1 /\ _` STRIP_ASSUME_TAC >> simp[]) >>
  `paths = MAP (\(ai,ds,ei,qi,zi). ai) cuts` by
    (sym_tac >> first_assum ACCEPT_TAC) >>
  map_every (fn (slot_ty,tab,agg,fresh,rest) =>
    mp_tac (Q.INST [`tab` |-> tab,`agg` |-> agg,`fresh` |-> fresh,`acts` |-> `acts'`]
      (INST_TYPE [Type.alpha |-> slot_ty] block_fresh_cut_root_suffix)) >>
    (impl_tac >-
      (rpt (conj_tac >- first_assum ACCEPT_TAC) >>
       reverse conj_tac >- first_assum ACCEPT_TAC >>
       qx_gen_tac `k` >> strip_tac >>
       qpat_assum `!i. i < LENGTH p ==> ?mr er kr. FLOOKUP ms_tab _ = SOME mr /\ _`
         (drule_then strip_assume_tac) >>
       rpt (first_assum (irule_at Any)))) >>
    disch_then (qx_choose_then rest assume_tac))
    [(``: bytes32 option``,`ms_tab'`,`AM'`,`cm`,`mr`),
     (``: string # num``,`es_tab'`,`AE'`,`ce`,`er`),
     (``: gas_event``,`ks_tab'`,`AK'`,`ck`,`kr`)] >>
  suspend "output"
QED

Resume block_initialized_fresh_cut[output]:
  qexistsl [`cuts`,`levels`,`M0 ++ Mb ++ M1`,`E0 ++ Eb ++ E1`,`K0 ++ Kb ++ K1`,
    `mr`,`er`,`kr`] >>
  conj_tac >-
    (qpat_assum `MAP _ cuts = paths` (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `!i ai ds ei qi zi. i < LENGTH cuts /\ _ ==> ?sfi tfi inci enti orderi resi nresti bbi. _`
       (fn th => qpat_assum `MAP _ cuts = paths` (fn peq =>
          qpat_assum `Abbrev (rows' = _)` (fn req =>
            ACCEPT_TAC (BETA_RULE (PURE_REWRITE_RULE
              [GSYM peq,REWRITE_RULE [markerTheory.Abbrev_def] req] th)))))) >>
  ntac 3 (conj_tac >- (sym_tac >> first_assum ACCEPT_TAC)) >>
  conj_tac >-
    (qpat_assum `AM' [] = FLAT _ ++ mr` (fn th =>
       qpat_assum `FLAT _ = M0 ++ Mb ++ M1` (fn eq => ACCEPT_TAC (REWRITE_RULE [eq] th)))) >>
  conj_tac >-
    (qpat_assum `AE' [] = FLAT _ ++ er` (fn th =>
       qpat_assum `FLAT _ = E0 ++ Eb ++ E1` (fn eq => ACCEPT_TAC (REWRITE_RULE [eq] th)))) >>
  conj_tac >-
    (qpat_assum `AK' [] = FLAT _ ++ kr` (fn th =>
       qpat_assum `FLAT _ = K0 ++ Kb ++ K1` (fn eq => ACCEPT_TAC (REWRITE_RULE [eq] th)))) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[block_activation_incoming] >>
  qpat_assum `MAP _ cuts = paths` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `MAP _ cuts = incoming` (fn th => pure_rewrite_tac[th]) >>
  `body1 = NONE ==> s1.vs_inst_idx < LENGTH ps1` by
    (qpat_assum `if s1.vs_inst_idx < LENGTH ps1 then _ else _` mp_tac >>
     Cases_on `s1.vs_inst_idx < LENGTH ps1`
     >- (qpat_assum `s1.vs_inst_idx < LENGTH ps1` (fn th => simp[NoAsms,th])) >>
     qpat_assum `~(s1.vs_inst_idx < LENGTH ps1)` (fn th => simp[NoAsms,th])) >>
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  qpat_assum `!F gs tail. Nnew <= F /\ LIST_REL _ (M0 ++ Mb ++ M1) gs ==> _`
    (qspecl_then [`fuel`,`gs`,`tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (fn th =>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >> mp_tac th))) >>
  Cases_on `SND (rooted_eval fuel C7 levels (root_entry with vs_gas_readings := gs ++ tail))` >>
  simp[NoAsms] >>
  strip_tac >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    strip_tac >> qpat_assum `body1 = NONE ==> _` (drule_then assume_tac) >>
      qpat_assum `s1.vs_inst_idx < LENGTH ps1 ==> _` (drule_then ACCEPT_TAC),
    strip_tac >> qpat_assum `inv_memory_observation next.inst_opcode /\ EL q xs1 = next ==> _`
      (fn th => MATCH_MP_TAC th >> conj_tac >> first_assum ACCEPT_TAC)]
QED

Finalise block_initialized_fresh_cut
