Theory dftPacketReturnCutGeometry
Ancestors
  dftPacketSelectedCutTransport dftPacketLastRowValidity
  dftPacketExistingPathInsertion dftGasInvBlockInit
  venomInst finite_map list rich_list

(* This statement is polymorphic so the three retained arrays use exactly the
   same final-child prefix argument, including after that child has returned. *)
Theorem dft_packet_return_cut_array:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (tab : (((num # num) list # num), 'a list list) fmap)
    (prior : ((num # num) list # num list # num # num # instruction list) list).
  cuts0 = prior ++ [(a,ds,e,0,z0)] /\
  cutsq = prior ++ [(a,ds,e,q,z)] /\
  FST (HD cuts0) = [] /\
  agg = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  FLOOKUP tab (a,e) = SOME row /\ q <= LENGTH row /\
  (!i ai di ei qi zi.
    i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) ==>
    ?sf tf inc entry order res nrest later ri.
      FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
      order = di ++ ei::later /\ FLOOKUP tab (ai,ei) = SOME ri /\
      qi <= LENGTH ri /\
      (SUC i < LENGTH cuts0 ==>
        qi < LENGTH ri /\ EL qi ri = agg (FST (EL (SUC i) cuts0)))) /\
  A0 = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) di) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cuts0) /\
  Aq = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (ai,f)))) di) ++
      FLAT (TAKE qi (THE (FLOOKUP tab (ai,ei))))) cutsq) ==>
  Aq = A0 ++ FLAT (TAKE q row) /\ (?rest. agg [] = Aq ++ rest)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- simp[MAP_APPEND,FLAT_APPEND,APPEND_ASSOC] >>
  qpat_x_assum `Aq = _` (fn th => rewrite_tac[th]) >>
  irule dft_packet_selected_cut_prefix >>
  conj_tac >- simp[] >>
  reverse conj_tac >- (Cases_on `prior` >> gvs[]) >>
  qexistsl_tac [`acts`,`tab`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH cuts0` by gvs[] >>
  Cases_on `i < LENGTH prior`
  >- (`EL i cuts0 = (ai,ds',ei,qi,zi)` by gvs[EL_APPEND_EQN] >>
      qpat_x_assum `!i ai di ei qi zi. _` (drule_all_then strip_assume_tac) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      asm_rewrite_tac[] >>
      `FST (EL (SUC i) cuts0) = FST (EL (SUC i) cutsq)` by
        (Cases_on `SUC i < LENGTH prior` >> simp[EL_APPEND_EQN] >>
         `SUC i = LENGTH prior` by gvs[] >> simp[]) >>
      gvs[]) >>
  `i = LENGTH prior` by gvs[] >>
  `EL i cuts0 = (a,ds,e,0,z0)` by simp[EL_APPEND_EQN] >>
  qpat_x_assum `!i ai di ei qi zi. _` (drule_all_then strip_assume_tac) >>
  gvs[EL_APPEND_EQN] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

(* The old zero-body anchor supplies all nonterminal selected records. *)
Theorem dft_packet_return_cut_geometry:
  !(acts : ((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks : (((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls : (gas_event, num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap).
  cuts0 = prior ++ [(a,ds,e,0,z0)] /\
  levels0 = pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)] /\
  cutsq = prior ++ [(a,ds,e,q,z0 ++ TAKE q xs)] /\
  levelsq = pre ++ [(sf,rows ++ [(bb,e,z0 ++ TAKE q xs)],NONE)] /\
  LENGTH cuts0 = LENGTH levels0 /\
  MAP (\(ai,di,ei,qi,zi). ai) cuts0 =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  (!i ai di ei qi zi.
    i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = di ++ ei::later /\
      (if SUC i = LENGTH cuts0 then
        ai = a /\ ei = e /\ qi = 0 /\ zi = z0
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts0) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels0 =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) di ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts0 then NONE else SOME (EL qi xsi))) ==>
  MAP (\(ai,di,ei,qi,zi). ai) cutsq =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cutsq = LENGTH levelsq /\
  MAP (\(ai,di,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cutsq =
  MAP (\(ai,di,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts0 /\
  (!i ai di ei qi zi.
    i < LENGTH cutsq /\ EL i cutsq = (ai,di,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = di ++ ei::later /\
      (if SUC i = LENGTH cutsq then
        ai = a /\ ei = e /\ qi = q /\ zi = z0 ++ TAKE q xs
       else
        ?cid h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cutsq) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levelsq =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) di ++
          [(bbi,ei,zi)], if SUC i = LENGTH cutsq then NONE else SOME (EL qi xsi)))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- gvs[] >> conj_tac >- gvs[] >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >>
  `LENGTH prior = LENGTH pre` by gvs[] >>
  `i < LENGTH cuts0` by gvs[] >>
  Cases_on `i < LENGTH prior`
  >- (`EL i cuts0 = (ai,di,ei,qi,zi)` by gvs[EL_APPEND_EQN] >>
      qpat_x_assum `!i ai di ei qi zi. _` (drule_all_then strip_assume_tac) >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      `EL i levelsq = EL i levels0` by gvs[EL_APPEND_EQN] >>
      `MAP (\(aj,dj,ej,qj,zj). aj) cutsq =
       MAP (\(aj,dj,ej,qj,zj). aj) cuts0` by gvs[] >>
      gvs[]) >>
  `i = LENGTH prior` by gvs[] >>
  `EL i cuts0 = (a,ds,e,0,z0)` by simp[EL_APPEND_EQN] >>
  qpat_x_assum `!i ai di ei qi zi. _` (drule_all_then strip_assume_tac) >>
  gvs[EL_APPEND_EQN] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem dft_packet_return_cut_row_shape:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  q < LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  z0 = DROP (phi_prefix_length bb.bb_instructions) ps /\
  z = z0 ++ TAKE q xs ==>
  LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z /\
  EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = EL q xs
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length ps` by
    metis_tac[dftIndexedExecTheory.dft_phi_prefix_append] >>
  `phi_prefix_length ps <= LENGTH ps` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  `!i. is_pseudo i.inst_opcode ==> ~is_terminator i.inst_opcode` by
    (gen_tac >> Cases_on `i.inst_opcode` >> simp[is_pseudo_def,is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP (phi_prefix_length ps) ps)` by
    (irule EVERY_DROP >> gvs[EVERY_MEM] >> metis_tac[]) >>
  simp[DROP_APPEND,LENGTH_TAKE,EL_APPEND_EQN,TAKE_APPEND] >>
  `phi_prefix_length ps - LENGTH ps = 0` by decide_tac >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem dft_packet_return_cut_lengths:
  !ms ess ks M0 E0 K0 Mq Eq Kq q.
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  LENGTH M0 = LENGTH E0 /\ LENGTH M0 = LENGTH K0 /\
  Mq = M0 ++ FLAT (TAKE q ms) /\
  Eq = E0 ++ FLAT (TAKE q ess) /\
  Kq = K0 ++ FLAT (TAKE q ks) ==>
  LENGTH Mq = LENGTH Eq /\ LENGTH Mq = LENGTH Kq
Proof
  rpt gen_tac >> strip_tac >>
  `MAP LENGTH ms = MAP LENGTH ess` by
    (simp[MAP_EQ_EVERY2] >> metis_tac[LIST_REL_LENGTH]) >>
  `MAP LENGTH ms = MAP LENGTH ks` by
    (simp[MAP_EQ_EVERY2] >> metis_tac[LIST_REL_LENGTH]) >>
  gvs[LENGTH_FLAT,MAP_TAKE] >> decide_tac
QED

Theorem dft_packet_return_cut_validity:
  !F. plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan =
      GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  levels_ok F C (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)])
    paths incoming root_fn entry root_path root_depth /\
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  q < LENGTH xs /\ EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  z0 = DROP (phi_prefix_length bb.bb_instructions) ps ==>
  levels_ok F C (pre ++ [(sf,rows ++ [(bb,e,z0 ++ TAKE q xs)],NONE)])
    paths incoming root_fn entry root_path root_depth
Proof
  gen_tac >> strip_tac >>
  `LENGTH (z0 ++ TAKE q xs) < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
   z0 ++ TAKE q xs = TAKE (LENGTH (z0 ++ TAKE q xs)) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (z0 ++ TAKE q xs)` by
    (qpat_x_assum `plan_ok = _` kall_tac >>
     qpat_x_assum `levels_ok = _` kall_tac >>
     qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` kall_tac >>
     metis_tac[dft_packet_return_cut_row_shape]) >>
  drule_all dft_packet_levels_last_row_replace >> simp[]
QED
