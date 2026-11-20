Theory dftPacketCallFreshRoot
Ancestors
  dftPacketCallFreshEntry dftPacketFreshRootGeometry dftPacketCutExtension
  dftPacketFreshSingletonNative
  dftPacketFreshSingletonStop dftPacketFreshSingletonObservation
  dftPacketCalleeAlignment
  dftGasFromListReplayBoundary dftRunRel venomInst venomExecSemantics
  venomExecProofs dftIndexedExec list rich_list arithmetic

Theorem fresh_cut_shape[local]:
  bb.bb_instructions = ps ++ xs /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  m = phi_prefix_length bb.bb_instructions /\
  ((q < LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q xs) /\
    z = DROP m ps ++ TAKE q xs /\ k = LENGTH ps-m+q) \/
   (m <= l /\ l < LENGTH ps /\ z = DROP m (TAKE l ps) /\ k = l-m)) ==>
  z = TAKE k (DROP m bb.bb_instructions) /\
  k < LENGTH (DROP m bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) z
Proof
  strip_tac >>
  `EVERY (\i. i.inst_opcode <> PHI) xs /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) ps` by
    (gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `phi_prefix_length ps <= LENGTH ps` by simp[phi_prefix_length_le] >>
  gvs[dft_phi_prefix_append, DROP_APPEND1, TAKE_APPEND2,
      TAKE_APPEND1, DROP_TAKE, EVERY_DROP, EVERY_TAKE]
QED

Theorem dft_packet_call_fresh_root_cut:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  lookup_function nm C7.ctx_functions = SOME csf /\
  ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\
  setup_callee ctf args b0 = SOME child_entry /\
  c.inst_opcode = INVOKE /\ c = EL q0 xs0 /\
  LAST cuts = (p,(ds:num list),d,q0,z0) /\ LAST plan = (bb0,d,z0) /\
  c = EL (LENGTH z0) (DROP (phi_prefix_length bb0.bb_instructions)
    bb0.bb_instructions) /\
  b = (d,c.inst_id)::p /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH cuts = LENGTH (pre ++ [(sf,plan,NONE)]) /\
  LENGTH M0 = LENGTH E0 /\ LENGTH M0 = LENGTH K0 /\
  cb.bb_instructions = cps ++ cxs /\
  EVERY (\i. is_pseudo i.inst_opcode) cps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) cxs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) cys /\
  MEM cb csf.fn_blocks /\
  lookup_block child_entry.vs_current_bb csf.fn_blocks = SOME cb /\
  eval_phis child_entry (cps ++ cys) = OK csp /\
  m = phi_prefix_length cb.bb_instructions /\
  ((FOLDR (dft_exec_cons g C8) OK
      (DROP (phi_prefix_length (cps ++ cys)) cps)
      (csp with vs_inst_idx := phi_prefix_length (cps ++ cys)) = OK be /\
    be.vs_inst_idx = LENGTH cps /\ q < LENGTH cxs /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q cxs) /\
    z = DROP m cps ++ TAKE q cxs /\ k = LENGTH cps-m+q /\
    cm = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [NONE] else []) (LENGTH cxs) /\
    ce = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [(csf.fn_name,(EL r cxs).inst_id)] else []) (LENGTH cxs) /\
    ck = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [(b,SUC d,(EL r cxs).inst_id)] else []) (LENGTH cxs) /\
    Mc = FLAT (TAKE q cm) /\ Ec = FLAT (TAKE q ce) /\ Kc = FLAT (TAKE q ck) /\
    lookup_block cb.bb_label csf.fn_blocks = SOME cb /\
    lookup_block cb.bb_label ctf.fn_blocks = SOME cbt /\
    cbt.bb_instructions = cps ++ cys /\
    EVERY inst_shape_ok cb.bb_instructions /\
    dft_remaining_inv csf cb cxs be /\ cys <> [] /\ ci = HD cys /\ s1 = be) \/
   (q = 0 /\ m <= l /\ l < LENGTH cps /\
    FOLDR (dft_exec_cons g C8) OK
      (DROP (phi_prefix_length (cps ++ cys)) (TAKE l cps))
      (csp with vs_inst_idx := phi_prefix_length (cps ++ cys)) = OK s1 /\
    z = DROP m (TAKE l cps) /\ k = l-m /\ Mc = [] /\ Ec = [] /\ Kc = [])) /\
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
  (!F gs0 t. N <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs0 ==>
    levels_ok F C7 (pre ++ [(sf,plan,NONE)])
      (MAP (\(ai,ds,ei,qi,zi). ai) cuts) incoming root_sf
      (root_entry with vs_gas_readings := gs0 ++ t) [] 0 /\
    (?extra. E0 = FST (rooted_eval F C7 (pre ++ [(sf,plan,NONE)])
      (root_entry with vs_gas_readings := gs0 ++ t)) ++ extra) /\
    (case SND (rooted_eval F C7 (pre ++ [(sf,plan,NONE)])
       (root_entry with vs_gas_readings := gs0 ++ t)) of
      OK u0 =>
        FST (rooted_eval F C7 (pre ++ [(sf,plan,NONE)])
          (root_entry with vs_gas_readings := gs0 ++ t)) = E0 /\
        u0.vs_gas_readings = t /\
        (!t'. rooted_eval F C7 (pre ++ [(sf,plan,NONE)])
          (root_entry with vs_gas_readings := gs0 ++ t') =
          (E0,OK (u0 with vs_gas_readings := t'))) /\
        (?before after. trace_blocks [] 0 F C7 root_sf
          (root_entry with vs_gas_readings := gs0 ++ t) =
          before ++ [((p,d,c.inst_id),sf,c,u0)] ++ after /\
          trace_gas before = ZIP (K0,gs0)) /\
        (!op. MEM op c.inst_operands ==> eval_operand op u0 = eval_operand op b0) /\
        (!callee argv. setup_callee callee argv
          (u0 with vs_gas_readings := b0.vs_gas_readings) = setup_callee callee argv b0) /\
        (!bb. lookup_block u0.vs_current_bb sf.fn_blocks = SOME bb ==>
          ?K : exec_result -> (string # num) list # exec_result.
            run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs0 ++ t) =
              SND (K (exec_block (F-d) C7 bb u0)) /\
            gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs0 ++ t) =
              E0 ++ gas_events_block (F-d) C7 sf.fn_name bb u0 ++
                FST (K (exec_block (F-d) C7 bb u0)) /\
            (!v. K (Halt v) = ([],Halt v)) /\
            (!a v. K (Abort a v) = ([],Abort a v)) /\
            (!msg. K (Error msg) = ([],Error msg)))
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs0 ++ t) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs0 ++ t) =
          FST (rooted_eval F C7 (pre ++ [(sf,plan,NONE)])
            (root_entry with vs_gas_readings := gs0 ++ t)))) /\
  cuts' = cuts ++ [(b,[],SUC d,q,z)] /\
  levels' = pre ++ [(sf,plan,SOME c);(csf,[(cb,SUC d,z)],NONE)] /\
  M' = M0 ++ Mc /\ E' = E0 ++ Ec /\ K' = K0 ++ Kc /\ N' = MAX N (SUC d) ==>
  MAP (\(ai,ds,ei,qi,zi). ai) cuts' =
    REVERSE (GENLIST (\i. DROP i b) (SUC (LENGTH b))) /\
  LENGTH cuts' = LENGTH levels' /\
  LENGTH M' = LENGTH E' /\ LENGTH M' = LENGTH K' /\
  (!F gs tail. N' <= F /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M' gs ==>
    levels_ok F C7 levels' (MAP (\(ai,ds,ei,qi,zi). ai) cuts')
      (incoming ++ [d]) root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E' = FST (rooted_eval F C7 levels'
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels' (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels' (root_entry with vs_gas_readings := gs ++ tail)) = E' /\
        u.vs_gas_readings = tail /\
        (?before after. trace_blocks [] 0 F C7 root_sf
          (root_entry with vs_gas_readings := gs ++ tail) =
          before ++ [((b,SUC d,(EL k (DROP m cb.bb_instructions)).inst_id),csf,
            EL k (DROP m cb.bb_instructions),u)] ++ after /\
          trace_gas before = ZIP (K',gs)) /\
        (!tail'. rooted_eval F C7 levels' (root_entry with vs_gas_readings := gs ++ tail') =
          (E',OK (u with vs_gas_readings := tail'))) /\
        (q = 0 /\ m <= l /\ l < LENGTH cps /\ z = DROP m (TAKE l cps) ==>
          u = s1 with vs_gas_readings := tail) /\
        (z = DROP m cps ++ TAKE q cxs /\
         inv_memory_observation ci.inst_opcode /\ EL q cxs = ci ==>
          ((!op. MEM op ci.inst_operands ==> eval_operand op u = eval_operand op s1) /\
           u.vs_initial_fmp = s1.vs_initial_fmp))
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels' (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `z = TAKE k (DROP m cb.bb_instructions) /\
   k < LENGTH (DROP m cb.bb_instructions) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) z` by
    (irule fresh_cut_shape >> metis_tac[]) >>
  `GENLIST (\i. DROP i b) (SUC (LENGTH b)) =
    b :: GENLIST (\i. DROP i p) (SUC (LENGTH p))` by
    simp[Once listTheory.GENLIST_CONS,combinTheory.o_DEF] >>
  conj_tac >- simp[] >>
  conj_tac >- (qpat_x_assum `LENGTH cuts = _` mp_tac >> simp[]) >>
  `LENGTH Mc = LENGTH Ec /\ LENGTH Mc = LENGTH Kc` by
    (qpat_assum `_ \/ _` strip_assume_tac >>
     simp[LENGTH_FLAT,MAP_TAKE,MAP_GENLIST,combinTheory.o_DEF,
          COND_RAND]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  `EVERY (\i. i.inst_opcode <> PHI) cxs /\
   EVERY (\i. i.inst_opcode <> PHI) cys` by
    (conj_tac >> irule EVERY_MONOTONIC >>
     qexists_tac `\i. ~is_pseudo i.inst_opcode` >>
     (conj_tac >- (gen_tac >> Cases_on `x.inst_opcode` >> simp[is_pseudo_def]) >>
      first_assum ACCEPT_TAC)) >>
  `phi_prefix_length (cps ++ cys) = m` by
    metis_tac[dft_phi_prefix_append] >>
  `!F ent. rooted_eval F C7 [(csf,[(cb,SUC d,z)],NONE)] ent =
     plan_eval F C7 csf.fn_name [(cb,SUC d,z)] ent` by
    (map_every qx_gen_tac [`fuel`,`ent`] >>
     qpat_x_assum `rooted_eval = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms] >>
     namedCases_on `plan_eval fuel C7 csf.fn_name [(cb,SUC d,z)] ent` ["events result"] >>
     Cases_on `result` >> simp[NoAsms]) >>
  `!fuel gsc tail. SUC d <= fuel /\
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc gsc ==>
      plan_ok fuel C7 csf d [(cb,SUC d,z)]
        (child_entry with vs_gas_readings := gsc ++ tail) /\
      (?extra. Ec = FST (rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)]
        (child_entry with vs_gas_readings := gsc ++ tail)) ++ extra) /\
      (!ec u. rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)]
          (child_entry with vs_gas_readings := gsc ++ tail) = (ec,OK u) ==>
        ec = Ec /\ u.vs_gas_readings = tail /\
        !tail'. rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)]
          (child_entry with vs_gas_readings := gsc ++ tail') =
          (ec,OK (u with vs_gas_readings := tail')))` by
    (`SUC d = SUC d` by simp[] >>
     drule_all dft_packet_call_singleton_cut >>
     disch_then (qspecl_then [`g`,`b`,`C8`,`C7`]
       (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
     qpat_assum `_ \/ _` strip_assume_tac
     >- suspend "singleton_body"
     >> suspend "singleton_pseudo") >>
  suspend "compose"
QED

Resume dft_packet_call_fresh_root_cut[singleton_body]:
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  qpat_x_assum `!be q z ms ess ks. FOLDR _ _ _ _ = OK be /\ _ ==> _`
    (qspecl_then [`be`,`q`,`z`,`cm`,`ce`,`ck`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >>
  qpat_x_assum `row_eval = _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `rooted_eval = _` kall_tac >>
  qpat_x_assum `plan_ok = _` kall_tac >>
  qpat_x_assum `levels_ok = _` kall_tac >>
  qpat_x_assum `call_setup = _` kall_tac >>
  simp[] >> metis_tac[]
QED

Resume dft_packet_call_fresh_root_cut[singleton_pseudo]:
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  qpat_x_assum `!k z t. _ /\ _ ==> _`
    (qspecl_then [`l`,`z`,`s1`] mp_tac) >>
  impl_tac >- metis_tac[] >> disch_tac >>
  qpat_x_assum `row_eval = _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `rooted_eval = _` kall_tac >>
  qpat_x_assum `plan_ok = _` kall_tac >>
  qpat_x_assum `levels_ok = _` kall_tac >>
  qpat_x_assum `call_setup = _` kall_tac >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  disch_then (qspec_then `tail` strip_assume_tac) >> gvs[]
QED

Resume dft_packet_call_fresh_root_cut[compose]:
  map_every qx_gen_tac [`fuel`,`gs`,`tail`] >> strip_tac >>
  `N <= fuel /\ SUC d <= fuel` by metis_tac[MAX_LE] >>
  `?gs0 gsc. gs = gs0 ++ gsc /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs0 /\
     LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mc gsc` by
    (qpat_x_assum `LIST_REL _ M' gs` mp_tac >>
     qpat_x_assum `M' = _` (fn th => rewrite_tac[th,LIST_REL_SPLIT1])) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `gs = _` SUBST_ALL_TAC >>
  qpat_assum `!F gs0 t. N <= F /\ LIST_REL _ M0 gs0 ==> _`
    (qspecl_then [`fuel`,`gs0`,`gsc ++ tail`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "old_case"))) >>
  qpat_assum `!fuel gsc tail. _` (qspecl_then [`fuel`,`gsc`,`tail`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `!events u. rooted_eval fuel C7 (pre ++ [(sf,plan,NONE)])
      (root_entry with vs_gas_readings := gs0 ++ (gsc ++ tail)) = (events,OK u) ==>
      u.vs_gas_readings = gsc ++ tail /\
      (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
      (!callee argv. setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
         setup_callee callee argv b0)` by
    (rpt strip_tac >> asm "old_case" mp_tac >>
     qpat_x_assum `rooted_eval fuel _ _ _ = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms] >> disch_then (map_every assume_tac o CONJUNCTS) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  drule_all dft_packet_fresh_root_geometry >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 kall_tac assume_tac)) >>
  conj_tac >-
    (pure_rewrite_tac[APPEND_ASSOC] >>
     first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_ASSOC])) >>
  `!t.
    (?extra. E0 ++ Ec = FST (rooted_eval fuel C7
      (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(cb,SUC d,z)],NONE)])
      (root_entry with vs_gas_readings := gs0 ++ gsc ++ t)) ++ extra) /\
    (!events v. rooted_eval fuel C7
      (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(cb,SUC d,z)],NONE)])
      (root_entry with vs_gas_readings := gs0 ++ gsc ++ t) = (events,OK v) ==>
      events = E0 ++ Ec /\ v.vs_gas_readings = t /\
      (!t'. rooted_eval fuel C7
        (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(cb,SUC d,z)],NONE)])
        (root_entry with vs_gas_readings := gs0 ++ gsc ++ t') =
        (E0 ++ Ec,OK (v with vs_gas_readings := t')))) /\
    (!events r. rooted_eval fuel C7 (pre ++ [(sf,plan,NONE)])
      (root_entry with vs_gas_readings := gs0 ++ gsc ++ t) = (events,r) /\
      (~?u. r = OK u) ==>
      rooted_eval fuel C7
        (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(cb,SUC d,z)],NONE)])
        (root_entry with vs_gas_readings := gs0 ++ gsc ++ t) = (events,r)) /\
    (!u. rooted_eval fuel C7 (pre ++ [(sf,plan,NONE)])
      (root_entry with vs_gas_readings := gs0 ++ gsc ++ t) = (E0,OK u) ==>
      rooted_eval fuel C7
        (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(cb,SUC d,z)],NONE)])
        (root_entry with vs_gas_readings := gs0 ++ gsc ++ t) =
        (E0 ++ FST (rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)]
          (child_entry with vs_gas_readings := gsc ++ t)),
         SND (rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)]
          (child_entry with vs_gas_readings := gsc ++ t))))` by
    suspend "semantic_package" >>
  suspend "semantic_finish"
QED

Resume dft_packet_call_fresh_root_cut[semantic_package]:
  irule dft_packet_fresh_level_semantics >>
  conj_tac >-
    (qx_gen_tac `t` >>
     qpat_assum `!F gs0 t. N <= F /\ LIST_REL _ M0 gs0 ==> _`
       (qspecl_then [`fuel`,`gs0`,`t`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "case_t"))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >> asm "case_t" mp_tac >>
     qpat_x_assum `rooted_eval fuel _ _ _ = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qx_gen_tac `t` >>
     qpat_assum `!fuel gsc tail. _` (qspecl_then [`fuel`,`gsc`,`t`] mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!ec u. rooted_eval fuel _ [(csf,_)] _ = _ ==> _` drule >>
     strip_tac >> qpat_x_assum `events = Ec` SUBST_ALL_TAC >>
     conj_tac >- simp[NoAsms] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >-
    (qexistsl_tac [`plan_eval fuel C7`,`call_setup C7`] >>
     reverse conj_tac >-
       (qpat_x_assum `rooted_eval = _` (fn th => rewrite_tac[th]) >>
        simp[NoAsms]) >>
     suspend "setup_all_tails") >>
  conj_tac >- (qexists_tac `M0` >> first_assum ACCEPT_TAC) >>
  qexists_tac `Mc` >> first_assum ACCEPT_TAC
QED

Resume dft_packet_call_fresh_root_cut[setup_all_tails]:
  map_every qx_gen_tac [`t`,`u`] >> disch_tac >>
  qpat_assum `!F gs0 t. N <= F /\ LIST_REL _ M0 gs0 ==> _`
    (qspecl_then [`fuel`,`gs0`,`gsc ++ t`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 kall_tac mp_tac)) >>
  qpat_assum `rooted_eval fuel _ _ _ = (E0,OK u)`
    (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,
      PURE_REWRITE_RULE [GSYM APPEND_ASSOC] th]) >>
  simp[NoAsms] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dft_packet_call_source_setup >> strip_tac >>
  qpat_x_assum `call_setup C7 c u = _` mp_tac >> simp[]
QED

Resume dft_packet_call_fresh_root_cut[semantic_finish]:
  qpat_x_assum `!t. (?extra. E0 ++ Ec = _) /\ _`
    (qspec_then `tail` (map_every assume_tac o CONJUNCTS)) >>
  conj_tac >-
    (qpat_assum `levels' = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `E' = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
     first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND])) >>
  namedCases_on `rooted_eval fuel C7 (pre ++ [(sf,plan,NONE)])
    (root_entry with vs_gas_readings := gs0 ++ gsc ++ tail)` ["ev0 r0"] >>
  Cases_on `?u0. r0 = OK u0`
  >- (pop_assum (qx_choose_then `u0` SUBST_ALL_TAC) >>
      asm "old_case" mp_tac >>
      qpat_assum `rooted_eval fuel _ _ _ = (ev0,OK u0)`
        (fn th => pure_rewrite_tac[APPEND_ASSOC,
          PURE_REWRITE_RULE [APPEND_ASSOC] th]) >>
      simp[NoAsms] >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_x_assum `ev0 = E0` SUBST_ALL_TAC >>
      qpat_x_assum `!u. (E0,OK u0) = (E0,OK u) ==> _`
        (qspec_then `u0` mp_tac) >>
      simp[NoAsms] >> disch_tac >>
      `eval_operands ops u0 = SOME args /\
       setup_callee csf args u0 = SOME (child_entry with vs_gas_readings := gsc ++ tail)` by
        (drule_all dft_packet_callee_alignment >> strip_tac >>
         `csf' = csf` by metis_tac[optionTheory.SOME_11] >>
         pop_assum SUBST_ALL_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_x_assum `setup_callee csf args u0 = _` mp_tac >>
         qpat_assum `u0.vs_gas_readings = _` (fn th => rewrite_tac[th])) >>
      namedCases_on `rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)]
        (child_entry with vs_gas_readings := gsc ++ tail)` ["child_events child_result"] >>
      Cases_on `child_result`
      >- suspend "child_success"
      >> suspend "child_stopped") >>
  qpat_x_assum `!events r. _ /\ _ ==> _`
    (qspecl_then [`ev0`,`r0`] mp_tac) >>
  (impl_tac >- (conj_tac >>> NTH_GOAL (simp[]) 1 >> first_assum ACCEPT_TAC)) >>
  disch_tac >> suspend "caller_stopped"
QED

Resume dft_packet_call_fresh_root_cut[caller_stopped]:
  asm "old_case" mp_tac >>
  qpat_assum `rooted_eval fuel C7 (pre ++ [(sf,plan,NONE)]) _ = (ev0,r0)`
    (fn th => pure_rewrite_tac[APPEND_ASSOC,
      PURE_REWRITE_RULE [APPEND_ASSOC] th]) >>
  qpat_assum `levels' = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `rooted_eval fuel C7 (pre ++ [(sf,plan,SOME c)] ++ _) _ = (ev0,r0)`
    (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,
      PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND] th]) >>
  qpat_x_assum `~?u. r0 = OK u` mp_tac >>
  Cases_on `r0` >> simp[NoAsms]
QED

Resume dft_packet_call_fresh_root_cut[child_success]:
  rename1 `rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)] _ = (child_events,OK child_state)` >>
  qpat_assum `levels' = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `rooted_eval fuel C7 (pre ++ [(sf,plan,SOME c)] ++ _) _ = _`
    (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,
      PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND,pairTheory.FST,pairTheory.SND] th]) >>
  simp_tac bool_ss [] >>
  `rooted_eval fuel C7 (pre ++ [(sf,plan,SOME c)] ++ [(csf,[(cb,SUC d,z)],NONE)])
    (root_entry with vs_gas_readings := gs0 ++ gsc ++ tail) =
      (E0 ++ child_events,OK child_state)` by
    (qpat_assum `rooted_eval fuel C7 (pre ++ [(sf,plan,SOME c)] ++ _) _ = _`
      (fn th => rewrite_tac[th]) >> simp[NoAsms]) >>
  qpat_x_assum `!events v. rooted_eval fuel _ (pre ++ [(sf,plan,SOME c)] ++ _) _ = _ ==> _` drule >>
  strip_tac >>
  `child_events = Ec` by
    (qpat_x_assum `E0 ++ child_events = E0 ++ Ec` mp_tac >> simp[NoAsms]) >>
  qpat_assum `E' = _` (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "success_native" >>
  conj_tac >-
    (qpat_assum `!t'. rooted_eval fuel _ (pre ++ [(sf,plan,SOME c)] ++ _) _ = _`
       (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
         ACCEPT_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND] th))) >>
  suspend "success_observation"
QED

Resume dft_packet_call_fresh_root_cut[success_observation]:
  `plan_eval fuel C7 csf.fn_name [(cb,SUC d,z)]
    (child_entry with vs_gas_readings := gsc ++ tail) = (child_events,OK child_state)` by
    (qpat_assum `!F ent. rooted_eval _ _ [(csf,_)] _ = _`
       (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `_ \/ _` strip_assume_tac
  >- (conj_tac >- suspend "body_not_pseudo" >>
      strip_tac >>
      `child_entry.vs_current_bb = cb.bb_label` by
        metis_tac[lookup_block_label] >>
      `lookup_block child_entry.vs_current_bb ctf.fn_blocks = SOME cbt` by metis_tac[] >>
      qpat_x_assum `s1 = be` SUBST_ALL_TAC >>
      `z = DROP (phi_prefix_length cb.bb_instructions) cps ++ TAKE q cxs` by
        metis_tac[] >>
      drule_all dft_packet_fresh_singleton_observation >>
      simp[NoAsms]) >>
  conj_tac >- suspend "pseudo_exact" >> suspend "pseudo_not_body"
QED

Resume dft_packet_call_fresh_root_cut[body_not_pseudo]:
  strip_tac >>
  `LENGTH z = LENGTH cps - m + LENGTH (TAKE q cxs)` by
    (qpat_assum `z = DROP m cps ++ TAKE q cxs` (fn th =>
      pure_rewrite_tac[th,LENGTH_APPEND,LENGTH_DROP] >> simp[NoAsms])) >>
  `LENGTH z = LENGTH (TAKE l cps) - m` by
    (qpat_assum `z = DROP m (TAKE l cps)` (fn th =>
      pure_rewrite_tac[th,LENGTH_DROP] >> simp[NoAsms])) >>
  `LENGTH (TAKE l cps) = l` by simp[LENGTH_TAKE] >>
  `m <= LENGTH cps` by metis_tac[dft_phi_prefix_append,phi_prefix_length_le] >>
  qpat_x_assum `q = 0` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th,TAKE_0,LENGTH])) >>
  `F` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
      [`LENGTH z = LENGTH cps - m + _`,`LENGTH z = LENGTH (TAKE l cps) - m`,
       `LENGTH (TAKE l cps) = l`,`m <= LENGTH cps`,`m <= l`,`l < LENGTH cps`] >>
     decide_tac)
QED

Resume dft_packet_call_fresh_root_cut[pseudo_not_body]:
  strip_tac >>
  `LENGTH z = LENGTH cps - m + LENGTH (TAKE q cxs)` by
    (qpat_assum `z = DROP m cps ++ TAKE q cxs` (fn th =>
      pure_rewrite_tac[th,LENGTH_APPEND,LENGTH_DROP] >> simp[NoAsms])) >>
  `LENGTH z = LENGTH (TAKE l cps) - m` by
    (qpat_assum `z = DROP m (TAKE l cps)` (fn th =>
      pure_rewrite_tac[th,LENGTH_DROP] >> simp[NoAsms])) >>
  `LENGTH (TAKE l cps) = l` by simp[LENGTH_TAKE] >>
  `m <= LENGTH cps` by decide_tac >>
  qpat_x_assum `q = 0` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th,TAKE_0,LENGTH])) >>
  `F` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
      [`LENGTH z = LENGTH cps - m + _`,`LENGTH z = LENGTH (TAKE l cps) - m`,
       `LENGTH (TAKE l cps) = l`,`m <= LENGTH cps`,`m <= l`,`l < LENGTH cps`] >>
     decide_tac)
QED

Resume dft_packet_call_fresh_root_cut[pseudo_exact]:
  strip_tac >>
  `SUC d = SUC d` by simp[] >>
  drule_all dft_packet_call_singleton_cut >>
  disch_then (qspecl_then [`g`,`b`,`C8`,`C7`]
    (CONJUNCTS_THEN2 kall_tac assume_tac)) >>
  qpat_x_assum `!k z t. _ /\ _ ==> _`
    (qspecl_then [`l`,`z`,`s1`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspecl_then [`fuel`,`tail`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 kall_tac assume_tac) >>
  `gsc = []` by
    ((qpat_x_assum `LIST_REL _ Mc gsc` mp_tac >>
     qpat_assum `Mc = []` (fn th => rewrite_tac[th,LIST_REL_def]) >> (simp[LIST_REL_def]))) >>
  qpat_x_assum `plan_eval fuel C7 csf.fn_name _ _ = (child_events,OK child_state)` mp_tac >>
  qpat_assum `gsc = []` (fn th => pure_rewrite_tac[th,APPEND]) >>
  qpat_assum `plan_eval fuel C7 csf.fn_name _ _ = ([],OK _)`
    (fn th => pure_rewrite_tac[th,pairTheory.PAIR_EQ,exec_result_11]) >>
  simp[NoAsms]
QED

Resume dft_packet_call_fresh_root_cut[success_native]:
  `plan_eval fuel C7 csf.fn_name [(cb,SUC d,z)]
    (child_entry with vs_gas_readings := gsc ++ tail) = (child_events,OK child_state)` by
    (qpat_assum `!F ent. rooted_eval _ _ [(csf,_)] _ = _`
       (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `(?be q ms ks.
      FOLDR (dft_exec_cons g C8) OK
        (DROP (phi_prefix_length (cps ++ cys)) cps)
        (csp with vs_inst_idx := phi_prefix_length (cps ++ cys)) = OK be /\
      be.vs_inst_idx = LENGTH cps /\ q < LENGTH cxs /\
      EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (TAKE q cxs) /\
      z = DROP m cps ++ TAKE q cxs /\ k = LENGTH cps-m+q /\
      ms = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [NONE] else []) (LENGTH cxs) /\
      ks = GENLIST (\r. if (EL r cxs).inst_opcode = GAS then [(b,SUC d,(EL r cxs).inst_id)] else []) (LENGTH cxs) /\
      Mc = FLAT (TAKE q ms) /\ Kc = FLAT (TAKE q ks)) \/
    (?l t. m <= l /\ l < LENGTH cps /\ k = l-m /\
      z = DROP m (TAKE l cps) /\ Mc = [] /\ Kc = [] /\
      FOLDR (dft_exec_cons g C8) OK
        (DROP (phi_prefix_length (cps ++ cys)) (TAKE l cps))
        (csp with vs_inst_idx := phi_prefix_length (cps ++ cys)) = OK t)` assume_tac >-
    (qpat_assum `_ \/ _` strip_assume_tac
     >- (disj1_tac >> qexistsl_tac [`be`,`q`,`cm`,`ck`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disj2_tac >> qexistsl_tac [`l`,`s1`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `SUC d = SUC d` by simp[] >>
  drule_all dft_packet_fresh_singleton_native >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `child_before` (qx_choose_then `child_after` strip_assume_tac))) >>
  qpat_x_assum `?before after. trace_blocks [] 0 fuel _ _ _ = _ /\ _`
    (qx_choose_then `before0` (qx_choose_then `after0` strip_assume_tac)) >>
  qmatch_goalsub_abbrev_tac `rt = _` >>
  `LENGTH before0 < LENGTH rt /\
   EL (LENGTH before0) rt = ((p,d,c.inst_id),sf,c,u0) /\
   TAKE (LENGTH before0) rt = before0` by
    (simp[Abbr `rt`,EL_APPEND_EQN,TAKE_APPEND,LENGTH_APPEND]) >>
  qpat_assum `Abbrev (rt = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all dft_packet_native_child_insert >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `after1` assume_tac)
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexistsl_tac [`TAKE (LENGTH before0) rt ++ [((p,d,c.inst_id),sf,c,u0)] ++ child_before`,`after1`] >>
  conj_tac >- (pure_rewrite_tac[GSYM APPEND_ASSOC] >>
    first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM APPEND_ASSOC])) >>
  qpat_assum `K' = _` (fn th => pure_rewrite_tac[th]) >>
  first_x_assum (qspecl_then [`K0`,`gs0`,`Kc`,`gsc`] mp_tac) >>
  (impl_tac >-
    (simp[NoAsms] >> conj_tac >- (simp[] >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `LIST_REL _ M0 gs0` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
     qpat_assum `LIST_REL _ Mc gsc` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[])) >>
  simp[NoAsms]
QED

Resume dft_packet_call_fresh_root_cut[child_stopped]:
  markerLib.RESUME_TAC >>
  qmatch_asmsub_abbrev_tac `rooted_eval fuel C7 [(csf,[(cb,SUC d,z)],NONE)] _ = (child_events,r)` >>
  `plan_eval fuel C7 csf.fn_name [(cb,SUC d,z)]
    (child_entry with vs_gas_readings := gsc ++ tail) = (child_events,r)` by
    (qpat_assum `!F ent. rooted_eval _ _ [(csf,_)] _ = _`
       (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `~(?v. r = OK v)` by simp[Abbr `r`] >>
  qpat_x_assum `?before after. trace_blocks [] 0 fuel _ _ _ = _ /\ _`
    (qx_choose_then `before0` (qx_choose_then `after0` strip_assume_tac)) >>
  `LENGTH before0 < LENGTH (trace_blocks [] 0 fuel C7 root_sf
      (root_entry with vs_gas_readings := gs0 ++ gsc ++ tail)) /\
   EL (LENGTH before0) (trace_blocks [] 0 fuel C7 root_sf
      (root_entry with vs_gas_readings := gs0 ++ gsc ++ tail)) = ((p,d,c.inst_id),sf,c,u0)` by
    (qpat_assum `trace_blocks [] 0 fuel _ _ _ = _`
       (fn th => pure_rewrite_tac[APPEND_ASSOC,
         PURE_REWRITE_RULE [APPEND_ASSOC] th]) >>
     simp[NoAsms,EL_APPEND_EQN,LENGTH_APPEND]) >>
  drule_all dftPacketNativeContinuationTheory.native_trace_blocks_continuation >>
  disch_then (qx_choose_then `bt` (qx_choose_then `rest` strip_assume_tac)) >>
  qpat_x_assum `!bb. lookup_block u0.vs_current_bb sf.fn_blocks = SOME bb ==> _` drule >>
  strip_tac >>
  `d < fuel` by decide_tac >>
  drule_all dft_packet_fresh_singleton_root_stop >>
  strip_tac >>
  qpat_assum `levels' = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `rooted_eval fuel C7 (pre ++ [(sf,plan,SOME c)] ++ _) _ = _`
    (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,
      PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND,pairTheory.FST,pairTheory.SND] th]) >>
  qpat_assum `run_blocks fuel C7 root_sf _ = r`
    (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,
      PURE_REWRITE_RULE [GSYM APPEND_ASSOC] th]) >>
  qpat_assum `gas_events_blocks fuel C7 root_sf _ = E0 ++ child_events`
    (fn th => pure_rewrite_tac[GSYM APPEND_ASSOC,
      PURE_REWRITE_RULE [GSYM APPEND_ASSOC] th]) >>
  simp[NoAsms,Abbr `r`]
QED

Finalise dft_packet_call_fresh_root_cut
