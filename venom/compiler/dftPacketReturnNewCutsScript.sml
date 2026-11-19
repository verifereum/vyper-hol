Theory dftPacketReturnNewCuts
Ancestors
  dftPacketReturnAnchorState dftPacketReturnCutGeometry
  finite_map
  dftPacketRootedOperational dftPacketInvokePrefixStop dftPacketSameLevelCompose
  dftPacketLiteralRowExtend dftPacketFillingBoundary dftPacketOperationalPrefix
  dftPacketLastRowValidity
  gasEvents venomInst venomState dftIndexedExec list rich_list arithmetic

Theorem return_segment_shape[local]:
  bb.bb_instructions = ps ++ xs /\ u.vs_inst_idx = LENGTH ps /\ q < LENGTH xs ==>
  u.vs_inst_idx + q <= LENGTH bb.bb_instructions /\
  TAKE q (DROP u.vs_inst_idx bb.bb_instructions) = TAKE q xs /\
  (!v. v.vs_inst_idx = u.vs_inst_idx + q ==> get_instruction bb v.vs_inst_idx = SOME (EL q xs)) /\
  (!f C owner.
    gas_events_block f C owner
      (bb with bb_instructions := TAKE (u.vs_inst_idx+q) bb.bb_instructions) u =
    gas_events_block f C owner
      <|bb_label := u.vs_current_bb; bb_instructions :=
          REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|> u)
Proof
  strip_tac >> simp[DROP_LENGTH_APPEND,get_instruction_def,EL_APPEND_EQN] >>
  rpt gen_tac >> irule gas_events_block_suffix_cong >>
  qexists_tac `TAKE q xs` >> simp[DROP_TAKE,DROP_LENGTH_APPEND,DROP_APPEND]
QED

Theorem return_cut_replay[local]:
  !f C root_fn root_entry sf bb a e ps xs q be gs0 gs1 E0 E1 K0 K1
    (A : bytes32 list -> (string # num) list # exec_result) D.
  bb.bb_instructions = ps ++ xs /\ be.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  LENGTH K0 = LENGTH gs0 /\ LENGTH K1 = LENGTH gs1 /\
  (!t. (?extra. E0 = FST (A t) ++ extra) /\
    (case SND (A t) of
      OK u => FST (A t) = E0 /\ u = (be with vs_gas_readings := t) /\
        lookup_block u.vs_current_bb sf.fn_blocks = SOME bb /\
        (?K. run_blocks f C root_fn (root_entry with vs_gas_readings := gs0 ++ t) =
               SND (K (exec_block (f-e) C bb u)) /\
             gas_events_blocks f C root_fn (root_entry with vs_gas_readings := gs0 ++ t) =
               E0 ++ gas_events_block (f-e) C sf.fn_name bb u ++ FST (K (exec_block (f-e) C bb u)) /\
             (!v. K (Halt v) = ([],Halt v)) /\
             (!a v. K (Abort a v) = ([],Abort a v)) /\
             (!msg. K (Error msg) = ([],Error msg))) /\
        (?i before after.
           trace_blocks [] 0 f C root_fn (root_entry with vs_gas_readings := gs0 ++ t) =
               before ++ [((a,e,i.inst_id),sf,i,u)] ++ after /\
           trace_gas before = ZIP (K0,gs0)) /\
        (!t'. A t' = (E0,OK (u with vs_gas_readings := t')))
    | stopped =>
        run_blocks f C root_fn (root_entry with vs_gas_readings := gs0 ++ t) = stopped /\
        gas_events_blocks f C root_fn (root_entry with vs_gas_readings := gs0 ++ t) = FST (A t))) /\
  (!t.
    (?extra. E1 = gas_events_block (f-e) C sf.fn_name (<|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|>) (be with vs_gas_readings := gs1 ++ t) ++ extra) /\
    (!v. (FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs) (be with vs_gas_readings := gs1 ++ t)) = OK v ==>
      gas_events_block (f-e) C sf.fn_name (<|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|>) (be with vs_gas_readings := gs1 ++ t) = E1 /\ v.vs_gas_readings = t /\
      trace_gas (trace_block a e (f-e) C sf
        (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions) (be with vs_gas_readings := gs1 ++ t)) = ZIP (K1,gs1) /\
      (!t'. FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs)
              (be with vs_gas_readings := gs1 ++ t') = OK (v with vs_gas_readings := t') /\
            gas_events_block (f-e) C sf.fn_name (<|bb_label := be.vs_current_bb; bb_instructions :=
        REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|>)
              (be with vs_gas_readings := gs1 ++ t') = E1))) /\
  (!t. D t = case SND (A (gs1 ++ t)) of
      OK u => (FST (A (gs1 ++ t)) ++ gas_events_block (f-e) C sf.fn_name
             (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions) u,
             FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs) u)
    | other => (FST (A (gs1 ++ t)),other)) ==>
  !tail.
    (?extra. E0 ++ E1 = FST (D tail) ++ extra) /\
    (case SND (D tail) of
      OK v => FST (D tail) = E0 ++ E1 /\ v.vs_gas_readings = tail /\
        (?before after.
           trace_blocks [] 0 f C root_fn (root_entry with vs_gas_readings := (gs0 ++ gs1) ++ tail) =
             before ++ [((a,e,(EL q xs).inst_id),sf,EL q xs,v)] ++ after /\
           trace_gas before = ZIP (K0 ++ K1,gs0 ++ gs1)) /\
        (!t'. D t' = (E0 ++ E1,OK (v with vs_gas_readings := t')))
    | stopped =>
        run_blocks f C root_fn (root_entry with vs_gas_readings := (gs0 ++ gs1) ++ tail) = stopped /\
        gas_events_blocks f C root_fn (root_entry with vs_gas_readings := (gs0 ++ gs1) ++ tail) = FST (D tail))
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `tail` >>
  Cases_on `A (gs1 ++ tail)` >>
  rename1 `A (gs1 ++ tail) = (ev,result)` >>
  Cases_on `?u. result = OK u`
  >- (pop_assum (qx_choose_then `u` SUBST_ALL_TAC) >>
      qpat_assum `!t. (?extra. E0 = FST (A t) ++ extra) /\ _`
        (qspec_then `gs1 ++ tail` mp_tac) >>
      qpat_assum `A (gs1 ++ tail) = _` (fn th => simp_tac (srw_ss()) [th]) >>
      disch_then (strip_assume_tac o CONJUNCT2) >>
      `u.vs_inst_idx = LENGTH ps` by simp[] >>
      drule_all return_segment_shape >> strip_tac >>
      `!t. gas_events_block (f-e) C sf.fn_name
              (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
              (be with vs_gas_readings := gs1 ++ t) =
           gas_events_block (f-e) C sf.fn_name
              <|bb_label := be.vs_current_bb; bb_instructions :=
                  REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE q xs|>
              (be with vs_gas_readings := gs1 ++ t)` by
        (gen_tac >>
         qspecl_then [`bb`,`ps`,`xs`,`be with vs_gas_readings := gs1 ++ t`,`q`] mp_tac
           (Q.GENL [`bb`,`ps`,`xs`,`u`,`q`] return_segment_shape) >> simp[]) >>
      qpat_assum `!t. (?extra. E1 = _ ++ extra) /\ _`
        (qspec_then `tail` mp_tac) >>
      simp_tac (srw_ss()) [LET_THM] >> strip_tac >>
      `D tail = (E0 ++ gas_events_block (f-e) C sf.fn_name
           (bb with bb_instructions := TAKE (LENGTH ps+q) bb.bb_instructions) u,
           FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs) u)` by simp[] >>
      qpat_assum `D tail = _` (fn th => simp_tac (srw_ss()) [th,APPEND_ASSOC]) >>
      conj_tac
      >- (qpat_x_assum `E1 = _ ++ extra` SUBST1_TAC >> qexists_tac `extra` >>
          qpat_assum `u = be with vs_gas_readings := gs1 ++ tail` SUBST1_TAC >>
          qpat_assum `!t. gas_events_block _ _ _ _ _ = _` (qspec_then `tail` SUBST1_TAC) >>
          rewrite_tac[APPEND_ASSOC]) >>
      Cases_on `?v. FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs) u = OK v`
      >- (pop_assum (qx_choose_then `v` assume_tac) >>
          qpat_assum `!v. FOLDR _ _ _ _ = OK v ==> _` (qspec_then `v` mp_tac) >>
          `FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs)
             (be with vs_gas_readings := gs1 ++ tail) = OK v` by metis_tac[] >>
          pop_assum (fn th => rewrite_tac[th]) >> strip_tac >>
          qpat_assum `FOLDR _ _ _ u = OK v` (fn th => simp_tac (srw_ss()) [th]) >>
          conj_tac
          >- (qpat_assum `u = _` SUBST1_TAC >>
              qpat_assum `!t. gas_events_block _ _ _ _ _ = _` (qspec_then `tail` SUBST1_TAC) >>
              first_assum ACCEPT_TAC) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac
          >- (`v.vs_inst_idx = u.vs_inst_idx + q` by
                (drule dft_packet_block_prefix_operational >>
                 disch_then (qspecl_then [`f-e`,`C`,`sf.fn_name`] mp_tac) >>
                 simp[LET_THM, IgnAsm `E1 = _ ++ extra`]) >>
              `get_instruction bb v.vs_inst_idx = SOME (EL q xs)` by metis_tac[] >>
              irule dft_packet_native_row_cut >>
              conj_tac >- asm_rewrite_tac[] >> conj_tac >- asm_rewrite_tac[] >>
              qexistsl_tac [`C`,`f`,`after`,`bb`,`before`,`i`,`q`,
                `root_entry with vs_gas_readings := gs0 ++ gs1 ++ tail`,`root_fn`,`u`] >>
              metis_tac[]) >>
          qx_gen_tac `t'` >>
          qpat_assum `!t. D t = _` (qspec_then `t'` SUBST1_TAC) >>
          qpat_assum `!t'. A t' = _` (qspec_then `gs1 ++ t'` SUBST1_TAC) >>
          qpat_assum `u = _` SUBST1_TAC >>
          simp_tac (srw_ss()) [] >>
          qpat_assum `!t. gas_events_block _ _ _ _ _ = _` (qspec_then `t'` SUBST1_TAC) >>
          qpat_assum `!t'. FOLDR _ _ _ _ = _ /\ _` (qspec_then `t'` (fn th => rewrite_tac[CONJUNCT1 th,CONJUNCT2 th]))) >>
      qabbrev_tac `r = FOLDR (dft_exec_cons (f-e) C) OK (TAKE q xs) u` >>
      `FOLDR (dft_exec_cons (f-e) C) OK (TAKE q (DROP u.vs_inst_idx bb.bb_instructions)) u = r` by simp[Abbr `r`] >>
      `EVERY (\i. ~is_terminator i.inst_opcode)
         (TAKE q (DROP u.vs_inst_idx bb.bb_instructions))` by metis_tac[] >>
      drule_all dft_packet_invoke_prefix_stop >> strip_tac >>
      qpat_assum `u.vs_inst_idx = LENGTH ps` (fn th =>
        qpat_x_assum `gas_events_blocks _ _ _ _ = E0 ++ gas_events_block _ _ _ _ u`
          (assume_tac o REWRITE_RULE [th])) >>
      Cases_on `r` >>
      qpat_assum `~(?v. _ = OK v)` (fn th => simp_tac (srw_ss()) [th]) >>
      metis_tac[]) >>
  qpat_assum `!t. (?extra. E0 = FST (A t) ++ extra) /\ _`
    (qspec_then `gs1 ++ tail` mp_tac) >>
  qpat_assum `!t. D t = _` (qspec_then `tail` mp_tac) >>
  Cases_on `result` >>
  qpat_assum `A (gs1 ++ tail) = _` (fn th => simp_tac (srw_ss()) [th]) >>
  disch_tac >> strip_tac >> fs[APPEND_ASSOC] >>
  qexists_tac `extra ++ E1` >> simp[APPEND_ASSOC]
QED

Theorem return_literal_extend[local]:
  !(R : (ir_function # (basic_block # num # instruction list) list # instruction option) list ->
          venom_state -> (string # num) list # exec_result)
    P row S f C pre sf rows bb e z0 z1 seg l H.
  l = phi_prefix_length bb.bb_instructions /\ z1 = z0 ++ seg /\
  z1 = TAKE (LENGTH z1) (DROP l bb.bb_instructions) /\
  LENGTH z1 <= LENGTH (DROP l bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z1 /\
  row = (\owner (b,k,z) ent. case eval_phis ent b.bb_instructions of
    OK sp => (gas_events_block (f-k) C owner
        (b with bb_instructions := TAKE (phi_prefix_length b.bb_instructions) b.bb_instructions ++ z)
        (sp with vs_inst_idx := phi_prefix_length b.bb_instructions),
      FOLDR (dft_exec_cons (f-k) C) OK z
        (sp with vs_inst_idx := phi_prefix_length b.bb_instructions))
    | other => ([],other)) /\
  P = (\owner plan ent. FOLDL (\(ev,r) x. case r of
    OK u => (ev ++ FST (row owner x u),SND (row owner x u))
    | other => (ev,other)) ([],OK ent) plan) /\
  R = (\levels ent. FOLDL (\(prior,r) (fn,plan,call). case r of
    OK s => (prior ++ FST (P fn.fn_name plan s),
      case SND (P fn.fn_name plan s) of
        OK caller => (case call of NONE => OK caller | SOME c => S c caller)
        | other => other)
    | other => (prior,other)) ([],OK ent) levels) /\
  H = (\v. (gas_events_block (f-e) C sf.fn_name
        (bb with bb_instructions := TAKE l bb.bb_instructions ++ z1) v,
        FOLDR (dft_exec_cons (f-e) C) OK seg v)) ==>
  !entry. R (pre ++ [(sf,rows ++ [(bb,e,z1)],NONE)]) entry =
    (case SND (R (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)]) entry) of
       OK v => (FST (R (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)]) entry) ++
                  FST (H v), SND (H v))
     | other => (FST (R (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)]) entry),other))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  irule dft_packet_rooted_row_extend >>
  qexistsl_tac [`P`,`S'`,`row`] >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `l = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `row = _` SUBST1_TAC >> simp_tac (srw_ss()) [] >>
  qpat_assum `l = _` (fn th => rewrite_tac[GSYM th]) >>
  qabbrev_tac `L = \z ent. case eval_phis ent bb.bb_instructions of
    OK sp => (gas_events_block (f-e) C sf.fn_name
        (bb with bb_instructions := TAKE l bb.bb_instructions ++ z)
        (sp with vs_inst_idx := l),
      FOLDR (dft_exec_cons (f-e) C) OK z (sp with vs_inst_idx := l))
    | other => ([],other)` >>
  `!u. L z1 u = case SND (L z0 u) of
       OK v => (FST (L z0 u) ++ FST (H v), SND (H v))
     | other => (FST (L z0 u),other)` by
    (irule dft_packet_literal_row_extend >> metis_tac[]) >>
  pop_assum mp_tac >> simp[Abbr `L`, NoAsms]
QED

(* The witnesses are the terminal entries of the inherited cut, not a new
   selection of a path through the tables. *)
Theorem return_anchor_snoc[local]:
  !(cuts0 : ((num # num) list # num list # num # num # instruction list) list)
    (levels0 : (ir_function # (basic_block # num # instruction list) list # instruction option) list).
  MAP (\(ai,di,ei,qi,zi). ai) cuts0 = REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts0 = LENGTH levels0 /\
  (!i ai di ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) /\
    SUC i = LENGTH cuts0 ==>
    ai = a /\ ei = e /\ qi = 0 /\ zi = z0 /\
    EL i levels0 = (sf, prior_rows di ++ [(bb,e,z0)],NONE)) ==>
  ?prior pre ds.
    cuts0 = prior ++ [(a,ds,e,0,z0)] /\
    levels0 = pre ++ [(sf,prior_rows ds ++ [(bb,e,z0)],NONE)] /\
    FST (HD cuts0) = []
Proof
  rpt gen_tac >> strip_tac >>
  `cuts0 <> []` by (strip_tac >> fs[GENLIST_EQ_NIL]) >>
  `levels0 <> []` by
    (strip_tac >> qpat_assum `LENGTH cuts0 = LENGTH levels0` mp_tac >>
     simp_tac (srw_ss()) [LENGTH_NIL, NoAsms] >>
     qpat_assum `levels0 = []` SUBST1_TAC >>
     simp_tac (srw_ss()) [LENGTH,LENGTH_NIL] >> first_assum ACCEPT_TAC) >>
  `PRE (LENGTH cuts0) < LENGTH cuts0 /\ SUC (PRE (LENGTH cuts0)) = LENGTH cuts0` by
    (`0 < LENGTH cuts0` by (Cases_on `cuts0` >> fs[]) >> decide_tac) >>
  qabbrev_tac `p = LAST cuts0` >> PairCases_on `p` >>
  `EL (PRE (LENGTH cuts0)) cuts0 = (p0,p1,p2,p3,p4)` by metis_tac[LAST_EL] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qexistsl_tac [`FRONT cuts0`,`FRONT levels0`,`p1`] >>
  conj_tac >- metis_tac[APPEND_FRONT_LAST] >>
  conj_tac >- metis_tac[APPEND_FRONT_LAST,LAST_EL] >>
  `HD (MAP (\(ai,di,ei,qi,zi). ai) cuts0) = FST (HD cuts0)` by
    (Cases_on `cuts0` >- fs[] >>
     simp_tac (srw_ss()) [MAP,HD] >> pairarg_tac >> simp[]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  qpat_assum `MAP (\(ai,di,ei,qi,zi). ai) cuts0 = _` SUBST1_TAC >>
  simp[HD_REVERSE,GENLIST_EQ_NIL,GENLIST_LAST]
QED

(* Only the final selected row is extended. The anchor below is the old cut
   at its zero-body prefix, chosen before the replay fuel and filling. *)
Theorem dft_packet_return_parent_new_cuts:
  !(N:num) C7 C8 root_sf root_tf root_entry
    (acts:((num # num) list,
      ir_function # ir_function # num # venom_state # num list #
      exec_result option # bytes32 list option) fmap)
    (blocks:(((num # num) list # num),
      basic_block # basic_block # instruction list # instruction list #
      instruction list # num list # venom_state # num #
      (venom_state # num) option # num # exec_result # bool #
      bytes32 list option) fmap)
    (calls:(gas_event,num # num # venom_state # num list # venom_state #
      (internal_return # venom_state # venom_state) option) fmap)
    (ms_tab:(((num # num) list # num),bytes32 option list list) fmap)
    (es_tab:(((num # num) list # num),(string # num) list list) fmap)
    (ks_tab:(((num # num) list # num),gas_event list list) fmap)
    row_eval plan_eval call_setup rooted_eval plan_ok levels_ok
    cp rho.
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
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  (?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)) /\
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
  FDOM blocks = FDOM ms_tab /\ FDOM blocks = FDOM es_tab /\
  FDOM blocks = FDOM ks_tab /\
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
  p = (e,cid)::a /\
  FLOOKUP acts p = SOME (csf,ctf,e,child_entry,child_order,NONE,NONE) /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
  FLOOKUP blocks (p,d) =
    SOME (cb,ct,cp,cx,cy,cr,ci,ch,SOME (cbe,chbe),cc,OK st,F,NONE) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),cnt,OK b0,F,NONE) /\
  FLOOKUP calls (a,e,cid) = SOME (cq,call_h,b0,done,child_entry,NONE) /\
  acts' = acts |+ (p,(csf,ctf,e,child_entry,child_order,
    SOME (IntRet ir child_out),SOME child_out.vs_gas_readings)) /\
  blocks' = blocks |+
    ((p,d),(cb,ct,cp,cx,cy,cr,ci,ch,SOME (cbe,chbe),
      LENGTH cy,IntRet ir child_out,T,SOME child_out.vs_gas_readings)) |+
    ((a,e),(bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),SUC cnt,
      OK (caller_post with vs_inst_idx := SUC b0.vs_inst_idx),F,NONE)) /\
  calls' = calls |+ ((a,e,cid),
    (cq,call_h,b0,done,child_entry,SOME (ir,child_out,caller_post))) /\
  AM = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ms_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AE = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP es_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  AK = (\a. FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab (a,e))))
    (FST (SND (SND (SND (SND (THE (FLOOKUP acts a))))))))) /\
  (!a e cid qi h b0 done child_entry ret.
    FLOOKUP calls (a,e,cid) = SOME (qi,h,b0,done,child_entry,ret) ==>
    ?ms ess ks. FLOOKUP ms_tab (a,e) = SOME ms /\
      FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks /\
      qi < LENGTH ms /\ qi < LENGTH ess /\ qi < LENGTH ks /\
      EL qi ms = AM ((e,cid)::a) /\ EL qi ess = AE ((e,cid)::a) /\
      EL qi ks = AK ((e,cid)::a)) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\
  FLOOKUP es_tab (a,e) = SOME ess /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  LENGTH ms = LENGTH xs /\ LENGTH ess = LENGTH ms /\ LENGTH ks = LENGTH ms /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  LIST_REL (\m keys. LENGTH m = LENGTH keys) ms ks /\
  be.vs_inst_idx = LENGTH ps /\ q < LENGTH xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE (SUC cnt) rho)) /\
  (!F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE (SUC cnt) rho)) /\
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
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess)))) /\
  z0 = DROP (phi_prefix_length bb.bb_instructions) ps /\ z = z0 ++ TAKE q xs /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts0 =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts0 = LENGTH levels0 /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts0 /\ EL i cuts0 = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts0 then ai = a /\ ei = e /\ qi = 0 /\ zi = z0
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
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs ==>
    levels_ok F C7 levels0
      (MAP (\(ai,ds,ei,qi,zi). ai) cuts0)
      (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cuts0)
      root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
    (?extra. E0 = FST (rooted_eval F C7 levels0
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail)) of
      OK u =>
        FST (rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail)) = E0 /\
        u.vs_gas_readings = tail /\
        (?before after.
          trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            before ++ [((a,e,(EL (LENGTH z0)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
              EL (LENGTH z0) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
          trace_gas before = ZIP (K0,gs)) /\
        (!tail'. rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail') =
          (E0,OK (u with vs_gas_readings := tail')))
    | stopped =>
        run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
        gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
          FST (rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail)))) ==>
  ?cuts levels Mcut Ecut Kcut mr er kr.
    MAP (\(ai,ds,ei,qi,zi). ai) cuts =
      REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
    LENGTH cuts = LENGTH levels /\
    (!i ai ds ei qi zi.
      i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
      ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
        ini hi bei counti fronti closedi resti later.
        FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
        FLOOKUP blocks' (ai,ei) =
          SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
        orderi = ds ++ ei::later /\
        (if SUC i = LENGTH cuts then ai = a /\ ei = e /\ qi = q /\ zi = z
         else ?cid h b0 done child_entry ret.
           EL (SUC i) (MAP (\(aj,dj,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
           FLOOKUP calls' (ai,ei,cid) = SOME (qi,h,b0,done,child_entry,ret) /\
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
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
    Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
    Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
      FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
    AM [] = Mcut ++ mr /\ AE [] = Ecut ++ er /\ AK [] = Kcut ++ kr /\
    LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
    (!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
      levels_ok F C7 levels
        (MAP (\(ai,ds,ei,qi,zi). ai) cuts)
        (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts' ai))))) cuts)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Ecut = FST (rooted_eval F C7 levels
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            trace_gas before = ZIP (Kcut,gs)) /\
          (!tail'. rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail') =
            (Ecut,OK (u with vs_gas_readings := tail')))
      | stopped =>
          run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `rows0 = \ds. MAP (\f. (FST (THE (FLOOKUP blocks (a,f))),f,
      DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)
        (FST (THE (FLOOKUP blocks (a,f)))).bb_instructions)) ds` >>
  `!i ai di ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) /\
     SUC i = LENGTH cuts0 ==>
     ai = a /\ ei = e /\ qi = 0 /\ zi = z0 /\
     EL i levels0 = (sf,rows0 di ++ [(bb,e,z0)],NONE)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. _` (drule_all_then mp_tac) >>
     qpat_assum `SUC i = LENGTH cuts0` (fn th => simp_tac (srw_ss()) [th]) >>
     strip_tac >>
     qpat_x_assum `ai = a` SUBST_ALL_TAC >>
     qpat_x_assum `ei = e` SUBST_ALL_TAC >>
     qpat_x_assum `zi = z0` SUBST_ALL_TAC >>
     qpat_assum `FLOOKUP acts a = SOME (sfi,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (bbi,_)` mp_tac >>
     qpat_assum `FLOOKUP acts a = SOME (sf,_)` (fn A =>
       qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,_)` (fn B =>
         simp_tac (srw_ss()) [A,B])) >>
     strip_tac >> strip_tac >>
     qpat_x_assum `bb = bbi` (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `sf = sfi` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `EL i levels0 = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [Abbr `rows0`, NoAsms] >> first_assum ACCEPT_TAC) >>
  `?prior pre ds. cuts0 = prior ++ [(a,ds,e,0,z0)] /\
      levels0 = pre ++ [(sf,rows0 ds ++ [(bb,e,z0)],NONE)] /\ FST (HD cuts0) = []` by
    (drule_all return_anchor_snoc >> disch_then ACCEPT_TAC) >>
  `!i ai di ei qi zi.
     i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) ==>
     ?sfi tfi inci enti orderi resi nresti later mi ei' ki.
       FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
       orderi = di ++ ei::later /\
       FLOOKUP ms_tab (ai,ei) = SOME mi /\ FLOOKUP es_tab (ai,ei) = SOME ei' /\
       FLOOKUP ks_tab (ai,ei) = SOME ki /\
       qi <= LENGTH mi /\ qi <= LENGTH ei' /\ qi <= LENGTH ki /\
       (SUC i < LENGTH cuts0 ==>
         qi < LENGTH mi /\ qi < LENGTH ei' /\ qi < LENGTH ki /\
         EL qi mi = AM (FST (EL (SUC i) cuts0)) /\
         EL qi ei' = AE (FST (EL (SUC i) cuts0)) /\
         EL qi ki = AK (FST (EL (SUC i) cuts0)))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai ds ei qi zi. _` (drule_all_then strip_assume_tac) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     Cases_on `SUC i = LENGTH cuts0`
     >- (qpat_assum `SUC i = LENGTH cuts0` (fn th =>
           qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _`
             (strip_assume_tac o REWRITE_RULE [th])) >>
         qexistsl_tac [`ms`,`ess`,`ks`] >>
         qpat_assum `ai = a` SUBST1_TAC >> qpat_assum `ei = e` SUBST1_TAC >>
         qpat_assum `qi = 0` SUBST1_TAC >>
         `~(SUC i < LENGTH cuts0)` by decide_tac >>
         qpat_assum `~(SUC i < LENGTH cuts0)` (fn th =>
           simp_tac (srw_ss()) [th,ZERO_LESS_EQ]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `SUC i <> LENGTH cuts0` (fn th =>
       qpat_x_assum `if SUC i = LENGTH cuts0 then _ else _`
         (strip_assume_tac o REWRITE_RULE [th])) >>
     qpat_assum `!a e cid qi h b0 done child_entry ret. _` (drule_then strip_assume_tac) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     rename1 `EL (SUC i) (MAP _ cuts0) = (ei,call_id)::ai` >>
     `SUC i < LENGTH cuts0` by decide_tac >>
     `FST (EL (SUC i) cuts0) = (ei,call_id)::ai` by
       (qpat_assum `EL (SUC i) (MAP _ cuts0) = _` mp_tac >>
        qpat_assum `SUC i < LENGTH cuts0` (fn th => simp[NoAsms,EL_MAP,th]) >>
        pairarg_tac >> pop_assum (fn th => simp[NoAsms,th])) >>
     pop_assum SUBST1_TAC >>
     rpt conj_tac >- decide_tac >- decide_tac >- decide_tac >>
     disch_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `cutsq = prior ++ [(a,ds,e,q,z)]` >>
  `cutsq = prior ++ [(a,ds,e,q,z)]` by simp[NoAsms,Abbr `cutsq`] >>
  qabbrev_tac `Mq = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) di) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cutsq)` >>
  `Mq = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) di) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cutsq)` by simp[NoAsms,Abbr `Mq`] >>
  `q <= LENGTH ms` by decide_tac >>
  `!i ai di ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) ==>
    ?sf tf inc entry order res nrest later ri.
      FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
      order = di ++ ei::later /\ FLOOKUP ms_tab (ai,ei) = SOME ri /\
      qi <= LENGTH ri /\
      (SUC i < LENGTH cuts0 ==>
        qi < LENGTH ri /\ EL qi ri = AM (FST (EL (SUC i) cuts0)))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai di ei qi zi. _ ==> ?sf tf inc entry order res nrest later mi ei' ki. _`
       (drule_all_then strip_assume_tac) >>
     goal_assum (drule_at (Pat `FLOOKUP acts ai = _`)) >>
     goal_assum (drule_at (Pat `_ = di ++ ei::later`)) >>
     qexists_tac `mi` >> rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
     disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `Mq = M0 ++ FLAT (TAKE q ms) /\ (?mr. AM [] = Mq ++ mr)` by
    (drule_all dft_packet_return_cut_array >> disch_then ACCEPT_TAC) >>
  qabbrev_tac `Enew = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) di) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cutsq)` >>
  `Enew = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) di) ++
    FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cutsq)` by simp[NoAsms,Abbr `Enew`] >>
  `q <= LENGTH ess` by decide_tac >>
  `!i ai di ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) ==>
    ?sf tf inc entry order res nrest later ri.
      FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
      order = di ++ ei::later /\ FLOOKUP es_tab (ai,ei) = SOME ri /\
      qi <= LENGTH ri /\
      (SUC i < LENGTH cuts0 ==>
        qi < LENGTH ri /\ EL qi ri = AE (FST (EL (SUC i) cuts0)))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai di ei qi zi. _ ==> ?sf tf inc entry order res nrest later mi ei' ki. _`
       (drule_all_then strip_assume_tac) >>
     goal_assum (drule_at (Pat `FLOOKUP acts ai = _`)) >>
     goal_assum (drule_at (Pat `_ = di ++ ei::later`)) >>
     qexists_tac `ei'` >> rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
     disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `Enew = E0 ++ FLAT (TAKE q ess) /\ (?er. AE [] = Enew ++ er)` by
    (drule_all dft_packet_return_cut_array >> disch_then ACCEPT_TAC) >>
  qabbrev_tac `Kq = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) di) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cutsq)` >>
  `Kq = FLAT (MAP (\(ai,di,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) di) ++
    FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cutsq)` by simp[NoAsms,Abbr `Kq`] >>
  `q <= LENGTH ks` by decide_tac >>
  `!i ai di ei qi zi. i < LENGTH cuts0 /\ EL i cuts0 = (ai,di,ei,qi,zi) ==>
    ?sf tf inc entry order res nrest later ri.
      FLOOKUP acts ai = SOME (sf,tf,inc,entry,order,res,nrest) /\
      order = di ++ ei::later /\ FLOOKUP ks_tab (ai,ei) = SOME ri /\
      qi <= LENGTH ri /\
      (SUC i < LENGTH cuts0 ==>
        qi < LENGTH ri /\ EL qi ri = AK (FST (EL (SUC i) cuts0)))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i ai di ei qi zi. _ ==> ?sf tf inc entry order res nrest later mi ei' ki. _`
       (drule_all_then strip_assume_tac) >>
     goal_assum (drule_at (Pat `FLOOKUP acts ai = _`)) >>
     goal_assum (drule_at (Pat `_ = di ++ ei::later`)) >>
     qexists_tac `ki` >> rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
     disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `Kq = K0 ++ FLAT (TAKE q ks) /\ (?kr. AK [] = Kq ++ kr)` by
    (drule_all dft_packet_return_cut_array >> disch_then ACCEPT_TAC) >>
  `LENGTH Mq = LENGTH Enew /\ LENGTH Mq = LENGTH Kq` by
    (irule dft_packet_return_cut_lengths >>
     qexistsl_tac [`E0`,`K0`,`M0`,`ess`,`ks`,`ms`,`q`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `levelsq = pre ++ [(sf,rows0 ds ++ [(bb,e,z0 ++ TAKE q xs)],NONE)]` >>
  `levelsq = pre ++ [(sf,rows0 ds ++ [(bb,e,z0 ++ TAKE q xs)],NONE)]` by simp[NoAsms,Abbr `levelsq`] >>
  `cutsq = prior ++ [(a,ds,e,q,z0 ++ TAKE q xs)]` by
    (qpat_assum `z = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule_all dft_packet_return_cut_geometry >> strip_tac >>
  `bb.bb_instructions = ps ++ xs /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
     EVERY (\i. ~is_pseudo i.inst_opcode) xs` by
    (qpat_assum `!a e bb bt ps xs ys rho hin h0 body count front closed brest. _`
       (qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,_)` o
        (fn th => fn src => mp_tac (MATCH_MP th src))) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
     z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
     EVERY (\i. ~is_terminator i.inst_opcode) z /\
     EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = EL q xs` by
    (drule_all dft_packet_return_cut_row_shape >> disch_then ACCEPT_TAC) >>
  `!fuel gs tail ev u. N <= fuel /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
     rooted_eval fuel C7 levels0 (root_entry with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
       ev = E0` by
    (rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
     qpat_assum `!F gs tail. _ ==> levels_ok F C7 levels0 _ _ _ _ _ _ /\ _`
       (qspecl_then [`fuel`,`gs`] (drule_all_then (qspec_then `tail` mp_tac))) >>
     qpat_assum `rooted_eval fuel C7 levels0 _ = (ev,OK u)`
       (fn th => simp_tac (srw_ss()) [th]) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!F gs tail ev u. N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) M0 gs /\
     rooted_eval F C7 levels0 (root_entry with vs_gas_readings := gs ++ tail) = (ev,OK u) ==>
     ev = E0 /\ u = (be with vs_gas_readings := tail)` by suspend "anchor" >>
  `!F gs tail.
      N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mq gs ==>
      levels_ok F C7 levelsq
        (MAP (\(ai,ds,ei,qi,zi). ai) cutsq)
        (MAP (\(ai,ds,ei,qi,zi). FST (SND (SND (THE (FLOOKUP acts ai))))) cutsq)
        root_sf (root_entry with vs_gas_readings := gs ++ tail) [] 0 /\
      (?extra. Enew = FST (rooted_eval F C7 levelsq
        (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
      (case SND (rooted_eval F C7 levelsq (root_entry with vs_gas_readings := gs ++ tail)) of
        OK u =>
          FST (rooted_eval F C7 levelsq (root_entry with vs_gas_readings := gs ++ tail)) = Enew /\
          u.vs_gas_readings = tail /\
          (?before after.
            trace_blocks [] 0 F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
              before ++ [((a,e,(EL (LENGTH z)
                (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)).inst_id),sf,
                EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions),u)] ++ after /\
            trace_gas before = ZIP (Kq,gs)) /\
          (!tail'. rooted_eval F C7 levelsq (root_entry with vs_gas_readings := gs ++ tail') =
            (Enew,OK (u with vs_gas_readings := tail')))
      | stopped =>
          run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
          gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
            FST (rooted_eval F C7 levelsq (root_entry with vs_gas_readings := gs ++ tail)))` by suspend "semantics" >>
  suspend "frame"
QED

Resume dft_packet_return_parent_new_cuts[anchor]:
  `0 < LENGTH xs` by decide_tac >>
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  rename1 `FLOOKUP blocks (p,d) = SOME (cb,ct,cps,cx,cy,cr,ci,ch,SOME (cbe,chbe),cc,OK st,F,NONE)` >>
  rename1 `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),cnt,OK b0,F,NONE)` >>
  irule dft_packet_return_anchor_state >>
  qexistsl_tac [`C7`,`C8`,`fuel`,`M0`,`N`,`a`,`acts`,`bb`,`blocks`,`NONE`,
    `bt`,`call_setup`,`calls`,`cb`,`SOME (cbe,chbe)`,`cc`,`ch`,`ci`,`F`,`cnt`,
    `cps`,`cr`,`ct`,`cuts0`,`cx`,`cy`,`d`,`e`,`es_tab`,`OK b0`,`gs`,`h0`,`hbe`,
    `hin`,`ks_tab`,`levels0`,`ms_tab`,`p`,`plan_eval`,`ps`,`row_order`,
    `root_entry`,`root_sf`,`root_tf`,`rooted_eval`,`row_eval`,`st`,`xs`,`ys`,`z0`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_return_parent_new_cuts[semantics]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `Mq = M0 ++ _` (fn th =>
    qpat_x_assum `LIST_REL _ Mq gs` (strip_assume_tac o REWRITE_RULE [th,LIST_REL_SPLIT1])) >>
  rename1 `gs = gs0 ++ gs1` >>
  qpat_assum `LIST_REL _ (FLAT (TAKE q ms)) gs1`
    (strip_assume_tac o MATCH_MP dft_packet_flat_filling_split) >>
  conj_tac >- suspend "validity" >>
  suspend "extend"
QED

Resume dft_packet_return_parent_new_cuts[validity]:
  rename1 `N <= fuel` >>
  qpat_assum `!F gs tail. _ ==> levels_ok F C7 levels0 _ _ _ _ _ _ /\ _`
    (qspecl_then [`fuel`,`gs0`] (drule_all_then (qspec_then `gs1 ++ tail` (mp_tac o CONJUNCT1)))) >>
  qpat_assum `cuts0 = prior ++ _` (fn th => rewrite_tac[th]) >>
  qpat_assum `cutsq = prior ++ _` (fn th => rewrite_tac[th]) >>
  qpat_assum `levels0 = pre ++ _` (fn th => rewrite_tac[th]) >>
  qpat_assum `levelsq = pre ++ _` (fn th => rewrite_tac[th]) >>
  qpat_assum `gs = gs0 ++ gs1` SUBST1_TAC >>
  qpat_assum `z = z0 ++ _` (fn th => rewrite_tac [GSYM th]) >>
  simp[NoAsms,MAP_APPEND,APPEND_ASSOC] >> disch_tac >>
  qpat_assum `plan_ok = _`
    (mp_then Any (fn th => qpat_assum `levels_ok = _`
      (mp_then Any (drule_at_then (Pat `levels_ok _ _ _ _ _ _ _ _ _`) irule) th))
      dft_packet_levels_last_row_replace) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_return_parent_new_cuts[extend]:
  rename1 `N <= fuel` >>
  qabbrev_tac `A = \t. rooted_eval fuel C7 levels0
    (root_entry with vs_gas_readings := gs0 ++ t)` >>
  qabbrev_tac `D = \t. rooted_eval fuel C7 levelsq
    (root_entry with vs_gas_readings := (gs0 ++ gs1) ++ t)` >>
  `!t. rooted_eval fuel C7 levelsq
    (root_entry with vs_gas_readings := (gs0 ++ gs1) ++ t) = D t` by
    simp[Abbr `D`,NoAsms] >>
  qpat_assum `gs = gs0 ++ gs1` SUBST1_TAC >>
  qpat_assum `Enew = _` SUBST1_TAC >>
  qpat_assum `Kq = _` SUBST1_TAC >>
  qpat_assum `EL (LENGTH z) _ = EL q xs` SUBST1_TAC >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule return_cut_replay >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_assum `LIST_REL _ M0 gs0` (mp_tac o MATCH_MP LIST_REL_LENGTH) >> decide_tac) >>
  conj_tac >-
    (qpat_assum `LIST_REL _ (FLAT (TAKE q ms)) gs1`
       (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     qpat_assum `LENGTH Mq = LENGTH Kq` mp_tac >>
     qpat_assum `Mq = M0 ++ _` SUBST1_TAC >>
     qpat_assum `Kq = K0 ++ _` SUBST1_TAC >>
     rewrite_tac[LENGTH_APPEND] >> decide_tac) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`A`,`bb`,`be`,`ps`] >>
  conj_tac >- suspend "replay_anchor" >>
  conj_tac >- suspend "replay_row" >>
  conj_tac >- suspend "replay_extend" >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_return_parent_new_cuts[replay_anchor]:
  qx_gen_tac `t` >>
  qpat_assum `!F gs tail. _ ==> levels_ok F C7 levels0 _ _ _ _ _ _ /\ _`
    (qspecl_then [`fuel`,`gs0`] (drule_all_then (qspec_then `t` (fn th =>
      strip_assume_tac (CONJUNCT1 th) >>
      strip_assume_tac (CONJUNCT1 (CONJUNCT2 th)) >>
      (mk_asm "anchor_case" (CONJUNCT2 (CONJUNCT2 th))))))) >>
  `!t. A t = rooted_eval fuel C7 levels0 (root_entry with vs_gas_readings := gs0 ++ t)` by
    simp[NoAsms,Abbr `A`] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  conj_tac >- (qexists_tac `extra` >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `ent = root_entry with vs_gas_readings := gs0 ++ t` >>
  asm_x "anchor_case" mp_tac >>
  Cases_on `rooted_eval fuel C7 levels0 ent` >>
  rename1 `rooted_eval fuel C7 levels0 ent = (ev,r)` >>
  Cases_on `r` >> simp_tac (srw_ss()) [] >>
  rename1 `rooted_eval fuel C7 levels0 ent = (ev,OK u)` >>
  strip_tac >>
  conj_tac >-
    (qpat_assum `rooted_eval fuel C7 levels0 ent = (ev,OK u)` mp_tac >>
     simp_tac (srw_ss()) [Abbr `ent`] >> disch_tac >>
     qpat_assum `!F gs tail ev u. _ ==> ev = E0 /\ u = _`
       (drule_all_then (ACCEPT_TAC o CONJUNCT2))) >>
  `!f owner b s k t1.
    s.vs_inst_idx + k <= LENGTH b.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) /\
    FOLDR (dft_exec_cons f C7) OK
      (TAKE k (DROP s.vs_inst_idx b.bb_instructions)) s = OK t1 ==>
    t1.vs_inst_idx = s.vs_inst_idx + k /\
    exec_block f C7 b s = exec_block f C7 b t1 /\
    gas_events_block f C7 owner b s =
      gas_events_block f C7 owner
        (b with bb_instructions := TAKE (s.vs_inst_idx + k) b.bb_instructions) s ++
      gas_events_block f C7 owner b t1` by
    (rpt gen_tac >> strip_tac >>
     drule_all (Q.SPECL [`f`,`C7`,`owner`] dft_packet_block_prefix_operational) >>
     simp_tac (srw_ss()) [LET_THM] >>
     disch_then (qspecl_then [`owner`,`f`,`C7`]
       (qspec_then `t1` mp_tac o CONJUNCT1)) >>
     qpat_assum `FOLDR (dft_exec_cons f C7) OK _ s = OK t1`
       (fn th => rewrite_tac [th])) >>
  drule_all dft_packet_rooted_success_operational >>
  rewrite_tac[SUB_0] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac
    (CONJUNCTS_THEN2 strip_assume_tac (CONJUNCTS_THEN2 strip_assume_tac
      (qx_choose_then `kont` strip_assume_tac)))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qexists_tac `kont` >> qpat_assum `ev = E0` (fn th => rewrite_tac[GSYM th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`EL (LENGTH z0) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)`,
                `before`,`after`] >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume dft_packet_return_parent_new_cuts[replay_row]:
  qx_gen_tac `t` >> simp_tac (srw_ss()) [LET_THM] >>
  qpat_assum `gs1 = FLAT gss` SUBST1_TAC >>
  qpat_assum `!F k kgss tail. _ /\ _ /\ _ /\
      (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE (SUC cnt) rho')) /\
      _ ==> _`
    (qspecl_then [`fuel`,`q`,`gss`,`t`] mp_tac) >>
  impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `q < LENGTH xs` mp_tac >> decide_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Resume dft_packet_return_parent_new_cuts[replay_extend]:
  `EVERY (\i. i.inst_opcode <> PHI) xs` by
    (qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) xs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `phi_prefix_length bb.bb_instructions = phi_prefix_length ps` by
    metis_tac[dft_phi_prefix_append] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH ps` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  `TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z =
     TAKE (LENGTH ps + q) bb.bb_instructions` by
    (qpat_assum `z = z0 ++ TAKE q xs` (fn th => rewrite_tac [th]) >>
     qpat_assum `z0 = DROP _ ps` (fn th => rewrite_tac [th]) >>
     qpat_assum `bb.bb_instructions = ps ++ xs` (fn th =>
       rewrite_tac [th,TAKE_SUM,DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND]) >>
     qpat_assum `phi_prefix_length bb.bb_instructions = phi_prefix_length ps`
       (fn th => qpat_assum `bb.bb_instructions = ps ++ xs`
         (fn bth => rewrite_tac [REWRITE_RULE [bth] th])) >>
     simp[NoAsms,TAKE_APPEND1,venomExecProofsTheory.phi_prefix_length_le,APPEND_ASSOC]) >>
  qabbrev_tac `H = \v. (gas_events_block (fuel-e) C7 sf.fn_name
      (bb with bb_instructions := TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z) v,
      FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs) v)` >>
  `!ent. rooted_eval fuel C7 (pre ++ [(sf,rows0 ds ++ [(bb,e,z)],NONE)]) ent =
    (case SND (rooted_eval fuel C7 (pre ++ [(sf,rows0 ds ++ [(bb,e,z0)],NONE)]) ent) of
       OK v => (FST (rooted_eval fuel C7 (pre ++ [(sf,rows0 ds ++ [(bb,e,z0)],NONE)]) ent) ++
                FST (H v), SND (H v))
     | other => (FST (rooted_eval fuel C7 (pre ++ [(sf,rows0 ds ++ [(bb,e,z0)],NONE)]) ent),other))` by
    (gen_tac >> irule return_literal_extend >> reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`C7`,`plan_eval fuel C7`,`call_setup C7`,`fuel`,
       `phi_prefix_length bb.bb_instructions`,`row_eval fuel C7`,`TAKE q xs`] >>
     rpt conj_tac
     >- (qpat_assum `LENGTH z < _` mp_tac >> decide_tac)
     >- (qpat_assum `plan_eval = _` (fn th => simp_tac (srw_ss()) [th]))
     >- (qpat_assum `row_eval = _` (fn th => simp_tac (srw_ss()) [th]))
     >- (qpat_assum `rooted_eval = _` (fn th => simp_tac (srw_ss()) [th]))
     >- simp[NoAsms,Abbr `H`]
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >> simp[NoAsms]) >>
  `levelsq = pre ++ [(sf,rows0 ds ++ [(bb,e,z)],NONE)]` by
    (qpat_assum `z = z0 ++ TAKE q xs` (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!ent. rooted_eval fuel C7 (pre ++ [(sf,rows0 ds ++ [(bb,e,z)],NONE)]) ent = _`
    (fn th => simp_tac (srw_ss()) [Abbr `A`,Abbr `D`,APPEND_ASSOC] >>
      qpat_assum `levelsq = pre ++ [(sf,rows0 ds ++ [(bb,e,z)],NONE)]`
        (fn qth => rewrite_tac [qth,th])) >>
  qpat_assum `levels0 = pre ++ _` (fn th => rewrite_tac [GSYM th]) >>
  qpat_assum `TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z = _`
    (fn th => simp[NoAsms,Abbr `H`,th])
QED

Resume dft_packet_return_parent_new_cuts[frame]:
  qpat_x_assum `z = z0 ++ TAKE q xs` SUBST_ALL_TAC >>
  `a <> p` by (qpat_assum `p = (e,cid)::a` (fn th => simp[NoAsms,th])) >>
  `!x. FST (SND (SND (THE (FLOOKUP acts' x)))) =
        FST (SND (SND (THE (FLOOKUP acts x))))` by
    (gen_tac >> qpat_assum `acts' = _` (fn th => rewrite_tac [th,FLOOKUP_UPDATE]) >>
     Cases_on `p = x`
     >- (pop_assum (SUBST1_TAC o SYM) >>
         qpat_assum `FLOOKUP acts p = _` (fn th => simp[NoAsms,th])) >>
     pop_assum (fn th => simp[NoAsms,th])) >>
  `!x f. FST (THE (FLOOKUP blocks' (x,f))) = FST (THE (FLOOKUP blocks (x,f)))` by
    (rpt gen_tac >>
     qpat_assum `blocks' = _` (fn th => rewrite_tac [th,FLOOKUP_UPDATE]) >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (cb,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,_)` mp_tac >>
     qpat_assum `a <> p` mp_tac >> POP_ASSUM_LIST kall_tac >>
     Cases_on `x = a` >- (Cases_on `f = e` >> gvs[]) >>
     Cases_on `x = p` >- (Cases_on `f = d` >> gvs[]) >> gvs[]) >>
  qexistsl_tac [`cutsq`,`levelsq`,`Mq`,`Enew`,`Kq`,`mr`,`er`,`kr`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "records" >>
  ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!x. FST (SND (SND (THE (FLOOKUP acts' x)))) = _`
    (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC
QED

Resume dft_packet_return_parent_new_cuts[records]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!i ai di ei qi zi. i < LENGTH cutsq /\ EL i cutsq = _ ==> _`
    (drule_all_then strip_assume_tac) >>
  `?res' nrest'. FLOOKUP acts' ai = SOME (sfi,tfi,inci,enti,orderi,res',nrest')` by
    (qpat_assum `acts' = _` (fn th => rewrite_tac [th,FLOOKUP_UPDATE]) >>
     qpat_assum `FLOOKUP acts ai = _` mp_tac >>
     qpat_assum `FLOOKUP acts p = _` mp_tac >> POP_ASSUM_LIST kall_tac >>
     Cases_on `ai = p` >> gvs[]) >>
  `?count' front' closed' rest'. FLOOKUP blocks' (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,count',front',closed',rest')` by
    (qpat_assum `blocks' = _` (fn th => rewrite_tac [th,FLOOKUP_UPDATE]) >>
     qpat_assum `FLOOKUP blocks (ai,ei) = _` mp_tac >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (bb,_)` mp_tac >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME (cb,_)` mp_tac >>
     qpat_assum `a <> p` mp_tac >> POP_ASSUM_LIST kall_tac >>
     Cases_on `ai = a` >- (Cases_on `ei = e` >> gvs[]) >>
     Cases_on `ai = p` >- (Cases_on `ei = d` >> gvs[]) >> gvs[]) >>
  goal_assum (drule_at (Pat `FLOOKUP acts' ai = _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP blocks' (ai,ei) = _`)) >>
  goal_assum (drule_at (Pat `_ = di ++ ei::later`)) >>
  reverse conj_tac
  >- (qpat_assum `!x f. FST (THE (FLOOKUP blocks' (x,f))) = _`
       (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
  IF_CASES_TAC
  >- (qpat_assum `(if SUC i = LENGTH cutsq then _ else _)` mp_tac >>
      qpat_assum `SUC i = LENGTH cutsq` (fn th => simp[NoAsms,th])) >>
  qpat_assum `SUC i <> LENGTH cutsq` (fn guard =>
    qpat_assum `(if SUC i = LENGTH cutsq then _ else _)`
      (strip_assume_tac o REWRITE_RULE [guard])) >>
  rename1 `FLOOKUP calls (ai,ei,call_id) = SOME (qi,hi_call,caller,donei,child_ent,reti)` >>
  `?ret'. FLOOKUP calls' (ai,ei,call_id) = SOME (qi,hi_call,caller,donei,child_ent,ret')` by
    (qpat_assum `calls' = _` (fn th => rewrite_tac [th,FLOOKUP_UPDATE]) >>
     qpat_assum `FLOOKUP calls (ai,ei,call_id) = _` mp_tac >>
     qpat_assum `FLOOKUP calls (a,e,cid) = SOME (cq,call_h,b0,done,child_entry,NONE)` mp_tac >>
     POP_ASSUM_LIST kall_tac >>
     Cases_on `ai = a` >- (Cases_on `ei = e` >> Cases_on `call_id = cid` >> gvs[]) >>
     gvs[]) >>
  goal_assum (drule_at (Pat `FLOOKUP calls' (ai,ei,_) = _`)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise dft_packet_return_parent_new_cuts
