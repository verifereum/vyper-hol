Theory gasFocusInitialSingletonPacket
Ancestors
  gasFocusInitialSingletonCut gasFocusInitialRowReplay dftFinitePacket
  dftPacketEntryReplay dftPacketObservationSuccess dftGasFromListTraceDefs
  dftGasFromListRestore dftGasPrefixProvider dftIndexedExec dftRunRel
  o1PassContract frameJointTransition gasEvents venomExecProofs
  venomExecSemantics venomInst venomState finite_map pred_set
  list rich_list arithmetic

Theorem focus_initial_singleton_packet:
  !N C7 C8 root_sf root_tf root_entry nm lbl bb bt ps xs ys rho sp st inst
    PG G tn oms om hs h.
  0 < N /\
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
  MEM root_sf C7.ctx_functions /\ root_tf = dft_fn root_sf /\
  dft_fn_rel root_sf root_tf /\
  C7.ctx_entry = SOME nm /\ C8.ctx_entry = SOME nm /\
  lookup_function nm C7.ctx_functions = SOME root_sf /\
  lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl /\
  root_entry.vs_prev_bb = NONE /\ root_entry.vs_current_bb = lbl /\
  root_entry.vs_inst_idx = 0 /\
  strict_dom_vars_defined root_sf root_entry /\
  fn_reachable root_sf root_entry.vs_current_bb /\
  ctx_labels_bound C7 root_entry.vs_labels /\
  ctx_labels_bound C8 root_entry.vs_labels /\
  lookup_block lbl root_sf.fn_blocks = SOME bb /\
  lookup_block lbl root_tf.fn_blocks = SOME bt /\
  bb.bb_label = lbl /\ bt.bb_label = lbl /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  EVERY inst_shape_ok bb.bb_instructions /\
  LENGTH xs = LENGTH ys /\ PERM rho (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  eval_phis root_entry bt.bb_instructions = OK sp /\
  st = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
  get_instruction bt st.vs_inst_idx = SOME inst /\
  (phi_prefix_length bt.bb_instructions = LENGTH ps ==>
    dft_remaining_inv root_sf bb xs st) ==>
  !body_entry. body_entry = (if phi_prefix_length bt.bb_instructions < LENGTH ps
                   then NONE else SOME (st,0)) ==>
  !ms. ms = (if IS_SOME body_entry then
        MAP (\i. if i.inst_opcode = GAS then [NONE] else []) xs else []) ==>
  !es. es = (if IS_SOME body_entry then
        MAP (\i. if i.inst_opcode = GAS then [(root_sf.fn_name,i.inst_id)] else []) xs else []) ==>
  !ks. ks = (if IS_SOME body_entry then
        MAP (\i. if i.inst_opcode = GAS then [([],1,i.inst_id)] else []) xs else []) ==>
  !row_eval. row_eval = (\F C owner (bb,e,z) s.
        case eval_phis s bb.bb_instructions of
          OK sp =>
           (gas_events_block (F-e) C owner
             (bb with bb_instructions :=
               TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions ++ z)
             (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions),
            FOLDR (dft_exec_cons (F-e) C) OK z
             (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))
        | other => ([],other)) ==>
  !plan_eval. plan_eval = (\F C owner plan entry.
        FOLDL (\(es,r) row.
          case r of
            OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
          | other => (es,other)) ([],OK entry) plan) ==>
  !call_setup. call_setup = (\C c s.
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
              | SOME cs => OK cs) ==>
  !rooted_eval. rooted_eval = (\F C levels entry.
        FOLDL (\(prior,r) (sf,plan,call).
          case r of
            OK ent =>
             (prior ++ FST (plan_eval F C sf.fn_name plan ent),
              case SND (plan_eval F C sf.fn_name plan ent) of
                OK caller =>
                  (case call of NONE => OK caller | SOME c => call_setup C c caller)
              | other => other)
          | other => (prior,other)) ([],OK entry) levels) ==>
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (0,[])
    (FEMPTY |+ ([],(root_sf,root_tf,0,root_entry,[1],NONE,NONE)))
    (FEMPTY |+ (([],1),(bb,bt,ps,xs,ys,rho,root_entry,0,body_entry,0,OK st,F,NONE)))
    FEMPTY (FEMPTY |+ (([],1),ms)) (FEMPTY |+ (([],1),es))
    (FEMPTY |+ (([],1),ks)) rooted_eval [] 1
    (JointConfig [] PG G tn root_tf inst st oms om hs h) (FLAT ms) (FLAT es)
    st.vs_gas_readings
Proof
  rpt gen_tac >> strip_tac >>
  map_every (fn v => qx_gen_tac v >>
    disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`body_entry`,`ms`,`es`,`ks`,`row_eval`,`plan_eval`,`call_setup`,`rooted_eval`] >>
  markerLib.REABBREV_TAC >>
  `sp = root_entry /\ phi_prefix_length bt.bb_instructions = 0` by
    metis_tac[eval_phis_no_prev] >>
  `st = root_entry` by gvs[venom_state_component_equality] >>
  gvs[] >>
  `?rest. dftGasFromListTraceDefs$trace_blocks [] 0 N C8
      (dft_fn root_sf) root_entry =
      (([],1,inst.inst_id),dft_fn root_sf,inst,root_entry)::rest` by
    (`N = SUC (N-1)` by decide_tac >>
     pop_assum (fn th => once_rewrite_tac[th]) >>
     simp[Once dftGasFromListTraceDefsTheory.trace_defs] >>
     `root_entry with vs_inst_idx := 0 = root_entry` by
       simp[venom_state_component_equality] >>
     simp[Once dftGasFromListTraceDefsTheory.trace_defs]) >>
  simp_tac bool_ss [dft_focus_packet_rel_def] >>
  simp_tac (bool_ss ++ pairSimps.PAIR_ss) [] >>
  qexistsl_tac [`[]`,`PG`,`G`,`tn`,`dft_fn root_sf`,`inst`,`root_entry`,
    `oms`,`om`,`hs`,`h`] >>
  simp_tac (srw_ss()) [FLOOKUP_UPDATE, FLOOKUP_EMPTY,
    dftGasFromListTraceDefsTheory.trace_gas_def] >>
  conj_tac >- metis_tac[] >> simp[] >>
  Cases_on `ps`
  >- (gvs[Abbr `body_entry`, Abbr `ms`, Abbr `es`, Abbr `ks`] >>
      suspend "body") >>
  gvs[Abbr `body_entry`, Abbr `ms`, Abbr `es`, Abbr `ks`] >>
  suspend "pseudo"
QED

Resume focus_initial_singleton_packet[pseudo]:
  `inst = h` by gvs[get_instruction_def] >> gvs[] >>
  conj_tac >- simp[FUN_EQ_THM] >>
  `h.inst_opcode <> PHI` by gvs[phi_prefix_length_def, AllCaseEqs()] >>
  `phi_prefix_length bb.bb_instructions = 0` by simp[phi_prefix_length_def] >>
  `!s. eval_phis s bb.bb_instructions = OK s` by simp[eval_phis_def] >>
  `root_entry with vs_inst_idx := 0 = root_entry` by
    simp[venom_state_component_equality] >>
  `!rs. (root_entry with vs_gas_readings := rs) with vs_inst_idx := 0 =
    root_entry with vs_gas_readings := rs` by
    simp[venom_state_component_equality] >>
  `!f rs. gas_events_block f C7 root_sf.fn_name (bb with bb_instructions := [])
    (root_entry with vs_gas_readings := rs) = []` by
    simp[Once gas_events_block_def, get_instruction_def] >>
  `MEM bb root_sf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  qexistsl_tac [`[([],[],1,0,[])]`, `[(root_sf,[(bb,1,[])],NONE)]`] >>
  simp[Abbr `rooted_eval`, Abbr `plan_eval`, Abbr `row_eval`,
    phi_prefix_length_def] >>
  rpt strip_tac >> rename1 `N <= fuel` >> qexists_tac `[]` >> simp[] >>
  `fuel = SUC (fuel-1)` by decide_tac >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs] >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs, get_instruction_def]
QED

Resume focus_initial_singleton_packet[body]:
  `MEM bb root_sf.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftRunRelTheory.dft_fn_rel_def,
      dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `0 < LENGTH bt.bb_instructions /\ inst = HD bt.bb_instructions` by
    (Cases_on `bt.bb_instructions` >> gvs[get_instruction_def]) >>
  simp[FUN_EQ_THM] >>
  conj_asm1_tac >- suspend "keys" >>
  conj_tac >- suspend "slot_sites_length" >>
  conj_tac >- suspend "slot_keys_length" >>
  conj_tac >- suspend "empty_inventory" >>
  conj_tac >- suspend "body_rows" >>
  conj_tac >- suspend "memory_predecessors" >>
  suspend "body_cuts"
QED

Resume focus_initial_singleton_packet[keys]:
  qpat_x_assum `ALL_DISTINCT (MAP _ bb.bb_instructions)` mp_tac >>
  rpt (pop_assum kall_tac) >> qspec_tac (`bb.bb_instructions`,`zs`) >>
  Induct >> simp[] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = GAS` >> gvs[] >>
  spose_not_then strip_assume_tac >>
  gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM i zs` >>
  Cases_on `i.inst_opcode = GAS` >> gvs[MEM_MAP] >> metis_tac[]
QED
Resume focus_initial_singleton_packet[slot_sites_length]:
  rpt (pop_assum kall_tac) >> qspec_tac (`bb.bb_instructions`,`zs`) >>
  Induct >> simp[] >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED
Resume focus_initial_singleton_packet[slot_keys_length]:
  rpt (pop_assum kall_tac) >> qspec_tac (`bb.bb_instructions`,`zs`) >>
  Induct >> simp[] >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED
Resume focus_initial_singleton_packet[empty_inventory]:
  rpt (pop_assum kall_tac) >> qspec_tac (`bb.bb_instructions`,`zs`) >>
  Induct >> simp[] >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED
Resume focus_initial_singleton_packet[body_rows]:
  conj_tac
  >- (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
      Cases_on `(EL n bb.bb_instructions).inst_opcode = GAS` >> simp[]) >>
  conj_tac
  >- (simp[LIST_REL_EL_EQN, EL_MAP] >> rpt strip_tac >>
      Cases_on `(EL n bb.bb_instructions).inst_opcode = GAS` >> simp[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[EL_MAP]) >>
  rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  `!zs. FLAT (MAP (\i. if i.inst_opcode = GAS then
       [(root_sf.fn_name,i.inst_id)] else []) zs) =
       MAP (\i. (root_sf.fn_name,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) zs) /\
     FLAT (MAP (\i. if i.inst_opcode = GAS then [(([],1,i.inst_id):gas_event)] else []) zs) =
       MAP (\i. (([],1,i.inst_id):gas_event)) (FILTER (\i. i.inst_opcode = GAS) zs)` by
    (Induct >> simp[] >> Cases_on `h.inst_opcode = GAS` >> simp[]) >>
  `!zs (gss:bytes32 list list). LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (MAP (\i. if i.inst_opcode = GAS then [NONE] else []) zs) gss ==>
      LENGTH (FLAT gss) = LENGTH (FILTER (\i. i.inst_opcode = GAS) zs)` by
    (Induct >- simp[] >> qx_gen_tac `i` >> Cases_on `gss` >> simp[] >>
     Cases_on `i.inst_opcode = GAS` >> simp[] >> rpt strip_tac >>
     imp_res_tac LIST_REL_LENGTH >> gvs[]) >>
  `LENGTH (FLAT kgss) = LENGTH (FILTER (\i. i.inst_opcode = GAS)
      (TAKE k bb.bb_instructions))` by
    (first_x_assum irule >> simp[MAP_TAKE]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_pseudo i.inst_opcode) (TAKE k bb.bb_instructions)` by
    (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     gvs[EVERY_EL, EL_TAKE] >> metis_tac[]) >>
  qspecl_then [`fuel-1`,`C7`,`root_sf.fn_name`,`root_entry`] mp_tac
    focus_initial_unvisited_row_replay >>
  disch_then (qspecl_then [`TAKE k bb.bb_instructions`,`FLAT kgss`,`tail`] mp_tac) >>
  simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM MAP_TAKE] >>
  qpat_assum `!zs. FLAT _ = _ /\ _` (fn th => pure_rewrite_tac[th]) >>
  conj_tac >- (qexists_tac `extra` >> first_assum ACCEPT_TAC) >>
  suspend "row_success"
QED
Resume focus_initial_singleton_packet[row_success]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!u. FOLDR _ _ _ _ = OK u ==> _` drule >> strip_tac >>
  conj_tac >- REFL_TAC >>
  conj_tac
  >- (pure_rewrite_tac[GSYM dftGasFromListTraceDefsTheory.trace_gas_def] >>
      irule dftGasSourcePrefixTheory.noninvoke_prefix_trace_keys >>
      simp[] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  gen_tac >>
  qpat_assum `!tail'. FOLDR _ _ _ _ = _`
    (qspec_then `tail'` assume_tac) >>
  qspecl_then [`fuel-1`,`C7`,`root_sf.fn_name`,`root_entry`] mp_tac
    focus_initial_unvisited_row_replay >>
  disch_then (qspecl_then [`TAKE k bb.bb_instructions`,`FLAT kgss`,`tail'`] mp_tac) >>
  simp[NoAsms] >>
  impl_tac >- (asm_rewrite_tac[]) >>
  disch_then (drule o CONJUNCT2) >>
  qpat_assum `root_entry.vs_inst_idx = 0` (fn th => simp[NoAsms, th])
QED

Resume focus_initial_singleton_packet[memory_predecessors]:
  strip_tac >>
  `LENGTH rho' = LENGTH bt.bb_instructions` by metis_tac[LIST_REL_LENGTH] >>
  `from_block [EL (HD rho') bb.bb_instructions] (HD bt.bb_instructions)` by
    (qpat_x_assum `LIST_REL _ rho' _` mp_tac >>
     Cases_on `rho'` >> Cases_on `bt.bb_instructions` >> gvs[]) >>
  `EL (HD rho') bb.bb_instructions = HD bt.bb_instructions` by
    (drule_all dftGasInvMemoryObservationTheory.inv_memory_observation_original >> simp[]) >>
  simp[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE (HD rho') bb.bb_instructions) /\
    (!r. r < HD rho' /\ (EL r bb.bb_instructions).inst_opcode = INVOKE ==>
      MEM r (TAKE 0 rho'))` by
    (irule dft_packet_memory_schedule_predecessors >>
     rpt (first_assum (irule_at Any)) >>
     qexistsl_tac [`[]`,`bt`,`bb`] >> simp[EL] >> metis_tac[]) >>
  metis_tac[TAKE_0, MEM]
QED
Resume focus_initial_singleton_packet[body_cuts]:
  gen_tac >> strip_tac >>
  qexistsl_tac [`[([],[],1,q,TAKE q bb.bb_instructions)]`,
    `[(root_sf,[(bb,1,TAKE q bb.bb_instructions)],NONE)]`,
    `FLAT (DROP q (MAP (\i. if i.inst_opcode = GAS then [NONE] else []) bb.bb_instructions))`,
    `FLAT (DROP q (MAP (\i. if i.inst_opcode = GAS then [(root_sf.fn_name,i.inst_id)] else []) bb.bb_instructions))`,
    `FLAT (DROP q (MAP (\i. if i.inst_opcode = GAS then [([],1,i.inst_id)] else []) bb.bb_instructions))`] >>
  simp[] >>
  conj_tac >- metis_tac[FLAT_APPEND, TAKE_DROP] >>
  conj_tac >- metis_tac[FLAT_APPEND, TAKE_DROP] >>
  conj_tac >- metis_tac[FLAT_APPEND, TAKE_DROP] >>
  pure_rewrite_tac[GSYM MAP_TAKE] >>
  `!zs. LENGTH (FLAT (MAP (\i. if i.inst_opcode = GAS then [NONE:bytes32 option] else []) zs)) =
      LENGTH (FILTER (\i. i.inst_opcode = GAS) zs) /\
    LENGTH (FLAT (MAP (\i. if i.inst_opcode = GAS then [(root_sf.fn_name,i.inst_id)] else []) zs)) =
      LENGTH (FILTER (\i. i.inst_opcode = GAS) zs) /\
    LENGTH (FLAT (MAP (\i. if i.inst_opcode = GAS then [(([],1,i.inst_id):gas_event)] else []) zs)) =
      LENGTH (FILTER (\i. i.inst_opcode = GAS) zs)` by
    (Induct >> simp[] >> Cases_on `h.inst_opcode = GAS` >> simp[]) >>
  simp[] >> rpt gen_tac >> strip_tac >> rename1 `N <= fuel` >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def] >>
     `h.inst_opcode <> PHI` by metis_tac[is_pseudo_def] >> simp[]) >>
  `!s. eval_phis s bb.bb_instructions = OK s` by
    (Cases_on `bb.bb_instructions` >> gvs[eval_phis_def, phi_prefix_length_def, AllCaseEqs()]) >>
  conj_tac
  >- simp[Abbr `rooted_eval`, Abbr `plan_eval`] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
      (TAKE q bb.bb_instructions)` by
    (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
     gvs[EVERY_EL, EL_TAKE] >> metis_tac[]) >>
  `LENGTH gs = LENGTH (FILTER (\i. i.inst_opcode = GAS) (TAKE q bb.bb_instructions))` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  qspecl_then [`fuel`,`C7`,`root_sf`,`root_entry`] mp_tac focus_initial_singleton_cut >>
  disch_then (qspecl_then [`bb`,`[]`,`bb.bb_instructions`,`root_entry`,`q`] mp_tac) >>
  impl_tac >- simp[] >>
  ntac 5 (CONV_TAC (LAND_CONV Unwind.UNWIND_FORALL_CONV)) >>
  qpat_assum `Abbrev (row_eval = _)`
    (fn th => pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  map_every (fn v =>
    CONV_TAC (LAND_CONV Unwind.UNWIND_FORALL_CONV) >>
    qpat_assum v
      (fn th => pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
    [`Abbrev (plan_eval = _)`,`Abbrev (call_setup = _)`,`Abbrev (rooted_eval = _)`] >>
  ntac 2 (CONV_TAC (LAND_CONV Unwind.UNWIND_FORALL_CONV)) >>
  disch_then (qspecl_then [`gs`,`tail`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `!i sf plan call. _` kall_tac >>
  `!zs. FLAT (MAP (\i. if i.inst_opcode = GAS then
       [(root_sf.fn_name,i.inst_id)] else []) zs) =
       MAP (\i. (root_sf.fn_name,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) zs) /\
     FLAT (MAP (\i. if i.inst_opcode = GAS then [(([],1,i.inst_id):gas_event)] else []) zs) =
       MAP (\i. (([],1,i.inst_id):gas_event)) (FILTER (\i. i.inst_opcode = GAS) zs)` by
    (Induct >> simp[] >> Cases_on `h.inst_opcode = GAS` >> simp[]) >>
  pure_asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  Cases_on `rooted_eval fuel C7 [(root_sf,[(bb,1,TAKE q bb.bb_instructions)],NONE)]
    (root_entry with vs_gas_readings := gs ++ tail)` >>
  rename1 `(ev,r)` >> Cases_on `r`
  >- (qpat_x_assum `!ev u. _ = (ev,OK u) ==> _` mp_tac >>
      simp_tac (srw_ss()) [] >> strip_tac >>
      fs[dftGasFromListTraceDefsTheory.trace_gas_def] >>
      suspend "cut_observation") >>
  qpat_x_assum `!ev r. _` mp_tac >>
  simp_tac (srw_ss()) []
QED

Resume focus_initial_singleton_packet[cut_observation]:
  conj_tac >- (qexistsl_tac [`before`,`after`] >> simp[]) >>
  strip_tac >>
  `FOLDR (dft_exec_cons (fuel-1) C7) OK (TAKE q bb.bb_instructions)
      (root_entry with vs_gas_readings := gs ++ tail) = OK v` by
    ((qpat_x_assum `!tail'. rooted_eval _ _ _ _ = _` (qspec_then `tail` mp_tac) >>
     simp[Abbr `rooted_eval`, Abbr `plan_eval`, Abbr `row_eval`] >>
     Cases_on `FOLDR (dft_exec_cons (fuel-1) C7) OK (TAKE q bb.bb_instructions)
       ((root_entry with vs_gas_readings := gs ++ tail) with vs_inst_idx := 0)` >>
     simp[] >> (gvs[]))) >>
  `bb.bb_instructions = TAKE q bb.bb_instructions ++
      HD bt.bb_instructions::DROP (SUC q) bb.bb_instructions` by
    metis_tac[TAKE_DROP_SUC, APPEND, APPEND_ASSOC] >>
  `?later. bt.bb_instructions = HD bt.bb_instructions::later` by
    (Cases_on `bt.bb_instructions` >> gvs[get_instruction_def]) >>
  `trace_gas (trace_block [] 1 (fuel-1) C7 root_sf
       (bb with bb_instructions := TAKE q bb.bb_instructions)
       (root_entry with vs_gas_readings := gs ++ tail)) =
     ZIP (MAP (\i. ([],1,i.inst_id))
       (FILTER (\i. i.inst_opcode = GAS) (TAKE q bb.bb_instructions)),gs)` by
    (irule dftGasSourcePrefixTheory.noninvoke_prefix_trace_keys >>
     rpt (first_assum (irule_at Any)) >> simp[EVERY_MEM] >>
     gvs[EVERY_MEM]) >>
  `ALL_DISTINCT (MAP (\i. (([],1,i.inst_id):gas_event))
      (FILTER (\i. i.inst_opcode = GAS) (TAKE q bb.bb_instructions)))` by
    (qpat_x_assum `ALL_DISTINCT (MAP (\i. ([],1,i.inst_id)) (FILTER _ bb.bb_instructions))` mp_tac >>
     qspecl_then [`q`,`bb.bb_instructions`] (fn th =>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) listTheory.TAKE_DROP >>
     simp[FILTER_APPEND_DISTRIB, MAP_APPEND, ALL_DISTINCT_APPEND]) >>
  drule_at (Pat `trace_gas source = _`)
    dftGasFromListReplayBoundaryTheory.trace_agrees_lookup_fill >>
  disch_then (qspecl_then [`[]`,`[]`] mp_tac) >>
  simp[EVERY_MEM, dftGasFromListTraceDefsTheory.trace_gas_def] >>
  strip_tac >>
  irule (Q.INST [`ps` |-> `[]`, `scheduled` |-> `[]`,
    `post` |-> `DROP (SUC q) bb.bb_instructions`, `be` |-> `root_entry`]
    (SPEC_ALL dft_packet_native_observation_success)) >>
  simp[] >> rpt (first_assum (irule_at Any)) >>
  qexistsl_tac [`fuel-1`,`q`] >>
  simp[TAKE_TAKE] >>
  qpat_assum `trace_agrees _ (trace_block _ _ _ _ _ _ _)` (irule_at Any) >>
  simp[Once dftGasFromListTraceDefsTheory.trace_defs, get_instruction_def,
    dftGasFromListTraceDefsTheory.trace_agrees_def,
    dftGasFromListTraceDefsTheory.trace_gas_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qpat_assum `bb.bb_instructions = TAKE _ _ ++ _` (fn th =>
    qpat_assum `EVERY (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions`
      (mp_tac o PURE_ONCE_REWRITE_RULE [th])) >>
  simp_tac (srw_ss()) [EVERY_APPEND, EVERY_DEF] >> strip_tac >>
  qpat_assum `bb.bb_instructions = TAKE _ _ ++ _` (fn th =>
    pure_rewrite_tac[GSYM th]) >> simp[] >>
  metis_tac[APPEND, APPEND_ASSOC]
QED

Finalise focus_initial_singleton_packet
