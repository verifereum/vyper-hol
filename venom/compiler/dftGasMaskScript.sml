(* One finite upper mask covers every compatible terminating source filling.
   The internal-return clause exposes complete consumption for composition. *)
Theory dftGasMask
Ancestors
  dftGasOracleSim dftGasSimFuel dftGasFromListRestore dftGasToListReplay
  dftRunRel dftDefs o1PassContract gasEvents gasCount
  venomExecSemantics venomState list rich_list sorting option

Theorem gas_events_invoke_update_var[local]:
  i.inst_opcode = INVOKE /\
  (!v. MEM (Var v) i.inst_operands ==> out <> v) ==>
  gas_events_step fuel C owner i (update_var out value s) =
  gas_events_step fuel C owner i s
Proof
  rpt strip_tac >> simp[gas_events_step_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rename1 `decode_invoke i = SOME decoded` >>
  PairCases_on `decoded` >> simp[] >>
  `i.inst_operands = Label decoded0 :: decoded1`
    by (gvs[decode_invoke_def] >>
        Cases_on `i.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  `eval_operands decoded1 (update_var out value s) = eval_operands decoded1 s`
    by (irule dftCommutationTheory.eval_operands_update_var >> rw[] >> gvs[MEM]) >>
  simp[dftCommutationTheory.setup_callee_update_var]
QED

Theorem gas_events_invoke_updates[local]:
  !us s.
  i.inst_opcode = INVOKE /\
  EVERY (\q. !v. MEM (Var v) i.inst_operands ==> FST q <> v) us ==>
  gas_events_step fuel C owner i
    (FOLDL (\u q. update_var (FST q) (SND q) u) s us) =
  gas_events_step fuel C owner i s
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >>
  irule gas_events_invoke_update_var >> simp[]
QED

(* A stopped extracted head cannot cross an unexecuted call. *)
Theorem stopped_head_no_crossed_invoke[local]:
  dft_gas_swap_pair x y /\
  (ev_step orc p d fuel C y s = Halt t \/
   ev_step orc p d fuel C y s = Abort a t) ==>
  x.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac
  >- (`~is_terminator y.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
      `y.inst_opcode = INVOKE` by
        metis_tac[dftGasSimLocalBoundaryTheory.ev_step_nonterminator_halt_invoke] >>
      drule_all dft_swap_invoke_partner_class >>
      simp[venomEffectsTheory.opcode_fail_class_def]) >>
  metis_tac[dftGasSimSwapStopTheory.ev_invoke_partner_no_abort]
QED

(* A continuation contributes sites only after the first segment is exact. *)
Theorem mask_prefix_after_exact[local]:
  s1 = e1 /\ (?extra. s2 = e2 ++ extra) ==>
  ?extra. s1 ++ s2 = (e1 ++ e2) ++ extra
Proof
  strip_tac >> gvs[] >> simp[APPEND_ASSOC]
QED

Theorem mask_prefix_extend[local]:
  (?extra. s1 = e1 ++ extra) ==>
  ?extra. s1 ++ s2 = e1 ++ extra
Proof
  strip_tac >> gvs[] >> simp[APPEND_ASSOC]
QED

Theorem noninvoke_block_events_prefix[local]:
  !fuel C owner bb s.
    EVERY (\i. i.inst_opcode <> INVOKE)
      (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?extra.
      MAP (\i. (owner,i.inst_id))
        (FILTER (\i. i.inst_opcode = GAS)
          (DROP s.vs_inst_idx bb.bb_instructions)) =
      gas_events_block fuel C owner bb s ++ extra
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions`
  >- (drule rich_listTheory.DROP_CONS_EL >>
      disch_then (fn th => fs[th]) >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
           gas_events_step_def] >>
      Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
      simp[] >>
      Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS` >>
      simp[] >>
      Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
      simp[] >>
      first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
      simp[] >>
      disch_then (qspec_then `v' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[] >> gvs[]) >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def, DROP_EQ_NIL]
QED

Theorem gas_events_block_suffix_cong[local]:
  !xs s bb bb'.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    DROP s.vs_inst_idx bb'.bb_instructions = xs ==>
    gas_events_block fuel C owner bb s = gas_events_block fuel C owner bb' s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`LENGTH bb.bb_instructions <= s.vs_inst_idx /\
       LENGTH bb'.bb_instructions <= s.vs_inst_idx` by
        gvs[DROP_EQ_NIL] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   s.vs_inst_idx < LENGTH bb'.bb_instructions` by
    (qpat_x_assum `DROP _ bb.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     qpat_x_assum `DROP _ bb'.bb_instructions = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   EL s.vs_inst_idx bb'.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs /\
   DROP (SUC s.vs_inst_idx) bb'.bb_instructions = xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[venomInstTheory.get_instruction_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  Cases_on `is_terminator h.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[] >>
  fs[rich_listTheory.DROP_CONS_EL]
QED

Theorem noninvoke_prefix_events_continue[local]:
  !pre s bb xs upper.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ xs /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    (!u. FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
         ?extra. upper = gas_events_block fuel C owner bb u ++ extra) ==>
    ?extra.
      MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++ upper =
      gas_events_block fuel C owner bb s ++ extra
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> first_x_assum (qspec_then `s` mp_tac) >> simp[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF] >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       gas_events_step_def] >>
  Cases_on `step_inst fuel C h s`
  >- (`?extra.
        MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++ upper =
        gas_events_block fuel C owner bb (v with vs_inst_idx := SUC s.vs_inst_idx) ++ extra`
        by (first_x_assum irule >> simp[] >> rpt strip_tac >>
            first_x_assum irule >> simp[dftIndexedExecTheory.dft_exec_cons_def]) >>
      Cases_on `h.inst_opcode = GAS` >> gvs[] >> metis_tac[]) >>
  Cases_on `h.inst_opcode = GAS` >> simp[]
QED

Theorem prefix_ok_cursor[local]:
  !pre s u.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH pre
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  fs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem noninvoke_prefix_events_family[local]:
  !pre s xs upper.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    (!u. FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
      ?extra. upper = gas_events_block fuel C owner
        <|bb_label := owner; bb_instructions :=
          REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> u ++ extra) ==>
    ?extra.
      MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++ upper =
      gas_events_block fuel C owner
        <|bb_label := owner; bb_instructions :=
          REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ xs)|> s ++ extra
Proof
  rpt strip_tac >> irule noninvoke_prefix_events_continue >>
  (reverse conj_tac >- simp[DROP_APPEND]) >> rpt strip_tac >>
  `u.vs_inst_idx = s.vs_inst_idx + LENGTH pre` by
    (irule prefix_ok_cursor >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `gas_events_block fuel C owner
     <|bb_label := owner; bb_instructions :=
       REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ xs)|> u =
   gas_events_block fuel C owner
     <|bb_label := owner; bb_instructions :=
       REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> u` by
    (irule gas_events_block_suffix_cong >> qexists_tac `xs` >>
     simp[DROP_APPEND, DROP_DROP_T]) >>
  gvs[]
QED

(* Fixed-reference diagnostic interface.  Neither the focus mask nor its
   upper sites may be chosen after pg, fg, tail, or u.  The second premise
   is an obligation on a reached-state family, NOT an existence claim. *)
Theorem stopped_focus_prefix_family[local]:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
  (!pg fg tail u.
    LENGTH pg = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) focus_slots fg /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := pg ++ fg ++ tail) = OK u ==>
    (?extra. focus_sites = gas_events_step fuel C owner y u ++ extra) /\
    (!v. step_inst fuel C y u <> OK v)) ==>
  !pg fg tail.
    LENGTH pg = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) focus_slots fg ==>
    ?extra.
      MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
        focus_sites =
      gas_events_block fuel C owner
        <|bb_label := owner; bb_instructions :=
          REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ y::post)|>
        (s with vs_gas_readings := pg ++ fg ++ tail) ++ extra
Proof
  rpt strip_tac >>
  qspecl_then [`pre`, `s with vs_gas_readings := pg ++ fg ++ tail`,
                `y::post`, `focus_sites`] mp_tac noninvoke_prefix_events_family >>
  simp[] >> disch_then irule >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       EL_APPEND_EQN] >>
  Cases_on `step_inst fuel C y u` >> gvs[]
QED

Theorem noninvoke_block_padding_mask[local]:
  EVERY (\i. i.inst_opcode <> INVOKE)
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  sites = MAP (\i. (owner,i.inst_id))
    (FILTER (\i. i.inst_opcode = GAS)
      (DROP s.vs_inst_idx bb.bb_instructions)) ==>
  ?raw_slots.
    LENGTH raw_slots = LENGTH sites /\
    MAP THE (FILTER IS_SOME raw_slots) = [] /\
    !gobs tail.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
      ?extra. sites = gas_events_block fuel C owner bb
        (s with vs_gas_readings := gobs ++ tail) ++ extra
Proof
  strip_tac >> qexists_tac `REPLICATE (LENGTH sites) NONE` >>
  simp[LENGTH_REPLICATE, FILTER_EQ_NIL, MEM_REPLICATE] >>
  rpt strip_tac >> gvs[] >>
  qspec_then `s with vs_gas_readings := gobs ++ tail` mp_tac
    (Q.SPECL [`fuel`, `C`, `owner`, `bb`] noninvoke_block_events_prefix) >>
  simp[]
QED

Theorem invoke_partner_concrete_updates[local]:
  dft_gas_swap_pair x y /\ y.inst_opcode = INVOKE /\ inst_wf x /\
  step_inst fuel C x s = OK t ==>
  ?us. EVERY (\q. MEM (FST q) x.inst_outputs /\
                   !v. MEM (Var v) y.inst_operands ==> FST q <> v) us /\
    t = FOLDL (\st q. update_var (FST q) (SND q) st)
      (s with vs_gas_readings :=
        DROP (if x.inst_opcode = GAS then 1 else 0) s.vs_gas_readings) us
Proof
  strip_tac >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> strip_tac >>
  Cases_on `x.inst_opcode = GAS`
  >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
      qexists_tac `[(x',case s.vs_gas_readings of [] => 0w | h::tl => h)]` >>
      simp[] >> metis_tac[dft_independent_gas_output]) >>
  `step_inst_base x s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all dftBlockSimTheory.pure_step_structure >> strip_tac >>
  qexists_tac `pairs` >>
  conj_tac
  >- (qpat_assum `dft_gas_swap_pair x y`
        (mp_tac o MATCH_MP dft_swap_output_frame) >>
      strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
      `MEM (FST q) x.inst_outputs` by
        (qpat_x_assum `MAP FST pairs = _` (SUBST1_TAC o SYM) >>
         simp[MEM_MAP] >> metis_tac[]) >>
      metis_tac[]) >>
  simp[pairTheory.LAMBDA_PROD]
QED

Theorem updates_readings_cursor[local]:
  !us s gs idx.
    (FOLDL (\st q. update_var (FST q) (SND q) st) s us)
      with <|vs_inst_idx := idx; vs_gas_readings := gs|> =
    FOLDL (\st q. update_var (FST q) (SND q) st)
      (s with <|vs_inst_idx := idx; vs_gas_readings := gs|>) us
Proof
  Induct >> simp[] >> rpt gen_tac >>
  gvs[update_var_def]
QED

Theorem invoke_partner_prefix_concrete[local]:
  !pre s pg rest u.
    y.inst_opcode = INVOKE /\
    EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x) pre /\
    LENGTH pg = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := pg ++ rest) = OK u ==>
    ?us.
      EVERY (\q. MEM (FST q) (FLAT (MAP (\x. x.inst_outputs) pre)) /\
        !v. MEM (Var v) y.inst_operands ==> FST q <> v) us /\
      u = FOLDL (\st q. update_var (FST q) (SND q) st)
        (s with <|vs_gas_readings := rest;
                   vs_inst_idx := s.vs_inst_idx + LENGTH pre|>) us
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[venom_state_component_equality] >>
  fs[EVERY_DEF] >>
  `~is_terminator h.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
  fs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := pg ++ rest)` >>
  gvs[] >>
  `?pg'. LENGTH pg' = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
    v.vs_gas_readings = pg' ++ rest` by
    (Cases_on `h.inst_opcode = GAS`
     >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
         Cases_on `pg` >> gvs[update_var_def]) >>
     `h.inst_opcode <> INVOKE` by
       (strip_tac >> gvs[dft_gas_swap_pair_def,
          venomEffectsTheory.effects_independent_def,
          venomEffectsTheory.write_effects_def,
          venomEffectsTheory.all_effects_def,
          venomEffectsTheory.empty_effects_def]) >>
     drule_all dft_nonconsuming_ok_readings >> strip_tac >>
     qexists_tac `pg` >> gvs[]) >>
  drule_all invoke_partner_concrete_updates >>
  disch_then (qx_choose_then `hs` strip_assume_tac) >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `pg'`, `rest`, `u`] mp_tac) >>
  simp[NoAsms] >>
  (impl_tac >-
    (qpat_x_assum `v = _` kall_tac >>
     `v with vs_gas_readings := pg' ++ rest = v` by
       (simp[venom_state_component_equality]) >>
     gvs[])) >>
  disch_then (qx_choose_then `ts` strip_assume_tac) >>
  qexists_tac `hs ++ ts` >>
  conj_tac
  >- (gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  gvs[updates_readings_cursor, FOLDL_APPEND, arithmeticTheory.ADD_CLAUSES]
QED

Theorem noninvoke_prefix_events_exact_at[local]:
  !pre s bb xs u.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ xs /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    gas_events_block fuel C owner bb s =
    MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
    gas_events_block fuel C owner bb u
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       gas_events_step_def] >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `xs`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS` >> gvs[]
QED

Theorem noninvoke_prefix_events_exact[local]:
  !pre s u xs.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ xs)|> s =
    MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> u
Proof
  rpt strip_tac >>
  `u.vs_inst_idx = s.vs_inst_idx + LENGTH pre` by
    (irule prefix_ok_cursor >> simp[] >> fs[EVERY_MEM] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `gas_events_block fuel C owner bb s` >>
  `gas_events_block fuel C owner bb s =
   MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
   gas_events_block fuel C owner bb u` by
    (irule noninvoke_prefix_events_exact_at >>
     simp[Abbr `bb`, DROP_APPEND]) >>
  `gas_events_block fuel C owner bb u =
   gas_events_block fuel C owner
     <|bb_label := owner; bb_instructions :=
       REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> u` by
    (irule gas_events_block_suffix_cong >> qexists_tac `xs` >>
     simp[Abbr `bb`, DROP_APPEND, DROP_DROP_T]) >>
  gvs[]
QED

Theorem noninvoke_prefix_readings_exact[local]:
  !pre s pg rest u.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    LENGTH pg = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := pg ++ rest) = OK u ==>
    u.vs_gas_readings = rest
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := pg ++ rest)` >> gvs[] >>
  `?pg'. LENGTH pg' = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
    v.vs_gas_readings = pg' ++ rest` by
    (Cases_on `h.inst_opcode = GAS`
     >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
         Cases_on `pg` >> gvs[update_var_def]) >>
     drule_all dft_nonconsuming_ok_readings >> strip_tac >>
     qexists_tac `pg` >> gvs[]) >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `pg'`, `rest`, `u`] mp_tac) >>
  simp[NoAsms] >> disch_then irule >>
  `v with vs_gas_readings := pg' ++ rest = v` by
    simp[venom_state_component_equality] >> gvs[]
QED

Theorem dft_blocks_gas_mask:
  !fuel C C' fn fn' s.
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
    dft_fn_rel fn fn' /\ strict_dom_vars_defined fn s /\
    fn_reachable fn s.vs_current_bb /\
    ctx_labels_bound C s.vs_labels /\
    ctx_labels_bound C' s.vs_labels /\ ~s.vs_call_ctx.cc_static /\
    terminates (run_blocks fuel C' fn' s) /\
    gas_count_blocks fuel C' fn' s <= LENGTH s.vs_gas_readings
    ==>
    ?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) s.vs_gas_readings /\
      (!t.
        (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
        EVERY IS_SOME raw_slots /\ unused = t.vs_gas_readings) /\
      !gobs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots gobs ==>
        (?extra.
          sites = gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) ++ extra) /\
        ((?fuel_src. terminates
          (run_blocks fuel_src C fn (s with vs_gas_readings := gobs ++ tail)))
         ==>
        terminates
          (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)) /\
        dft_res_rel
          (restore_result []
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail)))
          (restore_result [] (run_blocks fuel C' fn' s)) /\
        (!t.
          (?ir. run_blocks fuel C' fn' s = IntRet ir t) ==>
          gas_events_blocks fuel C fn
            (s with vs_gas_readings := gobs ++ tail) = sites /\
          residual_result tail (run_blocks fuel C' fn' s)
            (run_blocks fuel C fn (s with vs_gas_readings := gobs ++ tail))))
Proof
  cheat
QED
