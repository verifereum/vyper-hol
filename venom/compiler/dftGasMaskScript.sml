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

(* The crossed spine in a head extraction need not be call-free. *)
Theorem gas_head_crosses_invoke[local]:
  dft_gas_swap_pair
    (mk_inst 1 INVOKE [Label "callee"] [])
    (mk_inst 2 GAS [] ["g"])
Proof
  EVAL_TAC >> simp[]
QED

Theorem invoke_updates_concrete_frame[local]:
  !updates s.
  EVERY (\uw. ~MEM (Var (FST uw)) i.inst_operands /\
               ~MEM (FST uw) i.inst_outputs) updates /\
  i.inst_opcode = INVOKE ==>
  step_inst fuel C i
    (FOLDL (\st uw. update_var (FST uw) (SND uw) st) s updates) =
  (case step_inst fuel C i s of
     OK t => OK (FOLDL (\st uw. update_var (FST uw) (SND uw) st) t updates)
   | Halt t => Halt t | Abort a t => Abort a t
   | IntRet vals t => IntRet vals t | Error e => Error e)
Proof
  Induct >- (simp[] >> rpt strip_tac >>
    Cases_on `step_inst fuel C i s` >> simp[]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[] >>
  `step_inst fuel C i (update_var (FST h) (SND h) s) =
   (case step_inst fuel C i s of
      OK t => OK (update_var (FST h) (SND h) t)
    | Halt t => Halt t | Abort a t => Abort a t
    | IntRet vals t => IntRet vals t | Error e => Error e)`
    by (irule dftCommutationTheory.step_inst_invoke_frame >> metis_tac[]) >>
  simp[] >> Cases_on `step_inst fuel C i s` >> simp[]
QED

Theorem invoke_return_gas_frame[local]:
  !out outs ir w s j rs t v gs tail.
    ~MEM out outs /\
    bind_outputs outs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state
        (update_var out w s with <|vs_inst_idx := j; vs_gas_readings := rs|>) t)) = SOME v ==>
    ?b. bind_outputs outs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state
        (s with vs_gas_readings := gs) (t with vs_gas_readings := w::tail))) = SOME b /\
      b.vs_inst_idx = s.vs_inst_idx /\ b.vs_gas_readings = w::tail /\
      (update_var out w b with <|vs_inst_idx := j; vs_gas_readings := tail|>) =
      (v with vs_gas_readings := tail)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `retbase = adopt_return_fmp ir (merge_callee_state s t)` >>
  `adopt_return_fmp ir (merge_callee_state
      (update_var out w s with <|vs_inst_idx := j; vs_gas_readings := rs|>) t) =
      update_var out w retbase with vs_inst_idx := j` by
    (Cases_on `ir.iret_adopt_fmp` >>
     simp[Abbr `retbase`, adopt_return_fmp_def, merge_callee_state_def, update_var_def]) >>
  `adopt_return_fmp ir (merge_callee_state
      (s with vs_gas_readings := gs) (t with vs_gas_readings := w::tail)) =
      retbase with vs_gas_readings := w::tail` by
    (Cases_on `ir.iret_adopt_fmp` >>
     simp[Abbr `retbase`, adopt_return_fmp_def, merge_callee_state_def]) >>
  qpat_x_assum `bind_outputs _ _ _ = SOME v` mp_tac >>
  simp[bind_outputs_idx, dftCommutationTheory.bind_outputs_update_var] >>
  Cases_on `bind_outputs outs ir.iret_values retbase` >> simp[] >> strip_tac >>
  drule bind_outputs_inst_idx >>
  simp[Abbr `retbase`, merge_callee_state_inst_idx] >> strip_tac >>
  qexists_tac `x with vs_gas_readings := w::tail` >>
  simp[gasOracleReplayTheory.gas_bind_outputs, update_var_def]
QED

(* Bounded operational probe: a returning call is one variable-length
   segment, followed by the delayed GAS.  The only mask premise below is
   the blocks induction hypothesis at the actual callee entry. *)
Theorem invoke_gas_mask[local]:
  !fuel C C' x y s w rs name ops args f f' cs ir t u.
    x.inst_opcode = INVOKE /\ y.inst_opcode = GAS /\
    dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
    s.vs_gas_readings = w::rs /\
    decode_invoke x = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME f /\
    lookup_function name C'.ctx_functions = SOME f' /\
    dft_fn_rel f f' /\ eval_operands ops s = SOME args /\
    setup_callee f args (s with vs_gas_readings := rs) = SOME cs /\
    run_blocks fuel C' f' cs = IntRet ir t /\
    FOLDR (dft_exec_cons fuel C') OK [y;x] s = OK u /\
    (?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) cs.vs_gas_readings /\
      (!t0. (?ir0. run_blocks fuel C' f' cs = IntRet ir0 t0) ==>
        EVERY IS_SOME raw_slots /\ unused = t0.vs_gas_readings) /\
      !gobs tail.
        LIST_REL (\slot w0. slot = NONE \/ slot = SOME w0) raw_slots gobs ==>
        (?extra. sites = gas_events_blocks fuel C f
          (cs with vs_gas_readings := gobs ++ tail) ++ extra) /\
        ((?fuel_src. terminates (run_blocks fuel_src C f
          (cs with vs_gas_readings := gobs ++ tail))) ==>
          terminates (run_blocks fuel C f
            (cs with vs_gas_readings := gobs ++ tail)) /\
          dft_res_rel
            (restore_result [] (run_blocks fuel C f
              (cs with vs_gas_readings := gobs ++ tail)))
            (restore_result [] (run_blocks fuel C' f' cs)) /\
          (!t0. (?ir0. run_blocks fuel C' f' cs = IntRet ir0 t0) ==>
            gas_events_blocks fuel C f
              (cs with vs_gas_readings := gobs ++ tail) = sites /\
            residual_result tail (run_blocks fuel C' f' cs)
              (run_blocks fuel C f
                (cs with vs_gas_readings := gobs ++ tail))))) ==>
    ?m es unused.
      LENGTH m = LENGTH es /\
      PERM (MAP THE (FILTER IS_SOME m) ++ unused) rs /\
      EVERY IS_SOME m /\ unused = u.vs_gas_readings /\
      !gobs tail.
        LIST_REL (\slot w0. slot = NONE \/ slot = SOME w0)
          (m ++ [SOME w]) gobs ==>
        (?extra. es ++ [(s.vs_current_bb,y.inst_id)] =
          gas_events_block fuel C s.vs_current_bb
            <|bb_label := s.vs_current_bb; bb_instructions :=
              REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ [x;y]|>
            (s with vs_gas_readings := gobs ++ tail) ++ extra) /\
        ((?fuel_src. terminates
          (FOLDR (dft_exec_cons fuel_src C) OK [x;y]
            (s with vs_gas_readings := gobs ++ tail))) ==>
          terminates (FOLDR (dft_exec_cons fuel C) OK [x;y]
            (s with vs_gas_readings := gobs ++ tail)) /\
          dft_res_rel
            (restore_result [] (FOLDR (dft_exec_cons fuel C) OK [x;y]
              (s with vs_gas_readings := gobs ++ tail)))
            (restore_result [] (OK u)) /\
          gas_events_block fuel C s.vs_current_bb
            <|bb_label := s.vs_current_bb; bb_instructions :=
              REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ [x;y]|>
            (s with vs_gas_readings := gobs ++ tail) =
              es ++ [(s.vs_current_bb,y.inst_id)] /\
          residual_result tail (OK u)
            (FOLDR (dft_exec_cons fuel C) OK [x;y]
              (s with vs_gas_readings := gobs ++ tail)))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY IS_SOME raw_slots /\ unused = t.vs_gas_readings` by metis_tac[] >>
  `cs.vs_gas_readings = rs` by
    (drule gasOracleReplayTheory.gas_setup_callee_readings >> simp[]) >>
  `?out. y.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf y` mp_tac >>
     simp[venomWfTheory.inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `~MEM (Var out) x.inst_operands /\ ~MEM out x.inst_outputs` by
    (qpat_x_assum `dft_gas_swap_pair x y` mp_tac >>
     simp[dft_gas_swap_pair_def, venomInstTheory.inst_defs_def,
          venomInstTheory.inst_uses_def, pred_setTheory.DISJOINT_DEF,
          pred_setTheory.EXTENSION] >>
     metis_tac[dftBlockSimTheory.mem_var_operand_vars]) >>
  `?v. step_inst fuel C' x
      (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                 vs_gas_readings := rs|>) = OK v /\
        u = v with vs_inst_idx := SUC (SUC s.vs_inst_idx)` by
    (qpat_x_assum `FOLDR _ _ [y;x] s = OK u` mp_tac >>
     simp[dftIndexedExecTheory.dft_exec_cons_def, Once step_inst_def,
          step_inst_base_def, exec_gas_def, venomInstTheory.is_terminator_def] >>
     Cases_on `step_inst fuel C' x
       (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                  vs_gas_readings := rs|>)` >> simp[]) >>
  `setup_callee f' args
     (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                vs_gas_readings := rs|>) = SOME cs` by
    (drule dft_fn_rel_setup_callee >> disch_then (fn th => rewrite_tac[th]) >>
     qpat_x_assum `setup_callee f args _ = SOME cs` (SUBST1_TAC o SYM) >>
     simp[setup_callee_def, update_var_def]) >>
  `eval_operands ops
     (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                vs_gas_readings := rs|>) = SOME args` by
    (`x.inst_operands = Label name :: ops` by
       (gvs[decode_invoke_def] >> Cases_on `x.inst_operands` >> gvs[] >>
        Cases_on `h` >> gvs[]) >>
     `eval_operands ops (update_var out w s) = SOME args` by
       (gvs[dftCommutationTheory.eval_operands_update_var]) >>
     `!os. eval_operands os
         (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                    vs_gas_readings := rs|>) =
           eval_operands os (update_var out w s)` by
       (Induct >> simp[eval_operands_def] >> Cases_on `h` >>
        simp[eval_operand_def, lookup_var_def]) >>
     simp[]) >>
  `bind_outputs x.inst_outputs ir.iret_values
     (adopt_return_fmp ir (merge_callee_state
       (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                  vs_gas_readings := rs|>) t)) = SOME v` by
    (qpat_x_assum `step_inst fuel C' x _ = OK v` mp_tac >>
     simp[Once step_inst_def] >>
     Cases_on `bind_outputs x.inst_outputs ir.iret_values
       (adopt_return_fmp ir (merge_callee_state
         (update_var out w s with <|vs_inst_idx := SUC s.vs_inst_idx;
                                    vs_gas_readings := rs|>) t))` >> simp[]) >>
  `u.vs_gas_readings = t.vs_gas_readings` by
    (drule gasOracleReplayTheory.gas_bind_outputs_readings >>
     simp[gasOracleReplayTheory.gas_adopt_return_readings]) >>
  qexistsl_tac [`raw_slots`, `sites`, `unused`] >>
  gvs[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `LIST_REL _ (_ ++ _) gobs` mp_tac >>
  simp[LIST_REL_SPLIT1] >> strip_tac >> gvs[] >>
  rename1 `LIST_REL _ raw_slots pg` >>
  first_x_assum (qspecl_then [`pg`, `w::tail`] mp_tac) >>
  simp[] >> strip_tac >>
  `eval_operands ops (s with vs_gas_readings := pg ++ w::tail) = SOME args` by
    (simp[gasOracleReplayTheory.gas_eval_operands]) >>
  `setup_callee f args (s with vs_gas_readings := pg ++ w::tail) =
     SOME (cs with vs_gas_readings := pg ++ w::tail)` by
    (qpat_x_assum `setup_callee f args _ = SOME cs` mp_tac >>
     simp[gasOracleReplayTheory.gas_setup_callee, optionTheory.OPTION_MAP_EQ_SOME] >>
     strip_tac >> gvs[] >>
     qpat_x_assum `cs = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  qabbrev_tac `gs = pg ++ w::tail` >>
  conj_tac >- (
    simp[Once gas_events_block_def, venomInstTheory.get_instruction_def, EL_APPEND_EQN,
         Excl "APPEND_ASSOC"] >>
    simp[gas_events_step_def, venomInstTheory.is_terminator_def, Excl "APPEND_ASSOC"] >>
    Cases_on `run_blocks fuel C f (cs with vs_gas_readings := gs)` >>
    simp[Once step_inst_def, Excl "APPEND_ASSOC"] >>
    pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
    asm_rewrite_tac[] >>
    simp[]
    >~ [`run_blocks fuel C f _ = IntRet ret ct`]
    >- (`?fuel_src. terminates (run_blocks fuel_src C f
          (cs with vs_gas_readings := gs))` by
          (qexists_tac `fuel` >> simp[passSimulationDefsTheory.terminates_def]) >>
        qpat_x_assum `(?fuel_src. _) ==> _` mp_tac >>
        (impl_tac >- metis_tac[]) >> strip_tac >>
        qpat_x_assum `residual_result _ _ _` mp_tac >>
        simp[residual_result_def, stateEquivTheory.lift_result_def] >> strip_tac >>
        Cases_on `bind_outputs x.inst_outputs ret.iret_values
          (adopt_return_fmp ret (merge_callee_state
            (s with vs_gas_readings := gs)
            (t with vs_gas_readings := w::tail)))` >>
        simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
             EL_APPEND_EQN, gas_events_step_def,
             venomInstTheory.is_terminator_def] >>
        `extra = []` by metis_tac[APPEND_11, APPEND_NIL] >>
        Cases_on `step_inst fuel C y (x' with vs_inst_idx := SUC s.vs_inst_idx)` >>
        simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
    qexists_tac `extra ++ [(s.vs_current_bb,y.inst_id)]` >> simp[]) >>
  strip_tac >>
  `?n. terminates (run_blocks n C f (cs with vs_gas_readings := gs))` by
    (qexists_tac `fuel_src` >>
     qpat_x_assum `terminates (dft_exec_cons _ _ _ _ _)` mp_tac >>
     simp[dftIndexedExecTheory.dft_exec_cons_def, Once step_inst_def] >>
     Cases_on `run_blocks fuel_src C f (cs with vs_gas_readings := gs)` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `(?fuel_src. _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qpat_x_assum `residual_result _ _ _`
    (assume_tac o REWRITE_RULE [residual_result_def]) >>
  Cases_on `run_blocks fuel C f (cs with vs_gas_readings := gs)` >>
  qpat_x_assum `lift_result _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [stateEquivTheory.lift_result_def]) >>
  qpat_x_assum `ir = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = t with vs_gas_readings := _` SUBST_ALL_TAC >>
  drule_all invoke_return_gas_frame >>
  disch_then (qspecl_then [`gs`, `tail`] strip_assume_tac) >>
  `step_inst fuel C x (s with vs_gas_readings := gs) = OK b` by
    (simp[Once step_inst_def]) >>
  `step_inst fuel C y (b with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (update_var out w b with <|vs_inst_idx := SUC s.vs_inst_idx;
                                  vs_gas_readings := tail|>)` by
    (simp[Once step_inst_def, step_inst_base_def, exec_gas_def, update_var_def] >>
     first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [update_var_def])) >>
  `dft_exec_cons fuel C x (dft_exec_cons fuel C y OK)
      (s with vs_gas_readings := gs) =
    OK (v with <|vs_inst_idx := SUC (SUC s.vs_inst_idx);
                 vs_gas_readings := tail|>)` by
    simp[dftIndexedExecTheory.dft_exec_cons_def, venomInstTheory.is_terminator_def] >>
  qpat_x_assum `dft_exec_cons fuel C x _ _ = _`
    (fn th => rewrite_tac[th]) >>
  conj_tac >- simp[passSimulationDefsTheory.terminates_def] >>
  conj_tac >- simp[restore_result_def, dft_res_rel_def] >>
  qpat_x_assum `sites = _ ++ extra` kall_tac >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       EL_APPEND_EQN, gas_events_step_def, venomInstTheory.is_terminator_def,
       Excl "APPEND_ASSOC"] >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       EL_APPEND_EQN, gas_events_step_def, venomInstTheory.is_terminator_def] >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]
QED

Theorem prefix_events_splice[local]:
  !pre s bb xs u.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dft_exec_cons fuel C) OK pre s = OK u ==>
    gas_events_block fuel C owner bb s =
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|> s ++
    gas_events_block fuel C owner bb u
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF] >>
  qpat_x_assum `dft_exec_cons _ _ _ _ _ = _` mp_tac >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `xs`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN, APPEND_ASSOC] >>
  pure_rewrite_tac[GSYM venomInstTheory.get_instruction_def] >>
  pure_once_rewrite_tac[GSYM gas_events_block_def] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  irule gas_events_block_suffix_cong >> qexists_tac `pre` >>
  simp[DROP_APPEND, DROP_DROP_T, arithmeticTheory.ADD1]
QED

Theorem prefix_events_stopped[local]:
  !pre s bb xs.
    DROP s.vs_inst_idx bb.bb_instructions = pre ++ xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    (~?u. FOLDR (dft_exec_cons fuel C) OK pre s = OK u) ==>
    gas_events_block fuel C owner bb s =
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|> s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre ++ xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF] >>
  once_rewrite_tac[gas_events_block_def] >>
  simp[venomInstTheory.get_instruction_def, EL_APPEND_EQN, APPEND_ASSOC] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  `gas_events_block fuel C owner bb (v with vs_inst_idx := SUC s.vs_inst_idx) =
   gas_events_block fuel C owner
     <|bb_label := owner; bb_instructions :=
       REPLICATE (SUC s.vs_inst_idx) (mk_inst 0 STOP [] []) ++ pre|>
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (first_x_assum (qspecl_then
       [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `xs`] mp_tac) >>
     simp[] >> disch_then irule >>
     qpat_x_assum `!u. dft_exec_cons _ _ _ _ _ <> _` mp_tac >>
     simp[dftIndexedExecTheory.dft_exec_cons_def]) >>
  pop_assum SUBST1_TAC >>
  irule gas_events_block_suffix_cong >> qexists_tac `pre` >>
  simp[DROP_APPEND, DROP_DROP_T, arithmeticTheory.ADD1]
QED

Theorem prefix_independent_update_ok[local]:
  !pre s out w u.
    EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
      ~MEM out i.inst_outputs) pre ==>
    (FOLDR (dft_exec_cons fuel C) OK pre (update_var out w s) = OK u <=>
     ?v. FOLDR (dft_exec_cons fuel C) OK pre s = OK v /\
         u = update_var out w v)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (simp[] >> metis_tac[]) >>
  fs[EVERY_DEF] >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (mp_tac (Q.SPECL [`fuel`, `C`, `h`, `s`]
        dftCommutationTheory.step_inst_invoke_frame) >>
      disch_then (qspecl_then [`out`, `w`] mp_tac) >> simp[] >> strip_tac >>
      simp[dftIndexedExecTheory.dft_exec_cons_def] >>
      Cases_on `step_inst fuel C h s` >>
      simp[dftCommutationTheory.map_result_state_def] >>
      first_x_assum (qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `u`] mp_tac) >>
      simp[update_var_def]) >>
  mp_tac (Q.SPECL [`fuel`, `C`, `h`, `s`]
    dftCommutationTheory.step_inst_frame) >>
  disch_then (qspecl_then [`out`, `w`] mp_tac) >> simp[] >> strip_tac >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >>
      Cases_on `step_inst fuel C h s` >>
      simp[dftCommutationTheory.map_result_state_def] >>
      first_x_assum (qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `u`] mp_tac) >>
      simp[update_var_def]
QED

(* An actual OK cut itself witnesses termination at the current fuel.
   Its exact-successor premise can therefore be obtained from the conditional
   residual clause using terminates_def and residual_result_cases, even when
   a later segment errors.  Both segment certificates are fixed before fills. *)
Theorem mask_exact_cut_prefix[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  (!pg rest.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m1 pg ==>
    (?extra. e1 = gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>
      (s with vs_gas_readings := pg ++ rest) ++ extra) /\
    (!v. FOLDR (dft_exec_cons fuel C) OK pre
        (s with vs_gas_readings := pg ++ rest) = OK v ==>
      gas_events_block fuel C owner
        <|bb_label := owner; bb_instructions :=
          REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ pre|>
        (s with vs_gas_readings := pg ++ rest) = e1 /\
      v = u with vs_gas_readings := rest)) /\
  (!qg tail.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m2 qg ==>
    ?extra. e2 = gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ post|>
      (u with vs_gas_readings := qg ++ tail) ++ extra) ==>
  !gobs tail.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (m1 ++ m2) gobs ==>
    ?extra. e1 ++ e2 = gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ post)|>
      (s with vs_gas_readings := gobs ++ tail) ++ extra
Proof
  strip_tac >> simp[LIST_REL_SPLIT1] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!pg rest. LIST_REL _ m1 pg ==> _`
    (qspecl_then [`ys1`, `ys2 ++ tail`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_events_block fuel C owner bb st` >>
  Cases_on `?v. FOLDR (dft_exec_cons fuel C) OK pre st = OK v`
  >- (pop_assum strip_assume_tac >>
      `DROP st.vs_inst_idx bb.bb_instructions = pre ++ post` by
        (simp[Abbr `st`, Abbr `bb`] >>
         metis_tac[LENGTH_REPLICATE, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
      drule_all prefix_events_splice >> disch_then (qspec_then `owner` SUBST1_TAC) >>
      qpat_x_assum `!v. _` drule >>
      simp[Abbr `st`] >> strip_tac >> gvs[] >>
      drule_all prefix_ok_cursor >> simp[] >> strip_tac >>
      qpat_x_assum `!qg tail. _`
        (qspecl_then [`ys2`, `tail`] mp_tac) >> simp[] >>
      `gas_events_block fuel C owner bb (u with vs_gas_readings := ys2 ++ tail) =
       gas_events_block fuel C owner
         <|bb_label := owner; bb_instructions :=
           REPLICATE u.vs_inst_idx (mk_inst 0 STOP [] []) ++ post|>
         (u with vs_gas_readings := ys2 ++ tail)` by
        (irule gas_events_block_suffix_cong >> qexists_tac `post` >>
         simp[Abbr `bb`, DROP_APPEND, DROP_DROP_T]) >>
      simp[]) >>
  `DROP st.vs_inst_idx bb.bb_instructions = pre ++ post` by
    (simp[Abbr `st`, Abbr `bb`] >>
         metis_tac[LENGTH_REPLICATE, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  drule_all prefix_events_stopped >> disch_then (qspec_then `owner` SUBST1_TAC) >>
  simp[Abbr `st`] >> irule mask_prefix_extend >> simp[]
QED

Theorem stopped_invoke_fixed_entry_family[local]:
  y.inst_opcode = INVOKE /\
  EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x) pre /\
  (!fg tail.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) focus_slots fg ==>
    (?extra. focus_sites = gas_events_step fuel C owner y
      (s with <|vs_inst_idx := s.vs_inst_idx + LENGTH pre;
                vs_gas_readings := fg ++ tail|>) ++ extra) /\
    (!v. step_inst fuel C y
      (s with <|vs_inst_idx := s.vs_inst_idx + LENGTH pre;
                vs_gas_readings := fg ++ tail|>) <> OK v)) ==>
  !pg fg tail u.
    LENGTH pg = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) focus_slots fg /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := pg ++ fg ++ tail) = OK u ==>
    (?extra. focus_sites = gas_events_step fuel C owner y u ++ extra) /\
    (!v. step_inst fuel C y u <> OK v)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `FOLDR (dft_exec_cons fuel C) OK pre
     (s with vs_gas_readings := pg ++ (fg ++ tail)) = OK u` by
    simp[APPEND_ASSOC] >>
  drule_all invoke_partner_prefix_concrete >> strip_tac >>
  `EVERY (\q. ~MEM (Var (FST q)) y.inst_operands /\
                ~MEM (FST q) y.inst_outputs) us` by
    (fs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
     metis_tac[dft_swap_output_frame]) >>
  qpat_x_assum `!fg tail. _` (qspecl_then [`fg`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all invoke_updates_concrete_frame >>
  disch_then (qspecl_then [`fuel`, `C`,
    `s with <|vs_inst_idx := s.vs_inst_idx + LENGTH pre;
              vs_gas_readings := fg ++ tail|>`] mp_tac) >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (qexists_tac `extra` >> AP_THM_TAC >> AP_TERM_TAC >>
      sym_tac >> irule gas_events_invoke_updates >>
      fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `step_inst fuel C y
    (s with <|vs_inst_idx := s.vs_inst_idx + LENGTH pre;
              vs_gas_readings := fg ++ tail|>)` >> gvs[]
QED

Theorem stopped_invoke_fixed_entry_prefix[local]:
  y.inst_opcode = INVOKE /\
  EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x) pre /\
  (!fg tail.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) focus_slots fg ==>
    (?extra. focus_sites = gas_events_step fuel C owner y
      (s with <|vs_inst_idx := s.vs_inst_idx + LENGTH pre;
                vs_gas_readings := fg ++ tail|>) ++ extra) /\
    (!v. step_inst fuel C y
      (s with <|vs_inst_idx := s.vs_inst_idx + LENGTH pre;
                vs_gas_readings := fg ++ tail|>) <> OK v)) ==>
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
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule stopped_focus_prefix_family >>
  simp[] >> conj_tac
  >- (fs[EVERY_MEM] >> rpt strip_tac >>
      metis_tac[dft_gas_swap_pair_sym,
                dftGasInvCallPartnerTheory.inv_call_partner_class]) >>
  qexists_tac `focus_slots` >> simp[] >>
  metis_tac[stopped_invoke_fixed_entry_family]
QED

(* Successful instruction cuts expose the concrete remaining reading budget,
   including variable-length INVOKE segments. *)
Theorem prefix_ok_readings_events[local]:
  !xs s t bb.
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    FOLDR (dft_exec_cons fuel C) OK xs s = OK t ==>
    t.vs_gas_readings =
      DROP (LENGTH (gas_events_block fuel C owner bb s)) s.vs_gas_readings
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _::_`
       (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  first_x_assum (qspec_then `v with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then (drule_then assume_tac) >>
  mp_tac (cj 1 gas_count_suffix) >>
  disch_then (qspecl_then [`fuel`, `C`, `h`, `s`] mp_tac) >>
  simp[gas_count_suffix_def] >> strip_tac >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       gas_events_length, rich_listTheory.DROP_DROP_T] >>
  simp[SimpRHS, Once gas_count_block_def, venomInstTheory.get_instruction_def] >>
  simp[arithmeticTheory.ADD_COMM]
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
