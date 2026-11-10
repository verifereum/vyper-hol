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

Theorem invoke_partner_pure_portable[local]:
  dft_gas_swap_pair y x /\ y.inst_opcode = INVOKE /\ inst_wf x /\
  x.inst_opcode <> GAS /\
  dftGasInvCallPartner$inv_partner_inputs x s t /\
  step_inst fuel C x s = OK u ==>
  ?pairs. MAP FST pairs = x.inst_outputs /\
    u = FOLDL (\st (out,w). update_var out w st) s pairs /\
    step_inst fuel D x t = OK (FOLDL (\st (out,w). update_var out w st) t pairs)
Proof
  strip_tac >>
  drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> strip_tac >>
  `step_inst_base x s = OK u` by gvs[step_inst_non_invoke] >>
  simp[step_inst_non_invoke] >>
  Cases_on `x.inst_opcode` >> (
  gvs[venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
      venomEffectsTheory.empty_effects_def, venomEffectsTheory.all_effects_def,
      venomInstTheory.is_terminator_def, venomInstTheory.is_alloca_op_def,
      venomInstTheory.is_pseudo_def, venomInstTheory.is_ext_call_op_def,
      pred_setTheory.EXTENSION] >>
  qpat_x_assum `step_inst_base x s = OK u` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, AllCaseEqs()] >> strip_tac >>
  gvs[dftGasInvCallPartnerTheory.inv_partner_inputs_def, MEM] >>
  FIRST [
    qmatch_goalsub_abbrev_tac `update_var out2 value2 (update_var out1 value1 s)` >>
      qexists_tac `[(out1,value1); (out2,value2)]` >> simp[],
    qmatch_goalsub_abbrev_tac `update_var out value s` >>
      qexists_tac `[(out,value)]` >> simp[] >>
      gvs[Abbr `value`] >> metis_tac[],
    qexists_tac `[]` >> gvs[venomWfTheory.inst_wf_def] >> metis_tac[]])
QED

Theorem invoke_partner_step_portable[local]:
  dft_gas_swap_pair y x /\ y.inst_opcode = INVOKE /\ inst_wf x /\
  dftGasInvCallPartner$inv_partner_inputs x s t /\
  LENGTH pg = (if x.inst_opcode = GAS then 1 else 0) /\
  step_inst fuel C x (s with vs_gas_readings := pg ++ rs) = OK u ==>
  ?pairs. MAP FST pairs = x.inst_outputs /\
    u = FOLDL (\st (out,w). update_var out w st)
      (s with vs_gas_readings := rs) pairs /\
    step_inst fuel D x (t with vs_gas_readings := pg ++ rt) =
      OK (FOLDL (\st (out,w). update_var out w st)
        (t with vs_gas_readings := rt) pairs)
Proof
  strip_tac >> Cases_on `x.inst_opcode = GAS`
  >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
      Cases_on `pg` >> gvs[] >>
      qexists_tac `[(x',h)]` >> simp[] >>
      drule_all dftBlockSimTheory.step_inst_gas_single >>
      simp[]) >>
  `pg = []` by gvs[] >> gvs[] >>
  `dftGasInvCallPartner$inv_partner_inputs x
    (s with vs_gas_readings := rs) (t with vs_gas_readings := rt)` by
    gvs[dftGasInvCallPartnerTheory.inv_partner_inputs_def, eval_operand_def] >>
  drule_all invoke_partner_pure_portable >> metis_tac[]
QED

Theorem invoke_partner_inputs_updates[local]:
  !us x s t gs gt is it.
  dftGasInvCallPartner$inv_partner_inputs x s t ==>
  dftGasInvCallPartner$inv_partner_inputs x
    (FOLDL (\st q. update_var (FST q) (SND q) st)
      (s with <|vs_gas_readings := gs; vs_inst_idx := is|>) us)
    (FOLDL (\st q. update_var (FST q) (SND q) st)
      (t with <|vs_gas_readings := gt; vs_inst_idx := it|>) us)
Proof
  Induct >> rpt gen_tac
  >- (simp[dftGasInvCallPartnerTheory.inv_partner_inputs_def] >>
      rpt strip_tac >> Cases_on `op` >>
      gvs[eval_operand_def, lookup_var_def] >>
      metis_tac[eval_operand_def, lookup_var_def]) >>
  strip_tac >> PairCases_on `h` >> simp[] >>
  first_x_assum (qspecl_then
    [`x`, `update_var h0 h1 s`, `update_var h0 h1 t`] mp_tac) >>
  (impl_tac >-
    (gvs[dftGasInvCallPartnerTheory.inv_partner_inputs_def, update_var_def] >>
     rpt strip_tac >> Cases_on `op` >>
     gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[eval_operand_def, lookup_var_def])) >>
  simp[update_var_def]
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

Theorem invoke_return_partner_inputs[local]:
  y.inst_opcode = INVOKE /\ dft_gas_swap_pair x y /\
  step_inst fuel C y s = OK t ==>
  dftGasInvCallPartner$inv_partner_inputs x s t
Proof
  strip_tac >>
  drule_all dftBlockSimTheory.invoke_preserves_structural >> strip_tac >>
  `dft_gas_swap_pair y x` by metis_tac[dft_gas_swap_pair_sym] >>
  qpat_assum `dft_gas_swap_pair y x`
    (mp_tac o MATCH_MP dftRunRelTheory.dft_swap_output_frame) >> strip_tac >>
  simp[dftGasInvCallPartnerTheory.inv_partner_inputs_def] >>
  rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
  sym_tac >> irule venomInstPropsTheory.step_preserves_non_output_vars >>
  qexistsl_tac [`C`, `fuel`, `y`] >> simp[venomInstTheory.is_terminator_def] >> metis_tac[]
QED

Theorem invoke_partner_prefix_portable[local]:
  !pre s t pg rs rt u.
    y.inst_opcode = INVOKE /\
    EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x /\
      dftGasInvCallPartner$inv_partner_inputs x s t) pre /\
    LENGTH pg = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := pg ++ rs) = OK u ==>
    ?us. EVERY (\q. MEM (FST q) (FLAT (MAP (\x. x.inst_outputs) pre)) /\
      ~MEM (Var (FST q)) y.inst_operands /\ ~MEM (FST q) y.inst_outputs) us /\
    u = FOLDL (\st q. update_var (FST q) (SND q) st)
      (s with <|vs_gas_readings := rs; vs_inst_idx := s.vs_inst_idx + LENGTH pre|>) us /\
    FOLDR (dft_exec_cons fuel D) OK pre (t with vs_gas_readings := pg ++ rt) =
      OK (FOLDL (\st q. update_var (FST q) (SND q) st)
        (t with <|vs_gas_readings := rt; vs_inst_idx := t.vs_inst_idx + LENGTH pre|>) us)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[venom_state_component_equality] >>
  fs[EVERY_DEF] >>
  `~is_terminator h.inst_opcode` by gvs[dft_gas_swap_pair_def] >>
  fs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := pg ++ rs)` >> gvs[] >>
  `?lead pg'. pg = lead ++ pg' /\
    LENGTH lead = (if h.inst_opcode = GAS then 1 else 0) /\
    LENGTH pg' = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre)` by
    (Cases_on `h.inst_opcode = GAS`
     >- (Cases_on `pg` >> gvs[] >> qexistsl_tac [`[h']`, `t'`] >> simp[]) >>
     qexistsl_tac [`[]`, `pg`] >> gvs[]) >>
  `dft_gas_swap_pair y h` by metis_tac[dft_gas_swap_pair_sym] >>
  `?hs. MAP FST hs = h.inst_outputs /\
    v = FOLDL (\st q. update_var (FST q) (SND q) st)
      (s with vs_gas_readings := pg' ++ rs) hs /\
    step_inst fuel D h (t with vs_gas_readings := lead ++ (pg' ++ rt)) =
      OK (FOLDL (\st q. update_var (FST q) (SND q) st)
        (t with vs_gas_readings := pg' ++ rt) hs)` by
    (gvs[] >>
     qpat_x_assum `!s t pg rs rt u. _` kall_tac >>
     qpat_x_assum `step_inst fuel C h _ = OK v` mp_tac >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> strip_tac >>
     drule_at (Pat `step_inst _ _ _ _ = _`)
       (Q.INST [`pg` |-> `lead`, `rs` |-> `pg' ++ rs`, `rt` |-> `pg' ++ rt`]
          invoke_partner_step_portable) >>
     simp[pairTheory.LAMBDA_PROD] >> metis_tac[]) >>
  qabbrev_tac `ss = FOLDL (\st q. update_var (FST q) (SND q) st)
    (s with <|vs_gas_readings := s.vs_gas_readings; vs_inst_idx := SUC s.vs_inst_idx|>) hs` >>
  qabbrev_tac `tt = FOLDL (\st q. update_var (FST q) (SND q) st)
    (t with <|vs_gas_readings := t.vs_gas_readings; vs_inst_idx := SUC t.vs_inst_idx|>) hs` >>
  `EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x /\
     dftGasInvCallPartner$inv_partner_inputs x ss tt) pre` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `dftGasInvCallPartner$inv_partner_inputs x s t` by metis_tac[] >>
     drule invoke_partner_inputs_updates >>
     disch_then (qspec_then `hs` mp_tac) >>
     disch_then (qspecl_then [`s.vs_gas_readings`, `t.vs_gas_readings`,
       `SUC s.vs_inst_idx`, `SUC t.vs_inst_idx`] mp_tac) >>
     simp[Abbr `ss`, Abbr `tt`]) >>
  `FOLDR (dft_exec_cons fuel C) OK pre (ss with vs_gas_readings := pg' ++ rs) = OK u` by
    (simp[Abbr `ss`, updates_readings_cursor] >>
     qpat_x_assum `FOLDR (dft_exec_cons fuel C) OK pre _ = OK u` mp_tac >>
     simp[pairTheory.LAMBDA_PROD,
       GSYM foldl_update_var_idx,
       GSYM gasOracleReplayTheory.gas_fold_updates]) >>
  first_x_assum (qspecl_then [`ss`, `tt`, `pg'`, `rs`, `rt`, `u`] mp_tac) >>
  simp[NoAsms] >> (impl_tac >- metis_tac[]) >>
  disch_then (qx_choose_then `ts` strip_assume_tac) >>
  qexists_tac `hs ++ ts` >>
  conj_tac
  >- (`!q. MEM q hs ==> MEM (FST q) h.inst_outputs` by
        metis_tac[MEM_MAP] >>
      qpat_assum `dft_gas_swap_pair h y`
        (mp_tac o MATCH_MP dftRunRelTheory.dft_swap_output_frame) >>
      strip_tac >> fs[EVERY_APPEND, EVERY_MEM] >> metis_tac[]) >>
  gvs[Abbr `ss`, Abbr `tt`, FOLDL_APPEND,
      pairTheory.LAMBDA_PROD, GSYM foldl_update_var_idx,
      GSYM gasOracleReplayTheory.gas_fold_updates,
      foldl_update_var_inst_idx, arithmeticTheory.ADD_CLAUSES]
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

(* Lift an exact returning callee cut through the real caller frame. *)
Theorem invoke_return_residual[local]:
  i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME f /\
  eval_operands ops s = SOME args /\
  setup_callee f args s = SOME cs /\
  residual_result tail (IntRet ir u)
    (run_blocks fuel C f (cs with vs_gas_readings := gs)) /\
  bind_outputs i.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state s u)) = SOME t ==>
  step_inst fuel C i (s with vs_gas_readings := gs) =
    OK (t with vs_gas_readings := tail)
Proof
  strip_tac >>
  `setup_callee f args (s with vs_gas_readings := gs) =
     SOME (cs with vs_gas_readings := gs)` by
    (qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
     simp[gasOracleReplayTheory.gas_setup_callee, optionTheory.OPTION_MAP_EQ_SOME] >>
     strip_tac >> gvs[] >>
     qpat_x_assum `cs = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  Cases_on `run_blocks fuel C f (cs with vs_gas_readings := gs)` >>
  gvs[residual_result_def, stateEquivTheory.lift_result_def] >>
  simp[Once step_inst_def, gasOracleReplayTheory.gas_eval_operands,
       gasOracleReplayTheory.gas_merge_callee,
       gasOracleReplayTheory.gas_adopt_return,
       gasOracleReplayTheory.gas_bind_outputs]
QED

Theorem invoke_segment_mask[local]:
  !fuel C C' i s.
    (!fn fn' t.
      LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
      LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
      o1_ctx_shape C /\ o1_ctx_shape C' /\
      MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
      dft_fn_rel fn fn' /\ strict_dom_vars_defined fn t /\
      fn_reachable fn t.vs_current_bb /\
      ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
      ~t.vs_call_ctx.cc_static /\ terminates (run_blocks fuel C' fn' t) /\
      gas_count_blocks fuel C' fn' t <= LENGTH t.vs_gas_readings ==>
      ?m es unused.
        LENGTH m = LENGTH es /\
        PERM (MAP THE (FILTER IS_SOME m) ++ unused) t.vs_gas_readings /\
        (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
          EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
        !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
          (?extra. es = gas_events_blocks fuel C fn
             (t with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?j. terminates (run_blocks j C fn
             (t with vs_gas_readings := gs ++ tail))) ==>
           terminates (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)) /\
           dft_res_rel
             (restore_result [] (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)))
             (restore_result [] (run_blocks fuel C' fn' t)) /\
           (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
             gas_events_blocks fuel C fn (t with vs_gas_readings := gs ++ tail) = es /\
             residual_result tail (run_blocks fuel C' fn' t)
               (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail))))) /\
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    ctx_labels_bound C s.vs_labels /\ ctx_labels_bound C' s.vs_labels /\
    ~s.vs_call_ctx.cc_static /\ i.inst_opcode = INVOKE /\
    terminates (step_inst fuel C' i s) /\
    LENGTH (gas_events_step fuel C' s.vs_current_bb i s) <= LENGTH s.vs_gas_readings ==>
    ?m es unused.
      LENGTH m = LENGTH es /\
      PERM (MAP THE (FILTER IS_SOME m) ++ unused) s.vs_gas_readings /\
      (!u. (step_inst fuel C' i s = OK u \/
            (?ir. step_inst fuel C' i s = IntRet ir u)) ==>
        EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
      !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
        (?extra. es = gas_events_step fuel C s.vs_current_bb i
           (s with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?j. terminates (step_inst j C i (s with vs_gas_readings := gs ++ tail))) ==>
          terminates (step_inst fuel C i (s with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (step_inst fuel C i (s with vs_gas_readings := gs ++ tail)))
            (restore_result [] (step_inst fuel C' i s)) /\
          (((?u. step_inst fuel C' i s = OK u) \/
            (?ir u. step_inst fuel C' i s = IntRet ir u)) ==>
            gas_events_step fuel C s.vs_current_bb i
              (s with vs_gas_readings := gs ++ tail) = es /\
            residual_result tail (step_inst fuel C' i s)
              (step_inst fuel C i (s with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `terminates (step_inst _ _ _ _)` mp_tac >>
  simp[Once step_inst_def] >>
  Cases_on `decode_invoke i` >- simp[passSimulationDefsTheory.terminates_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 C'.ctx_functions`
  >- simp[passSimulationDefsTheory.terminates_def] >>
  simp[] >>
  Cases_on `eval_operands x1 s` >- simp[passSimulationDefsTheory.terminates_def] >>
  simp[] >>
  rename1 `lookup_function x0 C'.ctx_functions = SOME callee'` >>
  rename1 `eval_operands x1 s = SOME args` >>
  Cases_on `setup_callee callee' args s`
  >- simp[passSimulationDefsTheory.terminates_def] >>
  simp[] >> strip_tac >>
  rename1 `setup_callee callee' args s = SOME cs` >>
  `OPTREL (\f g. g = dft_fn f)
     (lookup_function x0 C.ctx_functions)
     (lookup_function x0 C'.ctx_functions)` by
    (irule o1PassLiftTheory.list_rel_lookup_function >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  Cases_on `lookup_function x0 C.ctx_functions` >>
  gvs[optionTheory.OPTREL_def] >>
  rename1 `lookup_function x0 C.ctx_functions = SOME callee` >>
  `dft_fn_rel callee (dft_fn callee)` by
    (drule dft_fn_rel_lookup_function >>
     disch_then (qspec_then `x0` mp_tac) >> simp[optionTheory.OPTREL_def]) >>
  `setup_callee callee args s = SOME cs` by
    metis_tac[dft_fn_rel_setup_callee] >>
  `fn_entry_label callee = SOME cs.vs_current_bb /\
   strict_dom_vars_defined callee cs /\
   ctx_labels_bound C cs.vs_labels /\ ctx_labels_bound C' cs.vs_labels /\
   ~cs.vs_call_ctx.cc_static` by
    metis_tac[dft_setup_callee_entry,
      dftGasSimInvariantTheory.ev_setup_callee_dominators,
      dftGasSimInvariantTheory.ev_setup_callee_labels_bound,
      dftGasSimInvariantTheory.ev_setup_callee_nonstatic] >>
  `fn_reachable callee cs.vs_current_bb` by
    simp[venomWfTheory.fn_reachable_def] >>
  `MEM callee C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `cs.vs_gas_readings = s.vs_gas_readings` by
    metis_tac[gasOracleReplayTheory.gas_setup_callee_readings] >>
  `gas_count_blocks fuel C' (dft_fn callee) cs <= LENGTH cs.vs_gas_readings` by
    (qpat_x_assum `LENGTH (gas_events_step _ _ _ _ _) <= _` mp_tac >>
     simp[gas_events_length, Once gas_count_step_def]) >>
  `terminates (run_blocks fuel C' (dft_fn callee) cs)` by
    (Cases_on `run_blocks fuel C' (dft_fn callee) cs` >>
     gvs[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `!fn t. _` (drule_all_then strip_assume_tac) >>
  `!rs. setup_callee callee args (s with vs_gas_readings := rs) =
       SOME (cs with vs_gas_readings := rs)` by
    (gen_tac >> qpat_x_assum `setup_callee callee args s = SOME cs` mp_tac >>
     simp[gasOracleReplayTheory.gas_setup_callee, optionTheory.OPTION_MAP_EQ_SOME] >>
     strip_tac >> gvs[] >>
     qpat_x_assum `cs = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  qexistsl [`m`, `es`, `unused`] >> simp[] >>
  Cases_on `run_blocks fuel C' (dft_fn callee) cs` >>
  gvs[passSimulationDefsTheory.terminates_def] >>
  simp[step_inst_def, gasOracleReplayTheory.gas_eval_operands,
       gas_events_step_def]
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!gs tail. _` (qspecl_then [`gs`, `tail`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      disch_then (qx_choose_then `j` assume_tac) >>
      `?j. terminates (run_blocks j C callee (cs with vs_gas_readings := gs ++ tail))` by
        (qexists_tac `j` >>
         Cases_on `run_blocks j C callee (cs with vs_gas_readings := gs ++ tail)` >>
         gvs[passSimulationDefsTheory.terminates_def]) >>
      gvs[GSYM passSimulationDefsTheory.terminates_def] >>
      qpat_x_assum `(?j. _) ==> _` (mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      Cases_on `run_blocks fuel C callee (cs with vs_gas_readings := gs ++ tail)` >>
      gvs[restore_result_def, dftRunRelTheory.dft_res_rel_def,
          stateEquivTheory.lift_result_def])
  >- (rpt gen_tac >> strip_tac >>
   qpat_x_assum `!gs tail. _` (qspecl_then [`gs`, `tail`] mp_tac) >>
   simp[] >> strip_tac >> simp[] >>
   disch_then (qx_choose_then `j` assume_tac) >>
   `?j. terminates (run_blocks j C callee (cs with vs_gas_readings := gs ++ tail))` by
     (qexists_tac `j` >>
      Cases_on `run_blocks j C callee (cs with vs_gas_readings := gs ++ tail)` >>
      gvs[passSimulationDefsTheory.terminates_def]) >>
   gvs[GSYM passSimulationDefsTheory.terminates_def] >>
   qpat_x_assum `(?j. _) ==> _` mp_tac >>
   impl_tac >- metis_tac[] >> strip_tac >>
   Cases_on `run_blocks fuel C callee (cs with vs_gas_readings := gs ++ tail)` >>
   gvs[restore_result_def, dftRunRelTheory.dft_res_rel_def,
       stateEquivTheory.lift_result_def]) >>
  rename1 `run_blocks fuel C' (dft_fn callee) cs = IntRet ir u` >>
  Cases_on `bind_outputs i.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state s u))` >> gvs[] >>
  rename1 `bind_outputs _ _ _ = SOME t` >>
  `t.vs_gas_readings = u.vs_gas_readings` by
    (drule gasOracleReplayTheory.gas_bind_outputs_readings >>
     simp[merge_callee_state_def, adopt_return_fmp_def]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs tail. _` (qspecl_then [`gs`, `tail`] mp_tac) >>
  simp[] >> strip_tac >>
  disch_then (qx_choose_then `j` assume_tac) >>
  `?j. terminates (run_blocks j C callee (cs with vs_gas_readings := gs ++ tail))` by
    (qexists_tac `j` >>
     Cases_on `run_blocks j C callee (cs with vs_gas_readings := gs ++ tail)` >>
     gvs[passSimulationDefsTheory.terminates_def]) >>
  gvs[GSYM passSimulationDefsTheory.terminates_def] >>
  qpat_x_assum `(?j. _) ==> _` mp_tac >>
  impl_tac >- metis_tac[] >> strip_tac >>
  Cases_on `run_blocks fuel C callee (cs with vs_gas_readings := gs ++ tail)` >>
  gvs[residual_result_def, stateEquivTheory.lift_result_def] >>
  simp[gasOracleReplayTheory.gas_merge_callee,
       gasOracleReplayTheory.gas_adopt_return,
       gasOracleReplayTheory.gas_bind_outputs,
       passSimulationDefsTheory.terminates_def, restore_result_def,
       dftRunRelTheory.dft_res_rel_def, residual_result_def,
       stateEquivTheory.lift_result_def]
QED

Theorem prefix_terminates_mono[local]:
  !pre s n m C.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    terminates (FOLDR (dft_exec_cons n C) OK pre s) /\ n <= m ==>
    FOLDR (dft_exec_cons m C) OK pre s =
    FOLDR (dft_exec_cons n C) OK pre s
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst n C h s` >>
  gvs[passSimulationDefsTheory.terminates_def] >>
  `step_inst m C h s = step_inst n C h s` by
    (irule o1PassLiftTheory.step_inst_terminates_mono >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  simp[] >> first_x_assum irule >>
  simp[passSimulationDefsTheory.terminates_def]
QED

Theorem prefix_terminates_coherent[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  terminates (FOLDR (dft_exec_cons n C) OK pre s) /\
  terminates (FOLDR (dft_exec_cons m C) OK pre s) ==>
  FOLDR (dft_exec_cons n C) OK pre s =
  FOLDR (dft_exec_cons m C) OK pre s
Proof
  strip_tac >>
  `FOLDR (dft_exec_cons (MAX n m) C) OK pre s =
   FOLDR (dft_exec_cons n C) OK pre s` by
    (irule prefix_terminates_mono >> simp[]) >>
  `FOLDR (dft_exec_cons (MAX n m) C) OK pre s =
   FOLDR (dft_exec_cons m C) OK pre s` by
    (irule prefix_terminates_mono >> simp[]) >>
  metis_tac[]
QED

Theorem prefix_exact_cut_terminates[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  FOLDR (dft_exec_cons k C) OK pre s = OK u /\
  terminates (FOLDR (dft_exec_cons j C) OK (pre ++ post) s) ==>
  terminates (FOLDR (dft_exec_cons j C) OK post u)
Proof
  strip_tac >>
  `terminates (FOLDR (dft_exec_cons j C) OK pre s)` by
    (qpat_x_assum `terminates _` mp_tac >>
     simp[FOLDR_APPEND, Once dftRunRelTheory.dft_exec_prefix_continue] >>
     Cases_on `FOLDR (dft_exec_cons j C) OK pre s` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  `FOLDR (dft_exec_cons j C) OK pre s =
   FOLDR (dft_exec_cons k C) OK pre s` by
    (irule prefix_terminates_coherent >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `terminates (FOLDR _ _ (_ ++ _) _)` mp_tac >>
  simp[FOLDR_APPEND, Once dftRunRelTheory.dft_exec_prefix_continue]
QED

Theorem mask_segments_compose[local]:
  let R = (\n D xs st. FOLDR (dft_exec_cons n D) OK xs st);
      E = (\xs st. gas_events_block fuel C owner
        <|bb_label := owner; bb_instructions :=
          REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> st);
      Seg = (\xs st m es unused.
        LENGTH m = LENGTH es /\
        PERM (MAP THE (FILTER IS_SOME m) ++ unused) st.vs_gas_readings /\
        (!v. (R fuel C' xs st = OK v \/
              (?ir. R fuel C' xs st = IntRet ir v)) ==>
          EVERY IS_SOME m /\ unused = v.vs_gas_readings) /\
        !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
          (?extra. es = E xs (st with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?j. terminates (R j C xs (st with vs_gas_readings := gs ++ tail))) ==>
            terminates (R fuel C xs (st with vs_gas_readings := gs ++ tail)) /\
            dft_res_rel
              (restore_result [] (R fuel C xs (st with vs_gas_readings := gs ++ tail)))
              (restore_result [] (R fuel C' xs st)) /\
            (((?v. R fuel C' xs st = OK v) \/
              (?ir v. R fuel C' xs st = IntRet ir v)) ==>
              E xs (st with vs_gas_readings := gs ++ tail) = es /\
              residual_result tail (R fuel C' xs st)
                (R fuel C xs (st with vs_gas_readings := gs ++ tail)))))
  in
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    R fuel C' pre s = OK u /\
    Seg pre s m1 e1 unused1 /\ Seg post u m2 e2 unused2 ==>
    Seg (pre ++ post) s (m1 ++ m2) (e1 ++ e2) unused2
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  `!n D st. R n D (pre ++ post) st =
    case R n D pre st of OK v => R n D post v | other => other` by
    simp[Abbr `R`, FOLDR_APPEND, Once dftRunRelTheory.dft_exec_prefix_continue] >>
  fs[Abbr `Seg`] >>
  `EVERY IS_SOME m1 /\ unused1 = u.vs_gas_readings` by metis_tac[] >>
  conj_tac
  >- (simp[FILTER_APPEND, MAP_APPEND, APPEND_ASSOC] >>
      irule PERM_TRANS >> qexists_tac `MAP THE (FILTER IS_SOME m1) ++ unused1` >>
      metis_tac[GSYM APPEND_ASSOC, PERM_APPEND_IFF]) >>
  conj_tac >- gvs[] >>
  `!pg rest. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m1 pg ==>
    (?extra. e1 = E pre (s with vs_gas_readings := pg ++ rest) ++ extra) /\
    (!v. R fuel C pre (s with vs_gas_readings := pg ++ rest) = OK v ==>
      E pre (s with vs_gas_readings := pg ++ rest) = e1 /\
      v = u with vs_gas_readings := rest)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!gs tail. LIST_REL _ m1 gs ==> _`
       (qspecl_then [`pg`, `rest`] mp_tac) >> simp[] >> strip_tac >>
     rpt strip_tac >>
     `?j. terminates (R j C pre (s with vs_gas_readings := pg ++ rest))` by
       (qexists_tac `fuel` >> simp[passSimulationDefsTheory.terminates_def]) >>
     gvs[residual_result_cases] >> metis_tac[]) >>
  `!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (m1 ++ m2) gs ==>
    ?extra. e1 ++ e2 = E (pre ++ post) (s with vs_gas_readings := gs ++ tail) ++ extra` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `E`] >>
     irule (SRULE [] mask_exact_cut_prefix) >>
     conj_tac >- simp[] >> qexistsl_tac [`m1`, `m2`, `u`] >>
     fs[Abbr `R`] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
  qpat_x_assum `LIST_REL _ (m1 ++ m2) gs` mp_tac >>
  simp[LIST_REL_SPLIT1] >> strip_tac >> gvs[] >>
  disch_then (qx_choose_then `j` assume_tac) >>
  `terminates (R j C pre (s with vs_gas_readings := (ys1 ++ ys2) ++ tail))` by
    (Cases_on `R j C pre (s with vs_gas_readings := (ys1 ++ ys2) ++ tail)` >>
     gvs[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `!gs tail. LIST_REL _ m1 gs ==> _`
    (qspecl_then [`ys1`, `ys2 ++ tail`] mp_tac) >>
  simp[APPEND_ASSOC] >> strip_tac >>
  `?j. terminates (R j C pre (s with vs_gas_readings := ys1 ++ ys2 ++ tail))` by
    metis_tac[APPEND_ASSOC] >>
  gvs[residual_result_cases] >>
  `R fuel C pre (s with vs_gas_readings := ys1 ++ ys2 ++ tail) =
     OK (u with vs_gas_readings := ys2 ++ tail)` by
    (qpat_x_assum `!gs' tail'. LIST_REL _ m1 gs' ==> _`
       (qspecl_then [`ys1`, `ys2 ++ tail`] mp_tac) >>
     simp[APPEND_ASSOC] >> impl_tac >- metis_tac[] >> simp[]) >>
  `terminates (R j C post (u with vs_gas_readings := ys2 ++ tail))` by
    metis_tac[prefix_exact_cut_terminates] >>
  `E (pre ++ post) (s with vs_gas_readings := ys1 ++ ys2 ++ tail) =
   E pre (s with vs_gas_readings := ys1 ++ ys2 ++ tail) ++
   E post (u with vs_gas_readings := ys2 ++ tail)` by
   (simp[Abbr `E`] >>
  qmatch_goalsub_abbrev_tac `gas_events_block fuel C owner bb st` >>
  `DROP st.vs_inst_idx bb.bb_instructions = pre ++ post` by
    (simp[Abbr `st`, Abbr `bb`] >>
     metis_tac[LENGTH_REPLICATE, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `FOLDR (dft_exec_cons fuel C) OK pre st =
     OK (u with vs_gas_readings := ys2 ++ tail)` by
    fs[Abbr `R`, Abbr `st`] >>
  drule_all prefix_events_splice >> disch_then (qspec_then `owner` SUBST1_TAC) >>
  simp[Abbr `st`] >>
  drule_all prefix_ok_cursor >> simp[] >> strip_tac >>
  irule gas_events_block_suffix_cong >> qexists_tac `post` >>
  simp[Abbr `bb`, DROP_APPEND, DROP_DROP_T]) >>
  qpat_x_assum `!gs tail. LIST_REL _ m2 gs ==> _`
    (qspecl_then [`ys2`, `tail`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `(?j. terminates (R j C post _)) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem noninvoke_segment_mask[local]:
  i.inst_opcode <> INVOKE /\ inst_wf i /\
  terminates (step_inst fuel C' i s) /\
  LENGTH (gas_events_step fuel C' s.vs_current_bb i s) <= LENGTH s.vs_gas_readings ==>
  ?m es unused.
    LENGTH m = LENGTH es /\
    PERM (MAP THE (FILTER IS_SOME m) ++ unused) s.vs_gas_readings /\
    (!u. (step_inst fuel C' i s = OK u \/
          (?ir. step_inst fuel C' i s = IntRet ir u)) ==>
      EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
    !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
      (?extra. es = gas_events_step fuel C s.vs_current_bb i
         (s with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?j. terminates (step_inst j C i (s with vs_gas_readings := gs ++ tail))) ==>
        terminates (step_inst fuel C i (s with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (step_inst fuel C i (s with vs_gas_readings := gs ++ tail)))
          (restore_result [] (step_inst fuel C' i s)) /\
        (((?u. step_inst fuel C' i s = OK u) \/
          (?ir u. step_inst fuel C' i s = IntRet ir u)) ==>
          gas_events_step fuel C s.vs_current_bb i
            (s with vs_gas_readings := gs ++ tail) = es /\
          residual_result tail (step_inst fuel C' i s)
            (step_inst fuel C i (s with vs_gas_readings := gs ++ tail))))
Proof
  strip_tac >> Cases_on `i.inst_opcode = GAS`
  >- (drule_all dftRunRelTheory.dft_gas_ok_shape >> strip_tac >>
      Cases_on `s.vs_gas_readings` >- gvs[gas_events_step_def] >>
      qexistsl_tac [`[SOME h]`, `[(s.vs_current_bb,i.inst_id)]`, `t`] >>
      simp[gas_events_step_def] >>
      simp[residual_result_cases, restore_result_def,
           dftRunRelTheory.dft_res_rel_def,
           passSimulationDefsTheory.terminates_def,
           venomStateTheory.update_var_def]) >>
  qexistsl_tac [`[]`, `[]`, `s.vs_gas_readings`] >>
  simp[gas_events_step_def] >>
  `!rs. residual_result rs (step_inst fuel C' i s)
    (step_inst fuel C i (s with vs_gas_readings := rs))` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke,
         dftGasToListReplayTheory.replay_base_non_gas] >>
  `gas_count_suffix 0 s (step_inst fuel C' i s)` by
    metis_tac[gas_count_step_def, cj 1 gas_count_suffix] >>
  Cases_on `step_inst fuel C' i s` >>
  gvs[gas_count_suffix_def, passSimulationDefsTheory.terminates_def,
      residual_result_def, stateEquivTheory.lift_result_def] >>
  gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `step_inst fuel C i (s with vs_gas_readings := tail)` >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >> gvs[] >>
  simp[restore_result_def, dftRunRelTheory.dft_res_rel_def]
QED

Theorem identity_mask_cons[local]:
  let R = (\n D xs st. FOLDR (dft_exec_cons n D) OK xs st);
      E = (\D xs st. gas_events_block fuel D st.vs_current_bb
        <|bb_label := st.vs_current_bb; bb_instructions :=
          REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> st);
      Seg = (\T F G rs m es unused.
        LENGTH m = LENGTH es /\
        PERM (MAP THE (FILTER IS_SOME m) ++ unused) rs /\
        (!v. (T = OK v \/ (?ir. T = IntRet ir v)) ==>
          EVERY IS_SOME m /\ unused = v.vs_gas_readings) /\
        !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
          (?extra. es = G gs tail ++ extra) /\
          ((?j. terminates (F j gs tail)) ==>
            terminates (F fuel gs tail) /\
            dft_res_rel (restore_result [] (F fuel gs tail)) (restore_result [] T) /\
            (((?v. T = OK v) \/ (?ir v. T = IntRet ir v)) ==>
              G gs tail = es /\ residual_result tail T (F fuel gs tail))));
      S = (\xs st m es unused.
        Seg (R fuel C' xs st)
          (\n gs tail. R n C xs (st with vs_gas_readings := gs ++ tail))
          (\gs tail. E C xs (st with vs_gas_readings := gs ++ tail))
          st.vs_gas_readings m es unused)
  in
    ~is_terminator h.inst_opcode /\ step_inst fuel C' h s = OK u /\
    u.vs_current_bb = s.vs_current_bb /\
    Seg (step_inst fuel C' h s)
      (\n gs tail. step_inst n C h (s with vs_gas_readings := gs ++ tail))
      (\gs tail. gas_events_step fuel C s.vs_current_bb h
        (s with vs_gas_readings := gs ++ tail)) s.vs_gas_readings m es unused /\
    S xs (u with vs_inst_idx := SUC s.vs_inst_idx) m' es' unused' ==>
    S (h::xs) s (m ++ m') (es ++ es') unused'
Proof
  rpt BasicProvers.LET_ELIM_TAC >>
  `!n D st. R n D [h] st =
    case step_inst n D h st of
      OK v => OK (v with vs_inst_idx := SUC st.vs_inst_idx)
    | other => other` by
    simp[Abbr `R`, dftIndexedExecTheory.dft_exec_cons_def] >>
  `!st. E C [h] st = gas_events_step fuel C st.vs_current_bb h st` by
    (gen_tac >> simp[Abbr `E`, Once gas_events_block_def,
       venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
     Cases_on `step_inst fuel C h st` >> simp[] >>
     simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  `S' [h] s m es unused` by
    (qpat_x_assum `S' xs _ _ _ _` kall_tac >>
     simp[Abbr `S'`, Abbr `Seg`] >>
     qpat_x_assum `Seg _ _ _ _ _ _ _` mp_tac >>
     simp[] >> strip_tac >> simp[] >>
     rpt gen_tac >> strip_tac >>
     first_x_assum (qspecl_then [`gs`, `tail`] mp_tac) >>
     simp[] >> strip_tac >> simp[] >>
     strip_tac >>
     `?j. terminates (step_inst j C h (s with vs_gas_readings := gs ++ tail))` by
       (qexists_tac `j` >>
        Cases_on `step_inst j C h (s with vs_gas_readings := gs ++ tail)` >>
        gvs[passSimulationDefsTheory.terminates_def]) >>
     qpat_x_assum `(?j. terminates (step_inst j _ _ _)) ==> _` mp_tac >>
     (impl_tac >- metis_tac[]) >> strip_tac >>
     simp[restore_result_def, dftRunRelTheory.dft_res_rel_def,
          passSimulationDefsTheory.terminates_def] >>
     qpat_x_assum `es = _ ++ extra` mp_tac >> simp[]) >>
  qabbrev_tac `Q = (\ys st a b c.
    Seg (R fuel C' ys st)
      (\n gs tail. R n C ys (st with vs_gas_readings := gs ++ tail))
      (\gs tail. gas_events_block fuel C s.vs_current_bb
        <|bb_label := s.vs_current_bb; bb_instructions :=
          REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] []) ++ ys|>
        (st with vs_gas_readings := gs ++ tail)) st.vs_gas_readings a b c)` >>
  `!ys st a b c. st.vs_current_bb = s.vs_current_bb ==>
    (Q ys st a b c <=> S' ys st a b c)` by
    (rpt gen_tac >> strip_tac >>
     qunabbrev_tac `Q` >> qunabbrev_tac `S'` >> qunabbrev_tac `E` >>
     BETA_TAC >> simp[]) >>
  `Q [h] s m es unused /\
   Q xs (u with vs_inst_idx := SUC s.vs_inst_idx) m' es' unused'` by
     simp[venomStateTheory.venom_state_accessors] >>
  `Q ([h] ++ xs) s (m ++ m') (es ++ es') unused'` by
    (qunabbrev_tac `Q` >> qunabbrev_tac `Seg` >> qunabbrev_tac `R` >>
     CONV_TAC (REDEPTH_CONV BETA_CONV) >>
     match_mp_tac (Q.INST
       [`u` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`, `unused1` |-> `unused`]
       (PURE_REWRITE_RULE [venomStateTheory.venom_state_accfupds]
         (CONV_RULE (REDEPTH_CONV BETA_CONV)
           (PURE_REWRITE_RULE [LET_THM] mask_segments_compose)))) >>
     conj_tac >- simp[] >>
     conj_tac >- simp[dftIndexedExecTheory.dft_exec_cons_def] >>
     rule_assum_tac (CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
     pure_asm_rewrite_tac [venomStateTheory.venom_state_accfupds] >> simp[]) >>
  metis_tac[APPEND]
QED

Theorem identity_suffix_mask[local]:
  !fuel C C'.
  let CalleeIH = (!fn fn' t.
      LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
      LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
      o1_ctx_shape C /\ o1_ctx_shape C' /\
      MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
      dft_fn_rel fn fn' /\ strict_dom_vars_defined fn t /\
      fn_reachable fn t.vs_current_bb /\
      ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
      ~t.vs_call_ctx.cc_static /\ terminates (run_blocks fuel C' fn' t) /\
      gas_count_blocks fuel C' fn' t <= LENGTH t.vs_gas_readings ==>
      ?m es unused.
        LENGTH m = LENGTH es /\
        PERM (MAP THE (FILTER IS_SOME m) ++ unused) t.vs_gas_readings /\
        (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
          EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
        !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
          (?extra. es = gas_events_blocks fuel C fn
             (t with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?j. terminates (run_blocks j C fn
             (t with vs_gas_readings := gs ++ tail))) ==>
           terminates (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)) /\
           dft_res_rel
             (restore_result [] (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)))
             (restore_result [] (run_blocks fuel C' fn' t)) /\
           (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
             gas_events_blocks fuel C fn (t with vs_gas_readings := gs ++ tail) = es /\
             residual_result tail (run_blocks fuel C' fn' t)
               (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)))));
      R = (\n D xs st. FOLDR (dft_exec_cons n D) OK xs st);
      E = (\D xs st. gas_events_block fuel D st.vs_current_bb
        <|bb_label := st.vs_current_bb; bb_instructions :=
          REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> st)
  in
  !fn bb xs post s.
    CalleeIH /\
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\ MEM fn C.ctx_functions /\
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
    EVERY (\i. MEM i bb.bb_instructions) xs /\ dft_remaining_inv fn bb (xs ++ post) s /\
    ctx_labels_bound C s.vs_labels /\ ctx_labels_bound C' s.vs_labels /\
    ~s.vs_call_ctx.cc_static /\ terminates (R fuel C' xs s) /\
    LENGTH (E C' xs s) <= LENGTH s.vs_gas_readings ==>
    ?m es unused.
      LENGTH m = LENGTH es /\
      PERM (MAP THE (FILTER IS_SOME m) ++ unused) s.vs_gas_readings /\
      (!u. (R fuel C' xs s = OK u \/ (?ir. R fuel C' xs s = IntRet ir u)) ==>
        EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
      !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
        (?extra. es = E C xs (s with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?j. terminates (R j C xs (s with vs_gas_readings := gs ++ tail))) ==>
          terminates (R fuel C xs (s with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (R fuel C xs (s with vs_gas_readings := gs ++ tail)))
            (restore_result [] (R fuel C' xs s)) /\
          (((?u. R fuel C' xs s = OK u) \/ (?ir u. R fuel C' xs s = IntRet ir u)) ==>
            E C xs (s with vs_gas_readings := gs ++ tail) = es /\
            residual_result tail (R fuel C' xs s)
              (R fuel C xs (s with vs_gas_readings := gs ++ tail))))
Proof
  ntac 3 gen_tac >> BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `LENGTH (E _ _ _) <= _` mp_tac >>
  qpat_x_assum `terminates (R _ _ _ _)` mp_tac >>
  qpat_x_assum `~s.vs_call_ctx.cc_static` mp_tac >>
  qpat_x_assum `ctx_labels_bound C' s.vs_labels` mp_tac >>
  qpat_x_assum `ctx_labels_bound C s.vs_labels` mp_tac >>
  qpat_x_assum `dft_remaining_inv _ _ _ _` mp_tac >>
  qpat_x_assum `EVERY (\i. MEM i _) xs` mp_tac >>
  qid_spec_tac `s` >> Induct_on `xs` >> gen_tac >> rpt strip_tac
  >- (qexistsl_tac [`[]`, `[]`, `s.vs_gas_readings`] >>
      simp[Abbr `R`, Abbr `E`, Once gas_events_block_def,
           venomInstTheory.get_instruction_def, residual_result_cases, restore_result_def,
           dftRunRelTheory.dft_res_rel_def,
           passSimulationDefsTheory.terminates_def] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  `inst_wf h` by fs[EVERY_MEM] >>
  `terminates (step_inst fuel C' h s)` by
    (qpat_x_assum `terminates (R _ _ _ _)` mp_tac >>
     simp[Abbr `R`, dftIndexedExecTheory.dft_exec_cons_def] >>
     Cases_on `step_inst fuel C' h s` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  `LENGTH (gas_events_step fuel C' s.vs_current_bb h s) <=
     LENGTH s.vs_gas_readings` by
    (qpat_x_assum `LENGTH (E _ _ _) <= _` mp_tac >>
     simp[Abbr `E`, Once gas_events_block_def,
          venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
     Cases_on `step_inst fuel C' h s` >> simp[]) >>
  `?m es unused.
    LENGTH m = LENGTH es /\
    PERM (MAP THE (FILTER IS_SOME m) ++ unused) s.vs_gas_readings /\
    (!u. (step_inst fuel C' h s = OK u \/
          (?ir. step_inst fuel C' h s = IntRet ir u)) ==>
      EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
    !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
      (?extra. es = gas_events_step fuel C s.vs_current_bb h
         (s with vs_gas_readings := gs ++ tail) ++ extra) /\
      ((?j. terminates (step_inst j C h (s with vs_gas_readings := gs ++ tail))) ==>
        terminates (step_inst fuel C h (s with vs_gas_readings := gs ++ tail)) /\
        dft_res_rel
          (restore_result [] (step_inst fuel C h (s with vs_gas_readings := gs ++ tail)))
          (restore_result [] (step_inst fuel C' h s)) /\
        (((?u. step_inst fuel C' h s = OK u) \/
          (?ir u. step_inst fuel C' h s = IntRet ir u)) ==>
          gas_events_step fuel C s.vs_current_bb h
            (s with vs_gas_readings := gs ++ tail) = es /\
          residual_result tail (step_inst fuel C' h s)
            (step_inst fuel C h (s with vs_gas_readings := gs ++ tail))))` by
    (Cases_on `h.inst_opcode = INVOKE`
     >- (irule invoke_segment_mask >> simp[GSYM markerTheory.Abbrev_def, Abbr `CalleeIH`]) >>
     irule noninvoke_segment_mask >> simp[]) >>
  Cases_on `?u. step_inst fuel C' h s = OK u`
  >- suspend "returning_head" >>
  `!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
    ~(?u. step_inst fuel C h (s with vs_gas_readings := gs ++ tail) = OK u)` by
    (rpt gen_tac >> strip_tac >> strip_tac >>
     qpat_x_assum `!gs tail. LIST_REL _ m gs ==> _`
       (qspecl_then [`gs`, `tail`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
     `?j. terminates (step_inst j C h (s with vs_gas_readings := gs ++ tail))` by
       (qexists_tac `fuel` >> simp[passSimulationDefsTheory.terminates_def]) >>
     qpat_x_assum `(?j. _) ==> _` mp_tac >>
     (impl_tac >- metis_tac[]) >> disch_then strip_assume_tac >>
     Cases_on `step_inst fuel C' h s`
     >- metis_tac[] >>
     qpat_x_assum `dft_res_rel _ _` mp_tac >>
     simp[restore_result_def, dftRunRelTheory.dft_res_rel_def]) >>
  `R fuel C' (h::xs) s = step_inst fuel C' h s` by
    (simp[Abbr `R`, dftIndexedExecTheory.dft_exec_cons_def] >>
     Cases_on `step_inst fuel C' h s` >> fs[]) >>
  `!gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
    R fuel C (h::xs) (s with vs_gas_readings := gs ++ tail) =
      step_inst fuel C h (s with vs_gas_readings := gs ++ tail) /\
    E C (h::xs) (s with vs_gas_readings := gs ++ tail) =
      gas_events_step fuel C s.vs_current_bb h
        (s with vs_gas_readings := gs ++ tail)` by
    (rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     simp[Abbr `R`, Abbr `E`, dftIndexedExecTheory.dft_exec_cons_def,
          Once gas_events_block_def, venomInstTheory.get_instruction_def,
          EL_APPEND_EQN] >>
     Cases_on `step_inst fuel C h (s with vs_gas_readings := gs ++ tail)` >> fs[] >>
     metis_tac[]) >>
  qexistsl_tac [`m`, `es`, `unused`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs tail. LIST_REL _ m gs ==> _ /\ _`
    (qspecl_then [`gs`, `tail`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> simp[] >>
  strip_tac >>
  `?j. terminates (step_inst j C h (s with vs_gas_readings := gs ++ tail))` by
    (qexists_tac `j` >>
     qpat_x_assum `terminates (R _ _ _ _)` mp_tac >>
     simp[Abbr `R`, dftIndexedExecTheory.dft_exec_cons_def] >>
     Cases_on `step_inst j C h (s with vs_gas_readings := gs ++ tail)` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  qpat_x_assum `!gs tail. LIST_REL _ m gs ==> _`
    (qspecl_then [`gs`, `tail`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  metis_tac[]
QED

Resume identity_suffix_mask[returning_head]:
  qpat_x_assum `?u. step_inst fuel C' h s = OK u` strip_assume_tac >>
  Cases_on `is_terminator h.inst_opcode`
  >- suspend "terminator_head" >>
  `dft_remaining_inv fn bb (xs ++ post) (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`] dftRunRelTheory.dft_remaining_inv_step)) >>
     simp[] >> metis_tac[APPEND]) >>
  `ctx_labels_bound C u.vs_labels /\ ctx_labels_bound C' u.vs_labels` by
    metis_tac[dftRunRelTheory.ctx_labels_bound_step] >>
  `~u.vs_call_ctx.cc_static` by
    metis_tac[venomInstProofsTheory.step_preserves_call_ctx] >>
  `terminates (R fuel C' xs (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (qpat_x_assum `terminates (R fuel C' (h::xs) s)` mp_tac >>
     simp[Abbr `R`, dftIndexedExecTheory.dft_exec_cons_def]) >>
  `u.vs_gas_readings = DROP (LENGTH (gas_events_step fuel C' s.vs_current_bb h s))
       s.vs_gas_readings` by
    (mp_tac (cj 1 gasCountTheory.gas_count_suffix) >>
     disch_then (qspecl_then [`fuel`, `C'`, `h`, `s`] mp_tac) >>
     simp[gasCountTheory.gas_count_suffix_def, gasEventsTheory.gas_events_length]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (fs[dftRunRelTheory.dft_remaining_inv_def]) >>
  `gas_events_block fuel C' s.vs_current_bb
     <|bb_label := s.vs_current_bb; bb_instructions :=
       REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ h::xs|>
     (u with vs_inst_idx := SUC s.vs_inst_idx) =
    E C' xs (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Abbr `E`] >> irule gas_events_block_suffix_cong >>
     qexists_tac `xs` >>
     simp[DROP_APPEND, DROP_DROP_T, arithmeticTheory.ADD1]) >>
  `LENGTH (E C' xs (u with vs_inst_idx := SUC s.vs_inst_idx)) <=
      LENGTH u.vs_gas_readings` by
    (qpat_x_assum `LENGTH (E C' (h::xs) s) <= _` mp_tac >>
     pure_once_rewrite_tac [markerTheory.Abbrev_def] >>
     simp[SimpLHS, Abbr `E`, Once gas_events_block_def,
          venomInstTheory.get_instruction_def, EL_APPEND_EQN]) >>
  `EVERY (\i. MEM i bb.bb_instructions) xs` by fs[] >>
  qpat_x_assum `!st. EVERY _ xs ==> _`
    (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[IgnAsm `u.vs_gas_readings = _`] >> strip_tac >>
  qexistsl_tac [`m ++ m'`, `es ++ es'`, `unused'`] >>
  qunabbrev_tac `R` >> qunabbrev_tac `E` >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  match_mp_tac (Q.INST [`u` |-> `u`, `unused` |-> `unused`]
    (CONV_RULE (REDEPTH_CONV BETA_CONV)
      (PURE_REWRITE_RULE [LET_THM] identity_mask_cons))) >>
  rule_assum_tac (CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
  rule_assum_tac (PURE_REWRITE_RULE
    [venomStateTheory.venom_state_accfupds, combinTheory.K_THM, REPLICATE, APPEND]) >>
  qpat_x_assum `u.vs_gas_readings = _` kall_tac >>
  qpat_assum `u.vs_current_bb = _` (fn th =>
    rule_assum_tac (PURE_REWRITE_RULE [th]) >> rewrite_tac [th] >> assume_tac th) >>
  simp[venomStateTheory.venom_state_accfupds] >>
  conj_tac
  >- (qpat_x_assum `!v. _ ==> EVERY IS_SOME m' /\ _`
        mp_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs tail. LIST_REL _ m' gs ==> _`
    (qspecl_then [`gs`, `tail`] mp_tac) >> simp[] >>
  POP_ASSUM_LIST (K all_tac) >> metis_tac[]
QED
Resume identity_suffix_mask[terminator_head]:
  `!n D st. R n D (h::xs) st =
     case step_inst n D h st of
       OK v => if v.vs_halted then Halt v else OK v
     | Halt v => Halt v | Abort a v => Abort a v
     | IntRet ir v => IntRet ir v | Error e => Error e` by
    (simp[Abbr `R`, dftIndexedExecTheory.dft_exec_cons_def] >>
     rpt gen_tac >> Cases_on `step_inst n D h st` >> simp[]) >>
  `!n D st. terminates (R n D (h::xs) st) <=>
      terminates (step_inst n D h st)` by
    (rpt gen_tac >> simp[] >> Cases_on `step_inst n D h st` >>
     simp[passSimulationDefsTheory.terminates_def] >>
     Cases_on `v.vs_halted` >> simp[passSimulationDefsTheory.terminates_def]) >>
  `!D st. E D (h::xs) st = gas_events_step fuel D st.vs_current_bb h st` by
    (simp[Abbr `E`, Once gas_events_block_def,
          venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
     rpt gen_tac >> Cases_on `step_inst fuel D h st` >> simp[]) >>
  qpat_x_assum `!u. _ ==> EVERY IS_SOME m /\ _`
    (qspec_then `u` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`m`, `es`, `unused`] >> simp[] >>
  conj_tac
  >- (Cases_on `u.vs_halted` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!gs tail. LIST_REL _ m gs ==> _`
    (qspecl_then [`gs`, `tail`] mp_tac) >> simp[] >>
  disch_then strip_assume_tac >> strip_tac >>
  qpat_x_assum `(?j. _) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> simp[residual_result_cases] >>
  strip_tac >> Cases_on `u.vs_halted` >>
  simp[restore_result_def, dftRunRelTheory.dft_res_rel_def,
       residual_result_cases, passSimulationDefsTheory.terminates_def]
QED
Finalise identity_suffix_mask

Theorem remaining_prefix_ok_cut[local]:
  !xs s u.
    wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
    dft_remaining_inv fn bb (xs ++ post) s /\
    EVERY (\i. ~is_terminator i.inst_opcode) xs /\
    FOLDR (dft_exec_cons fuel C) OK xs s = OK u ==>
    u.vs_halted = s.vs_halted /\ dft_remaining_inv fn bb post u
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  fs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> gvs[] >>
  `dft_remaining_inv fn bb (xs ++ post)
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`] dft_remaining_inv_step)) >>
     simp[] >> qexistsl_tac [`C`, `fuel`, `h`] >> simp[]) >>
  first_x_assum drule_all >> simp[] >>
  drule venomStepPropsTheory.step_inst_ok_halted >> simp[]
QED

Theorem extract_prefix_ok_cut[local]:
  wf_function fn /\ EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\
  EVERY (\i. ~is_terminator i.inst_opcode) (y::pre) /\
  FOLDR (dft_exec_cons fuel C) OK (y::pre) s = OK u ==>
  u.vs_current_bb = s.vs_current_bb /\
  u.vs_inst_idx = s.vs_inst_idx + LENGTH (y::pre) /\
  u.vs_halted = s.vs_halted /\ dft_remaining_inv fn bb post u
Proof
  strip_tac >>
  drule_all dftAvailabilityTheory.dft_prefix_frame >> strip_tac >>
  drule_all prefix_ok_cursor >> strip_tac >> simp[] >>
  fs[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C y s` >> gvs[] >>
  `dft_remaining_inv fn bb (pre ++ post)
    (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule dft_remaining_inv_step >> simp[] >>
     qexistsl_tac [`C`, `fuel`, `y`] >> simp[]) >>
  drule_all remaining_prefix_ok_cut >> simp[] >>
  drule venomStepPropsTheory.step_inst_ok_halted >> simp[]
QED

Theorem invoke_gas_returning_family[local]:
  y.inst_opcode = INVOKE /\ x.inst_opcode = GAS /\ inst_wf x /\
  dft_gas_swap_pair x y /\
  (!rest. step_inst fuel C y (s with vs_gas_readings := fg ++ rest) =
    OK (v with vs_gas_readings := rest)) ==>
  !w tail. ?a.
    step_inst fuel C x (s with vs_gas_readings := w::(fg ++ tail)) = OK a /\
    step_inst fuel C y a =
      OK (update_var (HD x.inst_outputs) w v with vs_gas_readings := tail)
Proof
  strip_tac >> drule_all dftRunRelTheory.dft_gas_ok_shape >> strip_tac >>
  rpt gen_tac >> simp[] >>
  drule dftRunRelTheory.dft_swap_output_frame >>
  disch_then (qspec_then `out` mp_tac) >> simp[] >> strip_tac >>
  `step_inst fuel C y (update_var out w (s with vs_gas_readings := fg ++ tail)) =
    OK (update_var out w (v with vs_gas_readings := tail))` by
    (mp_tac dftCommutationTheory.step_inst_invoke_frame >> simp[]) >>
  gvs[venomStateTheory.update_var_def]
QED

Theorem invoke_reached_prefix_observations[local]:
  y.inst_opcode = INVOKE /\
  EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x) pre /\
  LENGTH pg = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
  FOLDR (dft_exec_cons n C) OK pre
    (s with vs_gas_readings := pg ++ rest) = OK u ==>
  !k owner.
    (terminates (step_inst k C y u) <=>
     terminates (step_inst k C y
       (s with <|vs_gas_readings := rest;
                 vs_inst_idx := s.vs_inst_idx + LENGTH pre|>))) /\
    gas_events_step k C owner y u =
    gas_events_step k C owner y
      (s with <|vs_gas_readings := rest;
                vs_inst_idx := s.vs_inst_idx + LENGTH pre|>)
Proof
  strip_tac >> drule_all invoke_partner_prefix_concrete >> strip_tac >>
  `EVERY (\q. ~MEM (Var (FST q)) y.inst_operands /\
                ~MEM (FST q) y.inst_outputs) us` by
    (fs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
     metis_tac[dft_swap_output_frame]) >>
  rpt gen_tac >> conj_tac
  >- (drule_all invoke_updates_concrete_frame >>
      disch_then (qspecl_then [`k`, `C`,
        `s with <|vs_gas_readings := rest;
                  vs_inst_idx := s.vs_inst_idx + LENGTH pre|>`] mp_tac) >>
      strip_tac >> gvs[] >>
      Cases_on `step_inst k C y
        (s with <|vs_gas_readings := rest;
                  vs_inst_idx := s.vs_inst_idx + LENGTH pre|>)` >>
      gvs[passSimulationDefsTheory.terminates_def]) >>
  gvs[] >> irule gas_events_invoke_updates >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem invoke_reached_segment_mask[local]:
  !fuel C C' s pre y.
  let b0 = s with vs_inst_idx := s.vs_inst_idx + LENGTH pre in
    (!fn fn' t.
      LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
      LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
      o1_ctx_shape C /\ o1_ctx_shape C' /\
      MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
      dft_fn_rel fn fn' /\ strict_dom_vars_defined fn t /\
      fn_reachable fn t.vs_current_bb /\
      ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
      ~t.vs_call_ctx.cc_static /\ terminates (run_blocks fuel C' fn' t) /\
      gas_count_blocks fuel C' fn' t <= LENGTH t.vs_gas_readings ==>
      ?m es unused.
        LENGTH m = LENGTH es /\
        PERM (MAP THE (FILTER IS_SOME m) ++ unused) t.vs_gas_readings /\
        (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
          EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
        !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
          (?extra. es = gas_events_blocks fuel C fn
             (t with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?j. terminates (run_blocks j C fn
             (t with vs_gas_readings := gs ++ tail))) ==>
           terminates (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)) /\
           dft_res_rel
             (restore_result [] (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)))
             (restore_result [] (run_blocks fuel C' fn' t)) /\
           (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
             gas_events_blocks fuel C fn (t with vs_gas_readings := gs ++ tail) = es /\
             residual_result tail (run_blocks fuel C' fn' t)
               (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail))))) /\
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\
    ctx_labels_bound C b0.vs_labels /\ ctx_labels_bound C' b0.vs_labels /\
    ~b0.vs_call_ctx.cc_static /\ y.inst_opcode = INVOKE /\
    EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x) pre /\
    terminates (step_inst fuel C' y b0) /\
    LENGTH (gas_events_step fuel C' b0.vs_current_bb y b0) <= LENGTH b0.vs_gas_readings ==>
    ?m es unused.
      LENGTH m = LENGTH es /\
      PERM (MAP THE (FILTER IS_SOME m) ++ unused) b0.vs_gas_readings /\
      (!u. (step_inst fuel C' y b0 = OK u \/
            (?ir. step_inst fuel C' y b0 = IntRet ir u)) ==>
        EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
      !fg tail pg u n.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m fg /\
        LENGTH pg = LENGTH (FILTER (\x. x.inst_opcode = GAS) pre) /\
        FOLDR (dft_exec_cons n C) OK pre
          (s with vs_gas_readings := pg ++ (fg ++ tail)) = OK u ==>
        (?extra. es = gas_events_step fuel C s.vs_current_bb y u ++ extra) /\
        ((?j. terminates (step_inst j C y u)) ==>
          terminates (step_inst fuel C y (b0 with vs_gas_readings := fg ++ tail)) /\
          dft_res_rel
            (restore_result [] (step_inst fuel C y (b0 with vs_gas_readings := fg ++ tail)))
            (restore_result [] (step_inst fuel C' y b0)) /\
          (((?v. step_inst fuel C' y b0 = OK v) \/
            (?ir v. step_inst fuel C' y b0 = IntRet ir v)) ==>
            gas_events_step fuel C b0.vs_current_bb y
              (b0 with vs_gas_readings := fg ++ tail) = es /\
            residual_result tail (step_inst fuel C' y b0)
              (step_inst fuel C y (b0 with vs_gas_readings := fg ++ tail))))
Proof
  rpt gen_tac >> pure_rewrite_tac [LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all invoke_segment_mask >> strip_tac >> gvs[] >>
  qexistsl [`m`, `es`, `unused`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `FOLDR _ _ _ _ = OK _` mp_tac >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >> disch_tac >>
  drule_all invoke_reached_prefix_observations >> strip_tac >>
  qpat_x_assum `!gs tail. LIST_REL _ m gs ==> _`
    (qspecl_then [`fg`, `tail`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem gas_events_invoke_inst_idx[local]:
  y.inst_opcode = INVOKE ==>
  gas_events_step fuel D owner y (s with vs_inst_idx := k) =
  gas_events_step fuel D owner y s
Proof
  strip_tac >>
  simp[gas_events_step_def, instIdxIndepTheory.eval_ops_inst_idx,
       setup_callee_def, venom_state_component_equality]
QED

Theorem invoke_target_entry[local]:
  y.inst_opcode = INVOKE /\
  terminates (FOLDR (dft_exec_cons fuel D) OK (y::pre) s) /\
  LENGTH (gas_events_block fuel D s.vs_current_bb
    <|bb_label := s.vs_current_bb; bb_instructions :=
      REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (y::pre)|> s)
    <= LENGTH s.vs_gas_readings ==>
  terminates (step_inst fuel D y
    (s with vs_inst_idx := s.vs_inst_idx + LENGTH pre)) /\
  LENGTH (gas_events_step fuel D
    (s with vs_inst_idx := s.vs_inst_idx + LENGTH pre).vs_current_bb y
    (s with vs_inst_idx := s.vs_inst_idx + LENGTH pre)) <=
  LENGTH (s with vs_inst_idx := s.vs_inst_idx + LENGTH pre).vs_gas_readings
Proof
  strip_tac >>
  `terminates (step_inst fuel D y s)` by
    (qpat_x_assum `terminates (FOLDR _ _ _ _)` mp_tac >>
     simp[FOLDR, dftIndexedExecTheory.dft_exec_cons_def] >>
     Cases_on `step_inst fuel D y s` >>
     simp[passSimulationDefsTheory.terminates_def]) >>
  conj_tac
  >- (simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
      Cases_on `step_inst fuel D y s` >>
      gvs[passSimulationDefsTheory.terminates_def]) >>
  simp[gas_events_invoke_inst_idx] >>
  qpat_x_assum `LENGTH (gas_events_block _ _ _ _ _) <= _` mp_tac >>
  simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
       EL_APPEND_EQN, EL_REPLICATE] >>
  Cases_on `step_inst fuel D y s` >> simp[]
QED

Theorem prefix_stopped_or_reached_events[local]:
  !pre s y fuel C owner.
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre ==>
  let P = MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre);
      B = <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ [y])|>
  in
    ((~(?u. FOLDR (dft_exec_cons fuel C) OK pre s = OK u)) /\
      (?extra. P = gas_events_block fuel C owner B s ++ extra)) \/
    (?u. FOLDR (dft_exec_cons fuel C) OK pre s = OK u /\
      gas_events_block fuel C owner B s = P ++ gas_events_step fuel C owner y u)
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  Cases_on `?u. FOLDR (dft_exec_cons fuel C) OK pre s = OK u`
  >- (disj2_tac >> pop_assum strip_assume_tac >> qexists `u` >> simp[] >>
      drule_all noninvoke_prefix_events_exact >>
      disch_then (qspecl_then [`owner`, `[y]`] assume_tac) >>
      asm_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def,
           EL_APPEND_EQN] >>
      Cases_on `step_inst fuel C y u` >> simp[] >>
      Cases_on `is_terminator y.inst_opcode` >> simp[] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  disj1_tac >> simp[] >>
  mp_tac noninvoke_prefix_events_continue >>
  disch_then (qspecl_then [`pre`, `s`,
    `<|bb_label := owner; bb_instructions :=
       REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ (pre ++ [y])|>`,
    `[y]`, `[]`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[Excl "APPEND_ASSOC", DROP_APPEND, DROP_REPLICATE] >>
  `s.vs_inst_idx - (LENGTH pre + s.vs_inst_idx) = 0` by decide_tac >>
  simp[] >> metis_tac[]
QED

Theorem remaining_head_ready[local]:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  dft_remaining_inv fn bb (h::post) s ==>
  !v. MEM (Var v) h.inst_operands ==> v IN FDOM s.vs_vars
Proof
  rpt strip_tac >> irule dftRunRelTheory.dft_bubble_head_ready >>
  qexistsl_tac [`bb`, `fn`, `post`, `[]`, `h`] >>
  fs[dftRunRelTheory.dft_remaining_inv_def] >>
  metis_tac[dftScheduleOrderTheory.id_before_cons]
QED

Theorem invoke_partner_total_guards[local]:
  dft_gas_swap_pair h y /\ y.inst_opcode = INVOKE ==>
  ~is_pseudo h.inst_opcode /\ ~is_terminator h.inst_opcode /\
  h.inst_opcode <> ALLOCA /\ h.inst_opcode <> INVOKE /\
  h.inst_opcode <> CODECOPY /\ opcode_fail_class h.inst_opcode = NoFail /\
  ~dft_swap_runtime_error_opcode h.inst_opcode
Proof
  strip_tac >>
  `dft_gas_swap_pair y h` by metis_tac[dft_gas_swap_pair_sym] >>
  drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> strip_tac >>
  Cases_on `h.inst_opcode` >>
  gvs[dft_gas_swap_pair_def, dftDefsTheory.dft_abort_compatible_def,
      dftDefsTheory.dft_abort_kind_def, venomEffectsTheory.opcode_fail_class_def,
      dft_swap_runtime_error_opcode_def, venomInstTheory.is_alloca_op_def,
      venomEffectsTheory.read_effects_def, venomEffectsTheory.write_effects_def,
      venomInstTheory.is_ext_call_op_def, venomEffectsTheory.all_effects_def,
      venomInstTheory.is_terminator_def]
QED

Theorem invoke_partner_prefix_total[local]:
  !xs st.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (xs ++ post) st /\
  y.inst_opcode = INVOKE /\ EVERY (\x. dft_gas_swap_pair x y) xs ==>
  ?u. FOLDR (dft_exec_cons n D) OK xs st = OK u
Proof
  Induct >> simp[] >> rpt strip_tac >>
  drule_all invoke_partner_total_guards >> strip_tac >>
  `MEM h bb.bb_instructions` by
    fs[dftRunRelTheory.dft_remaining_inv_def] >>
  `inst_wf h` by fs[EVERY_MEM] >>
  `!v. MEM (Var v) h.inst_operands ==> v IN FDOM st.vs_vars` by
    (metis_tac[remaining_head_ready]) >>
  `!l. MEM (Label l) h.inst_operands ==> l IN FDOM st.vs_labels` by
    (fs[dftRunRelTheory.dft_remaining_inv_def] >> metis_tac[]) >>
  `!op. MEM op h.inst_operands ==> ?v. eval_operand op st = SOME v` by
    (metis_tac[dftRunRelTheory.dft_swap_operand_defined]) >>
  `?t. step_inst n D h st = OK t` by
    (irule dftRunRelTheory.dft_swap_guarded_nofail_total >> simp[]) >>
  `dft_remaining_inv fn bb (xs ++ post)
    (t with vs_inst_idx := SUC st.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`]
       dftRunRelTheory.dft_remaining_inv_step)) >>
     metis_tac[]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >> first_x_assum irule >> simp[]
QED

Theorem prefix_independent_update_events[local]:
  !xs s out w k.
    EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
      ~MEM out i.inst_outputs) xs ==>
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE k (mk_inst 0 STOP [] []) ++ xs|>
      ((update_var out w s) with vs_inst_idx := k) =
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> s
Proof
  `!h xs st. ~is_terminator h.inst_opcode ==>
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] []) ++ h::xs|> st =
    gas_events_step fuel C owner h st ++
      (case step_inst fuel C h st of
         OK v => gas_events_block fuel C owner
           <|bb_label := owner; bb_instructions :=
             REPLICATE (SUC st.vs_inst_idx) (mk_inst 0 STOP [] []) ++ xs|>
           (v with vs_inst_idx := SUC st.vs_inst_idx)
       | other => [])` by
    (rpt strip_tac >> simp[Once gas_events_block_def,
       venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
     Cases_on `step_inst fuel C h st` >> simp[] >>
     irule gas_events_block_suffix_cong >> qexists_tac `xs` >>
     simp[DROP_APPEND, DROP_DROP_T, arithmeticTheory.ADD1]) >>
  Induct_on `xs` >> rpt gen_tac >> strip_tac
  >- (simp[Once gas_events_block_def,
          venomInstTheory.get_instruction_def] >>
      simp[Once gas_events_block_def, venomInstTheory.get_instruction_def]) >>
  fs[EVERY_DEF] >>
  qpat_assum `!h xs st. _` (qspecl_then
    [`h`, `xs`, `(update_var out w s) with vs_inst_idx := k`]
    (fn th => simp[SRULE [] th])) >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[gas_events_invoke_inst_idx, gas_events_invoke_update_var,
           analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
           dftCommutationTheory.step_inst_invoke_frame] >>
      Cases_on `step_inst fuel C h s` >> simp[] >>
      first_x_assum (qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`] mp_tac) >>
      simp[update_var_def]) >>
  simp[gas_events_step_def,
       analysisSimProofsBaseTheory.step_inst_idx_indep,
       dftCommutationTheory.step_inst_frame] >>
  Cases_on `step_inst fuel C h s` >>
  simp[dftCommutationTheory.map_result_state_def,
       instIdxIndepTheory.exec_result_map_def] >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`] mp_tac) >>
  simp[update_var_def]
QED

Theorem prefix_independent_update_halt[local]:
  !xs s out w k u.
    EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
      ~MEM out i.inst_outputs) xs ==>
    (FOLDR (dft_exec_cons fuel C) OK xs
       ((update_var out w s) with vs_inst_idx := k) = Halt u <=>
     FOLDR (dft_exec_cons fuel C) OK xs s = Halt u)
Proof
  Induct >> rpt gen_tac >> strip_tac >- simp[] >>
  qpat_x_assum `!s out w k u. _` (fn ih =>
  fs[EVERY_DEF] >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[dftIndexedExecTheory.dft_exec_cons_def,
           analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
           dftCommutationTheory.step_inst_invoke_frame] >>
      Cases_on `step_inst fuel C h s` >> simp[] >>
      qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`, `u`] mp_tac ih >>
      simp[update_var_def]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def,
       analysisSimProofsBaseTheory.step_inst_idx_indep,
       dftCommutationTheory.step_inst_frame] >>
  Cases_on `step_inst fuel C h s` >>
  simp[dftCommutationTheory.map_result_state_def,
       instIdxIndepTheory.exec_result_map_def]
  >- (qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`, `u`] mp_tac ih >>
      simp[update_var_def]) >>
  metis_tac[dftRunRelTheory.dft_swap_nonterminator_halt_invoke])
QED

Theorem prefix_independent_update_error[local]:
  !xs s out w k e.
    EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
      ~MEM out i.inst_outputs) xs ==>
    (FOLDR (dft_exec_cons fuel C) OK xs
       ((update_var out w s) with vs_inst_idx := k) = Error e <=>
     FOLDR (dft_exec_cons fuel C) OK xs s = Error e)
Proof
  Induct >> rpt gen_tac >> strip_tac >- simp[] >>
  qpat_x_assum `!s out w k e. _` (fn ih =>
  fs[EVERY_DEF] >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[dftIndexedExecTheory.dft_exec_cons_def,
           analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
           dftCommutationTheory.step_inst_invoke_frame] >>
      Cases_on `step_inst fuel C h s` >> simp[] >>
      qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`, `e`] mp_tac ih >>
      simp[update_var_def]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def,
       analysisSimProofsBaseTheory.step_inst_idx_indep,
       dftCommutationTheory.step_inst_frame] >>
  Cases_on `step_inst fuel C h s` >>
  simp[dftCommutationTheory.map_result_state_def,
       instIdxIndepTheory.exec_result_map_def] >>
  qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`, `e`] mp_tac ih >>
  simp[update_var_def])
QED

Theorem prefix_independent_update_abort[local]:
  !xs s out w k a.
    EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
      ~MEM out i.inst_outputs) xs ==>
    ((?u. FOLDR (dft_exec_cons fuel C) OK xs
       ((update_var out w s) with vs_inst_idx := k) = Abort a u) <=>
     ?u. FOLDR (dft_exec_cons fuel C) OK xs s = Abort a u)
Proof
  Induct >> rpt gen_tac >> strip_tac >- simp[] >>
  qpat_x_assum `!s out w k a. _` (fn ih =>
  fs[EVERY_DEF] >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[dftIndexedExecTheory.dft_exec_cons_def,
           analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
           dftCommutationTheory.step_inst_invoke_frame] >>
      Cases_on `step_inst fuel C h s` >> simp[] >>
      qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`, `a`] mp_tac ih >>
      simp[update_var_def]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def,
       analysisSimProofsBaseTheory.step_inst_idx_indep,
       dftCommutationTheory.step_inst_frame] >>
  Cases_on `step_inst fuel C h s` >>
  simp[dftCommutationTheory.map_result_state_def,
       instIdxIndepTheory.exec_result_map_def] >>
  qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`, `a`] mp_tac ih >>
  simp[update_var_def])
QED

Theorem prefix_independent_update_terminates[local]:
  !xs s out w k.
    EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> out <> v) /\
      ~MEM out i.inst_outputs) xs ==>
    (terminates (FOLDR (dft_exec_cons fuel C) OK xs
       ((update_var out w s) with vs_inst_idx := k)) <=>
     terminates (FOLDR (dft_exec_cons fuel C) OK xs s))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[passSimulationDefsTheory.terminates_def] >>
  qpat_x_assum `!s out w k. _` (fn ih =>
  fs[EVERY_DEF] >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[dftIndexedExecTheory.dft_exec_cons_def,
           analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only,
           dftCommutationTheory.step_inst_invoke_frame] >>
      Cases_on `step_inst fuel C h s` >>
      simp[passSimulationDefsTheory.terminates_def] >>
      qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`] mp_tac ih >>
      simp[update_var_def, passSimulationDefsTheory.terminates_def]) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def,
       analysisSimProofsBaseTheory.step_inst_idx_indep,
       dftCommutationTheory.step_inst_frame] >>
  Cases_on `step_inst fuel C h s` >>
  simp[dftCommutationTheory.map_result_state_def,
       instIdxIndepTheory.exec_result_map_def,
       passSimulationDefsTheory.terminates_def] >>
  qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `out`, `w`, `SUC k`] mp_tac ih >>
  simp[update_var_def, passSimulationDefsTheory.terminates_def])
QED

Theorem prefix_nonterminator_no_intret[local]:
  !xs s ir u.
    EVERY (\i. ~is_terminator i.inst_opcode) xs ==>
    FOLDR (dft_exec_cons fuel C) OK xs s <> IntRet ir u
Proof
  Induct >> rpt gen_tac >> strip_tac >- simp[] >>
  fs[EVERY_DEF] >>
  simp[dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h s` >> simp[] >>
  metis_tac[dftRunRelTheory.dft_swap_nonterminator_no_intret]
QED

Theorem prefix_independent_updates_events[local]:
  !pairs s.
    EVERY (\p. EVERY (\i. ~is_terminator i.inst_opcode /\
      (!v. MEM (Var v) i.inst_operands ==> FST p <> v) /\
      ~MEM (FST p) i.inst_outputs) xs) pairs ==>
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|>
      (FOLDL (\st p. update_var (FST p) (SND p) st) s pairs) =
    gas_events_block fuel C owner
      <|bb_label := owner; bb_instructions :=
        REPLICATE s.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> s
Proof
  Induct >> rpt gen_tac >> strip_tac >- simp[] >>
  fs[EVERY_DEF] >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  simp[update_var_def] >> disch_then SUBST1_TAC >>
  mp_tac prefix_independent_update_events >>
  disch_then (qspecl_then
    [`xs`, `s`, `FST h`, `SND h`, `s.vs_inst_idx`] mp_tac) >>
  simp[update_var_def]
QED

Theorem invoke_partner_nongas_outputs[local]:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ i::post) s /\
  EVERY (\x. ~dft_must_order x i) pre /\
  c.inst_opcode = INVOKE /\ dft_gas_swap_pair c i /\
  i.inst_opcode <> GAS ==>
  ?pairs. MAP FST pairs = i.inst_outputs /\
    step_inst n D i s =
      OK (FOLDL (\st (out,w). update_var out w st) s pairs)
Proof
  strip_tac >>
  drule_all dftGasInvCallPartnerTheory.inv_call_partner_class >> strip_tac >>
  `dft_gas_swap_pair i c` by metis_tac[dft_gas_swap_pair_sym] >>
  drule_all invoke_partner_total_guards >> strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==> v IN FDOM s.vs_vars` by
    (Cases_on `pre = []` >- (gvs[] >> metis_tac[remaining_head_ready]) >>
     metis_tac[dft_remaining_inv_ready]) >>
  `!l. MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels` by
    (fs[dft_remaining_inv_def] >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==> ?v. eval_operand op s = SOME v` by
    metis_tac[dft_swap_operand_defined] >>
  `inst_wf i` by
    (fs[dftRunRelTheory.dft_remaining_inv_def, EVERY_MEM] >> metis_tac[]) >>
  `?t. step_inst n D i s = OK t` by
    (irule dft_swap_guarded_nofail_total >> simp[]) >>
  simp[] >>
  irule dftBlockSimTheory.pure_step_structure >>
  simp[] >>
  qpat_x_assum `step_inst n D i s = OK _` mp_tac >>
  simp[step_inst_non_invoke]
QED

Theorem prefix_extract_mask[local]:
  !fuel C C'.
  let CalleeIH = (!fn fn' t.
      LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
      LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
      o1_ctx_shape C /\ o1_ctx_shape C' /\
      MEM fn C.ctx_functions /\ fn' = dft_fn fn /\
      dft_fn_rel fn fn' /\ strict_dom_vars_defined fn t /\
      fn_reachable fn t.vs_current_bb /\
      ctx_labels_bound C t.vs_labels /\ ctx_labels_bound C' t.vs_labels /\
      ~t.vs_call_ctx.cc_static /\ terminates (run_blocks fuel C' fn' t) /\
      gas_count_blocks fuel C' fn' t <= LENGTH t.vs_gas_readings ==>
      ?m es unused.
        LENGTH m = LENGTH es /\
        PERM (MAP THE (FILTER IS_SOME m) ++ unused) t.vs_gas_readings /\
        (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
          EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
        !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
          (?extra. es = gas_events_blocks fuel C fn
             (t with vs_gas_readings := gs ++ tail) ++ extra) /\
          ((?j. terminates (run_blocks j C fn
             (t with vs_gas_readings := gs ++ tail))) ==>
           terminates (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)) /\
           dft_res_rel
             (restore_result [] (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)))
             (restore_result [] (run_blocks fuel C' fn' t)) /\
           (!u. (?ir. run_blocks fuel C' fn' t = IntRet ir u) ==>
             gas_events_blocks fuel C fn (t with vs_gas_readings := gs ++ tail) = es /\
             residual_result tail (run_blocks fuel C' fn' t)
               (run_blocks fuel C fn (t with vs_gas_readings := gs ++ tail)))));
      R = (\n D xs st. FOLDR (dft_exec_cons n D) OK xs st);
      E = (\D xs st. gas_events_block fuel D st.vs_current_bb
        <|bb_label := st.vs_current_bb; bb_instructions :=
          REPLICATE st.vs_inst_idx (mk_inst 0 STOP [] []) ++ xs|> st)
  in
  !fn bb pre y post s.
    CalleeIH /\
    LIST_REL (\f g. g = dft_fn f) C.ctx_functions C'.ctx_functions /\
    LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
    o1_ctx_shape C /\ o1_ctx_shape C' /\ MEM fn C.ctx_functions /\
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
    EVERY (\i. MEM i bb.bb_instructions) (pre ++ y::post) /\
    dft_remaining_inv fn bb (pre ++ y::post) s /\
    EVERY (\x. dft_gas_swap_pair x y /\ ~dft_must_order x y) pre /\
    ctx_labels_bound C s.vs_labels /\ ctx_labels_bound C' s.vs_labels /\
    ~s.vs_call_ctx.cc_static /\ terminates (R fuel C' (y::pre) s) /\
    LENGTH (E C' (y::pre) s) <= LENGTH s.vs_gas_readings ==>
    (!u. EVERY (\i. ~is_terminator i.inst_opcode) (y::pre) /\
      R fuel C' (y::pre) s = OK u ==>
      u.vs_current_bb = s.vs_current_bb /\
      u.vs_inst_idx = s.vs_inst_idx + LENGTH (y::pre) /\
      u.vs_halted = s.vs_halted /\ dft_remaining_inv fn bb post u) /\
    ?m es unused.
      LENGTH m = LENGTH es /\
      PERM (MAP THE (FILTER IS_SOME m) ++ unused) s.vs_gas_readings /\
      (!u. (R fuel C' (y::pre) s = OK u \/ (?ir. R fuel C' (y::pre) s = IntRet ir u)) ==>
        EVERY IS_SOME m /\ unused = u.vs_gas_readings) /\
      !gs tail. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) m gs ==>
        (?extra. es = E C (pre ++ [y]) (s with vs_gas_readings := gs ++ tail) ++ extra) /\
        ((?j. terminates (R j C (pre ++ [y]) (s with vs_gas_readings := gs ++ tail))) ==>
          terminates (R fuel C (pre ++ [y]) (s with vs_gas_readings := gs ++ tail)) /\
          dft_res_rel
            (restore_result [] (R fuel C (pre ++ [y]) (s with vs_gas_readings := gs ++ tail)))
            (restore_result [] (R fuel C' (y::pre) s)) /\
          (((?u. R fuel C' (y::pre) s = OK u) \/ (?ir u. R fuel C' (y::pre) s = IntRet ir u)) ==>
            E C (pre ++ [y]) (s with vs_gas_readings := gs ++ tail) = es /\
            residual_result tail (R fuel C' (y::pre) s)
              (R fuel C (pre ++ [y]) (s with vs_gas_readings := gs ++ tail))))
Proof
  rpt gen_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all extract_prefix_ok_cut >> simp[]) >>
  Cases_on `y.inst_opcode = INVOKE`
  >- (drule_all invoke_target_entry >> strip_tac >>
      `EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x) pre` by
        (fs[EVERY_MEM] >> metis_tac[MEM_APPEND, MEM]) >>
      mp_tac (Q.SPECL [`fuel`, `C`, `C'`, `s`, `pre`, `y`]
        invoke_reached_segment_mask) >>
      simp[LET_THM] >>
      disch_then (qx_choose_then `mf` (qx_choose_then `ef`
        (qx_choose_then `uf` strip_assume_tac))) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre` by
        (fs[EVERY_MEM] >> metis_tac[dft_gas_swap_pair_sym,
          dftGasInvCallPartnerTheory.inv_call_partner_class]) >>
      reverse (Cases_on `?v. step_inst fuel C' y
        (s with vs_inst_idx := LENGTH pre + s.vs_inst_idx) = OK v`)
      >- (qexistsl [`REPLICATE (LENGTH (FILTER (\i. i.inst_opcode = GAS) pre)) NONE ++ mf`,
           `MAP (\i. (s.vs_current_bb,i.inst_id))
             (FILTER (\i. i.inst_opcode = GAS) pre) ++ ef`, `uf`] >>
          `FILTER IS_SOME
             (REPLICATE (LENGTH (FILTER (\i. i.inst_opcode = GAS) pre)) (NONE : bytes32 option)) = []` by
            simp[FILTER_EQ_NIL, EVERY_REPLICATE] >>
          simp[FILTER_APPEND, MAP_APPEND] >> conj_tac
          >- (rpt gen_tac >>
              `~(?v. step_inst fuel C' y s = OK v)` by
                (qpat_x_assum `~(?v. step_inst _ _ _ _ = OK v)` mp_tac >>
                 simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
                 Cases_on `step_inst fuel C' y s` >> simp[]) >>
              simp[dftIndexedExecTheory.dft_exec_cons_def] >>
              Cases_on `step_inst fuel C' y s` >> gvs[] >>
              metis_tac[dftRunRelTheory.dft_swap_nonterminator_no_intret,
                        venomInstTheory.is_terminator_def]) >>
          rpt gen_tac >> strip_tac >>
          qpat_x_assum `LIST_REL _ (_ ++ _) gs` mp_tac >>
          pure_rewrite_tac[LIST_REL_SPLIT1] >>
          disch_then (qx_choose_then `pg` (qx_choose_then `fg` strip_assume_tac)) >>
          `LENGTH pg = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre)` by
            (qpat_x_assum `LIST_REL _ (REPLICATE _ _) pg`
               (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[]) >>
          conj_tac
          >- (drule prefix_stopped_or_reached_events >>
              disch_then (qspec_then `s with vs_gas_readings := gs ++ tail` mp_tac) >>
              disch_then (qspecl_then [`y`, `fuel`, `C`, `s.vs_current_bb`] mp_tac) >>
              simp[LET_THM] >>
              strip_tac
              >- (rename1 `MAP _ _ = _ ++ ep` >>
                  qexists_tac `ep ++ ef` >>
                  pure_rewrite_tac[APPEND_ASSOC] >> asm_rewrite_tac[]) >>
              qpat_x_assum `!fg tail pg u n. _`
                (qspecl_then [`fg`, `tail`, `pg`, `u`, `fuel`] mp_tac) >>
              simp[] >> strip_tac >>
              qpat_x_assum `?extra. ef = _ ++ extra`
                (qx_choose_then `er` assume_tac) >>
              qexists_tac `er` >> simp[APPEND_ASSOC]) >>
          strip_tac >>
          `dft_remaining_inv fn bb (pre ++ y::post)
            (s with vs_gas_readings := gs ++ tail)` by
            (irule dftRunRelTheory.dft_remaining_inv_gas_variant >>
             qexists `s` >> simp[]) >>
          `!n. ?u. FOLDR (dft_exec_cons n C) OK pre
            (s with vs_gas_readings := gs ++ tail) = OK u` by
            (gen_tac >> irule invoke_partner_prefix_total >> conj_tac
             >- (qexists `y` >> fs[EVERY_MEM]) >>
             qexistsl [`bb`, `fn`, `y::post`] >> simp[]) >>
          `EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_MEM] >>
          first_assum (qspec_then `fuel` (qx_choose_then `u` assume_tac)) >>
          `terminates (step_inst j C y u)` by
            (drule_all prefix_exact_cut_terminates >>
             simp[dftIndexedExecTheory.dft_exec_cons_def,
               venomInstTheory.is_terminator_def] >>
             Cases_on `step_inst j C y u` >>
             simp[passSimulationDefsTheory.terminates_def]) >>
          qpat_x_assum `gs = _` SUBST_ALL_TAC >>
          qpat_assum `!fg tail pg u n. _`
            (qspecl_then [`fg`, `tail`, `pg`, `u`, `fuel`] mp_tac) >>
          simp[APPEND_ASSOC] >> strip_tac >>
          qpat_x_assum `(?j. terminates (step_inst j C y u)) ==> _`
            (mp_tac) >>
          (impl_tac >- metis_tac[]) >> strip_tac >>
          mp_tac (Q.SPECL [`pre`, `s`, `pg`, `fg ++ tail`]
            invoke_partner_prefix_concrete) >>
          pure_rewrite_tac[APPEND_ASSOC] >>
          disch_then (drule_at (Pos last)) >>
          (impl_tac >- simp[]) >> strip_tac >>
          `EVERY (\q. ~MEM (Var (FST q)) y.inst_operands /\
                        ~MEM (FST q) y.inst_outputs) us` by
            (fs[EVERY_MEM, MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
             metis_tac[dft_swap_output_frame]) >>
          drule_all invoke_updates_concrete_frame >>
          disch_then (qspecl_then [`fuel`, `C`,
            `s with <|vs_gas_readings := fg ++ tail;
                      vs_inst_idx := s.vs_inst_idx + LENGTH pre|>`] mp_tac) >>
          strip_tac >>
          qmatch_asmsub_abbrev_tac
            `dft_res_rel (restore_result [] sr) (restore_result [] tr)` >>
          `~(?v. sr = OK v)` by
            (strip_tac >>
             qpat_x_assum `dft_res_rel _ _` mp_tac >>
             qpat_x_assum `~(?v. tr = OK v)` mp_tac >>
             pop_assum SUBST1_TAC >>
             Cases_on `tr` >>
             simp[dftRunRelTheory.dft_res_rel_def, restore_result_def]) >>
          `step_inst fuel C y u = sr` by
            (qpat_x_assum `step_inst fuel C y (FOLDL _ _ _) = _` mp_tac >>
             qpat_x_assum `u = _` (fn th => rewrite_tac[GSYM th]) >>
             Cases_on `sr` >> gvs[]) >>
          `FOLDR (dft_exec_cons fuel C) OK (pre ++ [y])
             (s with vs_gas_readings := (pg ++ fg) ++ tail) = sr` by
            (pure_rewrite_tac[FOLDR_APPEND] >>
             simp[Once dftRunRelTheory.dft_exec_prefix_continue] >>
             simp[dftIndexedExecTheory.dft_exec_cons_def,
               venomInstTheory.is_terminator_def] >>
             Cases_on `sr` >> gvs[]) >>
          `step_inst fuel C' y s = tr` by
            (qpat_x_assum `Abbrev (tr = _)` mp_tac >>
             simp[markerTheory.Abbrev_def,
               analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
             Cases_on `step_inst fuel C' y s` >> simp[] >> metis_tac[]) >>
          simp[dftIndexedExecTheory.dft_exec_cons_def,
            venomInstTheory.is_terminator_def] >>
          Cases_on `tr` >> gvs[] >>
          metis_tac[dftRunRelTheory.dft_swap_nonterminator_no_intret,
            venomInstTheory.is_terminator_def]) >>
      `?v. step_inst fuel C' y s = OK v` by
        (qpat_x_assum `?v. step_inst _ _ _ _ = OK v` mp_tac >>
         simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
         Cases_on `step_inst fuel C' y s` >> simp[]) >>

      `dft_remaining_inv fn bb (pre ++ post)
        (v with vs_inst_idx := SUC s.vs_inst_idx)` by
        (irule dftRunRelTheory.dft_remaining_inv_step >> metis_tac[
           venomInstTheory.is_terminator_def]) >>
      `?u. FOLDR (dft_exec_cons fuel C') OK pre
        (v with vs_inst_idx := SUC s.vs_inst_idx) = OK u` by
        (irule invoke_partner_prefix_total >> conj_tac
         >- (qexists `y` >> fs[EVERY_MEM]) >>
         qexistsl [`bb`, `fn`, `post`] >> simp[]) >>
      `uf = v.vs_gas_readings /\ EVERY IS_SOME mf` by
        (qpat_x_assum `!u. step_inst _ _ _ _ = OK u \/ _ ==> _`
          (qspec_then `v with vs_inst_idx := LENGTH pre + s.vs_inst_idx` mp_tac) >>
         simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only]) >>
      `v.vs_gas_readings = DROP (gas_count_step fuel C' y s) s.vs_gas_readings` by
        (mp_tac (cj 1 gasCountTheory.gas_count_suffix) >>
         disch_then (qspecl_then [`fuel`, `C'`, `y`, `s`] mp_tac) >>
         simp[gasCountTheory.gas_count_suffix_def]) >>
      qmatch_asmsub_abbrev_tac `LENGTH (gas_events_block fuel C' owner B s) <= _` >>
      `DROP (v with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
        B.bb_instructions = pre ++ []` by
        simp[Abbr `B`, DROP_APPEND, DROP_REPLICATE, arithmeticTheory.ADD1] >>
      drule_all noninvoke_prefix_events_exact_at >>
      disch_then (qspec_then `owner` assume_tac) >>
      `get_instruction B s.vs_inst_idx = SOME y` by
        simp[Abbr `B`, venomInstTheory.get_instruction_def, EL_APPEND_EQN] >>
      `gas_events_block fuel C' owner B s =
        gas_events_step fuel C' owner y s ++
        MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++
        gas_events_block fuel C' owner B u` by
        (CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [gas_events_block_def])) >>
         simp[venomInstTheory.is_terminator_def, APPEND_ASSOC]) >>
      `gas_count_step fuel C' y s +
        LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) <= LENGTH s.vs_gas_readings` by
        (qpat_x_assum `LENGTH (gas_events_block _ _ _ _ s) <= _` mp_tac >>
         asm_rewrite_tac[LENGTH_APPEND, LENGTH_MAP, cj 1 gas_events_length] >>
         decide_tac) >>
      `LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) <= LENGTH uf` by
        (fs[LENGTH_DROP] >> decide_tac) >>
      qabbrev_tac `k = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre)` >>
      qexistsl [`MAP SOME (TAKE k uf) ++ mf`,
        `MAP (\i. (owner,i.inst_id)) (FILTER (\i. i.inst_opcode = GAS) pre) ++ ef`,
        `DROP k uf`] >>
      conj_tac >- simp[LENGTH_TAKE, Abbr `k`] >>
      conj_tac
      >- (simp[NoAsms, FILTER_APPEND, FILTER_MAP, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF] >>
          irule PERM_TRANS >>
          qexists `MAP THE (FILTER IS_SOME mf) ++ uf` >>
          reverse conj_tac >- first_assum ACCEPT_TAC >>
          CONV_TAC (RAND_CONV (RAND_CONV
            (REWR_CONV (GSYM (Q.SPECL [`k`, `uf`] TAKE_DROP))))) >>
          pure_rewrite_tac[APPEND_ASSOC] >>
          rewrite_tac[PERM_APPEND_IFF, PERM_APPEND]) >>
      `u.vs_gas_readings = DROP k uf` by
        (mp_tac (Q.SPECL [`pre`, `v with vs_inst_idx := SUC s.vs_inst_idx`,
          `TAKE k uf`, `DROP k uf`, `u`]
          (Q.INST [`fuel` |-> `fuel`, `C` |-> `C'`] noninvoke_prefix_readings_exact)) >>
         simp[TAKE_DROP, LENGTH_TAKE, Abbr `k`] >>
         qpat_x_assum `FOLDR _ _ pre _ = OK u` mp_tac >>
         qpat_x_assum `v.vs_gas_readings = _` (SUBST1_TAC o SYM) >>
         simp[]) >>
      conj_tac
      >- (pure_asm_rewrite_tac[dftIndexedExecTheory.dft_exec_cons_def,
               venomInstTheory.is_terminator_def] >>
          simp[NoAsms] >>
          pure_asm_rewrite_tac[] >>
          simp[NoAsms, EVERY_APPEND, EVERY_MAP] >>
          metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `LIST_REL _ (_ ++ _) gs` mp_tac >>
      pure_rewrite_tac[LIST_REL_SPLIT1] >>
      disch_then (qx_choose_then `pg` (qx_choose_then `fg` strip_assume_tac)) >>
      `LENGTH pg = k` by
        (qpat_x_assum `LIST_REL _ (MAP SOME _) pg`
          (mp_tac o MATCH_MP LIST_REL_LENGTH) >> simp[LENGTH_TAKE]) >>
      conj_tac
      >- (drule prefix_stopped_or_reached_events >>
          disch_then (qspec_then `s with vs_gas_readings := gs ++ tail` mp_tac) >>
          disch_then (qspecl_then [`y`, `fuel`, `C`, `owner`] mp_tac) >>
          simp[LET_THM] >> strip_tac
          >- (rename1 `MAP _ _ = _ ++ ep` >>
              qexists_tac `ep ++ ef` >>
              pure_rewrite_tac[APPEND_ASSOC] >> asm_rewrite_tac[]) >>
          qpat_x_assum `!fg tail pg u n. _`
            (qspecl_then [`fg`, `tail`, `pg`, `u'`, `fuel`] mp_tac) >>
          simp[]) >>
      `pg = TAKE k uf` by
        (qpat_x_assum `LIST_REL _ (MAP SOME _) pg` mp_tac >>
         simp[LIST_REL_MAP1, combinTheory.o_DEF, SF ETA_ss]) >>
      `?w. FOLDR (dft_exec_cons fuel C) OK pre
        (s with vs_gas_readings := pg ++ (fg ++ tail)) = OK w` by
        (irule invoke_partner_prefix_total >> conj_tac
         >- (qexists `y` >> fs[EVERY_MEM]) >>
         qexistsl [`bb`, `fn`, `y::post`] >>
         simp[] >> irule dftRunRelTheory.dft_remaining_inv_gas_variant >>
         qexists `s` >> simp[]) >>
      `EVERY (\x. dft_gas_swap_pair x y /\ inst_wf x /\
        dftGasInvCallPartner$inv_partner_inputs x s
          (v with vs_inst_idx := SUC s.vs_inst_idx)) pre` by
        (fs[EVERY_MEM] >> rpt strip_tac >>
         `dftGasInvCallPartner$inv_partner_inputs x s v` by
           (irule invoke_return_partner_inputs >> metis_tac[]) >>
         gvs[dftGasInvCallPartnerTheory.inv_partner_inputs_def, eval_operand_def] >>
         Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
      drule_at (Pat `FOLDR _ _ _ _ = OK _`)
        (Q.INST [`D` |-> `C'`] invoke_partner_prefix_portable) >>
      disch_then (qspecl_then [`y`, `C'`,
        `v with vs_inst_idx := SUC s.vs_inst_idx`, `DROP k uf`] mp_tac) >>
      (impl_tac >- simp[Abbr `k`]) >>
      strip_tac >>
      `pg ++ DROP k uf = v.vs_gas_readings` by
        (asm_rewrite_tac[TAKE_DROP]) >>
      qpat_x_assum `FOLDR _ _ pre (v with <|vs_gas_readings := _; vs_inst_idx := _|>) = _`
        mp_tac >>
      simp[IgnAsm `uf = _`, IgnAsm `v.vs_gas_readings = _`] >>
      disch_tac >>
      disch_then (qx_choose_then `j` assume_tac) >>
      `terminates (step_inst j C y w)` by
        (`terminates (FOLDR (dft_exec_cons j C) OK [y] w)` by
           (irule prefix_exact_cut_terminates >>
            qexistsl [`fuel`, `pre`, `s with vs_gas_readings := gs ++ tail`] >>
            conj_tac
            >- (qpat_x_assum `terminates (FOLDR _ _ (pre ++ [y]) _)` mp_tac >> simp[]) >>
            conj_tac
            >- (qpat_x_assum `FOLDR _ _ pre _ = OK w` mp_tac >> simp[APPEND_ASSOC]) >>
            fs[EVERY_MEM]) >>
         qpat_x_assum `terminates (FOLDR _ _ [y] _)` mp_tac >>
         qpat_assum `y.inst_opcode = INVOKE` (fn th =>
           simp[NoAsms, th, FOLDR, dftIndexedExecTheory.dft_exec_cons_def,
             venomInstTheory.is_terminator_def]) >>
         Cases_on `step_inst j C y w` >>
         simp[NoAsms, passSimulationDefsTheory.terminates_def]) >>
      qpat_x_assum `!fg tail pg u n. _`
        (qspecl_then [`fg`, `tail`, `pg`, `w`, `fuel`] mp_tac) >>
      (impl_tac >-
        (conj_tac >- asm_rewrite_tac[] >>
         conj_tac >- asm_rewrite_tac[] >>
         qpat_x_assum `FOLDR _ _ pre _ = OK w` mp_tac >> simp[APPEND_ASSOC])) >>
      strip_tac >>
      qpat_x_assum `(?j. terminates (step_inst j C y w)) ==> _` mp_tac >>
      (impl_tac >- (qexists `j` >> asm_rewrite_tac[])) >>
      strip_tac >>
      qpat_x_assum `(_ \/ _) ==> _` mp_tac >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      `step_inst fuel C' y (s with vs_inst_idx := LENGTH pre + s.vs_inst_idx) =
        OK (v with vs_inst_idx := LENGTH pre + s.vs_inst_idx)` by
        (simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only]) >>
      qpat_assum `step_inst fuel C' y (s with vs_inst_idx := _) = OK _`
        (fn th => qpat_x_assum `residual_result tail _ _`
          (strip_assume_tac o SIMP_RULE (srw_ss())
            [th, residual_result_def, stateEquivTheory.lift_result_def])) >>
      `EVERY (\q. ~MEM (Var (FST q)) y.inst_operands /\
                    ~MEM (FST q) y.inst_outputs) us` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      drule_all invoke_updates_concrete_frame >>
      disch_then (qspecl_then [`fuel`, `C`,
        `s with <|vs_inst_idx := LENGTH pre + s.vs_inst_idx;
                  vs_gas_readings := fg ++ tail|>`] mp_tac) >>
      strip_tac >>
      `step_inst fuel C y
        (s with <|vs_inst_idx := LENGTH pre + s.vs_inst_idx;
                  vs_gas_readings := fg ++ tail|>) =
        OK (v with <|vs_inst_idx := LENGTH pre + s.vs_inst_idx;
                     vs_gas_readings := tail|>)` by
        (qpat_x_assum `stateEquiv$lift_result _ _ _ _ _` mp_tac >>
         Cases_on `step_inst fuel C y
           (s with <|vs_inst_idx := LENGTH pre + s.vs_inst_idx;
                     vs_gas_readings := fg ++ tail|>)` >>
         simp[NoAsms, stateEquivTheory.lift_result_def]) >>
      `step_inst fuel C y w = OK
        (FOLDL (\st q. update_var (FST q) (SND q) st)
          (v with <|vs_inst_idx := LENGTH pre + s.vs_inst_idx;
                    vs_gas_readings := tail|>) us)` by
        (qpat_x_assum `step_inst fuel C y (FOLDL _ _ _) = _` mp_tac >>
         qpat_assum `w = _` (fn th => rewrite_tac[GSYM th]) >>
         simp[IgnAsm `uf = _`, IgnAsm `v.vs_gas_readings = _`]) >>
      `EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_MEM] >>
      `FOLDR (dft_exec_cons fuel C) OK pre
        (s with vs_gas_readings := TAKE k uf ++ fg ++ tail) = OK w` by
        (qpat_x_assum `FOLDR _ _ pre _ = OK w` mp_tac >> simp[APPEND_ASSOC]) >>
      `FOLDR (dft_exec_cons fuel C) OK (pre ++ [y])
        (s with vs_gas_readings := TAKE k uf ++ fg ++ tail) =
        OK (u with vs_gas_readings := tail)` by
        (pure_rewrite_tac[FOLDR_APPEND] >>
         simp[Once dftRunRelTheory.dft_exec_prefix_continue] >>
         simp[dftIndexedExecTheory.dft_exec_cons_def,
           venomInstTheory.is_terminator_def, updates_readings_cursor,
           arithmeticTheory.ADD_CLAUSES] >>
         ` (\st q. update_var (FST q) (SND q) st) =
           (\st (out,value). update_var out value st)` by
           simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
         pop_assum (fn th => pure_rewrite_tac[th]) >>
         simp[venomExecSemanticsTheory.foldl_update_var_inst_idx,
           venomExecSemanticsTheory.foldl_update_var_idx,
           gasOracleReplayTheory.gas_fold_updates]) >>
      qpat_x_assum `ef = _ ++ extra` kall_tac >>
      qpat_x_assum `uf = _` kall_tac >>
      qpat_x_assum `v.vs_gas_readings = _` kall_tac >>
      simp[dftIndexedExecTheory.dft_exec_cons_def,
        venomInstTheory.is_terminator_def,
        passSimulationDefsTheory.terminates_def, restore_result_def,
        dftRunRelTheory.dft_res_rel_def, residual_result_def,
        stateEquivTheory.lift_result_def] >>
      drule_all noninvoke_prefix_events_exact >>
      disch_then (qspecl_then [`owner`, `[y]`] mp_tac) >>
      simp[NoAsms] >> disch_then SUBST1_TAC >>
      `EVERY (\q. !z. MEM (Var z) y.inst_operands ==> FST q <> z) us` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      `gas_events_step fuel C owner y w = ef` by
        (qpat_assum `w = _` (fn th => rewrite_tac[th]) >>
         simp[gas_events_invoke_updates, arithmeticTheory.ADD_COMM]) >>
      qpat_assum `step_inst fuel C y w = OK _` (fn step =>
        qpat_assum `gas_events_step fuel C owner y w = ef` (fn events =>
          simp[NoAsms, Once gas_events_block_def,
            venomInstTheory.get_instruction_def, EL_APPEND_EQN,
            step, events, venomInstTheory.is_terminator_def])) >>
      simp[NoAsms, Once gas_events_block_def,
        venomInstTheory.get_instruction_def] ) >>
  FAIL_TAC "noninvoke extraction pending"
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
