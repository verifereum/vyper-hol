(* Emitted-code inventories for recursive calldata decoding. *)
Theory entryDecoderCfgInventory
Ancestors
  entryObserverCfg entryDecoderCfgProducer entryDecoderCfgRules abiEncoder fragExec compileEnv venomExecSemantics
  venomInst list rich_list arithmetic pred_set

Theorem entry_straight_instruction_inventory[local]:
  fn_has_code start last_st fn /\
  last_st.cs_current_bb = start.cs_current_bb /\
  last_st.cs_current_insts = start.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  lookup_block start.cs_current_bb fn.fn_blocks = SOME bb /\
  LENGTH start.cs_current_insts <= idx /\ idx < LENGTH last_st.cs_current_insts /\
  get_instruction bb idx = SOME inst ==>
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  idx + 1 <= LENGTH last_st.cs_current_insts
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `idx - LENGTH start.cs_current_insts < LENGTH code` by gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  fs[EVERY_EL] >> metis_tac[]
QED

(* Only emitted instruction positions, with the final open cut included. *)
Definition entry_emitted_positions_def:
  entry_emitted_positions (start:compile_state) (last_st:compile_state) =
    {(lbl,idx) |
      (lbl <> start.cs_current_bb \/ LENGTH start.cs_current_insts <= idx) /\
      ((?bb. MEM bb (emitted_blocks start last_st) /\
             lbl = bb.bb_label /\ idx < LENGTH bb.bb_instructions) \/
       (lbl = last_st.cs_current_bb /\ idx <= LENGTH last_st.cs_current_insts))}
End

Theorem entry_emitted_positions_refl[local]:
  entry_emitted_positions st st = {(st.cs_current_bb,LENGTH st.cs_current_insts)}
Proof
  rw[EXTENSION, entry_emitted_positions_def, emitted_blocks_def] >>
  Cases_on `x` >> simp[] >> eq_tac >> strip_tac >> gvs[]
QED

Theorem entry_emitted_positions_cut_bound:
  compile_state_ok last_st /\
  (last_st.cs_current_bb,idx) IN entry_emitted_positions start last_st ==>
  idx <= LENGTH last_st.cs_current_insts
Proof
  simp[entry_emitted_positions_def, compile_state_ok_def, ALL_DISTINCT] >>
  strip_tac >> gvs[] >>
  `MEM bb last_st.cs_blocks` by
    (gvs[emitted_blocks_def] >> metis_tac[MEM_TAKE]) >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem entry_emitted_positions_start[local]:
  cs_extends start last_st /\ ~block_is_terminated start /\
  EVERY (\bb. bb.bb_instructions <> [] /\
    is_terminator (LAST bb.bb_instructions).inst_opcode)
    (emitted_blocks start last_st) ==>
  (start.cs_current_bb,LENGTH start.cs_current_insts) IN
    entry_emitted_positions start last_st
Proof
  simp[cs_extends_def] >> strip_tac >> Cases_on `new = []`
  >- (gvs[entry_emitted_positions_def, IS_PREFIX_APPEND] >> simp[]) >>
  `MEM (LAST new) new` by simp[LAST_MEM] >>
  `emitted_blocks start last_st = new` by
    (irule emitted_blocks_append >> simp[]) >>
  `isPREFIX start.cs_current_insts (LAST new).bb_instructions /\
   (LAST new).bb_label = start.cs_current_bb` by gvs[] >>
  `LENGTH start.cs_current_insts < LENGTH (LAST new).bb_instructions` by
    (fs[EVERY_MEM] >>
     first_x_assum drule >> strip_tac >>
     gvs[IS_PREFIX_APPEND, block_is_terminated_def] >>
     Cases_on `l` >> gvs[] >> Cases_on `start.cs_current_insts` >> gvs[]) >>
  simp[entry_emitted_positions_def] >> disj1_tac >>
  qexists_tac `LAST new` >> simp[]
QED

Theorem entry_cfg_closed_instruction[local]:
  entry_cfg_closed targets code /\ idx < LENGTH code ==>
  (EL idx code).inst_opcode <> PHI /\
  (((EL idx code).inst_opcode <> INVOKE /\
     ~is_terminator (EL idx code).inst_opcode /\ idx + 1 < LENGTH code) \/
   entry_cfg_branch targets (EL idx code))
Proof
  pure_rewrite_tac [entry_cfg_closed_def] >> strip_tac >>
  Cases_on `idx < LENGTH prefix`
  >- (simp[EL_APPEND1] >> fs[entry_cfg_open_def, EVERY_EL] >> metis_tac[]) >>
  `idx = LENGTH prefix` by gvs[] >>
  gvs[EL_APPEND2, entry_cfg_branch_def]
QED

Theorem entry_cfg_suffix_instruction[local]:
  (lbl <> start.cs_current_bb \/ LENGTH start.cs_current_insts <= idx) /\
  idx < LENGTH code ==>
  idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0)
    < LENGTH (entry_cfg_suffix start lbl code) /\
  EL (idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0))
    (entry_cfg_suffix start lbl code) = EL idx code
Proof
  rw[entry_cfg_suffix_def] >> simp[EL_DROP]
QED

Theorem entry_cfg_new_label_location[local]:
  cs_extends start last_st /\ lbl IN bound_labels last_st /\
  lbl NOTIN bound_labels start ==>
  lbl <> start.cs_current_bb /\
  (lbl = last_st.cs_current_bb \/
   ?bb. MEM bb (emitted_blocks start last_st) /\ bb.bb_label = lbl)
Proof
  rw[cs_extends_def, bound_labels_def, MEM_MAP] >>
  `emitted_blocks start last_st = new` by
    (irule emitted_blocks_append >> simp[]) >>
  gvs[MEM_APPEND, MEM_MAP] >> metis_tac[]
QED

Theorem entry_cfg_open_head[local]:
  entry_cfg_open code /\ isPREFIX code actual /\
  (code = [] ==> ?id. actual <> [] /\ HD actual = mk_inst id STOP [] []) ==>
  phi_prefix_length actual = 0
Proof
  Cases_on `code` >> Cases_on `actual` >>
  simp[entry_cfg_open_def, IS_PREFIX_APPEND, phi_prefix_length_def] >>
  rpt strip_tac >> gvs[mk_inst_def]
QED

Theorem entry_cfg_target_position[local]:
  entry_cfg_cert start last_st B {} F /\ fn_has_code start last_st fn /\
  (!bb. lookup_block last_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    ?id. get_instruction bb (LENGTH last_st.cs_current_insts) =
         SOME (mk_inst id STOP [] [])) /\ lbl IN B ==>
  ?bb. lookup_block lbl fn.fn_blocks = SOME bb /\
       (lbl,phi_prefix_length bb.bb_instructions) IN
         entry_emitted_positions start last_st
Proof
  strip_tac >>
  `cs_extends start last_st /\ lbl IN bound_labels last_st /\
   lbl NOTIN bound_labels start` by gvs[entry_cfg_cert_def] >>
  drule_all entry_cfg_new_label_location >> strip_tac
  >- (fs[fn_has_code_def] >>
      `entry_cfg_open last_st.cs_current_insts` by
        fs[entry_cfg_cert_def, entry_cfg_suffix_def] >>
      `phi_prefix_length bb.bb_instructions = 0` by
        (irule entry_cfg_open_head >> qexists_tac `last_st.cs_current_insts` >>
         simp[] >> strip_tac >> first_x_assum drule >>
         simp[get_instruction_def] >> Cases_on `bb.bb_instructions` >> simp[]) >>
      simp[entry_emitted_positions_def]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by fs[fn_has_code_def] >>
  qexists_tac `bb` >> simp[] >>
  `entry_cfg_closed B bb.bb_instructions` by
    (fs[entry_cfg_cert_def, EVERY_MEM, entry_cfg_suffix_def] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by fs[entry_cfg_closed_def] >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (drule entry_cfg_closed_instruction >> disch_then (qspec_then `0` mp_tac) >>
     Cases_on `bb.bb_instructions` >> simp[phi_prefix_length_def]) >>
  gvs[entry_emitted_positions_def] >> disj1_tac >>
  qexists_tac `bb` >> simp[] >> Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem entry_cfg_closed_suffix_instruction[local]:
  entry_cfg_closed targets (entry_cfg_suffix start lbl code) /\
  (lbl <> start.cs_current_bb \/ LENGTH start.cs_current_insts <= idx) /\
  idx < LENGTH code ==>
  ((EL idx code).inst_opcode <> INVOKE /\
   ~is_terminator (EL idx code).inst_opcode /\ idx + 1 < LENGTH code) \/
  entry_cfg_branch targets (EL idx code)
Proof
  disch_tac >>
  `idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0)
     < LENGTH (entry_cfg_suffix start lbl code) /\
   EL (idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0))
     (entry_cfg_suffix start lbl code) = EL idx code` by
    metis_tac[entry_cfg_suffix_instruction] >>
  fs[] >>
  drule entry_cfg_closed_instruction >>
  disch_then (qspec_then
    `idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0)` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  disj1_tac >> gvs[entry_cfg_suffix_def] >>
  Cases_on `lbl = start.cs_current_bb` >> gvs[]
QED

Theorem entry_cfg_open_suffix_instruction[local]:
  entry_cfg_open (entry_cfg_suffix start lbl code) /\
  (lbl <> start.cs_current_bb \/ LENGTH start.cs_current_insts <= idx) /\
  idx < LENGTH code ==>
  (EL idx code).inst_opcode <> INVOKE /\
  ~is_terminator (EL idx code).inst_opcode
Proof
  disch_tac >>
  `idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0)
     < LENGTH (entry_cfg_suffix start lbl code) /\
   EL (idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0))
     (entry_cfg_suffix start lbl code) = EL idx code` by
    metis_tac[entry_cfg_suffix_instruction] >>
  fs[] >>
  fs[entry_cfg_open_def, EVERY_EL] >>
  first_x_assum (qspec_then
    `idx - (if lbl = start.cs_current_bb then LENGTH start.cs_current_insts else 0)` mp_tac) >>
  simp[]
QED

Theorem entry_cfg_region_instruction[local]:
  entry_cfg_cert start last_st B {} F /\ fn_has_code start last_st fn /\
  (lbl,idx) IN entry_emitted_positions start last_st /\
  (lbl,idx) <> (last_st.cs_current_bb,LENGTH last_st.cs_current_insts) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ get_instruction bb idx = SOME inst ==>
  (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   (lbl,idx+1) IN entry_emitted_positions start last_st) \/
  entry_cfg_branch B inst
Proof
  strip_tac >>
  qpat_x_assum `(_,_) IN _` mp_tac >>
  simp[entry_emitted_positions_def] >> strip_tac
  >- (`lookup_block bb'.bb_label fn.fn_blocks = SOME bb'` by
        (fs[fn_has_code_def] >> first_x_assum drule >> simp[]) >>
      `bb = bb'` by gvs[] >> gvs[] >>
      `inst = EL idx bb.bb_instructions` by gvs[get_instruction_def] >>
      `entry_cfg_closed B
        (entry_cfg_suffix start bb.bb_label bb.bb_instructions)` by
        (fs[entry_cfg_cert_def, EVERY_MEM] >> metis_tac[]) >>
      `((EL idx bb.bb_instructions).inst_opcode <> INVOKE /\
        ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
        idx + 1 < LENGTH bb.bb_instructions) \/ entry_cfg_branch B inst` by
        metis_tac[entry_cfg_closed_suffix_instruction] >>
      gvs[] >> disj1_tac >> simp[entry_emitted_positions_def] >>
      conj_tac >- (strip_tac >> gvs[]) >>
      disj1_tac >> qexists_tac `bb` >> simp[]) >>
  gvs[] >>
  `idx < LENGTH last_st.cs_current_insts` by decide_tac >>
  `isPREFIX last_st.cs_current_insts bb.bb_instructions` by
    (fs[fn_has_code_def] >> metis_tac[]) >>
  `inst = EL idx last_st.cs_current_insts` by
    (gvs[IS_PREFIX_APPEND, get_instruction_def, EL_APPEND1]) >>
  `entry_cfg_open (entry_cfg_suffix start last_st.cs_current_bb
     last_st.cs_current_insts)` by fs[entry_cfg_cert_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    metis_tac[entry_cfg_open_suffix_instruction] >>
  disj1_tac >> simp[entry_emitted_positions_def] >> strip_tac >> gvs[]
QED

Theorem entry_cfg_successor_inventory:
  entry_cfg_cert start last_st B {} F /\ fn_has_code start last_st fn /\
  (!bb. lookup_block last_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    ?id. get_instruction bb (LENGTH last_st.cs_current_insts) =
      SOME (mk_inst id STOP [] [])) ==>
  !lbl idx bb inst.
    (lbl,idx) IN entry_emitted_positions start last_st /\
    (lbl,idx) <> (last_st.cs_current_bb,LENGTH last_st.cs_current_insts) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ get_instruction bb idx = SOME inst ==>
    (inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
     (lbl,idx+1) IN entry_emitted_positions start last_st) \/
    (?dest target. inst.inst_opcode = JMP /\ inst.inst_operands = [Label dest] /\
      lookup_block dest fn.fn_blocks = SOME target /\
      (dest,phi_prefix_length target.bb_instructions) IN entry_emitted_positions start last_st) \/
    (?cond yes no ybb nbb.
      inst.inst_opcode = JNZ /\ inst.inst_operands = [cond; Label yes; Label no] /\
      lookup_block yes fn.fn_blocks = SOME ybb /\ lookup_block no fn.fn_blocks = SOME nbb /\
      (yes,phi_prefix_length ybb.bb_instructions) IN entry_emitted_positions start last_st /\
      (no,phi_prefix_length nbb.bb_instructions) IN entry_emitted_positions start last_st)
Proof
  rpt strip_tac >> drule_all entry_cfg_region_instruction >> strip_tac
  >- simp[] >>
  gvs[entry_cfg_branch_def] >>
  metis_tac[entry_cfg_target_position]
QED

Theorem entry_cfg_region_closed:
  entry_cfg_cert start last_st B {} F /\ fn_has_code start last_st fn /\
  (!bb. lookup_block last_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    ?id. get_instruction bb (LENGTH last_st.cs_current_insts) =
      SOME (mk_inst id STOP [] [])) ==>
  observer_region_closed ctx fn
    (last_st.cs_current_bb,LENGTH last_st.cs_current_insts)
    (entry_emitted_positions start last_st)
Proof
  strip_tac >> irule entry_cfg_observer_region_closed >>
  rpt strip_tac >> drule_all entry_cfg_successor_inventory >> simp[]
QED

Theorem entry_cfg_region_safe:
  entry_cfg_cert start last_st B {} F /\ fn_has_code start last_st fn /\
  (!bb. lookup_block last_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    ?id. get_instruction bb (LENGTH last_st.cs_current_insts) =
      SOME (mk_inst id STOP [] [])) ==>
  observer_region_safe fn
    (last_st.cs_current_bb,LENGTH last_st.cs_current_insts)
    (entry_emitted_positions start last_st)
Proof
  strip_tac >> irule entry_cfg_observer_region_safe >>
  conj_tac >- simp[] >>
  rpt strip_tac >> drule_all entry_cfg_successor_inventory >> simp[]
QED

Theorem entry_cfg_closed_drop_terminates[local]:
  !n code. entry_cfg_closed B (DROP n code) ==>
    code <> [] /\ is_terminator (LAST code).inst_opcode
Proof
  Induct
  >- (simp[entry_cfg_closed_def] >> rpt strip_tac >>
      gvs[entry_cfg_branch_def, is_terminator_def]) >>
  Cases_on `code` >> simp[entry_cfg_closed_def] >> strip_tac >>
  `entry_cfg_closed B (DROP n t)` by
    (simp[entry_cfg_closed_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >> Cases_on `t` >> gvs[]
QED

Theorem entry_cfg_region_start:
  entry_cfg_cert start last_st B {} F /\ ~block_is_terminated start ==>
  (start.cs_current_bb,LENGTH start.cs_current_insts) IN
    entry_emitted_positions start last_st
Proof
  strip_tac >> irule entry_emitted_positions_start >>
  fs[entry_cfg_cert_def] >> fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[entry_cfg_suffix_def] >>
  metis_tac[entry_cfg_closed_drop_terminates, DROP_0]
QED

(* One adapter serves all three mutually recursive calldata compilers. *)
Theorem entry_cfg_preserves_observer_regions:
  entry_cfg_preserves c /\ compile_state_ok start /\
  ~block_is_terminated start /\ c start = (v,last_st) /\
  fn_has_code start last_st fn /\
  (!bb. lookup_block last_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    ?id. get_instruction bb (LENGTH last_st.cs_current_insts) =
      SOME (mk_inst id STOP [] [])) ==>
  observer_region_closed ctx fn
    (last_st.cs_current_bb,LENGTH last_st.cs_current_insts)
    (entry_emitted_positions start last_st) /\
  observer_region_safe fn
    (last_st.cs_current_bb,LENGTH last_st.cs_current_insts)
    (entry_emitted_positions start last_st) /\
  (start.cs_current_bb,LENGTH start.cs_current_insts) IN
    entry_emitted_positions start last_st /\
  (!idx. (last_st.cs_current_bb,idx) IN entry_emitted_positions start last_st ==>
    idx <= LENGTH last_st.cs_current_insts)
Proof
  strip_tac >>
  `entry_cfg_cert start start {} {} F` by metis_tac[entry_cfg_cert_initial] >>
  drule_all entry_cfg_preserves_apply >> strip_tac >>
  rpt conj_tac
  >- (drule_all entry_cfg_region_closed >> simp[])
  >- (drule_all entry_cfg_region_safe >> simp[])
  >- (drule_all entry_cfg_region_start >> simp[]) >>
  rpt strip_tac >> irule entry_emitted_positions_cut_bound >>
  conj_tac >- fs[entry_cfg_cert_def] >> qexists_tac `start` >> simp[]
QED
