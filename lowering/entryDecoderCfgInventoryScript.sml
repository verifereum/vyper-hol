(* Emitted-code inventories for recursive calldata decoding. *)
Theory entryDecoderCfgInventory
Ancestors
  entryObserverCfg abiEncoder fragExec compileEnv venomExecSemantics
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

Theorem entry_emitted_positions_cut_bound[local]:
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
