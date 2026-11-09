(* Predicate-valued availability at SSA instruction boundaries. *)
Theory ssaAvailablePred
Ancestors
  venomWf venomWfProps venomExecProofs venomInst list

Definition dom_pred_def:
  dom_pred fn lbl P <=>
    !db di v. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
      MEM v di.inst_outputs /\ fn_dominates fn db.bb_label lbl /\
      db.bb_label <> lbl ==> P v
End

Definition prefix_pred_def:
  prefix_pred bb n P <=>
    !j v. j < n /\ j < LENGTH bb.bb_instructions /\
      MEM v (EL j bb.bb_instructions).inst_outputs ==> P v
End

Definition boundary_pred_def:
  boundary_pred fn bb n P <=>
    dom_pred fn bb.bb_label P /\ prefix_pred bb n P
End

Theorem dom_pred_entry:
  fn_entry_label fn = SOME lbl ==> dom_pred fn lbl P
Proof
  rw[dom_pred_def] >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >>
  metis_tac[HD, LAST_CONS, is_fn_path_def, MEM]
QED

Theorem dom_pred_mono:
  dom_pred fn lbl P /\ (!v. P v ==> Q v) ==> dom_pred fn lbl Q
Proof
  simp[dom_pred_def] >> metis_tac[]
QED

Theorem prefix_pred_mono:
  prefix_pred bb n P /\ (!v. P v ==> Q v) ==> prefix_pred bb n Q
Proof
  simp[prefix_pred_def] >> metis_tac[]
QED

Theorem boundary_pred_mono:
  boundary_pred fn bb n P /\ (!v. P v ==> Q v) ==>
  boundary_pred fn bb n Q
Proof
  metis_tac[boundary_pred_def, dom_pred_mono, prefix_pred_mono]
QED

Theorem prefix_pred_zero[simp]:
  prefix_pred bb 0 P
Proof
  simp[prefix_pred_def]
QED

Theorem prefix_pred_suc:
  prefix_pred bb n P /\
  (!v. n < LENGTH bb.bb_instructions /\
       MEM v (EL n bb.bb_instructions).inst_outputs ==> P v) ==>
  prefix_pred bb (SUC n) P
Proof
  rw[prefix_pred_def] >> Cases_on `j = n` >> gvs[] >>
  `j < n` by decide_tac >> metis_tac[]
QED

Theorem boundary_pred_operand:
  wf_ssa fn /\ wf_function fn /\ fn_inst_wf fn /\
  MEM bb fn.fn_blocks /\ n < LENGTH bb.bb_instructions /\
  (EL n bb.bb_instructions).inst_opcode <> PHI /\
  boundary_pred fn bb n P /\
  MEM (Var v) (EL n bb.bb_instructions).inst_operands ==> P v
Proof
  rw[wf_ssa_def, def_dominates_uses_def, boundary_pred_def] >>
  `def_available_at fn bb (SOME (EL n bb.bb_instructions)) v` by
    metis_tac[EL_MEM] >>
  fs[def_available_at_def] >>
  Cases_on `def_bb = bb`
  >- (gvs[prefix_pred_def] >>
      `j = n` by metis_tac[inst_ids_el_eq, wf_function_def] >>
      gvs[] >>
      qpat_x_assum `!j v. _ ==> P v` irule >>
      qexists_tac `i` >> simp[] >> decide_tac) >>
  `def_bb.bb_label <> bb.bb_label` by metis_tac[same_label_same_block] >>
  metis_tac[dom_pred_def]
QED

Theorem boundary_pred_exit:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  bb_well_formed bb /\ n < LENGTH bb.bb_instructions /\
  is_terminator (EL n bb.bb_instructions).inst_opcode /\
  fn_reachable fn bb.bb_label /\ fn_cfg_edge fn bb.bb_label lbl /\
  boundary_pred fn bb n P ==> dom_pred fn lbl P
Proof
  strip_tac >>
  `n = PRE (LENGTH bb.bb_instructions)` by metis_tac[bb_well_formed_def] >>
  fs[boundary_pred_def] >> rw[dom_pred_def] >>
  Cases_on `db.bb_label = bb.bb_label`
  >- (`db = bb` by metis_tac[same_label_same_block] >> gvs[] >>
      `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = di`
        by metis_tac[MEM_EL] >>
      `inst_wf di` by metis_tac[fn_inst_wf_every_bb, EVERY_MEM] >>
      `~is_terminator di.inst_opcode` by metis_tac[terminator_no_outputs, MEM] >>
      `j < PRE (LENGTH bb.bb_instructions)` by
        (Cases_on `j = PRE (LENGTH bb.bb_instructions)` >> gvs[] >> decide_tac) >>
      metis_tac[prefix_pred_def]) >>
  `fn_dominates fn db.bb_label bb.bb_label` by
    metis_tac[fn_dominates_predecessor] >>
  metis_tac[dom_pred_def]
QED

Theorem boundary_pred_index_le:
  boundary_pred fn bb n P /\ m <= n ==> boundary_pred fn bb m P
Proof
  rw[boundary_pred_def, prefix_pred_def] >>
  first_x_assum irule >> qexists_tac `j` >> simp[] >> decide_tac
QED
