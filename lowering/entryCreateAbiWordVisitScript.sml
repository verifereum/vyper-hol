(* A fixed ABI-word packaging slice cannot own a CREATE visit, even
   when the selected prefix does not reach the end of that slice. *)
Theory entryCreateAbiWordVisit
Ancestors
  entryCreateNativeFirstExit entryCreateAdminSequence entryCreateBodyCut
  entryCreateFocusSpec createSizeCutRegion fragExec vyperStorageTrace
  vyperInterpreter venomInst list

Theorem abi_encode_word_selected_cut:
  body_inv tops ctx ce cx /\ MEM fnc ctx.ctx_functions /\
  create_cut_code {} sa sm /\ fn_has_code sa sm fnc /\
  create_cut_code {} sm sb /\ fn_has_code sm sb fnc /\
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sm sb) /\
  create_operand_cut sa sm E ctx fnc tops cx st0 source (es,s) /\
  (!v. storage_trace_frame (next v)) ==>
  create_operand_cut sa sb E ctx fnc tops cx st0 (bind source next) (es,s)
Proof
  strip_tac >> simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (irule create_cut_bind_left >> fs[create_operand_cut_def] >>
      qpat_assum `!p d k before hit after. _` irule >>
      goal_assum (drule_at Any) >> simp[]) >>
  (* The suffix cut holds for any action, including one that cannot fail.
     With the given horizon, an unsafe suffix visit would contradict it. *)
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut sm sb E ctx fnc tops cx st0 (\_. (INL (),ee)) (es,t)` by
    (irule create_admin_sequence_cut >> simp[]) >>
  qpat_x_assum `create_operand_cut sm sb _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def,create_cut_failure_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED
