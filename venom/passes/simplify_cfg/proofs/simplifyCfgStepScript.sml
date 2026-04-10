(*
 * Simplify CFG Pass — Per-Step Correctness Lemmas
 *
 * Proves that fix_all_phis is identity under well-formedness,
 * then defers to pipeline correctness for the core.
 *)

Theory simplifyCfgStep
Ancestors
  simplifyCfgHelpers simplifyCfgDefs stateEquiv venomExecSemantics venomWf
  venomInst venomState cfgTransform stateEquivProps cfgTransformProps
  venomExecProps

(* ================================================================
   Section 1: PHI well-formedness and fix_all_phis identity
   ================================================================ *)

(* All PHI label operands reference actual predecessors, and each PHI
   has at least 2 label-value pairs (so fix_phi_inst keeps it as PHI).
   Standard SSA well-formedness: a PHI node is only needed when a block
   has >= 2 predecessors, and each predecessor contributes one pair. *)

(* Helper: all Label operands in a list are in preds *)
Definition phi_ops_in_preds_def:
  phi_ops_in_preds preds ops <=>
    !l. MEM (Label l) ops ==> MEM l preds
End

(* filter_phi_ops is identity when all labels are in preds *)
Theorem filter_phi_ops_identity[local]:
  !preds ops.
    phi_ops_in_preds preds ops ==>
    filter_phi_ops preds ops = ops
Proof
  ho_match_mp_tac filter_phi_ops_ind >>
  rw[filter_phi_ops_def, phi_ops_in_preds_def] >>
  metis_tac[listTheory.MEM]
QED

(* fix_phi_inst is identity when ops don't change and have >= 4 elements *)
Theorem fix_phi_inst_identity[local]:
  !preds inst.
    (inst.inst_opcode = PHI ==>
     phi_ops_in_preds preds inst.inst_operands /\
     ?a b c d. inst.inst_operands = a::b::c::d) ==>
    fix_phi_inst preds inst = inst
Proof
  rw[fix_phi_inst_def, LET_THM] >>
  `filter_phi_ops preds inst.inst_operands = inst.inst_operands` by (
    match_mp_tac filter_phi_ops_identity >> simp[]) >>
  gvs[] >>
  simp[instruction_component_equality]
QED

(* fn_phi_preds_wf: all PHIs have labels in pred_labels and >= 2 pairs *)
Definition fn_phi_preds_wf_def:
  fn_phi_preds_wf func <=>
    !bb inst.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI ==>
      phi_ops_in_preds (pred_labels func bb.bb_label) inst.inst_operands /\
      ?a b c d. inst.inst_operands = a::b::c::d
End

(* FILTER P ++ FILTER ~P = original when P holds on a prefix and ~P on suffix *)
Theorem FILTER_SORTED_PARTITION[local]:
  !P l1 l2.
    EVERY P l1 /\ EVERY ($~ o P) l2 ==>
    FILTER P (l1 ++ l2) ++ FILTER ($~ o P) (l1 ++ l2) = l1 ++ l2
Proof
  Induct_on `l1` >> rpt strip_tac >>
  fs[listTheory.FILTER_APPEND_DISTRIB] >>
  `FILTER P l2 = []` by
    (rw[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM, combinTheory.o_DEF] >>
     fs[listTheory.EVERY_MEM, combinTheory.o_DEF]) >>
  `FILTER ($~ o P) l2 = l2` by rw[listTheory.FILTER_EQ_ID] >>
  simp[]
QED

(* Sorted list partition: FILTER P ++ FILTER ~P = l when P-elements precede ~P *)
Theorem sorted_filter_partition:
  !l.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) ==>
    FILTER (\i. i.inst_opcode = PHI) l ++
    FILTER (\i. i.inst_opcode <> PHI) l = l
Proof
  Induct >> rw[] >>
  Cases_on `h.inst_opcode = PHI` >> fs[]
  >- (
    (* h is PHI -- pass IH with shifted indices *)
    first_x_assum match_mp_tac >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
  >>
  (* h is not PHI -- no later element can be PHI *)
  `EVERY (\i. i.inst_opcode <> PHI) l` by (
    rw[listTheory.EVERY_EL] >> rpt strip_tac >>
    CCONTR_TAC >> gvs[] >>
    first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `FILTER (\i. i.inst_opcode = PHI) l = []` by (
    rw[listTheory.FILTER_EQ_NIL] >>
    fs[listTheory.EVERY_MEM] >> rpt strip_tac >> res_tac) >>
  `FILTER (\i. i.inst_opcode <> PHI) l = l` by
    simp[listTheory.FILTER_EQ_ID] >>
  asm_rewrite_tac[] >> simp[]
QED

(* MAP f l = l when f is identity on all elements *)
Theorem MAP_EQ_ID:
  !f l. (!x. MEM x l ==> f x = x) ==> MAP f l = l
Proof
  Induct_on `l` >> rw[]
QED

(* fix_phis_in_block is identity on well-formed blocks with fn_phi_preds_wf *)
Theorem fix_phis_in_block_identity[local]:
  !func bb.
    fn_phi_preds_wf func /\
    MEM bb func.fn_blocks /\
    bb_well_formed bb ==>
    fix_phis_in_block (pred_labels func bb.bb_label) bb = bb
Proof
  rw[fix_phis_in_block_def, LET_THM] >>
  (* Step 1: MAP fix_phi_inst = identity *)
  `MAP (fix_phi_inst (pred_labels func bb.bb_label)) bb.bb_instructions =
   bb.bb_instructions` by (
    match_mp_tac MAP_EQ_ID >>
    rw[] >> match_mp_tac fix_phi_inst_identity >>
    rw[] >> fs[fn_phi_preds_wf_def] >> metis_tac[]) >>
  simp[] >>
  (* Step 2: FILTER PHI ++ FILTER non-PHI = original on well-formed block *)
  `FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions ++
   FILTER (\i. i.inst_opcode <> PHI) bb.bb_instructions =
   bb.bb_instructions` by (
    match_mp_tac sorted_filter_partition >> fs[bb_well_formed_def]) >>
  simp[basic_block_component_equality]
QED

(* fix_all_phis is identity under fn_phi_preds_wf + wf_function *)
Theorem fix_all_phis_identity:
  !func.
    wf_function func /\
    fn_phi_preds_wf func ==>
    fix_all_phis func = func
Proof
  rw[fix_all_phis_def] >>
  `MAP (\bb. fix_phis_in_block (pred_labels func bb.bb_label) bb)
       func.fn_blocks = func.fn_blocks` by (
    match_mp_tac MAP_EQ_ID >>
    rw[] >> match_mp_tac fix_phis_in_block_identity >>
    simp[] >> fs[wf_function_def]) >>
  simp[ir_function_component_equality]
QED

(* ================================================================
   Section 2: phi_no_conflict -- SSA property for PHI reorder safety
   ================================================================ *)

(* Within each block, PHI outputs are distinct and no PHI reads
   a variable defined by another PHI in the same block.
   This is a standard SSA property: PHIs conceptually execute
   simultaneously, so they reference values from predecessor blocks,
   not from same-block PHI definitions. *)
Definition phi_no_conflict_def:
  phi_no_conflict fn <=>
    !bb.
      MEM bb fn.fn_blocks ==>
      let phis = FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions in
      let phi_outs = FLAT (MAP (\i. i.inst_outputs) phis) in
      let phi_uses = FLAT (MAP inst_uses phis) in
      ALL_DISTINCT phi_outs /\
      DISJOINT (set phi_outs) (set phi_uses)
End

val _ = export_theory();
