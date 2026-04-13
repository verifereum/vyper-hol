(*
 * Simplify CFG Pass — Collapse DFS Correctness
 *
 * Proves that collapse_dfs + subst_block_labels_fn preserves
 * run_function semantics (collapse_dfs_subst_correct).
 *
 * Strategy:
 *   1. subst_block_labels_fn is a SYNTACTIC identity after collapse_dfs
 *      because all merged-away labels are removed from PHIs during each step.
 *      Requires fn_phi_preds_wf (PHI labels correspond to actual predecessors).
 *   2. Each merge/bypass step preserves run_function semantics (fuel induction).
 *   3. collapse_dfs iterates these steps (via collapse_dfs_preserves).
 *   4. Compose by transitivity.
 *)

Theory simplifyCfgCollapseBase
Ancestors
  simplifyCfgHelpers simplifyCfgWf simplifyCfgDefs simplifyCfgPrevBB
  stateEquiv venomExecSemantics venomWf passSimulationDefs
  venomInst venomState cfgTransform stateEquivProps cfgTransformProps
  venomExecProps cfgTransformProofs venomExecProofs jumpIndep instIdxIndep

(* ================================================================
   Section 0: Well-formedness bundle
   ================================================================ *)

(* All useful wf facts from lookup_block + wf_function + fn_inst_wf *)
Theorem lookup_block_wf_facts:
  !func cb bb.
    wf_function func /\ fn_inst_wf func /\
    lookup_block cb func.fn_blocks = SOME bb ==>
    MEM bb func.fn_blocks /\
    bb_well_formed bb /\
    bb.bb_instructions <> [] /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_label = cb /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb func.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by
    (fs[wf_function_def] >> res_tac) >>
  `bb.bb_instructions <> []` by
    (fs[bb_well_formed_def]) >>
  ASM_REWRITE_TAC[] >>
  rpt conj_tac
  >- (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
      fs[venomWfTheory.fn_inst_wf_def] >> res_tac)
  >- metis_tac[venomExecProofsTheory.lookup_block_label]
  >> (rpt strip_tac >> fs[bb_well_formed_def] >>
      CCONTR_TAC >> fs[] >> res_tac >> fs[])
QED

(* Bridge: bb_well_formed ==> the "no interior terminators" form *)
Theorem bb_wf_no_interior_terminators:
  !bb. bb_well_formed bb ==>
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode)
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  CCONTR_TAC >> fs[] >> res_tac >> fs[]
QED

(* run_block OK post-state facts under bb_well_formed *)
Theorem run_block_ok_prev_bb_wf:
  !fuel ctx bb s w.
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx = 0 /\ run_block fuel ctx bb s = OK w ==>
    w.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  drule bb_wf_no_interior_terminators >> strip_tac >>
  mp_tac venomExecPropsTheory.run_block_ok_prev_bb >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `w`] mp_tac) >>
  fs[bb_well_formed_def]
QED

Theorem run_block_current_bb_in_succs_wf:
  !fuel ctx bb s w.
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx = 0 /\ run_block fuel ctx bb s = OK w ==>
    MEM w.vs_current_bb (bb_succs bb)
Proof
  rpt strip_tac >>
  drule bb_wf_no_interior_terminators >> strip_tac >>
  mp_tac venomExecPropsTheory.run_block_current_bb_in_succs >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `w`] mp_tac) >>
  fs[bb_well_formed_def]
QED

(* ================================================================
   Section 0.5: result_equiv helpers
   ================================================================ *)

Theorem result_equiv_empty_refl:
  !r : exec_result. result_equiv {} r r
Proof
  Cases >> simp[result_equiv_def, state_equiv_def, execution_equiv_def]
QED

Theorem result_equiv_empty_trans:
  !r1 r2 r3.
    result_equiv {} r1 r2 /\ result_equiv {} r2 r3 ==>
    result_equiv {} r1 r3
Proof
  metis_tac[stateEquivPropsTheory.result_equiv_trans]
QED

(* ================================================================
   Section 0.5: PHI well-formedness — Label operands in PHI
   instructions correspond to actual predecessor block labels.
   Established by fix_all_phis, preserved by merge/bypass.
   ================================================================ *)

Definition fn_phi_preds_wf_def:
  fn_phi_preds_wf func <=>
    !bb inst lbl.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI /\
      MEM (Label lbl) inst.inst_operands ==>
      MEM lbl (pred_labels func bb.bb_label)
End

(* Completeness direction: every predecessor label appears in PHI operands.
   I.e. if block bb has a predecessor with label lbl, then every PHI in bb
   has Label lbl in its operands. This is the converse of fn_phi_preds_wf. *)
Definition fn_phi_preds_complete_def:
  fn_phi_preds_complete func <=>
    !bb inst lbl.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI /\
      MEM lbl (pred_labels func bb.bb_label) ==>
      MEM (Label lbl) inst.inst_operands
End

(* wf_function implies blocks with same label are identical *)
Theorem wf_blocks_unique:
  !func a b.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    a.bb_label = b.bb_label ==> a = b
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    fs[wf_function_def, venomInstTheory.fn_labels_def] >>
  imp_res_tac venomExecPropsTheory.MEM_lookup_block >>
  fs[]
QED

(* ================================================================
   Section 1: subst_block_labels_fn is a syntactic identity
   after collapse_dfs
   ================================================================ *)

(* A label does not appear as a Label operand in any block_label_opcode
   instruction in the function. *)
Definition label_absent_fn_def:
  label_absent_fn lbl func <=>
    !bb inst.
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      is_block_label_opcode inst.inst_opcode ==>
      ~MEM (Label lbl) inst.inst_operands
End

(* All keys of label_map are absent from the function *)
Definition labels_absent_fn_def:
  labels_absent_fn label_map func <=>
    !old new. MEM (old, new) label_map ==> label_absent_fn old func
End

(* Well-formedness for bypass pass: no DJMP, JNZ conditions are not Labels,
   and single-successor blocks use JMP.
   Trivially true for Venom IR before lowering (no DJMP; conditions are Var/Lit;
   single-successor terminators are always JMP, not degenerate JNZ with l1=l2).
   Needed because: (1) subst_label_inst substitutes ALL Label operands, which
   would corrupt a Label condition; (2) num_succs=2 + no DJMP implies JNZ;
   (3) bypassing a trivial block requires the block to always succeed (JMP does,
   JNZ might fail if its condition evaluation fails). *)
Definition fn_bypass_safe_def:
  fn_bypass_safe func <=>
    !bb. MEM bb func.fn_blocks /\ bb.bb_instructions <> [] ==>
      (LAST bb.bb_instructions).inst_opcode <> DJMP /\
      (num_succs bb = 1 ==> (LAST bb.bb_instructions).inst_opcode = JMP) /\
      (num_succs bb = 2 ==> (LAST bb.bb_instructions).inst_opcode = JNZ) /\
      (!c l1 l2.
        (LAST bb.bb_instructions).inst_opcode = JNZ /\
        (LAST bb.bb_instructions).inst_operands = [c; Label l1; Label l2] ==>
        !l. c <> Label l)
End

(* MAP f l = l when f is pointwise identity on members of l *)
Theorem MAP_ID_ON:
  !f l. (!x. MEM x l ==> f x = x) ==> MAP f l = l
Proof
  gen_tac >> Induct >> rw[] >> metis_tac[]
QED

(* subst_label_map_op is identity when no key Label matches *)
Theorem subst_label_map_op_noop:
  !lm op. (!old new. MEM (old, new) lm ==>
    !l. op = Label l ==> l <> old) ==>
    subst_label_map_op lm op = op
Proof
  Induct_on `op` >> rw[subst_label_map_op_def] >>
  Cases_on `ALOOKUP lm s` >> simp[] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >> metis_tac[]
QED

(* MAP subst_label_map_op is identity when no key Label is in the list *)
Theorem MAP_subst_label_map_op_noop:
  !lm ops.
    (!old new. MEM (old, new) lm ==> ~MEM (Label old) ops) ==>
    MAP (subst_label_map_op lm) ops = ops
Proof
  rw[] >> irule MAP_ID_ON >> rw[] >>
  rename1 `MEM op ops` >>
  irule subst_label_map_op_noop >> rw[] >>
  first_x_assum (qspecl_then [`old`, `new`] mp_tac) >>
  rw[] >> metis_tac[]
QED

(* subst_block_labels_inst is identity when no key Label in operands *)
Theorem subst_block_labels_inst_noop:
  !lm inst.
    (!old new. MEM (old, new) lm ==>
      ~MEM (Label old) inst.inst_operands) ==>
    subst_block_labels_inst lm inst = inst
Proof
  rw[subst_block_labels_inst_def] >-
  (rw[subst_label_map_inst_def, venomInstTheory.instruction_component_equality] >>
   irule MAP_subst_label_map_op_noop >> metis_tac[]) >>
  simp[]
QED

(* subst_block_labels_block is identity when label_absent for all keys *)
Theorem subst_block_labels_block_noop:
  !lm bb.
    (!inst. MEM inst bb.bb_instructions /\
            is_block_label_opcode inst.inst_opcode ==>
      !old new. MEM (old, new) lm ==>
        ~MEM (Label old) inst.inst_operands) ==>
    subst_block_labels_block lm bb = bb
Proof
  rw[subst_block_labels_block_def,
     venomInstTheory.basic_block_component_equality] >>
  irule MAP_ID_ON >> rw[] >>
  rename1 `MEM inst _` >>
  Cases_on `is_block_label_opcode inst.inst_opcode`
  >- (rw[subst_block_labels_inst_def, subst_label_map_inst_def,
         venomInstTheory.instruction_component_equality] >>
      irule MAP_subst_label_map_op_noop >> metis_tac[])
  >> rw[subst_block_labels_inst_def]
QED

(* If all keys are absent, subst_block_labels_fn is identity *)
Theorem subst_block_labels_fn_identity:
  !lm func.
    labels_absent_fn lm func ==>
    subst_block_labels_fn lm func = func
Proof
  rw[subst_block_labels_fn_def, venomInstTheory.ir_function_component_equality] >>
  irule MAP_ID_ON >> rw[] >>
  rename1 `MEM bb _` >>
  irule subst_block_labels_block_noop >> rw[] >>
  fs[labels_absent_fn_def, label_absent_fn_def] >>
  metis_tac[]
QED

(* pred_labels are a subset of fn_labels *)
Theorem pred_labels_subset_fn_labels:
  !func x lbl.
    MEM lbl (pred_labels func x) ==> MEM lbl (fn_labels func)
Proof
  rw[pred_labels_def, block_preds_def, fn_labels_def,
     listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

(* ---- Helper: MEM in replace_block ---- *)

Theorem MEM_replace_block_imp:
  !x lbl bb' bbs.
    MEM x (replace_block lbl bb' bbs) ==>
    (x = bb' /\ (?y. MEM y bbs /\ y.bb_label = lbl)) \/
    (MEM x bbs /\ x.bb_label <> lbl)
Proof
  Induct_on `bbs` >> rw[replace_block_def] >> fs[listTheory.MEM_MAP] >>
  res_tac >> fs[] >> metis_tac[listTheory.MEM]
QED

(* ---- Helpers for update_succ_phi_labels ---- *)

(* update_succ_phi_labels preserves label_absent_fn when:
   (1) the label was absent from terminators in the input, and
   (2) for blocks in succs, subst_label_inst removes the label from PHIs,
   (3) for blocks not in succs, the label was absent from PHIs in the input. *)

(* Key: update_succ_phi_labels preserves block labels *)
(* Already proved: MAP_bb_label_update_succ_phi_labels *)

(* Key: update_succ_phi_labels doesn't change non-PHI instructions *)
(* Non-PHI instructions (including terminators) are preserved by
   update_succ_phi_labels because it only modifies PHI instructions. *)

(* ---- Invariant: collapse_dfs maintains labels_absent_fn ---- *)

(* num_preds = 1 means exactly one block has lbl in bb_succs *)
Theorem num_preds_1_unique_pred:
  !func lbl bb.
    num_preds func lbl = 1 /\
    MEM bb func.fn_blocks /\
    MEM lbl (bb_succs bb) ==>
    !bb2. MEM bb2 func.fn_blocks /\ MEM lbl (bb_succs bb2) ==> bb2 = bb
Proof
  rw[num_preds_def, block_preds_def] >>
  `LENGTH (FILTER (\b. MEM lbl (bb_succs b)) func.fn_blocks) = 1`
    by metis_tac[] >>
  `MEM bb (FILTER (\b. MEM lbl (bb_succs b)) func.fn_blocks)`
    by rw[listTheory.MEM_FILTER] >>
  `MEM bb2 (FILTER (\b. MEM lbl (bb_succs b)) func.fn_blocks)`
    by rw[listTheory.MEM_FILTER] >>
  Cases_on `FILTER (\b. MEM lbl (bb_succs b)) func.fn_blocks` >> fs[] >>
  Cases_on `t` >> fs[] >> metis_tac[]
QED

(* get_successors extracts exactly the Label operand names *)
Theorem MEM_get_successors:
  !inst lbl.
    is_terminator inst.inst_opcode ==>
    (MEM lbl (get_successors inst) <=> MEM (Label lbl) inst.inst_operands)
Proof
  rw[get_successors_def, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  eq_tac >> rw[]
  >- (Cases_on `y'` >> fs[get_label_def])
  >> qexists_tac `SOME lbl` >> rw[get_label_def] >>
  qexists_tac `Label lbl` >> rw[get_label_def]
QED

(* In well-formed block, only the LAST instruction is a terminator *)
Theorem bb_wf_terminator_is_last:
  !bb inst.
    bb_well_formed bb /\
    MEM inst bb.bb_instructions /\
    is_terminator inst.inst_opcode ==>
    inst = LAST bb.bb_instructions
Proof
  rw[bb_well_formed_def] >>
  fs[listTheory.MEM_EL] >>
  `n = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
  rw[] >>
  `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> fs[]) >>
  metis_tac[listTheory.LAST_EL]
QED

(* Label not in bb_succs means Label lbl not in terminator operands *)
Theorem label_not_in_succs_not_in_terminator:
  !bb lbl.
    bb_well_formed bb /\
    ~MEM lbl (bb_succs bb) ==>
    !inst. MEM inst bb.bb_instructions /\
           is_terminator inst.inst_opcode ==>
           ~MEM (Label lbl) inst.inst_operands
Proof
  rpt strip_tac >>
  `inst = LAST bb.bb_instructions`
    by metis_tac[bb_wf_terminator_is_last] >>
  fs[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> fs[] >>
  metis_tac[MEM_get_successors, listTheory.MEM_nub]
QED

(* If a label is not in fn_labels, it is absent from all block-label-opcode
   instructions. Requires wf_function (terminators target fn_labels via
   fn_succs_closed) and fn_phi_preds_wf (PHI labels are pred_labels ⊆ fn_labels). *)
Theorem not_in_fn_labels_label_absent:
  !lbl func.
    ~MEM lbl (fn_labels func) /\
    wf_function func /\
    fn_phi_preds_wf func ==>
    label_absent_fn lbl func
Proof
  rw[label_absent_fn_def, is_block_label_opcode_def]
  >- (
    (* Terminator case *)
    `~MEM lbl (bb_succs bb)` by
      (CCONTR_TAC >> fs[] >>
       fs[wf_function_def, fn_succs_closed_def] >> metis_tac[]) >>
    metis_tac[label_not_in_succs_not_in_terminator, wf_function_def]
  ) >>
  (* PHI case *)
  CCONTR_TAC >> fs[] >>
  `MEM lbl (pred_labels func bb.bb_label)` by
    (fs[fn_phi_preds_wf_def] >> metis_tac[]) >>
  metis_tac[pred_labels_subset_fn_labels]
QED

(* subst_label_inst removes old_lbl from PHI operands *)
Theorem subst_label_inst_removes:
  !old_lbl new_lbl inst.
    old_lbl <> new_lbl ==>
    ~MEM (Label old_lbl)
      (subst_label_inst old_lbl new_lbl inst).inst_operands
Proof
  simp[subst_label_inst_def, listTheory.MEM_MAP] >>
  rpt strip_tac >>
  Cases_on `y` >> fs[subst_label_op_def] >>
  BasicProvers.every_case_tac >> fs[]
QED

(* LAST of appended non-empty list *)
Theorem LAST_APPEND_CONS:
  !l1 h t. LAST (l1 ++ h::t) = LAST (h::t)
Proof
  Induct >> rw[listTheory.LAST_DEF]
QED

(* bb_succs of merged block = bb_succs of next_bb *)
Theorem bb_succs_merge_blocks_lemma:
  !l1 h t. LAST (l1 ++ [h] ++ t) = LAST (h::t)
Proof
  REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  rw[LAST_APPEND_CONS]
QED

Theorem bb_succs_merge_blocks:
  !bb next_bb.
    bb_well_formed bb /\ bb_well_formed next_bb ==>
    bb_succs (merge_blocks bb next_bb) = bb_succs next_bb
Proof
  rw[merge_blocks_def, bb_succs_def] >>
  Cases_on `next_bb.bb_instructions` >> fs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >> fs[bb_well_formed_def] >>
  `FRONT (h'::t') ++ [h] ++ t <> []` by simp[] >>
  Cases_on `FRONT (h'::t') ++ [h] ++ t` >> fs[] >>
  pop_assum (ASSUME_TAC o SYM) >>
  fs[bb_succs_merge_blocks_lemma]
QED

(* EVERY over merge_blocks: FRONT a ++ b preserves any predicate P *)
Theorem EVERY_merge_blocks:
  !P a b.
    EVERY P a.bb_instructions /\ EVERY P b.bb_instructions /\
    a.bb_instructions <> [] ==>
    EVERY P (merge_blocks a b).bb_instructions
Proof
  rw[merge_blocks_def, listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >>
  metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]
QED

(* Cons unfolding for update_succ_phi_labels *)
Theorem update_succ_phi_labels_cons:
  !old new bbs h succs.
    update_succ_phi_labels old new bbs (h::succs) =
    update_succ_phi_labels old new
      (case lookup_block h bbs of
         NONE => bbs
       | SOME sbb =>
           replace_block h
             (sbb with bb_instructions :=
                MAP (\inst. if inst.inst_opcode <> PHI then inst
                            else subst_label_inst old new inst)
                    sbb.bb_instructions) bbs)
      succs
Proof
  simp[update_succ_phi_labels_def, LET_THM]
QED

(* MEM in replace_block characterization *)
Theorem MEM_replace_block_cases:
  !x lbl bb' bbs.
    MEM x (replace_block lbl bb' bbs) <=>
    (x = bb' /\ (?y. MEM y bbs /\ y.bb_label = lbl)) \/
    (MEM x bbs /\ x.bb_label <> lbl)
Proof
  rw[replace_block_def, listTheory.MEM_MAP] >>
  eq_tac >> strip_tac
  >- (Cases_on `bb.bb_label = lbl` >> fs[] >> metis_tac[])
  >- metis_tac[]
  >> fs[] >> qexists_tac `x` >> simp[]
QED

(* update_succ_phi_labels ensures label_absent when:
   (1) terminators don't reference the label, and
   (2) PHIs in non-successor blocks don't reference it.
   PHIs in successor blocks get subst_label_inst applied. *)
(* If lookup_block h bbs = NONE then no block in bbs has label h *)
Theorem lookup_block_NONE_not_label:
  !h bbs bb. lookup_block h bbs = NONE /\ MEM bb bbs ==> bb.bb_label <> h
Proof
  rw[lookup_block_def] >>
  Induct_on `bbs` >> rw[listTheory.FIND_thm] >>
  BasicProvers.every_case_tac >> fs[]
QED

(* Terminators in the PHI-only MAP are unchanged from the original *)
Theorem phi_map_preserves_terminator:
  !old new insts inst.
    MEM inst (MAP (\i. if i.inst_opcode <> PHI then i
                       else subst_label_inst old new i) insts) /\
    is_terminator inst.inst_opcode ==>
    MEM inst insts
Proof
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  Cases_on `i.inst_opcode = PHI` >>
  gvs[subst_label_inst_def, is_terminator_def]
QED

(* PHIs in the MAP'd list have Label old removed *)
Theorem phi_map_removes_label:
  !old new insts inst.
    old <> new /\
    MEM inst (MAP (\i. if i.inst_opcode <> PHI then i
                       else subst_label_inst old new i) insts) /\
    inst.inst_opcode = PHI ==>
    ~MEM (Label old) inst.inst_operands
Proof
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  Cases_on `i.inst_opcode = PHI` >> gvs[] >>
  metis_tac[subst_label_inst_removes]
QED

(* The 4 preconditions that the IH needs after replace_block in the SOME case. *)
Theorem uspl_replace_block_preconds:
  !old new bbs h sbb succs.
    lookup_block h bbs = SOME sbb /\
    old <> new /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
               is_terminator inst.inst_opcode ==>
               ~MEM (Label old) inst.inst_operands) /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI /\ ~MEM bb.bb_label (h::succs) ==>
               ~MEM (Label old) inst.inst_operands) ==>
    let bbs' = replace_block h
          (sbb with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else subst_label_inst old new inst)
                sbb.bb_instructions) bbs in
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs') /\
    (!bb inst. MEM bb bbs' /\ MEM inst bb.bb_instructions /\
               is_terminator inst.inst_opcode ==>
               ~MEM (Label old) inst.inst_operands) /\
    (!bb inst. MEM bb bbs' /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI /\ ~MEM bb.bb_label succs ==>
               ~MEM (Label old) inst.inst_operands)
Proof
  rw[LET_THM] >> rpt conj_tac
  >- (* ALL_DISTINCT *)
     (imp_res_tac cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
      pop_assum (qspec_then `sbb with bb_instructions :=
        MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst old new inst)
            sbb.bb_instructions` mp_tac) >>
      imp_res_tac venomExecProofsTheory.lookup_block_label >> simp[])
  >- (* Terminators: split via MEM_replace_block_cases *)
     (rpt strip_tac >> gvs[MEM_replace_block_cases]
      >- (imp_res_tac phi_map_preserves_terminator >>
          imp_res_tac venomExecPropsTheory.lookup_block_MEM >> res_tac)
      >> res_tac)
  >> (* PHIs: split via MEM_replace_block_cases *)
  rpt strip_tac >> gvs[MEM_replace_block_cases]
  >- (imp_res_tac phi_map_removes_label >> fs[])
  >> res_tac
QED

Theorem update_succ_phi_labels_label_absent:
  !succs old new bbs.
    old <> new /\
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
               is_terminator inst.inst_opcode ==>
               ~MEM (Label old) inst.inst_operands) /\
    (!bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions /\
               inst.inst_opcode = PHI /\ ~MEM bb.bb_label succs ==>
               ~MEM (Label old) inst.inst_operands) ==>
    !bb inst. MEM bb (update_succ_phi_labels old new bbs succs) /\
              MEM inst bb.bb_instructions /\
              is_block_label_opcode inst.inst_opcode ==>
              ~MEM (Label old) inst.inst_operands
Proof
  Induct
  >- (rpt strip_tac >>
      fs[update_succ_phi_labels_def, is_block_label_opcode_def] >> res_tac)
  \\ rpt gen_tac \\ strip_tac
  \\ rw[update_succ_phi_labels_cons]
  \\ Cases_on `lookup_block h bbs` \\ fs[]
  >- (first_x_assum (qspecl_then [`old`, `new`, `bbs`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> fs[] >> rpt strip_tac >>
         first_x_assum (qspecl_then [`bb'`, `inst'`] mp_tac) >>
         simp[] >> imp_res_tac lookup_block_NONE_not_label >> fs[])) >>
      disch_tac >> res_tac)
  \\ rename1 `lookup_block h bbs = SOME sbb`
  \\ mp_tac (Q.SPECL [`old`, `new`, `bbs`, `h`, `sbb`, `succs`]
              uspl_replace_block_preconds)
  \\ (impl_tac >- (fs[LET_THM, listTheory.MEM] >> rpt strip_tac >> res_tac))
  \\ simp[LET_THM] \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [`old`, `new`,
      `replace_block h
         (sbb with bb_instructions :=
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                       else subst_label_inst old new inst)
               sbb.bb_instructions) bbs`] mp_tac)
  \\ (impl_tac >- (rpt conj_tac >> rpt strip_tac >> fs[] >> res_tac))
  \\ disch_tac \\ res_tac
QED

(* After a merge step, the merged-away label is absent *)
(* Core helper case 1: merged block's succs don't include next_lbl *)
Theorem merge_merged_no_succ_ref:
  !func bb next_bb.
    wf_function func /\
    MEM bb func.fn_blocks /\
    MEM next_bb func.fn_blocks /\
    bb.bb_label <> next_bb.bb_label /\
    can_merge_blocks func bb next_bb ==>
    ~MEM next_bb.bb_label (bb_succs (merge_blocks bb next_bb))
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `next_bb`] bb_succs_merge_blocks) >>
  (impl_tac >- (fs[wf_function_def] >> res_tac)) >>
  strip_tac >> fs[can_merge_blocks_def] >>
  mp_tac (Q.SPECL [`func`, `next_bb.bb_label`, `bb`] num_preds_1_unique_pred) >>
  (impl_tac >- fs[]) >>
  disch_then (qspec_then `next_bb` mp_tac) >>
  (impl_tac >- fs[]) >>
  strip_tac >> fs[]
QED

(* Core helper case 2: original block (not bb, not next_bb) has no succ ref *)
Theorem merge_other_no_succ_ref:
  !func bb next_bb blk.
    can_merge_blocks func bb next_bb /\
    MEM bb func.fn_blocks /\
    MEM blk func.fn_blocks /\
    MEM next_bb.bb_label (bb_succs blk) ==>
    blk = bb
Proof
  rpt strip_tac >> fs[can_merge_blocks_def] >>
  mp_tac (Q.SPECL [`func`, `next_bb.bb_label`, `bb`] num_preds_1_unique_pred) >>
  (impl_tac >- fs[]) >>
  disch_then (qspec_then `blk` mp_tac) >>
  simp[]
QED

(* Combined: no block in intermediate list has next_lbl in bb_succs *)
Theorem merge_intermediate_no_succ_ref:
  !func lbl bb next_bb blk.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_bb.bb_label func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_bb.bb_label /\
    MEM blk (replace_block lbl (merge_blocks bb next_bb)
              (remove_block next_bb.bb_label func.fn_blocks)) ==>
    ~MEM next_bb.bb_label (bb_succs blk)
Proof
  rpt strip_tac >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  fs[MEM_replace_block_cases]
  >- metis_tac[merge_merged_no_succ_ref]
  >> (
    fs[cfgTransformProofsTheory.MEM_remove_block_iff] >>
    imp_res_tac cfgTransformProofsTheory.MEM_remove_block >>
    metis_tac[merge_other_no_succ_ref])
QED

(* Terminators in intermediate blocks don't reference Label next_lbl *)
(* Any block in the intermediate list is well-formed *)
Theorem bb_well_formed_intermediate:
  !func lbl bb next_bb blk.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_bb.bb_label func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    MEM blk (replace_block lbl (merge_blocks bb next_bb)
              (remove_block next_bb.bb_label func.fn_blocks)) ==>
    bb_well_formed blk
Proof
  rpt strip_tac >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  fs[MEM_replace_block_cases]
  >- (gvs[] >>
      irule simplifyCfgHelpersTheory.bb_well_formed_merge_blocks >>
      fs[wf_function_def, can_merge_blocks_def] >> res_tac)
  >> (fs[cfgTransformProofsTheory.MEM_remove_block_iff] >>
      imp_res_tac cfgTransformProofsTheory.MEM_remove_block >>
      fs[wf_function_def])
QED

(* Terminators in intermediate blocks don't reference Label next_lbl *)
Theorem merge_intermediate_no_terminator_ref:
  !func lbl bb next_bb bb' inst.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_bb.bb_label func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_bb.bb_label /\
    MEM bb' (replace_block lbl (merge_blocks bb next_bb)
              (remove_block next_bb.bb_label func.fn_blocks)) /\
    MEM inst bb'.bb_instructions /\
    is_terminator inst.inst_opcode ==>
    ~MEM (Label next_bb.bb_label) inst.inst_operands
Proof
  rpt strip_tac >>
  metis_tac[merge_intermediate_no_succ_ref, bb_well_formed_intermediate,
            label_not_in_succs_not_in_terminator]
QED

(* Core: fn_phi_preds_wf + unique labels + lookup → PHI Label lbl means
   blk is a successor of the block found by lookup *)
Theorem phi_ref_implies_successor:
  !func blk inst lbl pred_blk.
    wf_function func /\ fn_phi_preds_wf func /\
    MEM blk func.fn_blocks /\
    MEM inst blk.bb_instructions /\
    inst.inst_opcode = PHI /\
    MEM (Label lbl) inst.inst_operands /\
    lookup_block lbl func.fn_blocks = SOME pred_blk ==>
    MEM blk.bb_label (bb_succs pred_blk)
Proof
  rpt strip_tac >>
  fs[fn_phi_preds_wf_def] >>
  first_x_assum (qspecl_then [`blk`, `inst`, `lbl`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Now: MEM lbl (pred_labels func blk.bb_label) *)
  (* Unfold: ∃b. MEM b fn_blocks ∧ b.bb_label = lbl ∧ MEM blk.bb_label (bb_succs b) *)
  fs[cfgTransformTheory.pred_labels_def, cfgTransformTheory.block_preds_def,
     listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  (* Witness y: MEM y fn_blocks, y.bb_label = lbl, MEM blk.bb_label (bb_succs y) *)
  (* lookup gives pred_blk with pred_blk.bb_label = lbl, MEM pred_blk fn_blocks *)
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  (* y and pred_blk have same label, both MEM → equal by wf *)
  metis_tac[wf_blocks_unique]
QED

(* wf_function + MEM → lookup_block *)
Theorem wf_lookup_block:
  !func bb.
    wf_function func /\ MEM bb func.fn_blocks ==>
    lookup_block bb.bb_label func.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  irule venomExecPropsTheory.MEM_lookup_block >>
  fs[wf_function_def, venomInstTheory.fn_labels_def]
QED

(* Merged block case: PHIs in merge_blocks don't reference Label next_bb.bb_label
   when the merged block is not a successor of itself *)
Theorem merged_block_no_phi_ref:
  !func bb next_bb inst.
    wf_function func /\ fn_phi_preds_wf func /\
    MEM bb func.fn_blocks /\
    MEM next_bb func.fn_blocks /\
    can_merge_blocks func bb next_bb /\
    ~MEM bb.bb_label (bb_succs (merge_blocks bb next_bb)) /\
    MEM inst (merge_blocks bb next_bb).bb_instructions /\
    inst.inst_opcode = PHI ==>
    ~MEM (Label next_bb.bb_label) inst.inst_operands
Proof
  rpt strip_tac >>
  fs[can_merge_blocks_def, no_phis_def] >>
  (* Get bb_succs(merged) = bb_succs(next_bb) *)
  mp_tac (Q.SPECL [`bb`, `next_bb`] bb_succs_merge_blocks) >>
  (impl_tac >- (fs[wf_function_def] >> res_tac)) >>
  strip_tac >>
  (* Unfold merge_blocks for instructions via SUBGOAL_THEN *)
  SUBGOAL_THEN ``MEM inst (FRONT bb.bb_instructions ++ next_bb.bb_instructions)``
    ASSUME_TAC >- fs[merge_blocks_def] >>
  gvs[listTheory.MEM_APPEND]
  >- (
    (* inst from FRONT(bb): phi_ref_implies_successor → contradiction *)
    mp_tac (Q.SPECL [`func`, `bb`, `inst`, `next_bb.bb_label`, `next_bb`]
      phi_ref_implies_successor) >>
    (impl_tac >- (
      simp[] >>
      conj_tac >- (
        irule rich_listTheory.MEM_FRONT_NOT_NIL >> simp[] >>
        fs[wf_function_def] >> res_tac >> fs[bb_well_formed_def]) >>
      metis_tac[wf_lookup_block])) >>
    strip_tac >> fs[])
  >> (
    (* inst from next_bb: contradicts EVERY no-PHI *)
    fs[listTheory.EVERY_MEM] >> res_tac >> fs[])
QED

(* PHIs in non-successor blocks don't reference Label next_lbl *)
Theorem merge_intermediate_no_phi_ref:
  !func lbl bb next_bb bb' inst.
    wf_function func /\
    fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_bb.bb_label func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb /\
    lbl <> next_bb.bb_label /\
    MEM bb' (replace_block lbl (merge_blocks bb next_bb)
              (remove_block next_bb.bb_label func.fn_blocks)) /\
    ~MEM bb'.bb_label (bb_succs (merge_blocks bb next_bb)) /\
    MEM inst bb'.bb_instructions /\
    inst.inst_opcode = PHI ==>
    ~MEM (Label next_bb.bb_label) inst.inst_operands
Proof
  rpt strip_tac >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  Cases_on `bb' = merge_blocks bb next_bb` >>
  gvs[]
  THENL [
    (* Case 1: bb' = merged block *)
    mp_tac (Q.SPECL [`func`, `bb`, `next_bb`, `inst`] merged_block_no_phi_ref) >>
    fs[simplifyCfgDefsTheory.merge_blocks_def] >>
    asm_rewrite_tac[],
    (* Case 2: bb' is from remove_block *)
    fs[MEM_replace_block_cases] >>
    imp_res_tac cfgTransformProofsTheory.MEM_remove_block >>
    mp_tac (Q.SPECL [`func`, `bb'`, `inst`, `next_bb.bb_label`, `next_bb`]
      phi_ref_implies_successor) >>
    simp[] >> strip_tac >>
    mp_tac (Q.SPECL [`bb`, `next_bb`] bb_succs_merge_blocks) >>
    (impl_tac >- (fs[wf_function_def] >> res_tac)) >>
    strip_tac >> fs[]
  ]
QED

(* replace_block on remove_block is identity when label matches *)
Theorem replace_block_remove_block_noop:
  !lbl bb bbs. replace_block lbl bb (remove_block lbl bbs) = remove_block lbl bbs
Proof
  gen_tac >> gen_tac >> Induct >>
  simp[cfgTransformTheory.replace_block_def, cfgTransformTheory.remove_block_def] >>
  rpt strip_tac >> IF_CASES_TAC >>
  gvs[cfgTransformTheory.replace_block_def, cfgTransformTheory.remove_block_def]
QED

(* subst_label_op with same old and new is identity *)
Theorem subst_label_op_same:
  !lbl op. subst_label_op lbl lbl op = op
Proof
  rpt gen_tac >> Cases_on `op` >> rw[cfgTransformTheory.subst_label_op_def]
QED

(* subst_label_inst with same old and new is identity *)
Theorem subst_label_inst_same:
  !lbl inst. subst_label_inst lbl lbl inst = inst
Proof
  rw[cfgTransformTheory.subst_label_inst_def,
     venomInstTheory.instruction_component_equality] >>
  irule MAP_ID_ON >> rw[subst_label_op_same]
QED

(* Replacing a block with itself is identity when ALL_DISTINCT labels *)
Theorem replace_block_self:
  !lbl bbs x.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    lookup_block lbl bbs = SOME x ==>
    replace_block lbl x bbs = bbs
Proof
  rpt strip_tac >>
  rw[cfgTransformTheory.replace_block_def] >>
  irule MAP_ID_ON >> rw[] >> rpt strip_tac >>
  rename1 `MEM blk bbs` >>
  mp_tac (Q.SPECL [`blk.bb_label`, `bbs`, `blk`]
    venomExecProofsTheory.MEM_lookup_block) >>
  simp[]
QED

(* General FOLDL identity when step function preserves invariant and is identity *)
Theorem FOLDL_INVARIANT_ID:
  !l f e. (!x y. P x /\ MEM y l ==> f x y = x) /\ P e ==>
           FOLDL f e l = e
Proof
  Induct >> rw[listTheory.FOLDL] >> fs[listTheory.MEM] >>
  first_x_assum irule >> metis_tac[]
QED

(* Record update with same field value is identity *)
Theorem bb_insts_update_id:
  !bb:basic_block. bb with bb_instructions := bb.bb_instructions = bb
Proof
  Cases >> simp[venomInstTheory.basic_block_component_equality]
QED

(* update_succ_phi_labels with same old and new is identity on well-formed blocks *)
Theorem update_succ_phi_labels_same:
  !succs lbl bbs.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) ==>
    update_succ_phi_labels lbl lbl bbs succs = bbs
Proof
  rpt strip_tac >>
  rw[simplifyCfgDefsTheory.update_succ_phi_labels_def, LET_THM] >>
  irule FOLDL_INVARIANT_ID >>
  qexists_tac `\bs. ALL_DISTINCT (MAP (\b. b.bb_label) bs)` >>
  rw[] >>
  Cases_on `lookup_block y x`
  THENL [
    simp[],
    simp[subst_label_inst_same, bb_insts_update_id] >>
    mp_tac (Q.SPECL [`y`, `x`, `x'`] replace_block_self) >>
    simp[]
  ]
QED
(* label_absent on remove_block when all references to lbl come from
   blocks with label lbl (via num_preds=1 + fn_phi_preds_wf) *)
Theorem label_absent_fn_remove_self_loop:
  !func lbl bb.
    wf_function func /\ fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    can_merge_blocks func bb bb ==>
    label_absent_fn lbl (func with fn_blocks := remove_block lbl func.fn_blocks)
Proof
  rpt strip_tac >>
  rw[label_absent_fn_def] >> rpt strip_tac >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  fs[cfgTransformProofsTheory.MEM_remove_block_iff] >>
  fs[is_block_label_opcode_def]
  THENL [
    (* Terminator case: bb' has Label lbl in terminator *)
    (* label_not_in_succs contrapositive: MEM lbl (bb_succs bb') *)
    CCONTR_TAC >> fs[] >>
    mp_tac (Q.SPECL [`func`, `lbl`, `bb`] num_preds_1_unique_pred) >>
    (impl_tac >- fs[can_merge_blocks_def]) >>
    disch_then (qspec_then `bb'` mp_tac) >>
    simp[] >>
    metis_tac[label_not_in_succs_not_in_terminator, wf_function_def],
    (* PHI case: bb' has Label lbl in PHI *)
    mp_tac (Q.SPECL [`func`, `bb'`, `inst`, `lbl`, `bb`]
      phi_ref_implies_successor) >>
    asm_rewrite_tac[] >> strip_tac >>
    gvs[can_merge_blocks_def, listTheory.MEM]
  ]
QED

Theorem label_absent_merge_step:
  !func lbl next_lbl bb next_bb.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_preds_wf func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    label_absent_fn next_lbl
      (func with fn_blocks :=
        update_succ_phi_labels next_lbl lbl
          (replace_block lbl (merge_blocks bb next_bb)
             (remove_block next_lbl func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb)))
Proof
  rpt strip_tac >>
  imp_res_tac venomExecProofsTheory.lookup_block_label >>
  reverse (Cases_on `lbl = next_lbl`) >>
  gvs[]
  THENL [
    (* Main case: lbl ≠ next_lbl *)
    rw[label_absent_fn_def] >> rpt strip_tac >>
    mp_tac (Q.SPECL [`bb_succs (merge_blocks bb next_bb)`,
      `next_bb.bb_label`, `bb.bb_label`,
      `replace_block bb.bb_label (merge_blocks bb next_bb)
         (remove_block next_bb.bb_label func.fn_blocks)`]
      update_succ_phi_labels_label_absent) >>
    (impl_tac >- (
      rpt conj_tac >> fs[]
      THENL [
        irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >>
        simp[simplifyCfgDefsTheory.merge_blocks_def] >>
        irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
        fs[wf_function_def, venomInstTheory.fn_labels_def],
        metis_tac[merge_intermediate_no_terminator_ref],
        metis_tac[merge_intermediate_no_phi_ref]
      ])) >>
    disch_then (qspecl_then [`bb'`, `inst`] mp_tac) >> simp[],
    (* Degenerate case: lbl = next_lbl → bb = next_bb (self-loop) *)
    REWRITE_TAC[replace_block_remove_block_noop] >>
    mp_tac (Q.SPECL [`bb_succs (merge_blocks bb bb)`, `bb.bb_label`,
      `remove_block bb.bb_label func.fn_blocks`] update_succ_phi_labels_same) >>
    (impl_tac >- (
      irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >>
      fs[wf_function_def, venomInstTheory.fn_labels_def])) >>
    DISCH_TAC >> fs[] >>
    mp_tac (Q.SPECL [`func`, `bb.bb_label`, `bb`] label_absent_fn_remove_self_loop) >>
    asm_rewrite_tac[] >> simp[]
  ]
QED

(* ----------------------------------------------------------------
   New approach: instead of proving subst is identity (which is FALSE
   in the a=target bypass edge case), we prove subst PRESERVES
   SEMANTICS. The key insight: label_map keys are dead labels (not in
   fn_labels, not in successors), so substituting them doesn't affect
   execution because vs_prev_bb always stays within fn_labels.
   ---------------------------------------------------------------- *)

(* After collapse_dfs, label_map keys are not in fn_labels of the output.
   Each merge step removes next_lbl from fn_blocks and adds it to lm.
   Each bypass step removes b.bb_label from fn_blocks and adds it to lm.
   fn_labels only shrinks, so old entries remain disjoint. *)
(* fn_labels after merge step = FILTER (≠ next_lbl) (fn_labels func).
   Proof: USPL preserves labels; replace_block preserves labels (merged has
   same label as lbl); remove_block removes next_lbl. *)
Theorem fn_labels_after_merge_step:
  !func lbl next_lbl bb next_bb.
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb ==>
    fn_labels (func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) =
    FILTER (\l. l <> next_lbl) (fn_labels func)
Proof
  rpt strip_tac >>
  simp[fn_labels_def, MAP_bb_label_update_succ_phi_labels] >>
  imp_res_tac lookup_block_label >>
  simp[fn_labels_replace_block, merge_blocks_def, fn_labels_remove_block]
QED

Theorem lm_keys_not_in_fn_labels_merge_step:
  !func lbl next_lbl bb next_bb label_map.
    (!old. MEM old (MAP FST label_map) ==> ~MEM old (fn_labels func)) /\
    wf_function func /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    let func' = func with fn_blocks :=
      update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb)) in
    !old. MEM old (MAP FST ((next_bb.bb_label, lbl) :: label_map)) ==>
      ~MEM old (fn_labels func')
Proof
  rpt strip_tac >> simp[LET_THM] >>
  imp_res_tac fn_labels_after_merge_step >>
  imp_res_tac lookup_block_label >>
  simp[listTheory.MEM_FILTER] >>
  gvs[] >>
  rpt strip_tac >> gvs[] >>
  res_tac
QED

(* fn_labels after do_merge_jump = FILTER (≠ b.bb_label) (fn_labels func) *)
Theorem fn_labels_after_do_merge_jump:
  !func a b label_map func' lm'.
    wf_function func /\ MEM a func.fn_blocks /\ MEM b func.fn_blocks /\
    do_merge_jump func a b label_map = SOME (func', lm') ==>
    fn_labels func' = FILTER (\l. l <> b.bb_label) (fn_labels func)
Proof
  rpt strip_tac >>
  fs[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  rename [`lookup_block target_lbl func.fn_blocks = SOME target`] >>
  imp_res_tac lookup_block_label >>
  simp[fn_labels_def, fn_labels_replace_block, fn_labels_remove_block]
QED

Theorem lm_keys_not_in_fn_labels_bypass_step:
  !func label_map bb succs func' lm'.
    (!old. MEM old (MAP FST label_map) ==> ~MEM old (fn_labels func)) /\
    wf_function func /\
    MEM bb func.fn_blocks /\
    try_bypass func label_map bb succs = (func', lm', T) ==>
    !old. MEM old (MAP FST lm') ==> ~MEM old (fn_labels func')
Proof
  ntac 3 gen_tac >> Induct_on `succs` >>
  rw[try_bypass_def] >>
  (* Handle guard: MEM target_lbl (bb_succs bb) ∨ target_lbl = bb.bb_label *)
  TRY (IF_CASES_TAC >> gvs[] >> res_tac >> NO_TAC) >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* Successful do_merge_jump case *)
  imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
  drule_all fn_labels_after_do_merge_jump >> strip_tac >>
  fs[do_merge_jump_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  rpt strip_tac >>
  imp_res_tac lookup_block_label >>
  fs[listTheory.MEM_FILTER] >>
  gvs[] >>
  first_x_assum (qspec_then `old` mp_tac) >> simp[] >>
  strip_tac >> simp[listTheory.MEM_FILTER]
QED

Triviality wf_keys_merge_obl:
  !func lbl next_lbl bb next_bb label_map.
    (wf_function func /\
     !old. MEM old (MAP FST label_map) ==> ~MEM old (fn_labels func)) /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    can_merge_blocks func bb next_bb ==>
    wf_function
      (func with fn_blocks :=
        update_succ_phi_labels next_lbl lbl
          (replace_block lbl (merge_blocks bb next_bb)
             (remove_block next_lbl func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb))) /\
    !old.
      old = next_bb.bb_label \/ MEM old (MAP FST label_map) ==>
      ~MEM old
        (fn_labels
           (func with fn_blocks :=
             update_succ_phi_labels next_lbl lbl
               (replace_block lbl (merge_blocks bb next_bb)
                  (remove_block next_lbl func.fn_blocks))
               (bb_succs (merge_blocks bb next_bb))))
Proof
  rpt gen_tac >> strip_tac >> fs[] >> conj_tac
  >- (irule (GEN_ALL simplifyCfgWfTheory.wf_function_merge_step) >>
      rpt (first_x_assum (irule_at Any)))
  >- (rpt strip_tac >>
      imp_res_tac fn_labels_after_merge_step >>
      imp_res_tac lookup_block_label >>
      fs[listTheory.MEM_FILTER] >> gvs[] >> res_tac)
QED

Triviality wf_keys_bypass_obl:
  !func label_map bb succs func' lm'.
    (wf_function func /\
     !old. MEM old (MAP FST label_map) ==> ~MEM old (fn_labels func)) /\
    MEM bb func.fn_blocks /\
    try_bypass func label_map bb succs = (func', lm', T) ==>
    wf_function func' /\
    (!old. MEM old (MAP FST lm') ==> ~MEM old (fn_labels func'))
Proof
  rpt gen_tac >> strip_tac >> fs[] >> conj_tac
  >- (irule (GEN_ALL simplifyCfgWfTheory.wf_function_try_bypass) >>
      rpt (first_x_assum (irule_at Any)))
  >- (mp_tac (SPECL [``func:ir_function``, ``label_map:(string#string) list``,
        ``bb:basic_block``, ``succs:string list``, ``func':ir_function``,
        ``lm':(string#string) list``] lm_keys_not_in_fn_labels_bypass_step) >>
      fs[])
QED

Theorem lm_keys_not_in_fn_labels_collapse_dfs:
  !func label_map visited wl func' lm' vis'.
    collapse_dfs func label_map visited wl = (func', lm', vis') ==>
    wf_function func /\
    (!old. MEM old (MAP FST label_map) ==> ~MEM old (fn_labels func)) ==>
    wf_function func' /\
    (!old. MEM old (MAP FST lm') ==> ~MEM old (fn_labels func'))
Proof
  rpt gen_tac >> ntac 2 strip_tac >>
  irule (SIMP_RULE (srw_ss()) []
    (ISPEC ``\(lm:(string#string) list) func. wf_function func /\
       (!old. MEM old (MAP FST lm) ==> ~MEM old (fn_labels func))``
     simplifyCfgHelpersTheory.collapse_dfs_preserves2)) >>
  conj_tac >- ACCEPT_TAC (INST_TYPE [alpha |-> ``:string``] wf_keys_merge_obl) >>
  conj_tac >- ACCEPT_TAC wf_keys_bypass_obl >>
  qexistsl_tac [`func`, `label_map`, `vis'`, `visited`, `wl`] >> fs[]
QED

(* ================================================================
   Section 2: merge_step preserves run_function semantics
   ================================================================ *)

(* run_block results depend only on the remaining instructions from
   vs_inst_idx onwards, not on the absolute index or block identity.
   States must agree on all fields except vs_inst_idx.
   Proved by complete induction on remaining instruction count.

   Key insight: step_inst_base for non-INVOKE doesn't read vs_inst_idx
   (instIdxIndep.step_inst_inst_idx_indep), so the step results agree
   modulo inst_idx. run_block overwrites inst_idx after each non-terminator
   step, so the inst_idx difference doesn't propagate through the state.
   For terminators: JMP/JNZ set idx=0 (identical OK states), STOP/RETURN
   produce Halt (execution_equiv ignores idx). *)

(* erm(set_idx_0) equality + OK idx=0 implies result_equiv.
   Key: case split on result constructors, not on step_inst_base application. *)
Theorem erm_eq_result_equiv:
  !(r1:exec_result) r2.
    instIdxIndep$exec_result_map (\s'. s' with vs_inst_idx := 0) r1 =
    instIdxIndep$exec_result_map (\s'. s' with vs_inst_idx := 0) r2 /\
    (!v. r1 = OK v ==> v.vs_inst_idx = 0) /\
    (!v. r2 = OK v ==> v.vs_inst_idx = 0) ==>
    result_equiv {} r1 r2
Proof
  Cases >> Cases >>
  simp[instIdxIndepTheory.exec_result_map_def, result_equiv_def,
       state_equiv_def, execution_equiv_def,
       venomStateTheory.venom_state_component_equality,
       venomStateTheory.lookup_var_def]
QED

(* The halted-check case expression preserves result_equiv. *)
Theorem term_case_preserves_result_equiv:
  !r1 r2 (vars:string set).
    result_equiv vars r1 r2 ==>
    result_equiv vars
      (case r1 of OK v => if v.vs_halted then Halt v else OK v
       | Halt v => Halt v | Abort a v => Abort a v
       | IntRet l v => IntRet l v | Error e => Error e)
      (case r2 of OK v => if v.vs_halted then Halt v else OK v
       | Halt v => Halt v | Abort a v => Abort a v
       | IntRet l v => IntRet l v | Error e => Error e)
Proof
  Cases >> Cases >> simp[result_equiv_def] >>
  rpt strip_tac >>
  `v.vs_halted = v'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> fs[result_equiv_def, state_equiv_def]
QED

(* Terminators are never INVOKE — used to bridge step_inst/step_inst_base *)
Theorem is_terminator_not_INVOKE:
  !op. is_terminator op ==> op <> INVOKE
Proof
  Cases >> simp[is_terminator_def]
QED

(* For terminators, the run_block case gives result_equiv when inputs
   differ only in vs_inst_idx. Uses step_inst (not step_inst_base) directly. *)
Theorem rb_term_idx_shift:
  !fuel ctx inst (s1:venom_state) s2.
    is_terminator inst.inst_opcode /\
    (s1 with vs_inst_idx := 0) = (s2 with vs_inst_idx := 0) ==>
    result_equiv {}
      (case step_inst fuel ctx inst s1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt v => Halt v | Abort a v => Abort a v
       | IntRet l v => IntRet l v | Error e => Error e)
      (case step_inst fuel ctx inst s2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt v => Halt v | Abort a v => Abort a v
       | IntRet l v => IntRet l v | Error e => Error e)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_INVOKE] >>
  fs[step_inst_non_invoke] >>
  `s1 = (s1 with vs_inst_idx := 0) with vs_inst_idx := s1.vs_inst_idx` by
    simp[venomStateTheory.venom_state_component_equality] >>
  `s2 = (s1 with vs_inst_idx := 0) with vs_inst_idx := s2.vs_inst_idx` by
    fs[venomStateTheory.venom_state_component_equality] >>
  qabbrev_tac `s0 = s1 with vs_inst_idx := 0` >>
  ONCE_ASM_REWRITE_TAC[] >>
  irule term_case_preserves_result_equiv >>
  irule erm_eq_result_equiv >>
  rpt conj_tac >>
  TRY (qspecl_then [`inst`, `s0`, `s1.vs_inst_idx`]
         mp_tac instIdxIndepTheory.terminator_step_inst_base_idx_norm0 >>
       qspecl_then [`inst`, `s0`, `s2.vs_inst_idx`]
         mp_tac instIdxIndepTheory.terminator_step_inst_base_idx_norm0 >>
       simp[] >> NO_TAC) >>
  metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0]
QED

(* Helper: step_inst_base on a state s equals exec_result_map over
   step_inst_base on (s with vs_inst_idx := 0), for non-terminators. *)
Theorem step_inst_base_idx_factor:
  !inst (s:venom_state).
    ~is_terminator inst.inst_opcode ==>
    step_inst_base inst s =
    instIdxIndep$exec_result_map (\s'. s' with vs_inst_idx := s.vs_inst_idx)
      (step_inst_base inst (s with vs_inst_idx := 0))
Proof
  rpt strip_tac >>
  qspecl_then [`inst`, `s with vs_inst_idx := 0`, `s.vs_inst_idx`]
    mp_tac instIdxIndepTheory.step_inst_inst_idx_indep >>
  (impl_tac >- fs[]) >> DISCH_TAC >>
  pop_assum (SUBST1_TAC o SYM o
    SIMP_RULE (srw_ss()) [venomStateTheory.venom_state_component_equality]) >>
  AP_TERM_TAC >> rw[venomStateTheory.venom_state_component_equality]
QED

(* update_var commutes with vs_inst_idx update *)
Theorem update_var_idx_commute:
  !x v s k.
    update_var x v (s with vs_inst_idx := k) =
    (update_var x v s) with vs_inst_idx := k
Proof
  rw[update_var_def, venomStateTheory.venom_state_component_equality]
QED

(* bind_outputs commutes with vs_inst_idx update *)
Theorem bind_outputs_idx_commute:
  !outs vals s k.
    bind_outputs outs vals (s with vs_inst_idx := k) =
    OPTION_MAP (\s'. s' with vs_inst_idx := k) (bind_outputs outs vals s)
Proof
  rw[bind_outputs_def] >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[] >>
  (* Show FOLDL update_var commutes with idx *)
  `!pairs s0. FOLDL (\s' (out,val). update_var out val s')
                     (s0 with vs_inst_idx := k) pairs =
              (FOLDL (\s' (out,val). update_var out val s') s0 pairs)
                with vs_inst_idx := k` suffices_by simp[] >>
  Induct >> simp[] >> Cases >> simp[update_var_idx_commute] >> fs[]
QED

(* update_var commutes with full bookkeeping update *)
Theorem update_var_bk_commute:
  !x v s pb cb idx.
    update_var x v (s with <|vs_prev_bb := pb;
                              vs_current_bb := cb;
                              vs_inst_idx := idx|>) =
    (update_var x v s) with <|vs_prev_bb := pb;
                               vs_current_bb := cb;
                               vs_inst_idx := idx|>
Proof
  rw[update_var_def, venomStateTheory.venom_state_component_equality]
QED

(* bind_outputs commutes with full bookkeeping update (prev_bb, current_bb, inst_idx).
   update_var only modifies vs_vars, so all three fields are preserved. *)
Theorem bind_outputs_bk_commute:
  !outs vals s pb cb idx.
    bind_outputs outs vals (s with <|vs_prev_bb := pb;
                                     vs_current_bb := cb;
                                     vs_inst_idx := idx|>) =
    OPTION_MAP (\s'. s' with <|vs_prev_bb := pb;
                                vs_current_bb := cb;
                                vs_inst_idx := idx|>)
               (bind_outputs outs vals s)
Proof
  rw[bind_outputs_def] >>
  Cases_on `LENGTH outs = LENGTH vals` >> simp[] >>
  `!pairs s0. FOLDL (\s' (out,val). update_var out val s')
                     (s0 with <|vs_prev_bb := pb;
                                 vs_current_bb := cb;
                                 vs_inst_idx := idx|>) pairs =
              (FOLDL (\s' (out,val). update_var out val s') s0 pairs)
                with <|vs_prev_bb := pb;
                        vs_current_bb := cb;
                        vs_inst_idx := idx|>` suffices_by simp[] >>
  Induct >> simp[] >> Cases >> simp[update_var_bk_commute] >> fs[]
QED

(* merge_callee_state commutes with bookkeeping update *)
Theorem merge_callee_state_bk_commute:
  !s callee pb cb idx.
    merge_callee_state
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>)
      callee =
    (merge_callee_state s callee)
      with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>
Proof
  rw[merge_callee_state_def, venomStateTheory.venom_state_component_equality]
QED

(* INVOKE step_inst with bookkeeping-modified state:
   non-OK results are identical; OK result has the bookkeeping update.
   Key: setup_callee overwrites caller's bookkeeping, so callee is identical.
   merge_callee_state preserves caller's bookkeeping. bind_outputs preserves it. *)
Theorem setup_callee_bk_indep[local]:
  !cfn args (s:venom_state) pb cb idx.
    setup_callee cfn args
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) =
    setup_callee cfn args s
Proof
  rw[setup_callee_def, venomStateTheory.venom_state_component_equality]
QED

Theorem step_inst_invoke_bk_factor:
  !fuel ctx inst (s:venom_state) pb cb idx.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) =
    case step_inst fuel ctx inst s of
      OK v => OK (v with <|vs_prev_bb := pb;
                            vs_current_bb := cb;
                            vs_inst_idx := idx|>)
    | Halt h => Halt h
    | Abort a h => Abort a h
    | IntRet v h => IntRet v h
    | Error e => Error e
Proof
  rpt strip_tac >>
  ASM_SIMP_TAC (srw_ss()) [venomExecSemanticsTheory.step_inst_def] >>
  (* Establish bk-independence for eval_operand and eval_operands *)
  `!op. eval_operand op
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) =
    eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `!ops. eval_operands ops
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) =
    eval_operands ops s` by (
    Induct >> simp[eval_operands_def] >>
    BasicProvers.EVERY_CASE_TAC >> simp[]) >>
  (* Rewrite all bk-dependent terms to make both sides structurally aligned *)
  ASM_REWRITE_TAC[setup_callee_bk_indep, merge_callee_state_bk_commute,
                  bind_outputs_bk_commute] >>
  (* Now LHS has OPTION_MAP (...) (bind_outputs ... (merge_callee_state s v))
     and RHS has bind_outputs ... (merge_callee_state s v) inside case *)
  simp_tac std_ss [optionTheory.OPTION_MAP_DEF] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* step_inst factors through exec_result_map for ALL non-terminator opcodes
   including INVOKE. The key insight: INVOKE's eval_operands, setup_callee,
   run_function, merge_callee_state, and bind_outputs are all independent of
   vs_inst_idx (setup_callee overwrites it; merge_callee_state preserves caller's;
   bind_outputs preserves it). *)
Theorem eval_operand_idx_indep:
  !op (s:venom_state). eval_operand op s = eval_operand op (s with vs_inst_idx := 0)
Proof
  Cases >> simp[eval_operand_def, venomStateTheory.lookup_var_def]
QED

Theorem eval_operands_idx_indep:
  !ops (s:venom_state). eval_operands ops s = eval_operands ops (s with vs_inst_idx := 0)
Proof
  Induct >- simp[eval_operands_def] >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC[eval_operands_def] >>
  ONCE_REWRITE_TAC[eval_operand_idx_indep] >>
  ONCE_ASM_REWRITE_TAC[] >>
  simp_tac (srw_ss()) []
QED

Theorem setup_callee_idx_indep:
  !f args (s:venom_state).
    setup_callee f args s = setup_callee f args (s with vs_inst_idx := 0)
Proof
  rw[setup_callee_def]
QED

Theorem merge_callee_state_idx_factor:
  !l (s:venom_state).
    merge_callee_state s l =
    merge_callee_state (s with vs_inst_idx := 0) l with vs_inst_idx := s.vs_inst_idx
Proof
  rw[merge_callee_state_def, venomStateTheory.venom_state_component_equality]
QED

(* INVOKE case: step_inst on s vs s with vs_inst_idx := 0 gives identical
   results except OK case where inst_idx differs.
   Key: setup_callee overwrites caller state, so callee is identical.
   Only merge_callee_state/bind_outputs in OK path depend on caller's idx. *)
Theorem step_inst_invoke_idx_factor:
  !fuel ctx inst (s:venom_state).
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst s =
    case step_inst fuel ctx inst (s with vs_inst_idx := 0) of
      OK s0 => OK (s0 with vs_inst_idx := s.vs_inst_idx)
    | other => other
Proof
  rpt strip_tac >>
  ASM_REWRITE_TAC[venomExecSemanticsTheory.step_inst_def] >>
  (* Rewrite only LHS to use (s with vs_inst_idx := 0) *)
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[eval_operands_idx_indep])) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[setup_callee_idx_indep])) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[merge_callee_state_idx_factor])) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[bind_outputs_idx_commute])) >>
  BasicProvers.every_case_tac >> simp[] >> fs[]
QED

(* Double update on vs_inst_idx: outer update wins *)
Theorem vs_inst_idx_double_update:
  !s a b. (s with vs_inst_idx := a) with vs_inst_idx := b = s with vs_inst_idx := b
Proof
  simp[venomStateTheory.venom_state_component_equality]
QED

(* Helper: non-terminator step_inst OK case on idx-differing states.
   If s1 produces OK v, then s2 produces OK v' with v ≡ v' mod idx. *)
Theorem step_inst_idx_OK:
  !fuel ctx inst s1 s2 v.
    ~is_terminator inst.inst_opcode /\
    (s1 with vs_inst_idx := 0) = (s2 with vs_inst_idx := 0) /\
    step_inst fuel ctx inst s1 = OK v ==>
    ?v'. step_inst fuel ctx inst s2 = OK v' /\
         (v with vs_inst_idx := 0) = (v' with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >| [
    (* INVOKE case: factor both sides through base *)
    qspecl_then [`fuel`,`ctx`,`inst`,`s1`] mp_tac step_inst_invoke_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    qspecl_then [`fuel`,`ctx`,`inst`,`s2`] mp_tac step_inst_invoke_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    (* s1 gave OK v. Factor rewrites step_inst s1 = case (base) of OK s0 => OK(s0 with idx:=s1.idx) | ... *)
    (* So base must be OK. Base for s2 is identical (states agree mod idx). *)
    Cases_on `step_inst fuel ctx inst (s1 with vs_inst_idx := 0)` >>
    gvs[] >>
    (* base = OK v'', s1 result = OK(v'' with idx:=s1.idx) = OK v, so v = v'' with idx:=s1.idx *)
    (* s2 result = OK(v'' with idx:=s2.idx) *)
    qexists_tac `v'' with vs_inst_idx := s2.vs_inst_idx` >>
    ASM_REWRITE_TAC[vs_inst_idx_double_update],
    (* Non-INVOKE case: factor through step_inst_base + exec_result_map *)
    qspecl_then [`inst`,`s1`] mp_tac step_inst_base_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    qspecl_then [`inst`,`s2`] mp_tac step_inst_base_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    qpat_x_assum `inst.inst_opcode <> INVOKE` (fn th =>
      let val rw = MATCH_MP venomExecSemanticsTheory.step_inst_non_invoke th
      in RULE_ASSUM_TAC (REWRITE_RULE[rw]) >> REWRITE_TAC[rw] end) >>
    Cases_on `step_inst_base inst (s1 with vs_inst_idx := 0)` >>
    gvs[instIdxIndepTheory.exec_result_map_def] >>
    (* Same as INVOKE: base = OK v'', witness = v'' with idx:=s2.idx *)
    qexists_tac `v'' with vs_inst_idx := s2.vs_inst_idx` >>
    ASM_REWRITE_TAC[vs_inst_idx_double_update]
  ]
QED

(* Helper: non-terminator step_inst non-OK case on idx-differing states.
   If s1 doesn't produce OK, both sides give result_equiv {} results. *)
Theorem step_inst_idx_nonOK:
  !fuel ctx inst s1 s2.
    ~is_terminator inst.inst_opcode /\
    (s1 with vs_inst_idx := 0) = (s2 with vs_inst_idx := 0) /\
    (!v. step_inst fuel ctx inst s1 <> OK v) ==>
    result_equiv {} (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >| [
    (* INVOKE: both sides factor through same base, non-OK passes through unchanged *)
    qspecl_then [`fuel`,`ctx`,`inst`,`s1`] mp_tac step_inst_invoke_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    qspecl_then [`fuel`,`ctx`,`inst`,`s2`] mp_tac step_inst_invoke_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    Cases_on `step_inst fuel ctx inst (s1 with vs_inst_idx := 0)` >>
    gvs[result_equiv_empty_refl],
    (* Non-INVOKE: both sides factor through exec_result_map *)
    qspecl_then [`inst`,`s1`] mp_tac step_inst_base_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    qspecl_then [`inst`,`s2`] mp_tac step_inst_base_idx_factor >>
    (impl_tac >- ASM_REWRITE_TAC[]) >> DISCH_TAC >>
    qpat_x_assum `inst.inst_opcode <> INVOKE` (fn th =>
      let val rw = MATCH_MP venomExecSemanticsTheory.step_inst_non_invoke th
      in RULE_ASSUM_TAC (REWRITE_RULE[rw]) >> REWRITE_TAC[rw] end) >>
    Cases_on `step_inst_base inst (s1 with vs_inst_idx := 0)` >>
    gvs[instIdxIndepTheory.exec_result_map_def] >>
    simp[stateEquivTheory.result_equiv_def,
         stateEquivTheory.execution_equiv_def,
         venomStateTheory.venom_state_component_equality,
         venomStateTheory.lookup_var_def]
  ]
QED

(* run_block_idx_shift DELETED — FALSE with PHI-parallel run_block semantics.
   run_block now ignores vs_inst_idx (always starts with eval_phis + run_block_non_phis
   from phi_prefix_length). The old theorem assumed run_block stepped from vs_inst_idx.
   Was unused downstream. See run_block_non_phis_idx_shift for the correct version. *)

(* ================================================================
   Section 2a: eval_phis / phi_prefix_length bridge lemmas
   eval_phis and phi_prefix_length depend only on the PHI prefix.
   These lemmas let us relate run_block on merged blocks to run_block
   on the original blocks.
   ================================================================ *)

Theorem is_terminator_not_PHI:
  !op. is_terminator op ==> op <> PHI
Proof Cases >> rw[is_terminator_def]
QED

(* eval_phis stops at first non-PHI, so appending after one is invisible *)
Theorem eval_phis_append_non_phi:
  !l s h rest. h.inst_opcode <> PHI ==>
    eval_phis s (l ++ h::rest) = eval_phis s l
Proof Induct >> rw[eval_phis_def]
QED

(* phi_prefix_length likewise *)
Theorem phi_prefix_length_append_non_phi:
  !l h rest. h.inst_opcode <> PHI ==>
    phi_prefix_length (l ++ h::rest) = phi_prefix_length l
Proof Induct >> rw[phi_prefix_length_def]
QED

Triviality phi_prefix_length_le_length:
  !l. phi_prefix_length l <= LENGTH l
Proof Induct >> simp[phi_prefix_length_def] >> rw[]
QED

(* General: phi_prefix_length l < LENGTH l when last element is not PHI *)
Triviality phi_prefix_length_lt_last_not_phi:
  !l. l <> [] /\ (LAST l).inst_opcode <> PHI ==>
    phi_prefix_length l < LENGTH l
Proof
  Induct >> simp[phi_prefix_length_def] >> rw[] >>
  Cases_on `l` >> fs[phi_prefix_length_def, listTheory.LAST_DEF]
QED

(* For well-formed blocks: phi_prefix_length < LENGTH (last is terminator, not PHI) *)
Theorem phi_prefix_length_lt_wf:
  !bb. bb_well_formed bb ==>
    phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  rw[] >> match_mp_tac phi_prefix_length_lt_last_not_phi >>
  fs[bb_well_formed_def] >> metis_tac[is_terminator_not_PHI]
QED

(* FRONT of well-formed block preserves eval_phis *)
Theorem eval_phis_FRONT_wf:
  !bb s. bb_well_formed bb ==>
    eval_phis s (FRONT bb.bb_instructions) = eval_phis s bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    metis_tac[is_terminator_not_PHI] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
    by metis_tac[listTheory.APPEND_FRONT_LAST] >>
  pop_assum (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[eval_phis_append_non_phi]
QED

(* FRONT of well-formed block preserves phi_prefix_length *)
Theorem phi_prefix_length_FRONT_wf:
  !bb. bb_well_formed bb ==>
    phi_prefix_length (FRONT bb.bb_instructions) =
    phi_prefix_length bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    metis_tac[is_terminator_not_PHI] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
    by metis_tac[listTheory.APPEND_FRONT_LAST] >>
  pop_assum (fn th => CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[phi_prefix_length_append_non_phi]
QED

(* If eval_phis returns Error on l, appending anything still returns Error *)
Theorem eval_phis_error_append:
  !l rest s e.
    eval_phis s l = Error e ==>
    eval_phis s (l ++ rest) = Error e
Proof
  Induct_on `l` >> simp[venomExecSemanticsTheory.eval_phis_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  Cases_on `x` >>
  Cases_on `eval_phis s l` >> gvs[] >>
  first_x_assum drule >> disch_then (qspec_then `rest` mp_tac) >> simp[]
QED

(* eval_phis on merged block = eval_phis on original block.
   Requires no_phis next_bb: otherwise merging could extend the PHI prefix. *)
Theorem eval_phis_merge_blocks:
  !bb next_bb s.
    bb_well_formed bb /\ no_phis next_bb /\
    next_bb.bb_instructions <> [] ==>
    eval_phis s (merge_blocks bb next_bb).bb_instructions =
    eval_phis s bb.bb_instructions
Proof
  rw[merge_blocks_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    metis_tac[is_terminator_not_PHI] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
    by metis_tac[listTheory.APPEND_FRONT_LAST] >>
  Cases_on `next_bb.bb_instructions` >- fs[] >>
  `h.inst_opcode <> PHI` by
    fs[no_phis_def, listTheory.EVERY_DEF] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV
    [ASSUME ``bb.bb_instructions =
      FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]``])) >>
  simp[GSYM listTheory.APPEND_ASSOC] >>
  simp[eval_phis_append_non_phi]
QED

(* phi_prefix_length on merged block = phi_prefix_length on original block *)
Theorem phi_prefix_length_merge_blocks:
  !bb next_bb.
    bb_well_formed bb /\ no_phis next_bb /\
    next_bb.bb_instructions <> [] ==>
    phi_prefix_length (merge_blocks bb next_bb).bb_instructions =
    phi_prefix_length bb.bb_instructions
Proof
  rw[merge_blocks_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    metis_tac[is_terminator_not_PHI] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
    by metis_tac[listTheory.APPEND_FRONT_LAST] >>
  Cases_on `next_bb.bb_instructions` >- fs[] >>
  `h.inst_opcode <> PHI` by
    fs[no_phis_def, listTheory.EVERY_DEF] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV
    [ASSUME ``bb.bb_instructions =
      FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]``])) >>
  simp[GSYM listTheory.APPEND_ASSOC] >>
  simp[phi_prefix_length_append_non_phi]
QED

(* eval_phis preserves halted *)
Theorem eval_phis_preserves_halted:
  !s insts s'. eval_phis s insts = OK s' ==> (s'.vs_halted <=> s.vs_halted)
Proof
  Induct_on `insts` >> rw[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> fs[] >>
  Cases_on `eval_one_phi s h` >> fs[] >>
  Cases_on `x` >> fs[] >>
  Cases_on `eval_phis s insts` >> fs[] >>
  rw[venomStateTheory.update_var_def]
QED

(* eval_phis preserves prev_bb *)
Theorem eval_phis_preserves_prev_bb:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_prev_bb = s.vs_prev_bb
Proof
  Induct_on `insts` >> rw[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> fs[] >>
  Cases_on `eval_one_phi s h` >> fs[] >>
  Cases_on `x` >> fs[] >>
  Cases_on `eval_phis s insts` >> fs[] >>
  rw[venomStateTheory.update_var_def]
QED

(* Index-shift for run_block_non_phis: the instruction-stepping loop DOES
   start from vs_inst_idx, so this theorem is correct. *)
Theorem run_block_non_phis_idx_shift:
  !n fuel ctx bb1 bb2 s1 s2.
    n = LENGTH bb1.bb_instructions - s1.vs_inst_idx /\
    (s1 with vs_inst_idx := 0) = (s2 with vs_inst_idx := 0) /\
    (LENGTH bb1.bb_instructions - s1.vs_inst_idx =
     LENGTH bb2.bb_instructions - s2.vs_inst_idx) /\
    s1.vs_inst_idx <= LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx <= LENGTH bb2.bb_instructions /\
    (!i. i < LENGTH bb1.bb_instructions - s1.vs_inst_idx ==>
         EL (s1.vs_inst_idx + i) bb1.bb_instructions =
         EL (s2.vs_inst_idx + i) bb2.bb_instructions) ==>
    result_equiv {}
      (run_block_non_phis fuel ctx bb1 s1)
      (run_block_non_phis fuel ctx bb2 s2)
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `n = 0`
  >- ((* No instructions remain *)
      fs[] >>
      `~(s1.vs_inst_idx < LENGTH bb1.bb_instructions)` by fs[] >>
      `~(s2.vs_inst_idx < LENGTH bb2.bb_instructions)` by fs[] >>
      ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
      simp[venomInstTheory.get_instruction_def,
           stateEquivTheory.result_equiv_def]) >>
  (* Inductive step: n > 0 *)
  fs[] >>
  `s1.vs_inst_idx < LENGTH bb1.bb_instructions` by fs[] >>
  `s2.vs_inst_idx < LENGTH bb2.bb_instructions` by fs[] >>
  `EL s1.vs_inst_idx bb1.bb_instructions =
   EL s2.vs_inst_idx bb2.bb_instructions` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[venomInstTheory.get_instruction_def] >>
  Cases_on `is_terminator
    (EL s2.vs_inst_idx bb2.bb_instructions).inst_opcode`
  >- ((* Terminator case *)
      asm_rewrite_tac[] >>
      irule rb_term_idx_shift >> ASM_REWRITE_TAC[]) >>
  (* Non-terminator case *)
  asm_rewrite_tac[] >>
  ASM_SIMP_TAC bool_ss [] >>
  Cases_on `step_inst fuel ctx (EL s2.vs_inst_idx bb2.bb_instructions) s1`
  >- (
    (* OK case: use step_inst_idx_OK for s2, then IH *)
    qspecl_then [`fuel`, `ctx`,
      `EL s2.vs_inst_idx bb2.bb_instructions`, `s1`, `s2`, `v`]
      mp_tac step_inst_idx_OK >>
    (impl_tac >- ASM_REWRITE_TAC[]) >>
    strip_tac >>
    ASM_REWRITE_TAC[] >>
    ASM_SIMP_TAC bool_ss [] >>
    qpat_x_assum `!m. m < _ ==> !fuel ctx. _`
      (qspec_then `LENGTH bb1.bb_instructions - SUC s1.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb1`, `bb2`,
      `v with vs_inst_idx := SUC s1.vs_inst_idx`,
      `v' with vs_inst_idx := SUC s2.vs_inst_idx`] mp_tac) >>
    (impl_tac
     >- (simp[vs_inst_idx_double_update] >>
         rpt strip_tac >>
         first_x_assum (qspec_then `SUC i` mp_tac) >>
         simp[arithmeticTheory.ADD_CLAUSES])) >>
    simp[]
  ) >>
  (* Non-OK cases: use step_inst_idx_nonOK for result_equiv *)
  qspecl_then [`fuel`, `ctx`,
    `EL s2.vs_inst_idx bb2.bb_instructions`, `s1`, `s2`]
    mp_tac step_inst_idx_nonOK >>
  (impl_tac >- (ASM_REWRITE_TAC[] >> simp[])) >>
  ASM_REWRITE_TAC[] >>
  Cases_on `step_inst fuel ctx (EL s2.vs_inst_idx bb2.bb_instructions) s2` >>
  simp[stateEquivTheory.result_equiv_def]
QED

(* ================================================================
   Section 2b: Helpers for merge_step_equiv
   ================================================================ *)

(* result_prev_bb_equiv for OK-OK implies prev_bb_equiv of carried states *)
Theorem result_prev_bb_equiv_OK:
  !s1 s2. result_prev_bb_equiv (OK s1) (OK s2) ==> prev_bb_equiv s1 s2
Proof
  simp[result_prev_bb_equiv_def]
QED

(* result_prev_bb_equiv OK on one side, non-OK on other is F *)
Theorem result_prev_bb_equiv_OK_mismatch:
  (!s e. ~result_prev_bb_equiv (OK s) (Halt e)) /\
  (!s e h. ~result_prev_bb_equiv (OK s) (Abort e h)) /\
  (!s v h. ~result_prev_bb_equiv (OK s) (IntRet v h)) /\
  (!s e. ~result_prev_bb_equiv (OK s) (Error e)) /\
  (!s e. ~result_prev_bb_equiv (Halt e) (OK s)) /\
  (!s e h. ~result_prev_bb_equiv (Abort e h) (OK s)) /\
  (!s v h. ~result_prev_bb_equiv (IntRet v h) (OK s)) /\
  (!s e. ~result_prev_bb_equiv (Error e) (OK s))
Proof
  simp[result_prev_bb_equiv_def]
QED

(* Left-decomposition: if left is OK, right must be OK with prev_bb_equiv *)
Theorem result_prev_bb_equiv_OK_left:
  !s1 r. result_prev_bb_equiv (OK s1) r ==>
    ?s2. r = OK s2 /\ prev_bb_equiv s1 s2
Proof
  rpt strip_tac >> Cases_on `r` >> fs[result_prev_bb_equiv_def]
QED

(* Non-OK left cases: the right side matches constructor *)
Theorem result_prev_bb_equiv_nonOK:
  (!s1 r. result_prev_bb_equiv (Halt s1) r ==>
    ?s2. r = Halt s2 /\ prev_bb_equiv s1 s2) /\
  (!a s1 r. result_prev_bb_equiv (Abort a s1) r ==>
    ?a2 s2. r = Abort a2 s2 /\ a = a2 /\ prev_bb_equiv s1 s2) /\
  (!v s1 r. result_prev_bb_equiv (IntRet v s1) r ==>
    ?v2 s2. r = IntRet v2 s2 /\ v = v2 /\ prev_bb_equiv s1 s2) /\
  (!e r. result_prev_bb_equiv (Error e) r ==>
    ?e2. r = Error e2 /\ e = e2)
Proof
  rpt conj_tac >> rpt gen_tac >> Cases_on `r` >> simp[result_prev_bb_equiv_def]
QED

(* Case analysis helper: if step results are result_prev_bb_equiv,
   and OK continuations preserve result_prev_bb_equiv,
   then the whole case expression preserves result_prev_bb_equiv.
   Eliminates manual Cases_on + OK_left + nonOK handling. *)
Theorem result_prev_bb_equiv_bind:
  !r1 r2 f1 f2.
    result_prev_bb_equiv r1 r2 /\
    (!v1 v2. r1 = OK v1 /\ r2 = OK v2 /\ prev_bb_equiv v1 v2 ==>
             result_prev_bb_equiv (f1 v1) (f2 v2))
    ==>
    result_prev_bb_equiv
      (case r1 of OK v => f1 v | Halt h => Halt h
       | Abort a s => Abort a s | IntRet vs s => IntRet vs s
       | Error e => Error e)
      (case r2 of OK v => f2 v | Halt h => Halt h
       | Abort a s => Abort a s | IntRet vs s => IntRet vs s
       | Error e => Error e)
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >>
  fs[result_prev_bb_equiv_def]
QED

Theorem result_prev_bb_equiv_terminator_ok:
  !v v'. prev_bb_equiv v v' ==>
    result_prev_bb_equiv
      (if v.vs_halted then Halt v else OK v)
      (if v'.vs_halted then Halt v' else OK v')
Proof
  rpt strip_tac >>
  `v.vs_halted = v'.vs_halted` by (
    qpat_x_assum `prev_bb_equiv v v'` mp_tac >>
    simp[prev_bb_equiv_def, venomStateTheory.venom_state_component_equality]) >>
  fs[] >> Cases_on `v'.vs_halted` >>
  fs[result_prev_bb_equiv_def]
QED

(* Continuation lemma: if r1 and r2 are result_prev_bb_equiv, and the
   OK continuations f/g preserve result_prev_bb_equiv, then the full
   case-dispatch preserves result_prev_bb_equiv. This eliminates the
   5-way case split + IH pattern in run_block induction proofs. *)
Theorem result_prev_bb_equiv_case_dispatch:
  !r1 r2 f g.
    result_prev_bb_equiv r1 r2 /\
    (!v1 v2. r1 = OK v1 /\ r2 = OK v2 /\ prev_bb_equiv v1 v2 ==>
       result_prev_bb_equiv (f v1) (g v2))
    ==>
    result_prev_bb_equiv
      (case r1 of OK s => f s | Halt h => Halt h | Abort a h => Abort a h
       | IntRet v h => IntRet v h | Error e => Error e)
      (case r2 of OK s => g s | Halt h => Halt h | Abort a h => Abort a h
       | IntRet v h => IntRet v h | Error e => Error e)
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[result_prev_bb_equiv_def]
QED

(* Running same non-PHI block on prev_bb_equiv states gives
   result_prev_bb_equiv. Proved by induction on remaining instructions. *)
Theorem run_block_prev_bb_equiv_same:
  !fuel ctx bb s1 s2.
    prev_bb_equiv s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    result_prev_bb_equiv
      (run_block fuel ctx bb s1)
      (run_block fuel ctx bb s2)
Proof
  rpt strip_tac >>
  irule run_block_prev_bb_equiv_gen >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      irule step_inst_all_prev_bb_equiv >> fs[listTheory.EVERY_EL])
  >> simp[result_prev_bb_equiv_def] >>
  imp_res_tac venomExecProofsTheory.eval_phis_no_phis >> simp[]
QED
(* Two small helpers for the prev_bb_equiv_subst proof *)
Triviality phi_prefix_length_opcode_eq:
  !l1 l2. LENGTH l1 = LENGTH l2 /\
    (!i. i < LENGTH l2 ==>
         (EL i l1).inst_opcode = (EL i l2).inst_opcode) ==>
    phi_prefix_length l1 = phi_prefix_length l2
Proof
  Induct >> rw[venomExecSemanticsTheory.phi_prefix_length_def] >>
  Cases_on `l2` >> fs[venomExecSemanticsTheory.phi_prefix_length_def] >>
  `h.inst_opcode = h'.inst_opcode` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >> first_x_assum match_mp_tac >> rw[] >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

(* In main semantics, PHI is not INVOKE so step_inst = step_inst_base *)
Triviality step_inst_phi_eq_base:
  !fuel ctx inst (s:venom_state).
    inst.inst_opcode = PHI ==> step_inst fuel ctx inst s = step_inst_base inst s
Proof
  rw[] >>
  `inst.inst_opcode <> INVOKE` by (Cases_on `inst.inst_opcode` >> fs[]) >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke]
QED

(* Running PHI-substituted block on prev_bb_equiv states with appropriate
   prev_bb values gives result_prev_bb_equiv.
   bb1 has old→new substitution in PHIs compared to bb2.
   s1.prev_bb = SOME new, s2.prev_bb = SOME old.
   Proof: irule run_block_prev_bb_equiv_gen. eval_phis handled by
   eval_phis_subst_prev_bb_equiv. Step-wise: PHI → step_inst = OK s (no-op),
   trivially prev_bb_equiv; non-PHI → identical instructions, step_inst_all_prev_bb_equiv. *)
Theorem run_block_prev_bb_equiv_subst:
  !n fuel ctx old new bb1 bb2 s1 s2.
    n = LENGTH bb1.bb_instructions - s1.vs_inst_idx /\
    prev_bb_equiv s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = SOME new /\
    s2.vs_prev_bb = SOME old /\
    old <> new /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    (!i. i < LENGTH bb2.bb_instructions ==>
         if (EL i bb2.bb_instructions).inst_opcode = PHI then
           EL i bb1.bb_instructions =
             subst_label_inst old new (EL i bb2.bb_instructions)
         else
           EL i bb1.bb_instructions = EL i bb2.bb_instructions) /\
    EVERY (\inst. phi_well_formed inst.inst_operands)
          (FILTER (\inst. inst.inst_opcode = PHI) bb2.bb_instructions) /\
    EVERY (\inst. ~MEM (Label new) inst.inst_operands)
          (FILTER (\inst. inst.inst_opcode = PHI) bb2.bb_instructions) ==>
    result_prev_bb_equiv
      (run_block fuel ctx bb1 s1)
      (run_block fuel ctx bb2 s2)
(* CHEATED: depends on step_inst_phi (PHI no-op), which is false in
   main's sequential PHI semantics. Needs rework. *)
Proof
  cheat
QED

(* run_block_prev_bb_equiv_idx_shift DELETED — FALSE with PHI-parallel semantics.
   run_block ignores vs_inst_idx; was unused downstream. *)

(* Helper: execution_equiv {} means states differ only in bookkeeping *)
Theorem execution_equiv_as_update:
  !s1 s2. execution_equiv {} s1 s2 ==>
    s1 = s2 with <|vs_prev_bb := s1.vs_prev_bb;
                    vs_current_bb := s1.vs_current_bb;
                    vs_inst_idx := s1.vs_inst_idx|>
Proof
  rw[execution_equiv_def, lookup_var_def,
     venomStateTheory.venom_state_component_equality] >>
  metis_tac[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM]
QED

Theorem bookkeeping_update_exec_equiv:
  !s pb cb idx. execution_equiv {}
    (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) s
Proof
  rw[execution_equiv_def, lookup_var_def]
QED

(* step_inst_base_jump_indep compat: old precond was <> PHI, now ~is_pseudo.
   Non-PHI non-terminator non-INVOKE opcodes are never PARAM in practice,
   but we handle PARAM explicitly here. *)
Triviality step_inst_base_bk_factor[local]:
  !inst s pb cb idx.
    inst.inst_opcode <> PHI /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    step_inst_base inst (s with <|vs_prev_bb := pb;
                                   vs_current_bb := cb;
                                   vs_inst_idx := idx|>) =
    instIdxIndep$exec_result_map
      (\s'. s' with <|vs_prev_bb := pb; vs_current_bb := cb;
                       vs_inst_idx := idx|>)
      (step_inst_base inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
      BasicProvers.EVERY_CASE_TAC >>
      gvs[update_var_def, instIdxIndepTheory.exec_result_map_def,
          venomStateTheory.venom_state_component_equality])
  >> (`~is_pseudo inst.inst_opcode` by (
        Cases_on `inst.inst_opcode` >> fs[is_pseudo_def]) >>
      simp[jumpIndepTheory.step_inst_base_jump_indep])
QED

(* Bookkeeping-update helper lemmas for eval_operand *)
Theorem eval_op_bk:
  !op s pb cb idx.
    eval_operand op
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) =
    eval_operand op s
Proof Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_ops_bk:
  !ops s pb cb idx.
    eval_operands ops
      (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>) =
    eval_operands ops s
Proof Induct >> simp[eval_operands_def, eval_op_bk]
QED

(* Terminator step with execution_equiv inputs produces
   lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {}).
   Jump terminators: both jump to same target → prev_bb_equiv on OK.
   Other terminators: halt/abort/intret with execution_equiv {} states. *)
Theorem step_inst_base_exec_equiv_term:
  !inst s pb cb idx.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
      (step_inst_base inst
        (s with <|vs_prev_bb := pb; vs_current_bb := cb; vs_inst_idx := idx|>))
      (step_inst_base inst s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  asm_simp_tac bool_ss [step_inst_base_def, eval_op_bk, eval_ops_bk,
       jump_to_def, halt_state_def, revert_state_def,
       LET_THM, set_returndata_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[lift_result_def, prev_bb_equiv_def, execution_equiv_def,
       venomStateTheory.venom_state_component_equality,
       lookup_var_def]
QED

(* Non-terminator step with execution_equiv: result states are execution_equiv {}.
   Uses step_inst_base_jump_indep to factor bookkeeping, then
   bookkeeping_update_exec_equiv for the result. *)
Theorem step_inst_base_exec_equiv_nonterm:
  !inst s1 s2.
    inst.inst_opcode <> PHI /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    execution_equiv {} s1 s2 ==>
    case step_inst_base inst s2 of
      OK s2' => ?s1'. step_inst_base inst s1 = OK s1' /\
                       execution_equiv {} s1' s2'
    | Halt h2 => ?h1. step_inst_base inst s1 = Halt h1 /\
                       execution_equiv {} h1 h2
    | Abort a h2 => ?h1. step_inst_base inst s1 = Abort a h1 /\
                          execution_equiv {} h1 h2
    | IntRet v h2 => ?h1. step_inst_base inst s1 = IntRet v h1 /\
                           execution_equiv {} h1 h2
    | Error e => step_inst_base inst s1 = Error e
Proof
  rpt strip_tac >>
  imp_res_tac execution_equiv_as_update >>
  qpat_x_assum `_ = _` SUBST1_TAC >>
  simp[step_inst_base_bk_factor,
       instIdxIndepTheory.exec_result_map_def] >>
  Cases_on `step_inst_base inst s2` >>
  simp[instIdxIndepTheory.exec_result_map_def] >>
  TRY (irule_at Any EQ_REFL) >>
  simp[execution_equiv_def, lookup_var_def]
QED

(* Like step_inst_base_exec_equiv_nonterm but for step_inst (handles INVOKE).
   For non-INVOKE: delegates to step_inst_base via step_inst_non_invoke.
   For INVOKE: setup_callee/run_function are identical (bookkeeping-independent),
   merge_callee_state preserves caller's bookkeeping, bind_outputs only updates vars. *)
Theorem step_inst_exec_equiv_nonterm:
  !fuel ctx inst s1 s2.
    inst.inst_opcode <> PHI /\
    ~is_terminator inst.inst_opcode /\
    execution_equiv {} s1 s2 ==>
    case step_inst fuel ctx inst s2 of
      OK s2' => ?s1'. step_inst fuel ctx inst s1 = OK s1' /\
                       execution_equiv {} s1' s2'
    | Halt h2 => ?h1. step_inst fuel ctx inst s1 = Halt h1 /\
                       execution_equiv {} h1 h2
    | Abort a h2 => ?h1. step_inst fuel ctx inst s1 = Abort a h1 /\
                          execution_equiv {} h1 h2
    | IntRet v h2 => ?h1. step_inst fuel ctx inst s1 = IntRet v h1 /\
                           execution_equiv {} h1 h2
    | Error e => step_inst fuel ctx inst s1 = Error e
Proof
  rpt strip_tac >>
  imp_res_tac execution_equiv_as_update >> pop_assum SUBST1_TAC >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[step_inst_invoke_bk_factor] >>
    Cases_on `step_inst fuel ctx inst s2` >>
    simp[execution_equiv_def, lookup_var_def])
  >> (
    simp[venomExecSemanticsTheory.step_inst_non_invoke,
         step_inst_base_bk_factor,
         instIdxIndepTheory.exec_result_map_def] >>
    Cases_on `step_inst_base inst s2` >>
    simp[instIdxIndepTheory.exec_result_map_def] >>
    TRY (irule_at Any EQ_REFL) >>
    simp[execution_equiv_def, lookup_var_def])
QED

(* One-step unfolding for run_block_non_phis at a non-terminator. *)
Theorem run_block_non_phis_nonterm_step:
  !fuel ctx bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE ==>
    run_block_non_phis fuel ctx bb s =
      case step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s of
        OK v => run_block_non_phis fuel ctx bb (v with vs_inst_idx := SUC s.vs_inst_idx)
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | IntRet vals s' => IntRet vals s'
      | Error e => Error e
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV
    [venomExecSemanticsTheory.run_block_non_phis_def])) >>
  simp[venomInstTheory.get_instruction_def,
       venomExecSemanticsTheory.step_inst_non_invoke]
QED

(* Same but uses step_inst (handles INVOKE too). *)
Theorem run_block_non_phis_nonterm_step_full:
  !fuel ctx bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    run_block_non_phis fuel ctx bb s =
      case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
        OK v => run_block_non_phis fuel ctx bb (v with vs_inst_idx := SUC s.vs_inst_idx)
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | IntRet vals s' => IntRet vals s'
      | Error e => Error e
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV
    [venomExecSemanticsTheory.run_block_non_phis_def])) >>
  simp[venomInstTheory.get_instruction_def]
QED

(* Terminator variant for run_block_non_phis. *)
Theorem run_block_non_phis_term_step:
  !fuel ctx bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    run_block_non_phis fuel ctx bb s =
      case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
        OK s' => if s'.vs_halted then Halt s' else OK s'
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | IntRet vals s' => IntRet vals s'
      | Error e => Error e
Proof
  rpt strip_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV
    [venomExecSemanticsTheory.run_block_non_phis_def])) >>
  simp[venomInstTheory.get_instruction_def]
QED

(* Generalized run_block_non_phis equivalence: execution_equiv inputs,
   no pseudo, same remaining instructions at different offsets →
   lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {}).
   Uses step_inst_exec_equiv_nonterm (handles INVOKE).
   run_block_non_phis version of exec_equiv_idx_shift.
   TRUE because run_block_non_phis starts from vs_inst_idx. *)
Theorem run_block_non_phis_exec_equiv_idx_shift:
  !n fuel ctx bb1 bb2 s1 s2.
    n = LENGTH bb1.bb_instructions - s1.vs_inst_idx /\
    (!i. i < LENGTH bb1.bb_instructions - s1.vs_inst_idx ==>
         (EL (s1.vs_inst_idx + i) bb1.bb_instructions).inst_opcode <> PHI /\
         (EL (s2.vs_inst_idx + i) bb2.bb_instructions).inst_opcode <> PHI /\
         EL (s1.vs_inst_idx + i) bb1.bb_instructions =
         EL (s2.vs_inst_idx + i) bb2.bb_instructions) /\
    execution_equiv {} s1 s2 /\
    (LENGTH bb1.bb_instructions - s1.vs_inst_idx =
     LENGTH bb2.bb_instructions - s2.vs_inst_idx) /\
    s1.vs_inst_idx <= LENGTH bb1.bb_instructions /\
    s2.vs_inst_idx <= LENGTH bb2.bb_instructions ==>
    lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
      (run_block_non_phis fuel ctx bb1 s1)
      (run_block_non_phis fuel ctx bb2 s2)
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `!m. m < n ==> _` (markerLib.hide_tac "IH") >>
  Cases_on `n = 0`
  >- ((* Base: no instructions remain *)
      gvs[] >>
      `~(s1.vs_inst_idx < LENGTH bb1.bb_instructions)` by fs[] >>
      `~(s2.vs_inst_idx < LENGTH bb2.bb_instructions)` by fs[] >>
      ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
      simp[venomInstTheory.get_instruction_def, lift_result_def])
  >> suspend "step_case"
QED

Resume run_block_non_phis_exec_equiv_idx_shift[step_case]:
  (* n > 0: setup *)
  `s1.vs_inst_idx < LENGTH bb1.bb_instructions` by fs[] >>
  `s2.vs_inst_idx < LENGTH bb2.bb_instructions` by fs[] >>
  (* Extract facts about current instruction *)
  `EL s1.vs_inst_idx bb1.bb_instructions =
   EL s2.vs_inst_idx bb2.bb_instructions /\
   (EL s1.vs_inst_idx bb1.bb_instructions).inst_opcode <> PHI /\
   (EL s2.vs_inst_idx bb2.bb_instructions).inst_opcode <> PHI` by (
    qpat_assum `!i. i < _ ==> _ /\ _ /\ _`
      (qspec_then `0` mp_tac) >> fs[]) >>
  fs[] >>
  Cases_on `is_terminator
    (EL s2.vs_inst_idx bb2.bb_instructions).inst_opcode`
  >- suspend "term_case"
  >> suspend "nonterm_case"
QED

Resume run_block_non_phis_exec_equiv_idx_shift[term_case]:
  (* Terminator case: terminators are never INVOKE, so step_inst = step_inst_base *)
  `(EL s2.vs_inst_idx bb2.bb_instructions).inst_opcode <> INVOKE` by
    metis_tac[is_terminator_not_INVOKE] >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb1`, `s1`]
    run_block_non_phis_term_step) >> simp[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb2`, `s2`]
    run_block_non_phis_term_step) >> simp[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  imp_res_tac execution_equiv_as_update >> pop_assum SUBST1_TAC >>
  mp_tac (Q.SPECL [`EL s2.vs_inst_idx bb2.bb_instructions`,
                    `s2`, `s1.vs_prev_bb`, `s1.vs_current_bb`,
                    `s1.vs_inst_idx`]
          step_inst_base_exec_equiv_term) >>
  simp[] >> DISCH_TAC >>
  Cases_on `step_inst_base (EL s2.vs_inst_idx bb2.bb_instructions) s2` >>
  Cases_on `step_inst_base (EL s2.vs_inst_idx bb2.bb_instructions)
    (s2 with <|vs_prev_bb := s1.vs_prev_bb;
                vs_current_bb := s1.vs_current_bb;
                vs_inst_idx := s1.vs_inst_idx|>)` >>
  fs[lift_result_def] >>
  (* OK/OK case: prev_bb_equiv v' v — expand and simplify *)
  qpat_x_assum `prev_bb_equiv _ _` mp_tac >>
  simp[prev_bb_equiv_def,
       venomStateTheory.venom_state_component_equality] >>
  strip_tac >> gvs[] >>
  Cases_on `v.vs_halted` >>
  simp[lift_result_def, prev_bb_equiv_def, execution_equiv_def,
       lookup_var_def,
       venomStateTheory.venom_state_component_equality]
QED

Resume run_block_non_phis_exec_equiv_idx_shift[nonterm_case]:
  (* Non-terminator case: use step_inst directly (handles INVOKE) *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb1`, `s1`]
    run_block_non_phis_nonterm_step_full) >> simp[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb2`, `s2`]
    run_block_non_phis_nonterm_step_full) >> simp[] >>
  disch_then (fn th => REWRITE_TAC[th]) >>
  mp_tac step_inst_exec_equiv_nonterm >>
  disch_then (qspecl_then [`fuel`, `ctx`,
    `EL s2.vs_inst_idx bb2.bb_instructions`,
    `s1`, `s2`] mp_tac) >>
  (impl_tac >- simp[]) >> DISCH_TAC >>
  Cases_on `step_inst fuel ctx
    (EL s2.vs_inst_idx bb2.bb_instructions) s2` >>
  fs[] >>
  TRY (simp[lift_result_def, execution_equiv_def, lookup_var_def] >>
       NO_TAC) >>
  (* OK case: s1 step = OK s1', exec_equiv s1' v, need IH *)
  `execution_equiv {} (s1' with vs_inst_idx := SUC s1.vs_inst_idx)
                      (v with vs_inst_idx := SUC s2.vs_inst_idx)` by
    fs[execution_equiv_def, lookup_var_def] >>
  markerLib.unhide_x_assum "IH"
    (qspec_then `LENGTH bb1.bb_instructions - SUC s1.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb1`, `bb2`,
    `s1' with vs_inst_idx := SUC s1.vs_inst_idx`,
    `v with vs_inst_idx := SUC s2.vs_inst_idx`] match_mp_tac) >>
  simp[] >> rpt strip_tac >> (
    `SUC i + s1.vs_inst_idx = i + SUC s1.vs_inst_idx` by decide_tac >>
    `SUC i + s2.vs_inst_idx = i + SUC s2.vs_inst_idx` by decide_tac >>
    qpat_assum `!i. i < LENGTH bb2.bb_instructions - s2.vs_inst_idx ==> _`
      (qspec_then `SUC i` mp_tac) >>
    (impl_tac >- decide_tac) >>
    asm_simp_tac bool_ss [])
QED

Finalise run_block_non_phis_exec_equiv_idx_shift;

(* Running merged block relates to running bb then next_bb.
   The merged block = FRONT(bb.insts) ++ next_bb.insts.
   Original: run_block bb → OK s_jumped → run_block next_bb s_jumped.
   Merged: run_block merged_bb → result.
   Non-OK from bb prefix: merged returns same non-OK (equality).
   OK from bb (terminator jump): merged continues into next_bb instructions,
   producing lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {}) with next_bb run.
   The difference: merged block doesn't do jump_to, so vs_prev_bb and
   vs_current_bb differ. prev_bb_equiv captures this for OK (both jump from
   next_bb's terminator to same target); execution_equiv {} for terminal
   (step_inst_base doesn't read bookkeeping fields). *)
(* When run_block returns OK from the terminator position, the result
   state is execution_equiv to the input state (terminator only changes
   bookkeeping: prev_bb, current_bb, inst_idx). *)
(* For any terminator: step_inst_base OK + ~halted implies exec_equiv.
   Only JMP/JNZ/DJMP produce OK + ~halted; all others halt or error. *)
Theorem step_inst_base_terminator_exec_equiv:
  !inst s v.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK v /\
    ~v.vs_halted ==>
    execution_equiv {} s v
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_terminator_def, step_inst_base_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[halt_state_def, revert_state_def, jump_to_def] >> rw[] >>
  fs[execution_equiv_def, lookup_var_def]
QED

(* run_block_non_phis version: at the terminator, exec_equiv holds *)
Theorem run_block_non_phis_terminator_exec_equiv:
  !fuel ctx bb s.
    bb_well_formed bb /\
    ~s.vs_halted /\
    s.vs_inst_idx = PRE (LENGTH bb.bb_instructions) ==>
    case run_block_non_phis fuel ctx bb s of
      OK v => execution_equiv {} s v /\ ~v.vs_halted
    | _ => T
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> [] /\
   is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_non_phis_def] >>
  simp[venomInstTheory.get_instruction_def] >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions =
   LAST bb.bb_instructions` by simp[listTheory.LAST_EL] >>
  simp[] >>
  `(LAST bb.bb_instructions).inst_opcode <> INVOKE` by
    metis_tac[is_terminator_not_INVOKE] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  Cases_on `step_inst_base (LAST bb.bb_instructions) s` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  metis_tac[step_inst_base_terminator_exec_equiv]
QED

(* step_inst OK preserves halted (for all opcodes including INVOKE) *)
Theorem foldl_update_var_preserves_halted[local]:
  !pairs acc. (FOLDL (\s' (out,val). update_var out val s') acc pairs).vs_halted
              = acc.vs_halted
Proof
  Induct >> rw[listTheory.FOLDL] >>
  Cases_on `h` >> rw[listTheory.FOLDL, venomStateTheory.update_var_def]
QED

Theorem step_inst_full_OK_preserves_halted[local]:
  !fuel ctx inst s v. step_inst fuel ctx inst s = OK v ==>
    (v.vs_halted <=> s.vs_halted)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    gvs[venomExecSemanticsTheory.step_inst_def] >>
    BasicProvers.every_case_tac >> gvs[] >>
    gvs[bind_outputs_def] >>
    simp[foldl_update_var_preserves_halted, merge_callee_state_def])
  >> (* non-INVOKE: step_inst = step_inst_base *)
  fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
  metis_tac[venomExecPropsTheory.step_inst_base_OK_preserves_halted]
QED

(* Step case for merge equivalence — NO INVOKE restriction.
 * Uses step_inst (with fuel,ctx) instead of step_inst_base.
 *)
(* run_block_non_phis version of merge_step_case.
   Same structure: one non-terminator step on both bb and merged, then IH. *)
Theorem run_block_non_phis_merge_step_case:
  !n fuel ctx bb next_bb s.
    n = PRE (LENGTH bb.bb_instructions) - s.vs_inst_idx /\
    n <> 0 /\
    bb_well_formed bb /\ bb_well_formed next_bb /\
    no_phis next_bb /\
    bb_succs bb <> [] /\
    ~s.vs_halted /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    (!m. m < n ==>
      !fuel ctx bb next_bb s.
        m = PRE (LENGTH bb.bb_instructions) - s.vs_inst_idx /\
        bb_well_formed bb /\ bb_well_formed next_bb /\
        no_phis next_bb /\
        bb_succs bb <> [] /\ ~s.vs_halted /\
        s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) ==>
        case run_block_non_phis fuel ctx bb s of
          OK s' =>
            lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
              (run_block_non_phis fuel ctx (merge_blocks bb next_bb) s)
              (run_block_non_phis fuel ctx next_bb (s' with vs_inst_idx := 0))
        | _ => T) ==>
    case run_block_non_phis fuel ctx bb s of
      OK s' =>
        lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
          (run_block_non_phis fuel ctx (merge_blocks bb next_bb) s)
          (run_block_non_phis fuel ctx next_bb (s' with vs_inst_idx := 0))
    | _ => T
Proof
  rpt strip_tac >>
  (* Arithmetic setup *)
  `s.vs_inst_idx < PRE (LENGTH bb.bb_instructions)` by decide_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `bb.bb_instructions <> []` by
    (qpat_assum `bb_well_formed bb` mp_tac >>
     simp_tac (srw_ss()) [bb_well_formed_def]) >>
  `next_bb.bb_instructions <> []` by
    (qpat_assum `bb_well_formed next_bb` mp_tac >>
     simp_tac (srw_ss()) [bb_well_formed_def]) >>
  `LENGTH (FRONT bb.bb_instructions) = PRE (LENGTH bb.bb_instructions)` by
    simp_tac (srw_ss()) [listTheory.LENGTH_FRONT, arithmeticTheory.PRE_SUB1] >>
  `s.vs_inst_idx < LENGTH (FRONT bb.bb_instructions)` by decide_tac >>
  (* EL idx in merged block = EL idx in bb *)
  `EL s.vs_inst_idx (FRONT bb.bb_instructions ++ next_bb.bb_instructions) =
   EL s.vs_inst_idx bb.bb_instructions` by (
    `EL s.vs_inst_idx (FRONT bb.bb_instructions ++ next_bb.bb_instructions) =
     EL s.vs_inst_idx (FRONT bb.bb_instructions)` by
      (match_mp_tac rich_listTheory.EL_APPEND1 >> decide_tac) >>
    `EL s.vs_inst_idx (FRONT bb.bb_instructions) =
     EL s.vs_inst_idx bb.bb_instructions` by
      (match_mp_tac rich_listTheory.EL_FRONT >>
       ASM_REWRITE_TAC [listTheory.NULL_EQ]) >>
    metis_tac []) >>
  `s.vs_inst_idx <
   LENGTH (FRONT bb.bb_instructions ++ next_bb.bb_instructions)` by
    (simp_tac (srw_ss()) [listTheory.LENGTH_APPEND] >> decide_tac) >>
  (* Not a terminator — only the last instruction is *)
  `~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by (
    qpat_assum `bb_well_formed bb` mp_tac >>
    simp_tac (srw_ss()) [bb_well_formed_def] >> strip_tac >>
    CCONTR_TAC >> full_simp_tac bool_ss [] >>
    res_tac >> decide_tac) >>
  (* Rewrite bb-side using one-step lemma *)
  `run_block_non_phis fuel ctx bb s =
   case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
     OK v => run_block_non_phis fuel ctx bb (v with vs_inst_idx := SUC s.vs_inst_idx)
   | Halt s' => Halt s' | Abort a s' => Abort a s'
   | IntRet vals s' => IntRet vals s' | Error e => Error e` by
    (match_mp_tac run_block_non_phis_nonterm_step_full >> simp[]) >>
  (* Rewrite merged-side using one-step lemma + EL equality *)
  `run_block_non_phis fuel ctx (merge_blocks bb next_bb) s =
   case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
     OK v => run_block_non_phis fuel ctx (merge_blocks bb next_bb)
               (v with vs_inst_idx := SUC s.vs_inst_idx)
   | Halt s' => Halt s' | Abort a s' => Abort a s'
   | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
    `run_block_non_phis fuel ctx (merge_blocks bb next_bb) s =
     case step_inst fuel ctx
       (EL s.vs_inst_idx (merge_blocks bb next_bb).bb_instructions) s of
       OK v => run_block_non_phis fuel ctx (merge_blocks bb next_bb)
                 (v with vs_inst_idx := SUC s.vs_inst_idx)
     | Halt s' => Halt s' | Abort a s' => Abort a s'
     | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
      match_mp_tac run_block_non_phis_nonterm_step_full >>
      simp[merge_blocks_def]) >>
    simp[merge_blocks_def]) >>
  ASM_REWRITE_TAC [] >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >>
  (* OK case: apply IH *)
  `SUC s.vs_inst_idx = s.vs_inst_idx + 1` by decide_tac >>
  first_x_assum (qspec_then `n - 1` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `next_bb`,
    `v with vs_inst_idx := s.vs_inst_idx + 1`] mp_tac) >>
  `~v.vs_halted` by
    metis_tac[step_inst_full_OK_preserves_halted] >>
  simp[]
QED

(* Block-level merge correctness (generalized to arbitrary start idx).
   The merged block = FRONT(bb.insts) ++ next_bb.insts.
   If run_block bb returns OK (terminator jump), the merged block
   produces an equivalent result to running next_bb from the jumped state.
   Non-OK from the prefix is identical (same instructions).
   Non-OK from the terminator: we don't claim anything (different code). *)
(* run_block_non_phis version of merge_equiv_gen.
   Induction on remaining instructions from vs_inst_idx. *)
Theorem run_block_non_phis_merge_equiv_gen:
  !n fuel ctx bb next_bb s.
    n = PRE (LENGTH bb.bb_instructions) - s.vs_inst_idx /\
    bb_well_formed bb /\ bb_well_formed next_bb /\
    no_phis next_bb /\
    bb_succs bb <> [] /\
    ~s.vs_halted /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) ==>
    case run_block_non_phis fuel ctx bb s of
      OK s' =>
        lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
          (run_block_non_phis fuel ctx (merge_blocks bb next_bb) s)
          (run_block_non_phis fuel ctx next_bb (s' with vs_inst_idx := 0))
    | _ => T
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `next_bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `LENGTH (FRONT bb.bb_instructions) = PRE (LENGTH bb.bb_instructions)`
    by metis_tac[rich_listTheory.LENGTH_FRONT] >>
  Cases_on `n = 0`
  >- suspend "base_case"
  >> (
    (* Step case: delegate to merge_step_case *)
    match_mp_tac run_block_non_phis_merge_step_case >>
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    fs[])
QED

Resume run_block_non_phis_merge_equiv_gen[base_case]:
  (* n=0, so idx = PRE(LENGTH bb.insts), at the terminator *)
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by decide_tac >>
  (* Get exec_equiv from the terminator step *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`]
    run_block_non_phis_terminator_exec_equiv) >>
  asm_simp_tac (srw_ss()) [] >>
  Cases_on `run_block_non_phis fuel ctx bb s` >> simp[] >>
  strip_tac >>
  (* OK case: v is exec_equiv to s and ~v.vs_halted *)
  `execution_equiv {} s (v with vs_inst_idx := 0)` by
    fs[execution_equiv_def, lookup_var_def] >>
  qspecl_then [`LENGTH next_bb.bb_instructions`, `fuel`, `ctx`,
    `merge_blocks bb next_bb`, `next_bb`, `s`,
    `v with vs_inst_idx := 0`]
    mp_tac run_block_non_phis_exec_equiv_idx_shift >>
  simp[merge_blocks_def, listTheory.LENGTH_APPEND] >>
  (impl_tac >- (
    `!i. i < LENGTH next_bb.bb_instructions ==>
         EL (i + PRE (LENGTH bb.bb_instructions))
             (FRONT bb.bb_instructions ++ next_bb.bb_instructions) =
         EL i next_bb.bb_instructions` by (
      rpt strip_tac >>
      `LENGTH (FRONT bb.bb_instructions) <=
       i + PRE (LENGTH bb.bb_instructions)` by decide_tac >>
      simp[rich_listTheory.EL_APPEND2] >> decide_tac) >>
    rpt strip_tac >> fs[listTheory.EVERY_EL, no_phis_def] >>
    res_tac >> fs[])) >>
  simp[]
QED

Finalise run_block_non_phis_merge_equiv_gen;


(* Top-level merge equiv: bridges run_block through eval_phis +
   run_block_non_phis, then uses run_block_non_phis_merge_equiv_gen. *)
Theorem run_block_merge_equiv:
  !fuel ctx bb next_bb s.
    bb_well_formed bb /\ bb_well_formed next_bb /\
    no_phis next_bb /\
    bb_succs bb <> [] /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 ==>
    case run_block fuel ctx bb s of
      OK s' =>
        lift_result prev_bb_equiv (execution_equiv {}) (execution_equiv {})
          (run_block fuel ctx (merge_blocks bb next_bb) s)
          (run_block fuel ctx next_bb (s' with vs_inst_idx := 0))
    | _ => T
Proof
  rpt strip_tac >>
  `next_bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_def] >>
  simp[] >>
  mp_tac (Q.SPECL [`PRE (LENGTH bb.bb_instructions)`,
    `fuel`, `ctx`, `bb`, `next_bb`, `s`]
    run_block_non_phis_merge_equiv_gen) >>
  simp[]
QED

(* ================================================================
   Helpers for merge_step_equiv_strong
   ================================================================ *)

(* Cons unfolding for update_succ_phi_labels *)
(* update_succ_phi_labels_cons — duplicate removed, see line 314 *)

(* Not in MAP bb_label → lookup gives NONE *)
Theorem lookup_block_not_MEM_NONE:
  !lbl bbs. ~MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs = NONE
Proof
  Induct_on `bbs` >>
  rw[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  fs[venomInstTheory.lookup_block_def]
QED

(* Helper: lookup through update_succ_phi_labels when label not in succs *)
Theorem lookup_block_update_succ_phi_not_in_succs:
  !old_lbl new_lbl bbs succs cb.
    ~MEM cb succs ==>
    lookup_block cb (update_succ_phi_labels old_lbl new_lbl bbs succs) =
    lookup_block cb bbs
Proof
  Induct_on `succs`
  >- simp[simplifyCfgDefsTheory.update_succ_phi_labels_def] >>
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [update_succ_phi_labels_cons] >>
  Cases_on `lookup_block h bbs` >> simp_tac (srw_ss()) []
  >- (first_x_assum match_mp_tac >> fs[]) >>
  rename1 `_ = SOME sbb` >>
  qmatch_goalsub_abbrev_tac `update_succ_phi_labels _ _ bbs' _` >>
  `lookup_block cb bbs' = lookup_block cb bbs` by (
    qunabbrev_tac `bbs'` >>
    irule cfgTransformProofsTheory.lookup_block_replace_neq >>
    imp_res_tac venomExecProofsTheory.lookup_block_label >> fs[]) >>
  qpat_x_assum `!old_lbl new_lbl bbs cb. _`
    (qspecl_then [`old_lbl`, `new_lbl`, `bbs'`, `cb`] mp_tac) >>
  fs[]
QED

(* Helper: lookup through update_succ_phi_labels preserves SOME/NONE *)
Theorem lookup_block_update_succ_phi_labels_exists:
  !old_lbl new_lbl bbs succs cb.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ((?bb. lookup_block cb bbs = SOME bb) <=>
     (?bb. lookup_block cb
       (update_succ_phi_labels old_lbl new_lbl bbs succs) = SOME bb))
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  >- ((* SOME in bbs → SOME in update *)
      imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
      imp_res_tac venomExecProofsTheory.lookup_block_label >>
      `MEM cb (MAP (\b. b.bb_label) bbs)` by
        (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
      `MEM cb (MAP (\b. b.bb_label)
         (update_succ_phi_labels old_lbl new_lbl bbs succs))` by
        simp[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
      fs[listTheory.MEM_MAP] >>
      rename1 `MEM y' _` >>
      `lookup_block cb (update_succ_phi_labels old_lbl new_lbl bbs succs) =
       SOME y'` by (
        irule venomExecProofsTheory.MEM_lookup_block >> rw[] >>
        fs[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels]) >>
      metis_tac[])
  >- ((* SOME in update → SOME in bbs *)
      imp_res_tac venomExecProofsTheory.lookup_block_MEM >>
      imp_res_tac venomExecProofsTheory.lookup_block_label >>
      `MEM cb (MAP (\b. b.bb_label)
         (update_succ_phi_labels old_lbl new_lbl bbs succs))` by
        (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
      `MEM cb (MAP (\b. b.bb_label) bbs)` by
        fs[simplifyCfgHelpersTheory.MAP_bb_label_update_succ_phi_labels] >>
      fs[listTheory.MEM_MAP] >>
      rename1 `MEM y' _` >>
      `lookup_block cb bbs = SOME y'` by (
        irule venomExecProofsTheory.MEM_lookup_block >> rw[]) >>
      metis_tac[])
QED

(* Block lookup at lbl in the merged function *)
Theorem lookup_block_merge_lbl:
  !func lbl next_lbl bb next_bb.
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    wf_function func /\
    lbl <> next_lbl ==>
    ?merged_bb.
      lookup_block lbl
        (update_succ_phi_labels next_lbl lbl
          (replace_block lbl (merge_blocks bb next_bb)
             (remove_block next_lbl func.fn_blocks))
          (bb_succs (merge_blocks bb next_bb))) =
      SOME merged_bb /\
      merged_bb.bb_label = lbl
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  qabbrev_tac `bbs1 = remove_block next_lbl func.fn_blocks` >>
  qabbrev_tac `merged = merge_blocks bb next_bb` >>
  qabbrev_tac `bbs2 = replace_block lbl merged bbs1` >>
  (* merged.bb_label = lbl *)
  `merged.bb_label = lbl` by (
    qunabbrev_tac `merged` >>
    simp[simplifyCfgDefsTheory.merge_blocks_def] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label) >>
  (* lookup lbl in bbs1 *)
  `lookup_block lbl bbs1 = SOME bb` by (
    qunabbrev_tac `bbs1` >>
    simp[cfgTransformProofsTheory.lookup_block_remove_neq]) >>
  (* lookup lbl in bbs2 = SOME merged *)
  `lookup_block lbl bbs2 = SOME merged` by (
    qunabbrev_tac `bbs2` >>
    irule cfgTransformProofsTheory.lookup_block_replace_eq >>
    metis_tac[]) >>
  (* ALL_DISTINCT bbs2 *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs2)` by (
    qunabbrev_tac `bbs2` >> qunabbrev_tac `bbs1` >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> rw[] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >> rw[]) >>
  (* ∃bb. lookup in update = SOME bb *)
  `?mb. lookup_block lbl
     (update_succ_phi_labels next_lbl lbl bbs2
        (bb_succs merged)) = SOME mb` by (
    irule (iffLR lookup_block_update_succ_phi_labels_exists) >>
    metis_tac[]) >>
  qexists_tac `mb` >> rw[] >>
  imp_res_tac venomExecProofsTheory.lookup_block_label
QED

(* next_lbl is not in func' *)
Theorem lookup_block_merge_next_lbl:
  !func lbl next_lbl bb next_bb.
    lookup_block lbl func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    wf_function func /\
    lbl <> next_lbl ==>
    lookup_block next_lbl
      (update_succ_phi_labels next_lbl lbl
        (replace_block lbl (merge_blocks bb next_bb)
           (remove_block next_lbl func.fn_blocks))
        (bb_succs (merge_blocks bb next_bb))) =
    NONE
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def] >>
  qabbrev_tac `bbs1 = remove_block next_lbl func.fn_blocks` >>
  qabbrev_tac `merged = merge_blocks bb next_bb` >>
  qabbrev_tac `bbs2 = replace_block lbl merged bbs1` >>
  `merged.bb_label = lbl` by (
    qunabbrev_tac `merged` >>
    simp[simplifyCfgDefsTheory.merge_blocks_def] >>
    imp_res_tac venomExecProofsTheory.lookup_block_label) >>
  (* Chain: remove → NONE, replace_neq → NONE, update preserves NONE *)
  `lookup_block next_lbl bbs1 = NONE` by (
    qunabbrev_tac `bbs1` >>
    simp[cfgTransformProofsTheory.lookup_block_remove_eq]) >>
  `lookup_block next_lbl bbs2 = NONE` by (
    qunabbrev_tac `bbs2` >>
    simp[cfgTransformProofsTheory.lookup_block_replace_neq]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) bbs2)` by (
    qunabbrev_tac `bbs2` >> qunabbrev_tac `bbs1` >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_replace_block >> rw[] >>
    irule cfgTransformProofsTheory.ALL_DISTINCT_remove_block >> rw[]) >>
  `~(?b. lookup_block next_lbl
     (update_succ_phi_labels next_lbl lbl bbs2 (bb_succs merged)) = SOME b)` by (
    strip_tac >>
    `?b. lookup_block next_lbl bbs2 = SOME b` by
      metis_tac[lookup_block_update_succ_phi_labels_exists] >>
    fs[]) >>
  Cases_on `lookup_block next_lbl
    (update_succ_phi_labels next_lbl lbl bbs2 (bb_succs merged))` >>
  fs[]
QED
(* JMP instruction with inst_wf always returns OK via step_inst *)
Theorem step_inst_jmp_ok[local]:
  !inst s fuel ctx.
    inst_wf inst /\ inst.inst_opcode = JMP ==>
    ?lbl. step_inst fuel ctx inst s = OK (jump_to lbl s)
Proof
  rpt strip_tac >>
  `?lbl. inst.inst_operands = [Label lbl] /\ inst.inst_outputs = []` by
    fs[inst_wf_def] >>
  qexists_tac `lbl` >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    simp[step_inst_non_invoke] >>
  ASM_REWRITE_TAC[] >>
  `inst = <|inst_id := inst.inst_id; inst_opcode := JMP;
            inst_operands := [Label lbl]; inst_outputs := []|>` by
    simp[instruction_component_equality] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[step_jmp_behavior]
QED

(* When run_block on bb fails (non-OK) and bb has a JMP terminator (single_succ_jmp),
   then run_block on merge_blocks bb next_bb also fails with the same result.
   Key insight: with single_succ_jmp, JMP always returns OK (given ~halted, inst_wf).
   So the failure must be at a non-terminator in FRONT(bb.insts). The merged block
   has the same non-terminators as a prefix, so it fails identically. *)
(* Helper: run_block_non_phis on merged = on bb when bb doesn't return OK.
   Induction on remaining instructions. At non-terminator: same instruction
   in both → identical step → IH. At terminator (JMP): always OK → contradiction. *)
Theorem run_block_non_phis_merge_nonOK_same:
  !n fuel ctx bb next_bb s.
    n = PRE (LENGTH bb.bb_instructions) - s.vs_inst_idx /\
    bb_well_formed bb /\ bb_well_formed next_bb /\
    single_succ_jmp bb (HD (bb_succs bb)) /\
    EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    ~s.vs_halted /\
    (!v. run_block_non_phis fuel ctx bb s <> OK v) ==>
    run_block_non_phis fuel ctx (merge_blocks bb next_bb) s =
    run_block_non_phis fuel ctx bb s
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  `bb.bb_instructions <> []` by
    (qpat_assum `bb_well_formed bb` mp_tac >>
     simp_tac (srw_ss()) [bb_well_formed_def]) >>
  `next_bb.bb_instructions <> []` by
    (qpat_assum `bb_well_formed next_bb` mp_tac >>
     simp_tac (srw_ss()) [bb_well_formed_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `LENGTH (FRONT bb.bb_instructions) = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[rich_listTheory.LENGTH_FRONT] >>
  Cases_on `n = 0`
  >- (
    (* Base: at terminator — JMP always OK, contradicts non-OK hypothesis *)
    `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by decide_tac >>
    `EL s.vs_inst_idx bb.bb_instructions = LAST bb.bb_instructions` by
      simp[listTheory.LAST_EL] >>
    `(LAST bb.bb_instructions).inst_opcode = JMP` by
      fs[single_succ_jmp_def] >>
    `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by
      (ASM_REWRITE_TAC[] >> EVAL_TAC) >>
    `inst_wf (LAST bb.bb_instructions)` by
      fs[listTheory.EVERY_EL, listTheory.LAST_EL] >>
    `?lbl. step_inst fuel ctx (LAST bb.bb_instructions) s =
           OK (jump_to lbl s)` by metis_tac[step_inst_jmp_ok] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`]
      run_block_non_phis_term_step) >>
    simp[] >> ASM_REWRITE_TAC[] >>
    simp[venomStateTheory.jump_to_def] >> metis_tac[])
  >> (
    (* Step: non-terminator — same instruction in both, then IH *)
    `s.vs_inst_idx < PRE (LENGTH bb.bb_instructions)` by decide_tac >>
    `s.vs_inst_idx < LENGTH (FRONT bb.bb_instructions)` by decide_tac >>
    `~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` by (
      strip_tac >>
      `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
        (qpat_x_assum `bb_well_formed bb`
           (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
         first_x_assum match_mp_tac >> ASM_REWRITE_TAC[]) >>
      decide_tac) >>
    `EL s.vs_inst_idx (merge_blocks bb next_bb).bb_instructions =
     EL s.vs_inst_idx bb.bb_instructions` by (
      simp[merge_blocks_def] >>
      `EL s.vs_inst_idx (FRONT bb.bb_instructions ++ next_bb.bb_instructions) =
       EL s.vs_inst_idx (FRONT bb.bb_instructions)` by
        (match_mp_tac rich_listTheory.EL_APPEND1 >> decide_tac) >>
      `EL s.vs_inst_idx (FRONT bb.bb_instructions) =
       EL s.vs_inst_idx bb.bb_instructions` by
        (match_mp_tac rich_listTheory.EL_FRONT >>
         ASM_REWRITE_TAC[listTheory.NULL_EQ]) >>
      metis_tac[]) >>
    `s.vs_inst_idx < LENGTH (merge_blocks bb next_bb).bb_instructions` by
      (simp[merge_blocks_def, listTheory.LENGTH_APPEND] >> decide_tac) >>
    (* Unfold run_block_non_phis on both sides *)
    `run_block_non_phis fuel ctx bb s =
     case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
       OK v => run_block_non_phis fuel ctx bb
                 (v with vs_inst_idx := SUC s.vs_inst_idx)
     | Halt s' => Halt s' | Abort a s' => Abort a s'
     | IntRet vals s' => IntRet vals s' | Error e => Error e` by
      (match_mp_tac run_block_non_phis_nonterm_step_full >> simp[]) >>
    `run_block_non_phis fuel ctx (merge_blocks bb next_bb) s =
     case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
       OK v => run_block_non_phis fuel ctx (merge_blocks bb next_bb)
                 (v with vs_inst_idx := SUC s.vs_inst_idx)
     | Halt s' => Halt s' | Abort a s' => Abort a s'
     | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
      `run_block_non_phis fuel ctx (merge_blocks bb next_bb) s =
       case step_inst fuel ctx
         (EL s.vs_inst_idx (merge_blocks bb next_bb).bb_instructions) s of
         OK v => run_block_non_phis fuel ctx (merge_blocks bb next_bb)
                   (v with vs_inst_idx := SUC s.vs_inst_idx)
       | Halt s' => Halt s' | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s' | Error e => Error e` by (
        match_mp_tac run_block_non_phis_nonterm_step_full >>
        simp[merge_blocks_def]) >>
      ASM_REWRITE_TAC[]) >>
    ASM_REWRITE_TAC[] >>
    Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
    simp[] >>
    (* OK case: apply IH *)
    first_x_assum (qspec_then `n - 1` mp_tac) >>
    (impl_tac >- decide_tac) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `next_bb`,
      `v with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
    `~v.vs_halted` by metis_tac[step_inst_full_OK_preserves_halted] >>
    disch_then match_mp_tac >> simp[] >> gvs[])
QED

(* Splitting a list at the phi prefix boundary *)
Theorem phi_prefix_split:
  !l. phi_prefix_length l < LENGTH l ==>
    ?pre h rest. l = pre ++ h :: rest /\
      LENGTH pre = phi_prefix_length l /\
      h.inst_opcode <> PHI
Proof
  Induct_on `l` >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rpt strip_tac >>
  IF_CASES_TAC >> gvs[] >>
  qexistsl [`h :: pre`, `h'`, `rest`] >>
  simp[]
QED

(* If bb is well-formed, has single_succ_jmp, eval_phis succeeds, ~halted,
   and run_block doesn't return OK, then phi_prefix_length < PRE LENGTH.
   (Otherwise all of FRONT is PHI, run_block_non_phis starts at JMP which always OK.) *)
(* Top-level run_block version: delegates to run_block_non_phis_merge_nonOK_same
   since run_block_def = run_block_non_phis ... (s with vs_inst_idx := 0). *)
Theorem run_block_merge_nonOK_same:
  !n fuel ctx bb next_bb s.
    n = PRE (LENGTH bb.bb_instructions) - s.vs_inst_idx /\
    bb_well_formed bb /\ bb_well_formed next_bb /\
    single_succ_jmp bb (HD (bb_succs bb)) /\
    EVERY inst_wf bb.bb_instructions /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    ~s.vs_halted /\
    (!v. run_block fuel ctx bb s <> OK v) ==>
    run_block fuel ctx (merge_blocks bb next_bb) s = run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_def] >> simp[] >>
  match_mp_tac run_block_non_phis_merge_nonOK_same >>
  qexists `PRE (LENGTH bb.bb_instructions)` >> simp[] >>
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `!v. run_block _ _ bb _ <> OK v` mp_tac >> simp[] >>
  qexists `v` >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_block_def] >> simp[]
QED

(* Per-element extraction for phi_values_agree: if the whole list agrees,
   then any individual PHI instruction in the list satisfies the case property *)
Theorem phi_values_agree_MEM:
  !insts a b inst.
    phi_values_agree a b insts /\ MEM inst insts /\ inst.inst_opcode = PHI /\
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) ==>
    case (resolve_phi a inst.inst_operands, resolve_phi b inst.inst_operands) of
      (NONE, _) => T | (SOME _, NONE) => T | (SOME va, SOME vb) => va = vb
Proof
  Induct_on `insts` >> simp[phi_values_agree_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
  (* Goal 1: h is PHI, inst = h *)
  >- (Cases_on `resolve_phi a h.inst_operands` >> gvs[] >>
      Cases_on `resolve_phi b h.inst_operands` >> gvs[])
  (* Goal 2: h is PHI, MEM inst insts — use IH *)
  >- (first_x_assum match_mp_tac >> rpt conj_tac
      >- (Cases_on `resolve_phi a h.inst_operands` >> gvs[] >>
          Cases_on `resolve_phi b h.inst_operands` >> gvs[])
      >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC,
          rpt strip_tac >>
          first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]])
  (* Goal 3: h not PHI, MEM inst insts — prefix contradiction *)
  >- (gvs[listTheory.MEM_EL] >>
      first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[])
QED

val _ = export_theory();
