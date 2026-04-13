(*
 * CFG Normalization -- Simulation Helpers
 *
 * Lemmas for proving insert_split preserves semantics.
 * Cached separately from main proof for faster iteration.
 *)

Theory cfgNormSim
Ancestors
  cfgNormDefs cfgTransformProofs stateEquiv venomExecSemantics
  venomWf execEquivProofs
Libs
  cfgNormDefsTheory cfgTransformTheory cfgTransformProofsTheory
  stateEquivTheory venomExecSemanticsTheory venomInstTheory
  venomStateTheory venomWfTheory finite_mapTheory

(* ================================================================
   Section 1: Basic structural lemmas
   ================================================================ *)

(* subst_label_terminator preserves bb_label *)
Theorem subst_label_terminator_bb_label:
  !old_lbl new_lbl bb.
    (subst_label_terminator old_lbl new_lbl bb).bb_label = bb.bb_label
Proof
  rw[subst_label_terminator_def]
QED

(* subst_label_terminator preserves length *)
Theorem subst_label_terminator_length:
  !old_lbl new_lbl bb.
    LENGTH (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[subst_label_terminator_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  simp[listTheory.LENGTH_APPEND, listTheory.LENGTH_FRONT]
QED

(* subst_label_terminator preserves non-terminator instructions *)
Theorem subst_label_terminator_non_term:
  !old_lbl new_lbl bb k.
    k < LENGTH bb.bb_instructions /\
    ~is_terminator (EL k bb.bb_instructions).inst_opcode ==>
    EL k (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    EL k bb.bb_instructions
Proof
  rw[subst_label_terminator_def, listTheory.EL_MAP]
QED

(* update_phis_for_split preserves bb_label *)
Theorem update_phis_for_split_bb_label:
  !old_lbl new_lbl var_repls bb.
    (update_phis_for_split old_lbl new_lbl var_repls bb).bb_label = bb.bb_label
Proof
  rw[update_phis_for_split_def]
QED

(* update_phis_for_split preserves length *)
Theorem update_phis_for_split_length:
  !old_lbl new_lbl var_repls bb.
    LENGTH (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[update_phis_for_split_def]
QED

(* update_phis_for_split preserves non-PHI instructions *)
Theorem update_phis_for_split_non_phi:
  !old_lbl new_lbl var_repls bb k.
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode <> PHI ==>
    EL k (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions =
    EL k bb.bb_instructions
Proof
  rw[update_phis_for_split_def, listTheory.EL_MAP]
QED

(* update_phis_for_split: PHI instruction has updated operands *)
Theorem update_phis_for_split_phi:
  !old_lbl new_lbl var_repls bb k.
    k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = PHI ==>
    EL k (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions =
    (EL k bb.bb_instructions) with inst_operands :=
      update_phi_ops old_lbl new_lbl var_repls
        (EL k bb.bb_instructions).inst_operands
Proof
  rw[update_phis_for_split_def, listTheory.EL_MAP] >>
  simp[instruction_component_equality]
QED

(* ================================================================
   Section 2: Build split block properties
   ================================================================ *)

(* The split block label is split_block_name *)
Theorem build_split_block_label:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    split_bb.bb_label = split_block_name pred_bb.bb_label target_bb.bb_label
Proof
  rw[build_split_block_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

(* build_forwarding_assigns: the var_repls map original vars to fwd vars *)
Theorem build_forwarding_assigns_repls:
  !split_label id_base vars repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    MAP FST repls = vars /\
    (!v new_v. ALOOKUP repls v = SOME new_v ==>
               new_v = STRCAT (STRCAT split_label "_fwd_") v)
Proof
  Induct_on `vars` >> simp[build_forwarding_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rw[] >> gvs[]
QED

(* build_forwarding_assigns: the instructions are ASSIGN *)
Theorem build_forwarding_assigns_insts:
  !split_label id_base vars repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    LENGTH insts = LENGTH vars /\
    (!k. k < LENGTH vars ==>
         (EL k insts).inst_opcode = ASSIGN /\
         (EL k insts).inst_operands = [Var (EL k vars)] /\
         (EL k insts).inst_outputs =
           [STRCAT (STRCAT split_label "_fwd_") (EL k vars)])
Proof
  Induct_on `vars` >> simp[build_forwarding_assigns_def] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `k` >> gvs[]
QED

(* ================================================================
   Section 3: Lookup in insert_split
   ================================================================ *)

(* Helper: replace_block twice preserves labels *)
Theorem insert_split_labels_eq[local]:
  !func pred_bb target_bb split_bb var_repls.
    MAP (\bb. bb.bb_label)
      (replace_block target_bb.bb_label
         (update_phis_for_split pred_bb.bb_label split_bb.bb_label
            var_repls target_bb)
         (replace_block pred_bb.bb_label
            (subst_label_terminator target_bb.bb_label split_bb.bb_label
               pred_bb) func.fn_blocks)) =
    MAP (\bb. bb.bb_label) func.fn_blocks
Proof
  rpt gen_tac >>
  `MAP (\bb. bb.bb_label)
     (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label
           pred_bb) func.fn_blocks) =
   MAP (\bb. bb.bb_label) func.fn_blocks` by (
    irule fn_labels_replace_block >>
    simp[subst_label_terminator_bb_label]) >>
  `MAP (\bb. bb.bb_label)
     (replace_block target_bb.bb_label
        (update_phis_for_split pred_bb.bb_label split_bb.bb_label
           var_repls target_bb)
        (replace_block pred_bb.bb_label
           (subst_label_terminator target_bb.bb_label split_bb.bb_label
              pred_bb) func.fn_blocks)) =
   MAP (\bb. bb.bb_label)
     (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label
           pred_bb) func.fn_blocks)` by (
    irule fn_labels_replace_block >>
    simp[update_phis_for_split_bb_label]) >>
  gvs[]
QED

(* fn_labels of insert_split *)
Theorem fn_labels_insert_split:
  !func pred_bb target_bb id_base.
    let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base in
    fn_labels (insert_split func pred_bb target_bb id_base) =
    fn_labels func ++ [split_bb.bb_label]
Proof
  rw[insert_split_def, fn_labels_def] >>
  pairarg_tac >> gvs[] >>
  simp[listTheory.MAP_APPEND] >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `split_bb`, `var_repls`]
            insert_split_labels_eq) >>
  simp[]
QED

(* Helper: lookup_block over appended lists *)
Theorem lookup_block_APPEND:
  !lbl bbs1 bbs2.
    lookup_block lbl (bbs1 ++ bbs2) =
    case lookup_block lbl bbs1 of
      SOME bb => SOME bb
    | NONE => lookup_block lbl bbs2
Proof
  Induct_on `bbs1` >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[] >>
  gvs[GSYM lookup_block_def]
QED

(* Helper: lookup_block NONE means label not in labels *)
Theorem lookup_block_NONE:
  !lbl bbs.
    lookup_block lbl bbs = NONE <=> ~MEM lbl (MAP (\bb. bb.bb_label) bbs)
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> gvs[GSYM lookup_block_def] >>
  eq_tac >> rw[]
QED

(* The core block list after two replace_blocks *)
Definition insert_split_blocks_def:
  insert_split_blocks func pred_bb target_bb split_bb var_repls =
    replace_block target_bb.bb_label
      (update_phis_for_split pred_bb.bb_label split_bb.bb_label
         var_repls target_bb)
      (replace_block pred_bb.bb_label
         (subst_label_terminator target_bb.bb_label split_bb.bb_label
            pred_bb) func.fn_blocks)
End

(* lookup in the core blocks = lookup in original for non-pred non-target *)
Theorem lookup_insert_split_blocks_other[local]:
  !func pred_bb target_bb split_bb var_repls lbl.
    lbl <> pred_bb.bb_label /\ lbl <> target_bb.bb_label ==>
    lookup_block lbl (insert_split_blocks func pred_bb target_bb split_bb var_repls) =
    lookup_block lbl func.fn_blocks
Proof
  rw[insert_split_blocks_def] >>
  `lookup_block lbl
     (replace_block target_bb.bb_label
        (update_phis_for_split pred_bb.bb_label split_bb.bb_label
           var_repls target_bb)
        (replace_block pred_bb.bb_label
           (subst_label_terminator target_bb.bb_label split_bb.bb_label
              pred_bb) func.fn_blocks)) =
   lookup_block lbl
     (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label
           pred_bb) func.fn_blocks)` by (
    irule lookup_block_replace_neq >>
    simp[update_phis_for_split_bb_label]) >>
  simp[] >>
  irule lookup_block_replace_neq >>
  simp[subst_label_terminator_bb_label]
QED

(* lookup in the core blocks for pred_bb *)
Theorem lookup_insert_split_blocks_pred[local]:
  !func pred_bb target_bb split_bb var_repls.
    pred_bb.bb_label <> target_bb.bb_label /\
    (?bb. lookup_block pred_bb.bb_label func.fn_blocks = SOME bb) ==>
    lookup_block pred_bb.bb_label
      (insert_split_blocks func pred_bb target_bb split_bb var_repls) =
    SOME (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)
Proof
  rw[insert_split_blocks_def] >>
  `lookup_block pred_bb.bb_label
     (replace_block target_bb.bb_label
        (update_phis_for_split pred_bb.bb_label split_bb.bb_label
           var_repls target_bb)
        (replace_block pred_bb.bb_label
           (subst_label_terminator target_bb.bb_label split_bb.bb_label
              pred_bb) func.fn_blocks)) =
   lookup_block pred_bb.bb_label
     (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label
           pred_bb) func.fn_blocks)` by (
    irule lookup_block_replace_neq >>
    simp[update_phis_for_split_bb_label]) >>
  simp[] >>
  irule lookup_block_replace_eq >>
  simp[subst_label_terminator_bb_label]
QED

(* lookup in the core blocks for target_bb *)
Theorem lookup_insert_split_blocks_target[local]:
  !func pred_bb target_bb split_bb var_repls.
    pred_bb.bb_label <> target_bb.bb_label /\
    (?bb. lookup_block target_bb.bb_label func.fn_blocks = SOME bb) ==>
    lookup_block target_bb.bb_label
      (insert_split_blocks func pred_bb target_bb split_bb var_repls) =
    SOME (update_phis_for_split pred_bb.bb_label split_bb.bb_label
            var_repls target_bb)
Proof
  rw[insert_split_blocks_def] >>
  irule lookup_block_replace_eq >>
  simp[update_phis_for_split_bb_label] >>
  `lookup_block target_bb.bb_label
     (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label
           pred_bb) func.fn_blocks) =
   lookup_block target_bb.bb_label func.fn_blocks` by (
    irule lookup_block_replace_neq >>
    simp[subst_label_terminator_bb_label]) >>
  simp[]
QED

(* Now the insert_split lookup lemmas use the above *)

(* lookup in insert_split for other blocks *)
Theorem lookup_block_insert_split_other:
  !func pred_bb target_bb id_base lbl.
    let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base in
    lbl <> pred_bb.bb_label /\ lbl <> target_bb.bb_label /\
    lbl <> split_bb.bb_label ==>
    lookup_block lbl (insert_split func pred_bb target_bb id_base).fn_blocks =
    lookup_block lbl func.fn_blocks
Proof
  rw[insert_split_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  simp[lookup_block_APPEND, insert_split_blocks_def] >>
  `lookup_block lbl
     (replace_block target_bb.bb_label
        (update_phis_for_split pred_bb.bb_label split_bb.bb_label
           var_repls target_bb)
        (replace_block pred_bb.bb_label
           (subst_label_terminator target_bb.bb_label split_bb.bb_label
              pred_bb) func.fn_blocks)) =
   lookup_block lbl func.fn_blocks` by (
    `lookup_block lbl
       (replace_block target_bb.bb_label
          (update_phis_for_split pred_bb.bb_label split_bb.bb_label
             var_repls target_bb)
          (replace_block pred_bb.bb_label
             (subst_label_terminator target_bb.bb_label split_bb.bb_label
                pred_bb) func.fn_blocks)) =
     lookup_block lbl
       (replace_block pred_bb.bb_label
          (subst_label_terminator target_bb.bb_label split_bb.bb_label
             pred_bb) func.fn_blocks)` by (
      irule lookup_block_replace_neq >>
      simp[update_phis_for_split_bb_label]) >>
    simp[] >>
    irule lookup_block_replace_neq >>
    simp[subst_label_terminator_bb_label]) >>
  simp[] >>
  Cases_on `lookup_block lbl func.fn_blocks` >>
  simp[lookup_block_def, listTheory.FIND_thm]
QED

(* lookup in insert_split for pred_bb *)
Theorem lookup_block_insert_split_pred:
  !func pred_bb target_bb id_base.
    let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base in
    pred_bb.bb_label <> target_bb.bb_label /\
    (?bb. lookup_block pred_bb.bb_label func.fn_blocks = SOME bb) ==>
    lookup_block pred_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
    SOME (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)
Proof
  rw[insert_split_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  simp[lookup_block_APPEND, insert_split_blocks_def] >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `split_bb`, `var_repls`]
            lookup_insert_split_blocks_pred) >>
  simp[insert_split_blocks_def]
QED

(* lookup in insert_split for target_bb *)
Theorem lookup_block_insert_split_target:
  !func pred_bb target_bb id_base.
    let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base in
    pred_bb.bb_label <> target_bb.bb_label /\
    (?bb. lookup_block target_bb.bb_label func.fn_blocks = SOME bb) ==>
    lookup_block target_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
    SOME (update_phis_for_split pred_bb.bb_label split_bb.bb_label
            var_repls target_bb)
Proof
  rw[insert_split_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  simp[lookup_block_APPEND, insert_split_blocks_def] >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `split_bb`, `var_repls`]
            lookup_insert_split_blocks_target) >>
  simp[insert_split_blocks_def]
QED

(* lookup in insert_split for the new split block *)
Theorem lookup_block_insert_split_new:
  !func pred_bb target_bb id_base.
    let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base in
    ~MEM split_bb.bb_label (fn_labels func) ==>
    lookup_block split_bb.bb_label
      (insert_split func pred_bb target_bb id_base).fn_blocks =
    SOME split_bb
Proof
  rw[insert_split_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  simp[lookup_block_APPEND, insert_split_blocks_def] >>
  `lookup_block split_bb.bb_label
     (replace_block target_bb.bb_label
        (update_phis_for_split pred_bb.bb_label split_bb.bb_label var_repls
           target_bb)
        (replace_block pred_bb.bb_label
           (subst_label_terminator target_bb.bb_label split_bb.bb_label
              pred_bb) func.fn_blocks)) = NONE` by (
    simp[lookup_block_NONE] >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `split_bb`, `var_repls`]
              insert_split_labels_eq) >>
    gvs[fn_labels_def, insert_split_blocks_def]) >>
  simp[lookup_block_def, listTheory.FIND_thm]
QED

(* ================================================================
   Section 4: PHI resolution equivalence
   ================================================================ *)

(* update_phi_ops preserves resolve_phi for non-old_label predecessors *)
Theorem resolve_phi_update_phi_ops_other:
  !prev ops old_label new_label var_repls.
    prev <> old_label /\ prev <> new_label ==>
    resolve_phi prev (update_phi_ops old_label new_label var_repls ops) =
    resolve_phi prev ops
Proof
  rpt gen_tac >> strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`ops`, `var_repls`, `new_label`, `old_label`] >>
  ho_match_mp_tac update_phi_ops_ind >>
  simp[update_phi_ops_def, resolve_phi_def] >>
  rw[] >> simp[resolve_phi_def]
QED

(* update_phi_ops: resolve_phi with new_label finds the updated value,
   provided new_label is fresh (does not appear as a label key in ops) *)
Theorem resolve_phi_update_phi_ops_match:
  !old_label new_label var_repls ops val_op.
    resolve_phi old_label ops = SOME val_op /\
    resolve_phi new_label ops = NONE ==>
    resolve_phi new_label
      (update_phi_ops old_label new_label var_repls ops) =
    SOME (case val_op of
            Var v => (case ALOOKUP var_repls v of
                        NONE => Var v
                      | SOME new_v => Var new_v)
          | x => x)
Proof
  recInduct update_phi_ops_ind >>
  simp[update_phi_ops_def, resolve_phi_def] >>
  rw[] >> gvs[resolve_phi_def]
QED

(* ================================================================
   Section 5: result_equiv UNIV helpers
   ================================================================ *)

Theorem result_equiv_UNIV_refl:
  !r. result_equiv UNIV r r
Proof
  Cases >> simp[result_equiv_def, execution_equiv_def,
                state_equiv_def, lookup_var_def]
QED

Theorem result_equiv_UNIV_trans:
  !r1 r2 r3. result_equiv UNIV r1 r2 /\ result_equiv UNIV r2 r3 ==>
              result_equiv UNIV r1 r3
Proof
  metis_tac[stateEquivProofsTheory.result_equiv_trans]
QED
