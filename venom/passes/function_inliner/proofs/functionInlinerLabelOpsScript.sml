(*
 * Function Inliner — label_ops_closed preservation
 *
 * label_ops_closed says every Label operand in every instruction
 * refers to a label that exists as a block label in the function.
 * This file proves it is preserved through inline_one_site
 * (inline_call_site, fix_inline_phis, renumber_fn_inst_ids).
 *)

Theory functionInlinerLabelOps
Ancestors
  functionInlinerDefs functionInlinerFresh functionInlinerRenumber
  functionInlinerInline
  venomInst cfgTransform venomWf

open stringTheory listTheory rich_listTheory pairTheory indexedListsTheory

open functionInlinerDefsTheory functionInlinerFreshTheory
     functionInlinerRenumberTheory functionInlinerInlineTheory
     venomInstTheory cfgTransformTheory venomWfTheory

(* ================================================================
   Definition
   ================================================================ *)

Definition label_ops_closed_def:
  label_ops_closed fn <=>
    !bb inst lbl.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      MEM (Label lbl) inst.inst_operands ==>
      MEM lbl (fn_labels fn)
End

(* ================================================================
   Basic helpers
   ================================================================ *)

Triviality FIND_MEM_local:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Triviality FIND_SOME_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Triviality lookup_block_label:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >> imp_res_tac FIND_SOME_P >> fs[]
QED

Triviality lookup_block_mem:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  rw[lookup_block_def] >> imp_res_tac FIND_MEM_local
QED

Triviality MEM_replace_block:
  !bb lbl bb' bbs.
    MEM bb (replace_block lbl bb' bbs) ==>
    bb = bb' \/ (MEM bb bbs /\ bb.bb_label <> lbl)
Proof
  rw[replace_block_def, MEM_MAP] >>
  Cases_on `y.bb_label = lbl` >> gvs[] >> metis_tac[]
QED

(* MEM in replace_block: either the replacement or an original *)
Triviality MEM_replace_block_label:
  !lbl bb' bbs l.
    bb'.bb_label = lbl /\
    MEM l (MAP (\b. b.bb_label) bbs) ==>
    MEM l (MAP (\b. b.bb_label) (replace_block lbl bb' bbs))
Proof
  Induct_on `bbs` >>
  rw[replace_block_def] >>
  fs[] >> rw[] >> fs[] >>
  DISJ2_TAC >> simp[GSYM replace_block_def]
QED

(* If lbl is in fn_labels of original, it's in fn_labels of replace_block result *)
Triviality fn_labels_caller_in_result:
  !lbl caller bb_lbl bb' ret_lbl more_blocks di.
    MEM lbl (fn_labels caller) /\
    bb'.bb_label = bb_lbl ==>
    MEM lbl (fn_labels (caller with fn_blocks :=
               replace_block bb_lbl bb' caller.fn_blocks ++
               [<|bb_label := ret_lbl; bb_instructions := di|>] ++
               more_blocks))
Proof
  rw[fn_labels_def, MAP_APPEND, MEM_APPEND] >>
  DISJ1_TAC >> DISJ1_TAC >>
  irule MEM_replace_block_label >> simp[]
QED

Triviality MEM_replace_block_original:
  !bb lbl bb' bbs.
    MEM bb bbs /\ bb.bb_label <> lbl ==>
    MEM bb (replace_block lbl bb' bbs)
Proof
  rw[replace_block_def, MEM_MAP] >>
  qexists_tac `bb` >> simp[]
QED

(* ================================================================
   renumber preserves label_ops_closed
   ================================================================ *)

Theorem renumber_label_ops_closed:
  !fn. label_ops_closed fn ==> label_ops_closed (renumber_fn_inst_ids fn)
Proof
  rw[label_ops_closed_def, renumber_fn_inst_ids_fn_labels] >>
  rpt strip_tac >>
  first_x_assum irule >>
  (* inst's projection appears in FLAT of original blocks *)
  `MEM (inst.inst_opcode, inst.inst_operands, inst.inst_outputs)
       (MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
            (FLAT (MAP (\bb. bb.bb_instructions)
                       (renumber_fn_inst_ids fn).fn_blocks)))` by (
    simp[MEM_MAP, MEM_FLAT, PULL_EXISTS] >> metis_tac[]) >>
  `MEM (inst.inst_opcode, inst.inst_operands, inst.inst_outputs)
       (MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
            (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)))` by
    metis_tac[renumber_fn_inst_ids_inst_proj] >>
  fs[MEM_MAP, MEM_FLAT, PULL_EXISTS] >>
  metis_tac[]
QED

(* ================================================================
   fix_inline_phis preserves label_ops_closed
   ================================================================ *)

(* subst_label_op maps valid labels to valid labels *)
Triviality subst_label_op_mem_labels:
  !ops old new lbl lbls.
    MEM (Label lbl) (MAP (subst_label_op old new) ops) /\
    (!lbl. MEM (Label lbl) ops ==> MEM lbl lbls) /\
    MEM new lbls ==>
    MEM lbl lbls
Proof
  Induct >> rw[subst_label_op_def] >>
  Cases_on `h` >> gvs[subst_label_op_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >> metis_tac[]
QED

(* Key helper: MEM in a conditional MAP preserves or substitutes label ops *)
Triviality mem_map_cond_label:
  !insts orig_lbl new_lbl inst lbl lbls.
    MEM inst (MAP (\i. if i.inst_opcode <> PHI then i
                       else subst_label_inst orig_lbl new_lbl i) insts) /\
    MEM (Label lbl) inst.inst_operands /\
    (!i lbl. MEM i insts /\ MEM (Label lbl) i.inst_operands ==> MEM lbl lbls) /\
    MEM new_lbl lbls ==>
    MEM lbl lbls
Proof
  Induct >> simp[] >> rpt gen_tac >>
  DISCH_THEN (fn th => map_every ASSUME_TAC (CONJUNCTS th)) >>
  fs[MEM_MAP] >> gvs[]
  >- (
    qpat_x_assum `MEM (Label _) (if _ then _ else _).inst_operands` mp_tac >>
    IF_CASES_TAC >> simp[subst_label_inst_def] >>
    strip_tac >> metis_tac[subst_label_op_mem_labels])
  >- (
    qpat_x_assum `MEM (Label _) (if _ then _ else _).inst_operands` mp_tac >>
    IF_CASES_TAC >> simp[subst_label_inst_def] >>
    strip_tac >> metis_tac[subst_label_op_mem_labels])
QED

Theorem fix_inline_phis_label_ops_closed:
  !orig_lbl new_lbl ret_bb fn.
    label_ops_closed fn /\
    MEM new_lbl (fn_labels fn) ==>
    label_ops_closed (fix_inline_phis orig_lbl new_lbl ret_bb fn)
Proof
  rw[label_ops_closed_def, fix_inline_phis_def, LET_THM,
     fn_labels_fix_inline_phis, MEM_MAP] >>
  rpt strip_tac >>
  rename1 `MEM bb0 fn.fn_blocks` >>
  Cases_on `MEM bb0.bb_label (bb_succs ret_bb)` >> fs[]
  >- (irule mem_map_cond_label >> metis_tac[])
  >- metis_tac[]
QED

(* ================================================================
   inline_call_site preserves label_ops_closed
   ================================================================ *)

(* clone_operand maps callee labels to prefixed labels *)
Triviality clone_operand_label:
  !prefix labels op lbl.
    clone_operand prefix labels op = Label lbl ==>
    (?l. op = Label l /\ MEM l labels /\ lbl = STRCAT prefix l) \/
    (?l. op = Label l /\ ~MEM l labels /\ lbl = l)
Proof
  Cases_on `op` >> rw[clone_operand_def] >>
  Cases_on `MEM s labels` >> fs[]
QED

(* clone_instruction: all Label operands either get prefixed or kept *)
Triviality clone_instruction_label_mem:
  !prefix labels inst lbl.
    MEM (Label lbl) (clone_instruction prefix labels inst).inst_operands ==>
    (?l. MEM (Label l) inst.inst_operands /\ MEM l labels /\
         lbl = STRCAT prefix l) \/
    (?l. MEM (Label l) inst.inst_operands /\ ~MEM l labels /\ lbl = l)
Proof
  rw[clone_instruction_def, MEM_MAP] >>
  (SUBGOAL_THEN ``clone_operand prefix labels y = Label lbl``
     ASSUME_TAC >- simp[]) >>
  imp_res_tac clone_operand_label >> metis_tac[]
QED

(* rewrite_inline_inst: Label operands come from original inst or return_label *)
Triviality rewrite_inline_inst_label_ops:
  !invoke_ops invoke_outs return_label inst param_idx result pi'.
    rewrite_inline_inst invoke_ops invoke_outs return_label inst param_idx =
      (result, pi') ==>
    !inst' lbl.
      MEM inst' result /\
      MEM (Label lbl) inst'.inst_operands ==>
      MEM (Label lbl) inst.inst_operands \/ lbl = return_label
Proof
  rw[rewrite_inline_inst_def, LET_THM] >>
  Cases_on `inst.inst_opcode = PARAM` >> fs[] >>
  Cases_on `inst.inst_opcode = RET` >> fs[] >> gvs[]
  (* After case splits, most goals have inst' = ... with concrete operands *)
  >> TRY (Cases_on `param_idx < LENGTH invoke_ops` >> fs[] >> gvs[])
  >> TRY (Cases_on `is_label_op (EL param_idx invoke_ops)` >> fs[]
          >> gvs[] >> Cases_on `EL param_idx invoke_ops` >> fs[is_label_op_def])
  >> TRY (gvs[MEM_APPEND, MEM_MAPi, MEM_EL] >> metis_tac[MEM_EL])
QED

(* rewrite_inline_insts: Label operands come from original insts or return_label *)
Triviality rewrite_inline_insts_label_ops:
  !invoke_ops invoke_outs return_label insts param_idx result pi'.
    rewrite_inline_insts invoke_ops invoke_outs return_label insts param_idx =
      (result, pi') ==>
    !inst' lbl.
      MEM inst' result /\
      MEM (Label lbl) inst'.inst_operands ==>
      (?inst. MEM inst insts /\ MEM (Label lbl) inst.inst_operands) \/
      lbl = return_label
Proof
  Induct_on `insts` >> rw[rewrite_inline_insts_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  fs[MEM_APPEND] >>
  drule rewrite_inline_inst_label_ops >> strip_tac
  >- (
    first_x_assum (qspecl_then [`inst'`, `lbl`] mp_tac) >> rw[] >>
    metis_tac[])
  >- (
    first_x_assum drule >> strip_tac >>
    first_x_assum (qspecl_then [`inst'`, `lbl`] mp_tac) >> rw[] >>
    metis_tac[])
QED

(* Blocks from rewrite_inline_blocks have labels from callee or return_label *)
Triviality rewrite_inline_blocks_label_ops:
  !invoke_ops invoke_outs return_label bbs param_idx result pi'.
    rewrite_inline_blocks invoke_ops invoke_outs return_label bbs param_idx =
      (result, pi') ==>
    !bb inst lbl.
      MEM bb result /\
      MEM inst bb.bb_instructions /\
      MEM (Label lbl) inst.inst_operands ==>
      (?bb0 inst0. MEM bb0 bbs /\ MEM inst0 bb0.bb_instructions /\
                   MEM (Label lbl) inst0.inst_operands) \/
      lbl = return_label
Proof
  Induct_on `bbs` >> rw[rewrite_inline_blocks_def, LET_THM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  fs[rewrite_inline_block_def, LET_THM] >>
  pairarg_tac >> gvs[]
  >- (
    drule rewrite_inline_insts_label_ops >> strip_tac >>
    first_x_assum (qspecl_then [`inst`, `lbl`] mp_tac) >> rw[] >>
    metis_tac[])
  >- (
    first_x_assum drule >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`, `lbl`] mp_tac) >> rw[] >>
    metis_tac[])
QED

(* clone_function + rewrite_inline_blocks: labels from label_ops_closed callee
   become MAP (STRCAT prefix) (fn_labels callee) or return_label *)
Triviality rewritten_clone_labels:
  !prefix invoke_ops invoke_outs return_label callee bb inst lbl
   rewritten_blocks pi'.
    label_ops_closed callee /\
    rewrite_inline_blocks invoke_ops invoke_outs return_label
      (clone_function prefix callee).fn_blocks 0 = (rewritten_blocks, pi') /\
    MEM bb rewritten_blocks /\
    MEM inst bb.bb_instructions /\
    MEM (Label lbl) inst.inst_operands ==>
    MEM lbl (MAP (STRCAT prefix) (fn_labels callee)) \/ lbl = return_label
Proof
  rw[] >>
  drule rewrite_inline_blocks_label_ops >> strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `lbl`] mp_tac) >> rw[] >>
  gvs[clone_function_def, LET_THM, MEM_MAP, clone_basic_block_def] >>
  (* Have: Label lbl = clone_operand prefix (fn_labels callee) y'' *)
  (SUBGOAL_THEN ``clone_operand prefix (fn_labels callee) y'' = Label lbl``
     ASSUME_TAC >- simp[]) >>
  imp_res_tac clone_operand_label
  >- metis_tac[]
  >- (fs[label_ops_closed_def] >> metis_tac[])
QED

(* Case 1 helper: inst from a block in replace_block *)
Triviality label_ops_case_replace_block:
  !caller callee prefix call_bb idx inst lbl bb
   rewritten_blocks _0' ret_lbl result_fn.
    label_ops_closed caller /\ label_ops_closed callee /\
    fn_has_entry callee /\
    lookup_block call_bb.bb_label caller.fn_blocks = SOME call_bb /\
    idx < LENGTH call_bb.bb_instructions /\
    rewrite_inline_blocks
      (rotate_invoke_ops call_bb.bb_instructions❲idx❳.inst_operands)
      call_bb.bb_instructions❲idx❳.inst_outputs ret_lbl
      (clone_function prefix callee).fn_blocks 0 =
      (rewritten_blocks, _0') /\
    (!l. MEM l (fn_labels caller) ==> MEM l (fn_labels result_fn)) /\
    (!l. MEM l (MAP (\b. b.bb_label) rewritten_blocks) ==>
         MEM l (fn_labels result_fn)) /\
    MEM bb (replace_block call_bb.bb_label
        (call_bb with bb_instructions :=
           TAKE idx call_bb.bb_instructions ++
           [<|inst_id := 0; inst_opcode := JMP;
              inst_operands :=
                [Label (case (clone_function prefix callee).fn_blocks of
                          [] => "" | eb::v1 => eb.bb_label)];
              inst_outputs := []|>])
        caller.fn_blocks) /\
    MEM inst bb.bb_instructions /\
    MEM (Label lbl) inst.inst_operands ==>
    MEM lbl (fn_labels result_fn)
Proof
  rpt strip_tac >>
  drule MEM_replace_block >> strip_tac >> gvs[]
  >- ( (* Goal 1: TAKE — inst from original block *)
    qpat_x_assum `!l. MEM l (fn_labels caller) ==> _` irule >>
    fs[label_ops_closed_def] >>
    imp_res_tac lookup_block_mem >> imp_res_tac MEM_TAKE >> metis_tac[])
  >- ( (* Goal 2: JMP — clone entry label *)
    qpat_x_assum `!l. MEM l (MAP _ rewritten_blocks) ==> _` irule >>
    imp_res_tac rewrite_inline_blocks_labels >>
    Cases_on `(clone_function prefix callee).fn_blocks` >>
    gvs[fn_has_entry_def, clone_function_def, LET_THM] >>
    simp[MEM_MAP] >> qexists_tac `h` >> simp[])
  >- ( (* Goal 3: original unmodified block *)
    qpat_x_assum `!l. MEM l (fn_labels caller) ==> _` irule >>
    fs[label_ops_closed_def] >> metis_tac[])
QED

(* Main theorem: inline_call_site preserves label_ops_closed *)
Theorem inline_call_site_label_ops_closed:
  !prefix ret_lbl caller callee bb_lbl idx.
    label_ops_closed caller /\
    label_ops_closed callee /\
    fn_has_entry callee /\
    lookup_block bb_lbl caller.fn_blocks <> NONE /\
    idx < LENGTH (THE (lookup_block bb_lbl caller.fn_blocks)).bb_instructions ==>
    label_ops_closed (inline_call_site prefix ret_lbl caller callee bb_lbl idx)
Proof
  simp[inline_call_site_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block bb_lbl caller.fn_blocks` >> gvs[] >>
  rename1 `SOME call_bb` >> pairarg_tac >> gvs[] >>
  imp_res_tac lookup_block_label >>
  simp[label_ops_closed_def] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `fn_labels (caller with fn_blocks := result_blocks)` >>
  (* Key structural facts about result_blocks *)
  (SUBGOAL_THEN ``!l. MEM l (fn_labels caller) ==>
       MEM l (fn_labels (caller with fn_blocks := result_blocks))``
    ASSUME_TAC >- (
    rw[] >> qunabbrev_tac `result_blocks` >>
    irule fn_labels_caller_in_result >> simp[])) >>
  (SUBGOAL_THEN ``!l. MEM l (MAP (\b. b.bb_label) rewritten_blocks) ==>
       MEM l (fn_labels (caller with fn_blocks := result_blocks))``
    ASSUME_TAC >- (
    rw[] >> simp[Abbr `result_blocks`, fn_labels_def, MAP_APPEND,
                 MEM_APPEND, MEM_MAP])) >>
  (SUBGOAL_THEN ``MEM ret_lbl (fn_labels (caller with fn_blocks := result_blocks))``
    ASSUME_TAC >- (
    simp[Abbr `result_blocks`, fn_labels_def, MAP_APPEND,
         MEM_APPEND, MEM_MAP])) >>
  (* Now dispatch by block membership *)
  fs[MEM_APPEND] >> gvs[]
  (* Case 1: MEM bb (replace_block ...) *)
  >- (irule label_ops_case_replace_block >> metis_tac[])
  (* Case 2: return block (DROP of original instructions) *)
  >- (
    qpat_x_assum `!l. MEM l (fn_labels caller) ==> _` irule >>
    fs[label_ops_closed_def] >>
    imp_res_tac lookup_block_mem >> imp_res_tac MEM_DROP_IMP >>
    metis_tac[])
  (* Case 3: rewritten clone blocks *)
  >- (
    drule_all rewritten_clone_labels >> strip_tac >> gvs[] >>
    (* gvs[] solves lbl=ret_lbl case; remaining: prefixed label *)
    (* First establish MEM lbl (MAP bb_label rewritten_blocks) *)
    (SUBGOAL_THEN ``MEM lbl (MAP (\b. b.bb_label) rewritten_blocks)``
      ASSUME_TAC >- (
      imp_res_tac rewrite_inline_blocks_labels >>
      fs[clone_function_def, LET_THM, MAP_MAP_o,
         combinTheory.o_DEF, clone_basic_block_def, fn_labels_def])) >>
    qpat_x_assum `!l. MEM l (MAP _ rewritten_blocks) ==> _` irule >>
    fs[MEM_MAP] >> metis_tac[])
QED

(* find_invoke_site guarantees the block exists (no ALL_DISTINCT needed) *)
Triviality find_invoke_site_lookup:
  !name bbs lbl idx.
    find_invoke_site name bbs = SOME (lbl, idx) ==>
    ?bb. lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[find_invoke_site_def, lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  Cases_on `find_invoke_idx name h.bb_instructions 0` >> gvs[] >>
  Cases_on `h.bb_label = lbl` >> gvs[] >>
  first_x_assum drule >> simp[lookup_block_def, FIND_thm]
QED

(* ================================================================
   Composition: inline_one_site preserves label_ops_closed
   ================================================================ *)

Theorem inline_one_site_label_ops_closed:
  !caller callee ist caller' ist'.
    inline_one_site caller callee ist = SOME (caller', ist') /\
    label_ops_closed caller /\
    label_ops_closed callee /\
    fn_has_entry callee /\
    ALL_DISTINCT (fn_labels caller) /\
    ALL_DISTINCT (fn_labels callee) /\
    labels_no_inline_return callee /\
    labels_fresh_above ist.is_inline_count caller ==>
    label_ops_closed caller'
Proof
  rw[inline_one_site_def] >>
  Cases_on `find_invoke_site callee.fn_name caller.fn_blocks` >> gvs[] >>
  rename1 `SOME site` >> Cases_on `site` >> gvs[LET_THM] >>
  rename1 `find_invoke_site _ _ = SOME (bb_lbl, idx)` >>
  imp_res_tac find_invoke_site_lookup >>
  Cases_on `lookup_block bb_lbl caller.fn_blocks` >> gvs[] >>
  rename1 `lookup_block _ _ = SOME call_bb` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) caller.fn_blocks)` by
    fs[fn_labels_def] >>
  `idx < LENGTH call_bb.bb_instructions` by
    metis_tac[find_invoke_site_idx_bound] >>
  qabbrev_tac `pfx = inline_prefix ist.is_inline_count` >>
  qabbrev_tac `rl = return_block_label pfx ist.is_label_counter` >>
  qabbrev_tac `c1 = inline_call_site pfx rl caller callee bb_lbl idx` >>
  (* Step 1: inline_call_site preserves label_ops_closed *)
  `label_ops_closed c1` by (
    qunabbrev_tac `c1` >>
    irule inline_call_site_label_ops_closed >>
    simp[]) >>
  (* Step 2: fix_inline_phis preserves label_ops_closed *)
  Cases_on `lookup_block rl c1.fn_blocks` >> gvs[]
  >- (
    (* No fix_phis case *)
    irule renumber_label_ops_closed >> simp[])
  >- (
    (* fix_phis case *)
    irule renumber_label_ops_closed >>
    irule fix_inline_phis_label_ops_closed >>
    conj_tac >- simp[] >>
    (* Need: MEM rl (fn_labels c1) *)
    `MEM rl (fn_labels c1)` by (
      qunabbrev_tac `c1` >>
      qpat_x_assum `lookup_block bb_lbl _ = SOME call_bb`
        (fn th => ASSUME_TAC (MATCH_MP inline_call_site_fn_labels th)) >>
      simp[MEM_APPEND]) >>
    simp[])
QED

val _ = export_theory();
