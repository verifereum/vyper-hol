(* Strict-dominance + within-block iszero machinery for phase 3.
 *
 * Loop-robust invariants for the iszero-resolution simulation:
 *   strict_dom_iszero_inv  — ISZERO defs in strict dominators are consistent
 *   (within_block_iszero_inv lives in aoIsZeroInv)
 *
 * All lemmas here are ported verbatim from the (deleted) monolith proof;
 * they are SSA/dominance facts independent of the transform itself.
 *)
Theory aoStrictDomObligation
Ancestors
  algebraicOptDefs aoIsZeroInv
  venomWf venomState venomInst venomExecSemantics
  venomInstProps venomExecProps venomExecProofs
  stateEquiv dfgAnalysisProps passSimulationProps dfgSoundStep
Libs
  pairLib BasicProvers

(* ===== SSA / membership helpers ===== *)
(* all_distinct_flat_map_unique and mem_fn_insts_blocks shared from
   passSimulationProps *)

Theorem mem_block_mem_fn_insts:
  !fn bb inst.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  simp[fn_insts_def] >> metis_tac[mem_fn_insts_blocks]
QED

(* Two function instructions sharing an inst_id live in the same block. *)
Theorem mem_two_blocks_eq:
  !fn bb1 bb2 inst.
    wf_function fn /\ MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    MEM inst bb1.bb_instructions /\ MEM inst bb2.bb_instructions ==>
    bb1 = bb2
Proof
  rpt strip_tac >>
  qspecl_then [`fn.fn_blocks`,
               `\b. MAP (\i. i.inst_id) b.bb_instructions`,
               `bb1`, `bb2`, `inst.inst_id`] mp_tac all_distinct_flat_map_unique >>
  impl_tac
  >- (fs[wf_function_def, fn_inst_ids_distinct_def] >>
      simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  simp[]
QED

(* SSA: a variable is the output of at most one function instruction. *)
Theorem ssa_output_unique:
  !fn i1 i2 v.
    ssa_form fn /\ MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==>
    i1 = i2
Proof
  rpt strip_tac >>
  qspecl_then [`fn_insts fn`, `\i:instruction. i.inst_outputs`, `i1`, `i2`, `v`]
    mp_tac all_distinct_flat_map_unique >>
  impl_tac >- fs[ssa_form_def] >>
  simp[]
QED

(* ===== eval_phis preservation helpers ===== *)

(* lookup_var unchanged across a block's eval_phis for any variable that is
   not an output of any PHI in that block. *)
Theorem eval_phis_lookup_not_bb_phi:
  !bb s s' x.
    eval_phis s bb.bb_instructions = OK s' /\
    (!inst. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
            ~MEM x inst.inst_outputs) ==>
    lookup_var x s' = lookup_var x s
Proof
  rpt strip_tac >>
  `FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
    (irule eval_phis_flookup_not_phi_output >>
     first_assum (irule_at Any) >> metis_tac[]) >>
  fs[lookup_var_def]
QED

(* A variable whose DFG definition is not a PHI is not output by any PHI. *)
Theorem dfg_def_not_bb_phi:
  !fn0 bb x inst.
    ssa_form fn0 /\ MEM bb fn0.fn_blocks /\
    dfg_get_def (dfg_build_function fn0) x = SOME inst /\
    inst.inst_opcode <> PHI ==>
    !p. MEM p bb.bb_instructions /\ p.inst_opcode = PHI ==>
        ~MEM x p.inst_outputs
Proof
  rpt strip_tac >>
  `MEM x inst.inst_outputs /\ MEM inst (fn_insts fn0)` by
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
  `MEM p (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
  `inst = p` by metis_tac[ssa_output_unique] >>
  gvs[]
QED

(* An operand of an ISZERO living in a block other than bb is defined in that
   other block (block-local DFG), hence not output by any PHI in bb. *)
Theorem iszero_operand_not_bb_phi:
  !fn0 bb d_bb inst x w.
    wf_function fn0 /\ ssa_form fn0 /\ dfg_block_local fn0 /\
    MEM bb fn0.fn_blocks /\ MEM d_bb fn0.fn_blocks /\
    d_bb.bb_label <> bb.bb_label /\
    MEM inst d_bb.bb_instructions /\
    dfg_get_def (dfg_build_function fn0) x = SOME inst /\
    inst.inst_opcode = ISZERO /\ MEM (Var w) inst.inst_operands ==>
    !p. MEM p bb.bb_instructions /\ p.inst_opcode = PHI ==> ~MEM w p.inst_outputs
Proof
  rpt strip_tac >>
  `MEM p (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
  `?inst_u. dfg_get_def (dfg_build_function fn0) w = SOME inst_u` by
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_defs_complete] >>
  `dfg_tracked_opcode inst.inst_opcode` by
    asm_simp_tac (srw_ss()) [dfg_tracked_opcode_def] >>
  `MEM inst_u d_bb.bb_instructions` by
    (qpat_x_assum `dfg_block_local _`
       (assume_tac o REWRITE_RULE[dfg_block_local_def]) >>
     first_x_assum (qspecl_then [`x`, `inst`, `w`, `inst_u`] mp_tac) >>
     simp[] >> disch_then (qspec_then `d_bb` mp_tac) >> simp[]) >>
  `MEM w inst_u.inst_outputs /\ MEM inst_u (fn_insts fn0)` by
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
  `inst_u = p` by metis_tac[ssa_output_unique] >>
  `bb = d_bb` by metis_tac[mem_two_blocks_eq] >>
  gvs[]
QED

(* ===== strict_dom / wbiz / dominance machinery ===== *)
Definition strict_dom_iszero_inv_def:
  strict_dom_iszero_inv fn0 dfg s <=>
    !x inst op d_bb.
      dfg_get_def dfg x = SOME inst /\
      inst.inst_opcode = ISZERO /\ inst.inst_operands = [op] /\
      MEM d_bb fn0.fn_blocks /\ MEM inst d_bb.bb_instructions /\
      fn_dominates fn0 d_bb.bb_label s.vs_current_bb /\
      d_bb.bb_label <> s.vs_current_bb ==>
      !val_x val_op.
        lookup_var x s = SOME val_x /\
        eval_operand op s = SOME val_op ==>
        val_x = bool_to_word (val_op = 0w)
End
val _ = delsimps ["strict_dom_iszero_inv_def"]

Theorem strict_dom_iszero_inv_inst_idx:
  !fn0 dfg s n.
    strict_dom_iszero_inv fn0 dfg (s with vs_inst_idx := n) =
    strict_dom_iszero_inv fn0 dfg s
Proof
  rpt gen_tac >> simp[strict_dom_iszero_inv_def, lookup_var_def] >>
  `!op. eval_operand op (s with vs_inst_idx := n) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[]
QED

(* strict_dom_iszero_inv is preserved across a block's eval_phis: the ISZERO
   defs (and their operands) involved live in strict dominators, distinct from
   the block being entered, so eval_phis (which only writes this block's PHI
   outputs) leaves their values unchanged. *)
Theorem eval_phis_strict_dom_iszero_inv:
  !fn0 bb s s'.
    wf_function fn0 /\ wf_ssa fn0 /\ dfg_block_local fn0 /\
    MEM bb fn0.fn_blocks /\ s.vs_current_bb = bb.bb_label /\
    eval_phis s bb.bb_instructions = OK s' /\
    strict_dom_iszero_inv fn0 (dfg_build_function fn0) s ==>
    strict_dom_iszero_inv fn0 (dfg_build_function fn0) s'
Proof
  rpt strip_tac >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `s' = s with vs_vars := s'.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  `s'.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `s' = _` (fn th => simp[Once th])) >>
  qpat_x_assum `strict_dom_iszero_inv _ _ s`
    (assume_tac o REWRITE_RULE[strict_dom_iszero_inv_def]) >>
  simp[strict_dom_iszero_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `dfg_get_def _ x = SOME inst` >>
  `lookup_var x s' = lookup_var x s` by
    (`!p. MEM p bb.bb_instructions /\ p.inst_opcode = PHI ==>
          ~MEM x p.inst_outputs` by
       (qspecl_then [`fn0`, `bb`, `x`, `inst`] mp_tac dfg_def_not_bb_phi >>
        impl_tac >- gvs[] >> simp[]) >>
     metis_tac[eval_phis_lookup_not_bb_phi]) >>
  `eval_operand op s' = eval_operand op s` by
    (Cases_on `op` >> simp[eval_operand_def]
     >- ((* Var *) rename1 `Var w` >>
         `!p. MEM p bb.bb_instructions /\ p.inst_opcode = PHI ==>
              ~MEM w p.inst_outputs` by
           (qspecl_then [`fn0`, `bb`, `d_bb`, `inst`, `x`, `w`]
              mp_tac iszero_operand_not_bb_phi >>
            impl_tac >- gvs[] >> simp[]) >>
         metis_tac[eval_phis_lookup_not_bb_phi])
     >> ((* Label *) qpat_x_assum `s' = _` (fn th => simp[Once th]))) >>
  rpt strip_tac >>
  `lookup_var x s = SOME val_x /\ eval_operand op s = SOME val_op` by gvs[] >>
  metis_tac[]
QED

(* Initial: vacuously true at function entry (no strict dominators) *)
Theorem strict_dom_iszero_inv_initial:
  !fn0 dfg s.
    fn_entry_label fn0 = SOME s.vs_current_bb ==>
    strict_dom_iszero_inv fn0 dfg s
Proof
  rw[strict_dom_iszero_inv_def] >> rpt strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >> DISJ2_TAC >>
  qexists_tac `[s.vs_current_bb]` >>
  simp[is_fn_path_def, fn_entry_label_def, entry_block_def]
QED

(* Preserved at block boundaries. Key argument:
   - Case d_bb = bb (just executed): ISZERO ran during exec_block,
     outputs/inputs unchanged after by SSA.
   - Case d_bb <> bb: d_bb strictly dominated bb, exec_block doesn't
     modify d_bb's variables (SSA uniqueness). *)
(* SSA: output of instruction in one block is not in outputs of another block *)
Triviality ssa_output_not_in_other_block[local]:
  !fn0 d_bb bb inst x.
    ssa_form fn0 /\ wf_function fn0 /\
    MEM d_bb fn0.fn_blocks /\ MEM bb fn0.fn_blocks /\
    MEM inst d_bb.bb_instructions /\ MEM x inst.inst_outputs /\
    d_bb <> bb ==>
    ~MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  fs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rename1 `MEM inst' bb.bb_instructions` >>
  `MEM inst (fn_insts fn0) /\ MEM inst' (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts] >>
  `ssa_form fn0` by simp[] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn0)))` by
    fs[ssa_form_def] >>
  `inst = inst'` by metis_tac[all_distinct_flat_map_unique] >>
  gvs[] >>
  `fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
  fs[fn_inst_ids_distinct_def] >>
  qmatch_asmsub_abbrev_tac `ALL_DISTINCT (FLAT (MAP fid _))` >>
  qspecl_then [`fn0.fn_blocks`, `fid`, `d_bb`, `bb`]
    (fn th => `d_bb = bb` by
      (mp_tac th >> simp[Abbr `fid`, listTheory.MEM_MAP] >> metis_tac[]))
    all_distinct_flat_map_unique >>
  gvs[]
QED


Theorem strict_dom_iszero_inv_state_equiv_compat:
  !fn0 dfg fv s1 s2.
    strict_dom_iszero_inv fn0 dfg s1 /\
    state_equiv fv s1 s2 /\
    (!x inst. dfg_get_def dfg x = SOME inst ==> x NOTIN fv) /\
    (!x inst op. dfg_get_def dfg x = SOME inst /\
      inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var op] ==>
      op NOTIN fv) ==>
    strict_dom_iszero_inv fn0 dfg s2
Proof
  rpt gen_tac >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  qpat_x_assum `strict_dom_iszero_inv _ _ s1`
    (assume_tac o REWRITE_RULE[strict_dom_iszero_inv_def]) >>
  simp[strict_dom_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  `x NOTIN fv` by metis_tac[] >>
  `lookup_var x s1 = lookup_var x s2` by
    (fs[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
  `eval_operand op s1 = eval_operand op s2` by
    (Cases_on `op` >> simp_tac std_ss [eval_operand_def] >>
     TRY (fs[state_equiv_def, execution_equiv_def] >> NO_TAC) >>
     rename1 `Var vn` >>
     `vn NOTIN fv` by metis_tac[] >>
     simp_tac std_ss [eval_operand_def] >>
     fs[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
  `lookup_var x s1 = SOME val_x /\ eval_operand op s1 = SOME val_op` by
    metis_tac[] >>
  metis_tac[]
QED

(* ===== Within-block iszero step preservation ===== *)

(* SSA: operand's definer precedes the user; only one definer exists.
   So no later instruction in the same block can define that variable.
   Uses def_dominates_uses + ssa_form + inst_ids_el_eq. *)
Triviality ssa_operand_not_later_output[local]:
  !fn0 bb j idx v.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    j < LENGTH bb.bb_instructions /\ idx < LENGTH bb.bb_instructions /\
    j <= idx /\
    MEM (Var v) (EL j bb.bb_instructions).inst_operands ==>
    ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `ssa_form fn0 /\ def_dominates_uses fn0` by fs[wf_ssa_def] >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by
    metis_tac[listTheory.EL_MEM] >>
  `MEM (EL idx bb.bb_instructions) bb.bb_instructions` by
    metis_tac[listTheory.EL_MEM] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE[def_dominates_uses_def]) >>
  first_x_assum (qspecl_then [`bb`, `EL j bb.bb_instructions`, `v`]
    mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `MEM def_inst (fn_insts fn0)` by metis_tac[mem_block_mem_fn_insts] >>
  `MEM (EL idx bb.bb_instructions) (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts] >>
  `def_inst = EL idx bb.bb_instructions` by
    (qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                  `def_inst`, `EL idx bb.bb_instructions`, `v`]
       mp_tac all_distinct_flat_map_unique >>
     impl_tac >- fs[ssa_form_def] >>
     simp[]) >>
  gvs[] >>
  `fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `i < LENGTH bb.bb_instructions /\
       j < LENGTH bb.bb_instructions` by DECIDE_TAC >>
      `i = idx` by metis_tac[inst_ids_el_eq] >>
      `j' = j` by metis_tac[inst_ids_el_eq] >>
      DECIDE_TAC)
  >- (`MEM (EL idx bb.bb_instructions) def_bb.bb_instructions` by gvs[] >>
      `MEM (EL idx bb.bb_instructions).inst_id
        (MAP (\i. i.inst_id) bb.bb_instructions)` by
        (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
      `MEM (EL idx bb.bb_instructions).inst_id
        (MAP (\i. i.inst_id) def_bb.bb_instructions)` by
        (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
      `bb = def_bb` by
        (qspecl_then [`fn0.fn_blocks`,
           `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
           `bb`, `def_bb`,
           `(EL idx bb.bb_instructions).inst_id`]
           mp_tac all_distinct_flat_map_unique >>
         impl_tac >- fs[fn_inst_ids_distinct_def] >>
         simp[]) >>
      gvs[])
QED

(* j = idx case: the stepped instruction IS the ISZERO *)
Triviality wbiz_step_new[local]:
  !fn0 bb idx fuel ctx s s' iz_op x val_x val_op.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    (EL idx bb.bb_instructions).inst_opcode = ISZERO /\
    (EL idx bb.bb_instructions).inst_operands = [iz_op] /\
    MEM x (EL idx bb.bb_instructions).inst_outputs /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    lookup_var x (s' with vs_inst_idx := SUC s.vs_inst_idx) = SOME val_x /\
    eval_operand iz_op (s' with vs_inst_idx := SUC s.vs_inst_idx) =
      SOME val_op ==>
    val_x = bool_to_word (val_op = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst.inst_outputs = [x]` by
    (fs[inst_wf_def] >>
     Cases_on `inst.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    (irule step_inst_non_invoke >> simp[]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_base_def, exec_pure1_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >> strip_tac >> gvs[] >>
  qpat_x_assum `lookup_var _ _ = _` mp_tac >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strip_tac >> gvs[] >>
  Cases_on `iz_op` >>
  qpat_x_assum `eval_operand _ _ = SOME val_op` mp_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  TRY (strip_tac >> gvs[eval_operand_def] >> NO_TAC) >>
  rename1 `Var vn` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  `vn <> x` by
    (strip_tac >> gvs[] >>
     qspecl_then [`fn0`, `bb`, `idx`, `idx`, `vn`]
       mp_tac ssa_operand_not_later_output >>
     simp[Abbr `inst`]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

(* j < idx case: existing ISZERO preserved by step *)
Triviality wbiz_step_old[local]:
  !fn0 bb j idx fuel ctx s s' iz_op x val_x val_op.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    j < idx /\ j < LENGTH bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    (EL j bb.bb_instructions).inst_opcode = ISZERO /\
    (EL j bb.bb_instructions).inst_operands = [iz_op] /\
    MEM x (EL j bb.bb_instructions).inst_outputs /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    (!val_x' val_op'.
      lookup_var x s = SOME val_x' /\
      eval_operand iz_op s = SOME val_op' ==>
      val_x' = bool_to_word (val_op' = 0w)) /\
    lookup_var x (s' with vs_inst_idx := SUC s.vs_inst_idx) = SOME val_x /\
    eval_operand iz_op (s' with vs_inst_idx := SUC s.vs_inst_idx) =
      SOME val_op ==>
    val_x = bool_to_word (val_op = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `MEM (EL j bb.bb_instructions) (fn_insts fn0) /\
   MEM inst (fn_insts fn0)` by
    metis_tac[mem_block_mem_fn_insts, listTheory.EL_MEM] >>
  `~MEM x inst.inst_outputs` by
    (strip_tac >>
     `EL j bb.bb_instructions = inst` by
       (qspecl_then [`fn_insts fn0`, `\i. i.inst_outputs`,
                     `EL j bb.bb_instructions`, `inst`, `x`]
          mp_tac all_distinct_flat_map_unique >>
        impl_tac >- fs[ssa_form_def] >> simp[]) >>
     `j = idx` by
       (`fn_inst_ids_distinct fn0` by fs[wf_function_def] >>
        `j < LENGTH bb.bb_instructions` by DECIDE_TAC >>
        metis_tac[inst_ids_el_eq]) >>
     DECIDE_TAC) >>
  `!v. ~MEM v (EL idx bb.bb_instructions).inst_outputs ==>
       lookup_var v s' = lookup_var v s` by
    metis_tac[venomInstPropsTheory.step_preserves_non_output_vars] >>
  `lookup_var x s' = lookup_var x s` by
    (first_x_assum irule >> gvs[Abbr `inst`]) >>
  `lookup_var x (s' with vs_inst_idx := SUC s.vs_inst_idx) =
   lookup_var x s` by gvs[lookup_var_def] >>
  `s'.vs_labels = s.vs_labels` by
    metis_tac[venomInstPropsTheory.step_preserves_labels] >>
  sg `eval_operand iz_op (s' with vs_inst_idx := SUC s.vs_inst_idx) =
      eval_operand iz_op s`
  >- (Cases_on `iz_op`
      >- REWRITE_TAC[eval_operand_def]
      >- (REWRITE_TAC[eval_operand_def] >>
          rename1 `lookup_var vn` >>
          `lookup_var vn s' = lookup_var vn s` suffices_by
            simp[lookup_var_def] >>
          first_x_assum irule >> simp[Abbr `inst`] >>
          qspecl_then [`fn0`, `bb`, `j`, `idx`, `vn`]
            mp_tac ssa_operand_not_later_output >>
          impl_tac >- simp[] >> simp[])
      >- (REWRITE_TAC[eval_operand_def] >> gvs[])) >>
  gvs[]
QED

Theorem wbiz_step:
  !fn0 bb idx fuel ctx s s'.
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    inst_wf (EL idx bb.bb_instructions) /\
    ~is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    step_inst fuel ctx (EL idx bb.bb_instructions) s = OK s' /\
    within_block_iszero_inv fn0 bb idx s ==>
    within_block_iszero_inv fn0 bb (SUC idx)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  simp[within_block_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  Cases_on `j = idx`
  >- (gvs[] >> irule wbiz_step_new >> metis_tac[])
  >- (`j < idx` by DECIDE_TAC >>
      qspecl_then [`fn0`, `bb`, `j`, `idx`, `fuel`, `ctx`, `s`, `s'`,
                   `iz_op`, `x`, `val_x`, `val_op`]
        mp_tac wbiz_step_old >>
      impl_tac >- (simp[] >> fs[within_block_iszero_inv_def] >> metis_tac[])
      >> simp[])
QED

(* Terminator step preserves within_block_iszero_inv up to LENGTH *)
Triviality exec_block_wbiz_aux_term[local]:
  !fn0 bb fuel ctx s s_step inst.
    wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    inst = EL s.vs_inst_idx bb.bb_instructions /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s_step /\
    within_block_iszero_inv fn0 bb s.vs_inst_idx s ==>
    within_block_iszero_inv fn0 bb (LENGTH bb.bb_instructions) s_step
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `s.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by
    (fs[bb_well_formed_def] >> metis_tac[]) >>
  simp[within_block_iszero_inv_def] >> rpt gen_tac >> rpt strip_tac >>
  `j < s.vs_inst_idx` by
    (`~is_terminator (EL j bb.bb_instructions).inst_opcode` by
       simp[is_terminator_def] >>
     `j <> s.vs_inst_idx` by (strip_tac >> gvs[]) >>
     DECIDE_TAC) >>
  `!v. lookup_var v s_step = lookup_var v s` by
    metis_tac[venomExecPropsTheory.step_terminator_preserves_vars] >>
  `s_step.vs_labels = s.vs_labels` by
    metis_tac[venomExecPropsTheory.step_inst_preserves_labels_always] >>
  `eval_operand iz_op s_step = eval_operand iz_op s` by
    (Cases_on `iz_op`
     >- REWRITE_TAC[eval_operand_def]
     >- (REWRITE_TAC[eval_operand_def] >> simp[lookup_var_def])
     >- (REWRITE_TAC[eval_operand_def] >> gvs[])) >>
  `lookup_var x s_step = SOME val_x` by gvs[] >>
  `lookup_var x s = SOME val_x` by gvs[] >>
  `eval_operand iz_op s = SOME val_op` by gvs[] >>
  fs[within_block_iszero_inv_def] >> metis_tac[]
QED

(* exec_block_wbiz_aux: exec_block maintains within_block_iszero_inv.
   Proof by measure induction on LENGTH - vs_inst_idx.
   Terminator case: ISZEROs at j < idx preserved by step_terminator_preserves_vars.
   Non-terminator case: wbiz_step + IH. *)
Triviality exec_block_wbiz_aux[local]:
  !n fn0 bb fuel ctx s s'.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    wf_ssa fn0 /\ wf_function fn0 /\ MEM bb fn0.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    within_block_iszero_inv fn0 bb s.vs_inst_idx s /\
    exec_block fuel ctx bb s = OK s' ==>
    within_block_iszero_inv fn0 bb (LENGTH bb.bb_instructions) s'
Proof
  Induct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once venomExecSemanticsTheory.exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  TRY (fs[venomInstTheory.get_instruction_def] >> NO_TAC) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `step_inst fuel ctx inst s = OK s_step` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s.vs_inst_idx bb.bb_instructions` by
    fs[venomInstTheory.get_instruction_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()]
  >- (* terminator *)
     (qspecl_then [`fn0`, `bb`, `fuel`, `ctx`, `s`, `s'`,
                   `EL s.vs_inst_idx bb.bb_instructions`]
        mp_tac exec_block_wbiz_aux_term >>
      impl_tac >- (simp[] >> fs[venomInstTheory.get_instruction_def]) >>
      simp[])
  >- (* non-terminator: wbiz_step + IH *)
     (`s.vs_inst_idx < LENGTH bb.bb_instructions` by
        fs[venomInstTheory.get_instruction_def] >>
      `within_block_iszero_inv fn0 bb (SUC s.vs_inst_idx)
         (s_step with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qspecl_then [`fn0`, `bb`, `s.vs_inst_idx`, `fuel`, `ctx`,
                      `s`, `s_step`]
           mp_tac wbiz_step >>
         impl_tac >- (simp[] >> metis_tac[listTheory.EVERY_EL]) >>
         simp[]) >>
      first_x_assum (qspecl_then [`fn0`, `bb`, `fuel`, `ctx`,
         `s_step with vs_inst_idx := SUC s.vs_inst_idx`, `s'`]
         mp_tac) >>
      impl_tac >- simp[] >>
      simp[])
QED

Triviality exec_block_iszero_val[local]:
  !fn0 bb fuel ctx s s' iz_inst x iz_op.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM bb fn0.fn_blocks /\
    exec_block fuel ctx bb s = OK s' /\
    within_block_iszero_inv fn0 bb s.vs_inst_idx s /\
    EVERY inst_wf bb.bb_instructions /\
    MEM iz_inst bb.bb_instructions /\
    iz_inst.inst_opcode = ISZERO /\
    iz_inst.inst_operands = [iz_op] /\
    MEM x iz_inst.inst_outputs ==>
    !val_x val_op.
      lookup_var x s' = SOME val_x /\
      eval_operand iz_op s' = SOME val_op ==>
      val_x = bool_to_word (val_op = 0w)
Proof
  rpt gen_tac >> strip_tac >>
  `within_block_iszero_inv fn0 bb (LENGTH bb.bb_instructions) s'` by
    (qspecl_then [`LENGTH bb.bb_instructions - s.vs_inst_idx`, `fn0`, `bb`,
                  `fuel`, `ctx`, `s`, `s'`]
       mp_tac exec_block_wbiz_aux >>
     impl_tac >- simp[] >> simp[]) >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = iz_inst` by
    metis_tac[listTheory.MEM_EL] >>
  fs[within_block_iszero_inv_def] >> metis_tac[]
QED

(* Prefix of a valid path is valid *)
Triviality is_fn_path_take[local]:
  !fn l1 l2. is_fn_path fn (l1 ++ l2) ==> is_fn_path fn l1
Proof
  gen_tac >> Induct_on `l1` >> simp[is_fn_path_def] >>
  rpt gen_tac >>
  Cases_on `l1`
  >- simp[is_fn_path_def]
  >- (simp[is_fn_path_def] >> rpt strip_tac >>
      first_x_assum (qspec_then `l2` mp_tac) >> simp[])
QED

Theorem fn_dominates_trans:
  !fn a b c.
    fn_dominates fn a b /\ fn_dominates fn b c ==>
    fn_dominates fn a c
Proof
  rpt gen_tac >> strip_tac >>
  fs[fn_dominates_def] >> rpt strip_tac >>
  rename1 `LAST path = c` >>
  `MEM b path` by metis_tac[] >>
  qpat_x_assum `MEM b path`
    (strip_assume_tac o
     ONCE_REWRITE_RULE [listTheory.MEM_SPLIT_APPEND_first]) >>
  gvs[] >>
  rename1 `pfx ++ [b] ++ sfx` >>
  `pfx ++ [b] <> []` by simp[] >>
  `HD (pfx ++ [b]) = HD (pfx ++ [b] ++ sfx)` by
    (Cases_on `pfx` >> simp[]) >>
  `LAST (pfx ++ [b]) = b` by
    (simp[GSYM listTheory.SNOC_APPEND, listTheory.LAST_SNOC]) >>
  `is_fn_path fn (pfx ++ [b])` by
    (irule is_fn_path_take >> qexists_tac `sfx` >> simp[]) >>
  `MEM a (pfx ++ [b])` by metis_tac[] >>
  metis_tac[listTheory.MEM_APPEND, listTheory.MEM]
QED

(* Dominance is antisymmetric: mutual dominance implies equality *)
Theorem fn_dominates_antisym:
  !fn a b. fn_dominates fn a b /\ fn_dominates fn b a /\ a <> b ==> F
Proof
  spose_not_then strip_assume_tac >>
  `fn_reachable fn b` by metis_tac[fn_dominates_dom_reachable] >>
  fs[fn_reachable_def] >>
  `?path. is_fn_path fn path /\ path <> [] /\
          HD path = entry /\ LAST path = b` by
    metis_tac[rtc_to_fn_path] >>
  `!n path. LENGTH path <= n /\
     is_fn_path fn path /\ path <> [] /\
     HD path = entry /\ LAST path = b ==> F`
    suffices_by metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  completeInduct_on `n` >> rpt strip_tac >>
  `MEM a path'` by
    (qpat_x_assum `fn_dominates fn a b`
       (strip_assume_tac o REWRITE_RULE[fn_dominates_def]) >>
     metis_tac[]) >>
  qpat_x_assum `MEM a path'`
    (strip_assume_tac o ONCE_REWRITE_RULE[listTheory.MEM_SPLIT_APPEND_first]) >>
  rename1 `path' = pfx_a ++ [a] ++ sfx_a` >>
  `sfx_a <> []` by
    (CCONTR_TAC >> gvs[listTheory.LAST_APPEND_CONS]) >>
  `is_fn_path fn (pfx_a ++ [a])` by
    metis_tac[is_fn_path_take, listTheory.APPEND_ASSOC] >>
  `MEM b (pfx_a ++ [a])` by
    (qpat_x_assum `fn_dominates fn b a` mp_tac >>
     REWRITE_TAC[fn_dominates_def] >> strip_tac >>
     pop_assum (qspec_then `pfx_a ++ [a]` mp_tac) >>
     simp[listTheory.LAST_APPEND_CONS] >>
     disch_then irule >>
     Cases_on `pfx_a` >> gvs[]) >>
  `MEM b pfx_a` by
    (qpat_x_assum `MEM b (pfx_a ++ [a])` mp_tac >>
     simp[listTheory.MEM_APPEND]) >>
  qpat_x_assum `MEM b pfx_a`
    (strip_assume_tac o ONCE_REWRITE_RULE[listTheory.MEM_SPLIT_APPEND_first]) >>
  rename1 `pfx_a = pfx_b ++ [b] ++ sfx_b` >>
  `is_fn_path fn (pfx_b ++ [b])` by
    metis_tac[is_fn_path_take, listTheory.APPEND_ASSOC] >>
  first_x_assum (qspec_then `LENGTH (pfx_b ++ [b])` mp_tac) >>
  impl_tac >- (
    gvs[listTheory.LENGTH_APPEND] >> DECIDE_TAC) >>
  disch_then (qspec_then `pfx_b ++ [b]` mp_tac) >>
  simp[listTheory.LAST_APPEND_CONS] >>
  Cases_on `pfx_b` >> gvs[]
QED

(* Under SSA, operands of instructions in a strict dominator block
   are not outputs of instructions in the dominated block *)
Triviality ssa_cross_block_operand_not_output[local]:
  !fn0 d_bb bb inst v.
    wf_function fn0 /\ wf_ssa fn0 /\
    MEM d_bb fn0.fn_blocks /\ MEM bb fn0.fn_blocks /\
    MEM inst d_bb.bb_instructions /\
    MEM (Var v) inst.inst_operands /\
    fn_dominates fn0 d_bb.bb_label bb.bb_label /\
    d_bb.bb_label <> bb.bb_label ==>
    ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rpt strip_tac >>
  `ssa_form fn0 /\ def_dominates_uses fn0` by fs[wf_ssa_def] >>
  fs[def_dominates_uses_def] >>
  first_x_assum (qspecl_then [`d_bb`, `inst`, `v`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `d_bb <> bb` by (CCONTR_TAC >> gvs[]) >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `fn_dominates fn0 bb.bb_label d_bb.bb_label` by simp[] >>
      metis_tac[fn_dominates_antisym])
  >- (`MEM v (FLAT (MAP (\i. i.inst_outputs) def_bb.bb_instructions))` by
        (simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
      metis_tac[ssa_output_not_in_other_block])
QED

Theorem strict_dom_iszero_inv_exec_preserved:
  !fn0 dfg bb fuel ctx s s'.
    wf_function fn0 /\ wf_ssa fn0 /\
    dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    exec_block fuel ctx bb s = OK s' /\
    within_block_iszero_inv fn0 bb s.vs_inst_idx s /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    ~s'.vs_halted /\
    EVERY inst_wf bb.bb_instructions /\
    fn_reachable fn0 s.vs_current_bb /\
    strict_dom_iszero_inv fn0 dfg s ==>
    strict_dom_iszero_inv fn0 dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  rw[strict_dom_iszero_inv_def] >> rpt strip_tac >>
  Cases_on `d_bb.bb_label = s.vs_current_bb`
  >- ((* d_bb = bb: ISZERO executed during this block *)
      `d_bb = bb` by
        (`d_bb.bb_label = bb.bb_label` by gvs[] >>
         metis_tac[same_label_same_block]) >>
      gvs[] >>
      `MEM x inst.inst_outputs` by
        metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
      qspecl_then [`fn0`, `bb`, `fuel`, `ctx`, `s`, `s'`,
                   `inst`, `x`, `op`] mp_tac exec_block_iszero_val >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`val_x`, `val_op`] mp_tac) >> simp[])
  >- ((* d_bb ≠ bb: values preserved across exec_block *)
      `d_bb <> bb` by (CCONTR_TAC >> gvs[]) >>
      `MEM x inst.inst_outputs` by
        metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
      `MEM s'.vs_current_bb (bb_succs bb)` by
        (qspecl_then [`fuel`, `ctx`, `bb`, `s`, `s'`]
           mp_tac exec_block_current_bb_in_succs >>
         impl_tac >- (
           rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
           rpt strip_tac >> spose_not_then assume_tac >>
           fs[bb_well_formed_def] >> res_tac >> DECIDE_TAC) >>
         simp[]) >>
      `fn_cfg_edge fn0 s.vs_current_bb s'.vs_current_bb` by
        (simp[fn_cfg_edge_def] >> metis_tac[]) >>
      `fn_reachable fn0 s'.vs_current_bb` by
        metis_tac[fn_reachable_step] >>
      `fn_dominates fn0 d_bb.bb_label s.vs_current_bb` by
        metis_tac[fn_dominates_predecessor] >>
      `~MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
        metis_tac[ssa_output_not_in_other_block] >>
      `lookup_var x s' = lookup_var x s` by
        metis_tac[exec_block_preserves_non_output_vars] >>
      `eval_operand op s' = eval_operand op s` by
        (Cases_on `op` >> simp_tac std_ss [eval_operand_def]
         >- (rename1 `lookup_var vn` >>
             `MEM (Var vn) inst.inst_operands` by simp[] >>
             `~MEM vn (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
               metis_tac[ssa_cross_block_operand_not_output] >>
             metis_tac[exec_block_preserves_non_output_vars])
         >- (`s'.vs_labels = s.vs_labels` by
               metis_tac[venomExecPropsTheory.exec_block_preserves_labels] >>
             simp[])) >>
      fs[strict_dom_iszero_inv_def] >> metis_tac[])
QED

(* idx=0 specialisation (within_block holds initially). *)
Theorem strict_dom_iszero_inv_preserved:
  !fn0 dfg bb fuel ctx s s'.
    wf_function fn0 /\ wf_ssa fn0 /\
    dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    exec_block fuel ctx bb s = OK s' /\
    s.vs_inst_idx = 0 /\
    ~s'.vs_halted /\
    EVERY inst_wf bb.bb_instructions /\
    fn_reachable fn0 s.vs_current_bb /\
    strict_dom_iszero_inv fn0 dfg s ==>
    strict_dom_iszero_inv fn0 dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  qspecl_then [`fn0`, `dfg`, `bb`, `fuel`, `ctx`, `s`, `s'`]
    mp_tac strict_dom_iszero_inv_exec_preserved >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gvs[wbiz_initial, bb_well_formed_def]) >>
  simp[]
QED

(* exec_block starting at the PHI-prefix boundary preserves strict_dom_iszero_inv,
   given the invariant holds at the post-eval_phis state. *)
Theorem strict_dom_iszero_inv_exec_from_phi_prefix:
  !fn0 dfg bb fuel ctx s_phi s'.
    wf_function fn0 /\ wf_ssa fn0 /\
    dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    bb.bb_label = s_phi.vs_current_bb /\
    exec_block fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s' /\
    bb.bb_instructions <> [] /\
    ~s'.vs_halted /\
    EVERY inst_wf bb.bb_instructions /\
    fn_reachable fn0 s_phi.vs_current_bb /\
    strict_dom_iszero_inv fn0 dfg s_phi ==>
    strict_dom_iszero_inv fn0 dfg s'
Proof
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `exec_block fuel ctx bb s_pp = OK s'` >>
  `s_pp.vs_current_bb = s_phi.vs_current_bb` by simp[Abbr `s_pp`] >>
  `s_pp.vs_inst_idx = phi_prefix_length bb.bb_instructions` by simp[Abbr `s_pp`] >>
  `strict_dom_iszero_inv fn0 (dfg_build_function fn0) s_pp` by
    (simp[Abbr `s_pp`] >>
     ONCE_REWRITE_TAC[strict_dom_iszero_inv_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  `within_block_iszero_inv fn0 bb s_pp.vs_inst_idx s_pp` by simp[wbiz_phi_prefix] >>
  qspecl_then [`fn0`, `dfg_build_function fn0`, `bb`, `fuel`, `ctx`, `s_pp`, `s'`]
    mp_tac strict_dom_iszero_inv_exec_preserved >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[phi_prefix_length_le]) >>
  simp[]
QED

(* run_block version: combines eval_phis preservation with the exec_block
   (post-PHI-prefix) preservation. *)
Theorem strict_dom_iszero_inv_run_block_preserved:
  !fn0 dfg bb fuel ctx s s'.
    wf_function fn0 /\ wf_ssa fn0 /\ dfg_block_local fn0 /\
    dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    run_block fuel ctx bb s = OK s' /\
    ~s'.vs_halted /\
    EVERY inst_wf bb.bb_instructions /\
    fn_reachable fn0 s.vs_current_bb /\
    strict_dom_iszero_inv fn0 dfg s ==>
    strict_dom_iszero_inv fn0 dfg s'
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `bb_well_formed bb` by fs[wf_function_def] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `?s_phi. eval_phis s bb.bb_instructions = OK s_phi /\
     exec_block fuel ctx bb
       (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK s'` by
    (qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
     simp[Once run_block_def] >>
     DISJ_CASES_THEN STRIP_ASSUME_TAC
       (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
     gvs[]) >>
  `strict_dom_iszero_inv fn0 (dfg_build_function fn0) s_phi` by
    metis_tac[eval_phis_strict_dom_iszero_inv] >>
  `s_phi.vs_current_bb = s.vs_current_bb` by
    (`s_phi = s with vs_vars := s_phi.vs_vars` by
       metis_tac[eval_phis_only_updates_vs_vars] >>
     pop_assum (fn th => simp[Once th])) >>
  qspecl_then [`fn0`, `dfg_build_function fn0`, `bb`, `fuel`, `ctx`,
               `s_phi`, `s'`] mp_tac strict_dom_iszero_inv_exec_from_phi_prefix >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  simp[]
QED

(* strict_dom_iszero_inv preserved through per-step within a block.
   Key: dominator ISZERO outputs/operands are not in current block's outputs. *)
Theorem strict_dom_iszero_inv_step_preserved_local:
  !fn0 dfg bb inst fuel ctx s s'.
    wf_function fn0 /\ wf_ssa fn0 /\
    dfg = dfg_build_function fn0 /\
    MEM bb fn0.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    bb.bb_label = s.vs_current_bb /\
    step_inst fuel ctx inst s = OK s' /\
    strict_dom_iszero_inv fn0 dfg s ==>
    strict_dom_iszero_inv fn0 dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn0` by fs[wf_ssa_def] >>
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  simp_tac std_ss [strict_dom_iszero_inv_def] >>
  rpt gen_tac >> rpt strip_tac >>
  `fn_dominates fn0 d_bb.bb_label bb.bb_label /\
   d_bb.bb_label <> bb.bb_label` by gvs[] >>
  `d_bb <> bb` by metis_tac[same_label_same_block] >>
  `MEM x inst'.inst_outputs` by
    metis_tac[dfgAnalysisPropsTheory.dfg_build_function_correct] >>
  `~MEM x (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    metis_tac[ssa_output_not_in_other_block] >>
  `~MEM x inst.inst_outputs` by
    (strip_tac >> gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  `lookup_var x s' = lookup_var x s` by
    metis_tac[venomInstPropsTheory.step_preserves_non_output_vars] >>
  `!vn. MEM (Var vn) inst'.inst_operands ==> ~MEM vn inst.inst_outputs` by
    (rpt strip_tac >>
     `~MEM vn (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
       metis_tac[ssa_cross_block_operand_not_output] >>
     gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `!opr. MEM opr inst'.inst_operands ==>
     eval_operand opr s' = eval_operand opr s` by
    (rpt strip_tac >> Cases_on `opr` >> simp[eval_operand_def] >>
     TRY (metis_tac[venomInstPropsTheory.step_preserves_labels]) >>
     rename1 `lookup_var vn2` >>
     `~MEM vn2 inst.inst_outputs` by metis_tac[] >>
     metis_tac[venomInstPropsTheory.step_preserves_non_output_vars]) >>
  qpat_x_assum `strict_dom_iszero_inv _ _ s`
    (mp_tac o REWRITE_RULE [strict_dom_iszero_inv_def]) >>
  disch_then (qspecl_then [`x`, `inst'`, `op`, `d_bb`] mp_tac) >>
  gvs[] >> disch_then (qspecl_then [`val_x`, `val_op`] mp_tac) >>
  gvs[] >>
  `MEM op inst'.inst_operands` by gvs[] >>
  metis_tac[]
QED

