(*
 * MakeSSA (make_ssa_current_fn) only renames: there is a map orig from
 * output variables to input variables under which every output
 * instruction is an input non-PHI with the same id, or comes from a PHI
 * (inserted or carried over, possibly simplified to an ASSIGN or a NOP)
 * that defines a renamed copy of an input variable.
 *)
Theory makeSsaCurrentOrigin
Ancestors
  makeSsaCurrentDefs venomWf cfgWf venomInst irSupply unitShapeDefs
  o1PassContract makeSsaOriginRename makeSsaOriginCleanup
  makeSsaOriginInvariant makeSsaOriginInsert makeSsaCurrentProps list

Theorem origin_ordered_defs[local]:
  EVERY (\p. ?inst. MEM inst (fn_insts fn) /\ MEM (FST p) inst.inst_outputs)
    (compute_defs (MAP THE (FILTER IS_SOME
      (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels))))
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (FST p) (MAP FST (compute_defs
    (MAP THE (FILTER IS_SOME (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels)))))` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qspec_then `fn with fn_blocks := MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl fn.fn_blocks) labels))` mp_tac
    (Q.GEN `fn` (Q.GEN `v` origin_compute_defs_key)) >>
  disch_then (qspec_then `FST p` mp_tac) >>
  simp[fn_insts_def, fn_insts_blocks_MEM] >> strip_tac >>
  drule lookup_blocks_filter_MEM >> strip_tac >> metis_tac[]
QED

(* Intuition (the prover may ignore it).
   - orig starts as the identity.  The only new names are the fresh
     formal_var_<n> that push_current_name takes for a variable v when its
     counter is nonzero; set orig n := orig v there.  fresh_ir_var returns a
     name outside irs_used_vars, which covers every variable in the blocks
     and on the rename stacks (makeSsaCurrentProps: add_phi_nodes_supply_ok,
     rename_current_blocks_vars_covered), so the update never changes orig
     on anything already related; and orig stays the identity on fn's own
     variables (ir_supply_covers_fn).
   - Renaming keeps every instruction equal modulo orig (outputs mapped by
     orig, operands Var u |-> Var (orig u), same id and opcode), as long as
     every name on the stack of key k has orig = orig k: latest_current_name
     then preserves orig.  This holds even if a block is renamed twice.
     replace_block replaces every block with the label; labels stay those of
     fn, which wf_function keeps distinct.
   - Instructions after PHI insertion are fn's own or
     build_phi_inst_supply id var preds, with var a compute_defs key, i.e.
     an output of some fn instruction; its operands are Label/Var var.
   - simplify_current_phis_if rewrites only the leading PHI prefix of a
     block into kept PHIs, then ASSIGN [Var v] (v a Var operand) or NOP; the
     prefix length is unchanged, so reassign_current_inst_ids leaves the ids
     of the instructions after the prefix alone.
   - Input PHIs have one output and Label/Var operands (fn_inst_wf). *)
Theorem make_ssa_current_fn_origin:
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  fn_phis_cover_preds fn /\
  (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = PHI ==>
     ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands)) /\
     !l v. MEM (l,v) (phi_pairs inst.inst_operands) ==>
       fn_cfg_edge fn l bb.bb_label) /\
  fn_phi_outputs_single_def fn /\ fn_phis_non_degenerate fn /\
  all_reachable fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ?orig.
    !inst'. MEM inst' (fn_insts fn') ==>
      (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode <> PHI /\
         inst'.inst_id = inst.inst_id /\
         inst'.inst_opcode = inst.inst_opcode /\
         MAP orig inst'.inst_outputs = inst.inst_outputs /\
         MAP (\op. case op of Var u => Var (orig u) | _ => op)
           inst'.inst_operands = inst.inst_operands) \/
      (inst'.inst_opcode = NOP /\ inst'.inst_outputs = [] /\
       inst'.inst_operands = []) \/
      ((inst'.inst_opcode = PHI \/ inst'.inst_opcode = ASSIGN) /\
       ?w inst. inst'.inst_outputs = [w] /\ MEM inst (fn_insts fn) /\
         MEM (orig w) inst.inst_outputs /\
         (inst'.inst_opcode = ASSIGN ==> ?u. inst'.inst_operands = [Var u]) /\
         (!op. MEM op inst'.inst_operands ==> ?x. op = Var x \/ op = Label x) /\
         !u. MEM (Var u) inst'.inst_operands ==>
             orig u = orig w \/
             (inst.inst_opcode = PHI /\ MEM (Var (orig u)) inst.inst_operands))
Proof
  rpt strip_tac >>
  `(?orig. !i. MEM i (fn_insts fn') ==> origin_after_cleanup fn orig i)` suffices_by
    simp[origin_after_cleanup_def, origin_ordinary_def, origin_phi_def] >>
  rpt strip_tac >>
  qpat_x_assum `make_ssa_current_fn _ _ = _` mp_tac >>
  simp[make_ssa_current_fn_def] >> Cases_on `fn_entry_label fn` >> simp[]
  >- (strip_tac >> gvs[] >> qexists_tac `I` >> rpt strip_tac >>
      irule origin_before_after >> irule origin_input_identity >> simp[]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `compute_defs ordered` >>
  qabbrev_tac `defs = compute_defs ordered` >>
  `ssa_vars_covered s (FLAT (MAP block_ir_vars fn.fn_blocks))` by
    gvs[venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
        venomFnScheduleRunnerTheory.list_subset_def, ssa_vars_covered_def, fn_ir_vars_def, EVERY_MEM] >>
  `ssa_vars_covered s (MAP FST defs)` by
    (simp[Abbr `defs`, Abbr `ordered`] >>
     irule compute_defs_lookup_blocks_vars_covered >> simp[]) >>
  `EVERY (\p. ?inst. MEM inst (fn_insts fn) /\ MEM (FST p) inst.inst_outputs) defs` by
    simp[Abbr `defs`, Abbr `ordered`, origin_ordered_defs] >>
  `EVERY (\bb. EVERY (origin_before_cleanup fn I) bb.bb_instructions) bbs1` by
    (irule origin_add_phi_nodes >> goal_assum (drule_at Any) >>
     simp[origin_input_blocks]) >>
  `ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids fn.fn_blocks))
     (FLAT (MAP block_ir_inst_ids bbs1)) s1 /\
   MAP basic_block_bb_label bbs1 = MAP basic_block_bb_label fn.fn_blocks /\
   ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs1))` by
    (irule add_phi_nodes_supply_ok >> goal_assum (drule_at Any) >>
     gvs[wf_function_def, fn_inst_ids_distinct_def, fn_labels_def,
         fn_ir_inst_ids_def, venomFnScheduleRunnerTheory.ir_supply_covers_fn_def,
         venomFnScheduleRunnerTheory.list_subset_def, EVERY_MEM,
         block_ir_inst_ids_def] >>
     once_rewrite_tac[GSYM bb_label_eta] >>
     gvs[GSYM (lambdify block_ir_inst_ids_def)] >> metis_tac[]) >>
  `ssa_supply_extends s s1` by metis_tac[ssa_ids_supply_ok_extends] >>
  `origin_stacks_covered s1 (SND (init_current_rename_state defs))` by
    (irule origin_init_covered >>
     gvs[ssa_vars_covered_def, EVERY_MEM, MEM_MAP, ssa_supply_extends_def] >>
     metis_tac[]) >>
  drule (cj 1 origin_rename_tree) >>
  disch_then (qspecl_then [`fn`, `I`] mp_tac) >>
  (impl_tac >- simp[origin_blocks_covered_iff, origin_init_coherent]) >> strip_tac >>
  drule origin_cleanup_blocks >> disch_then (qspec_then `blocks_have_leading_phi fn.fn_blocks` mp_tac) >>
  strip_tac >> qexists_tac `orig'` >>
  gvs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]
QED
