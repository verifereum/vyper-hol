(*
 * MakeSSA's o1 function rows.  The walk runs MakeSSA at positions 0 and 4,
 * and the step from row k to row SUC k there needs, besides
 * fmp_sig_no_param (every pass but FmpLowering keeps it):
 *   k = 0: make_ssa_input_ok and no_raw_fmp_ops of the output;
 *   k = 4: no ALLOCA, pseudos as a block prefix, no PARAM-family opcode
 *          outside the first block, and SSA form.
 * MakeSSA inserts PHIs only at non-entry frontier blocks, the rename keeps
 * every block's opcode sequence, and the cleanup turns PHIs only into ASSIGN
 * or NOP and leaves PHI-free blocks alone.  So a non-entry block gets no
 * PARAM and keeps its PHIs in front, and the entry block keeps its opcode
 * sequence, hence its PARAM prefix.
 *)
Theory o1MakeSsaRows
Ancestors
  o1MakeSsaFormats o1MakeSsaFrontier o1MakeSsaCfg o1PassContract
  makeSsaCurrentDefs makeSsaCurrentProps makeSsaCurrentInputOk
  makeSsaCurrentNonDegenerate makeSsaCurrentWfSsa makeSsaDefs
  venomPassDispatcher venomPassSchedule venomFnScheduleRunnerProps
  fmpStepBridge unitShapeDefs simplifyCfgStruct simplifyCfgDefs venomWf
  venomInst callLayoutDefs list o1ContractMakeSsaSrcOpcodes

(* ===== Pseudo prefixes from opcodes ===== *)

Theorem is_pseudo_not_param:
  is_pseudo op /\ ~is_param_opcode op ==> op = PHI
Proof
  Cases_on `op` >> simp[is_pseudo_def, is_param_opcode_def]
QED

(* A block without PARAMs has only PHIs as pseudos, and those come first. *)
Theorem pseudos_prefix_no_params:
  bb_well_formed bb /\
  EVERY (\i. ~is_param_opcode i.inst_opcode) bb.bb_instructions ==>
  pseudos_prefix bb
Proof
  rw[pseudos_prefix_def, bb_well_formed_def] >>
  `MEM (EL j bb.bb_instructions) bb.bb_instructions` by metis_tac[MEM_EL] >>
  `(EL j bb.bb_instructions).inst_opcode = PHI` by
    (gvs[EVERY_MEM] >> metis_tac[is_pseudo_not_param]) >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by metis_tac[] >>
  simp[is_pseudo_def]
QED

Theorem pseudos_prefix_same_opcodes:
  MAP (\i. i.inst_opcode) b1.bb_instructions =
  MAP (\i. i.inst_opcode) b2.bb_instructions /\
  pseudos_prefix b1 ==> pseudos_prefix b2
Proof
  simp[pseudos_prefix_def] >> rpt strip_tac >>
  `LENGTH b1.bb_instructions = LENGTH b2.bb_instructions` by
    metis_tac[LENGTH_MAP] >>
  `!n. n < LENGTH b2.bb_instructions ==>
       (EL n b2.bb_instructions).inst_opcode =
       (EL n b1.bb_instructions).inst_opcode` by
    (rpt strip_tac >>
     `n < LENGTH b1.bb_instructions` by gvs[] >>
     `EL n (MAP (\i. i.inst_opcode) b2.bb_instructions) =
      EL n (MAP (\i. i.inst_opcode) b1.bb_instructions)` by metis_tac[] >>
     gvs[EL_MAP]) >>
  `i < LENGTH b2.bb_instructions` by decide_tac >>
  metis_tac[]
QED

(* ===== The entry block keeps its opcode sequence ===== *)

Theorem add_phi_nodes_supply_entry_op_seq:
  add_phi_nodes_supply s df pm li bbs defs = (bbs',s') /\
  EVERY (\bb. bb.bb_label = entry ==>
    MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs /\
  (!d fs. ALOOKUP df d = SOME fs ==> ~MEM entry fs) ==>
  EVERY (\bb. bb.bb_label = entry ==>
    MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs'
Proof
  strip_tac >> drule add_phi_nodes_supply_invariant >>
  disch_then irule >> simp[] >> rpt strip_tac >> IF_CASES_TAC >>
  gvs[insert_phi_at_block_def] >> metis_tac[]
QED

Theorem update_current_succ_phis_entry_op_seq:
  !succs bbs.
    EVERY (\bb. bb.bb_label = entry ==>
      MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs ==>
    EVERY (\bb. bb.bb_label = entry ==>
      MAP (\i. i.inst_opcode) bb.bb_instructions = ops)
      (update_current_succ_phis rs lbl bbs succs)
Proof
  Induct >> gvs[update_current_succ_phis_def] >> rpt strip_tac >>
  first_x_assum irule >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule EVERY_replace_block >> simp[] >>
  drule lookup_block_member_label >> strip_tac >> rename1 `MEM b bbs` >>
  simp[MAP_MAP_o, combinTheory.o_DEF, COND_RAND] >> strip_tac >>
  `MAP (\inst. if inst.inst_opcode <> PHI then inst.inst_opcode else PHI)
     b.bb_instructions = MAP (\i. i.inst_opcode) b.bb_instructions` by
    (simp[MAP_EQ_f] >> rw[]) >>
  pop_assum SUBST1_TAC >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem rename_current_blocks_entry_op_seq:
  (!t s rs bbs sm ctrs s' bbs'.
    rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') /\
    EVERY (\bb. bb.bb_label = entry ==>
      MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs ==>
    EVERY (\bb. bb.bb_label = entry ==>
      MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs') /\
  (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
    rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') /\
    EVERY (\bb. bb.bb_label = entry ==>
      MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs ==>
    EVERY (\bb. bb.bb_label = entry ==>
      MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs')
Proof
  ho_match_mp_tac makeSsaCurrentInductTheory.current_dom_tree_induction >>
  rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >> first_x_assum drule >> disch_then irule >>
      irule update_current_succ_phis_entry_op_seq >>
      irule EVERY_replace_block >> simp[] >>
      drule lookup_block_member_label >> strip_tac >>
      drule rename_current_block_insts_opcodes >> strip_tac >>
      gvs[EVERY_MEM] >> metis_tac[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >> pairarg_tac >> gvs[] >>
  first_x_assum drule >> disch_then irule >>
  first_x_assum drule_all >> simp[]
QED

Theorem simplify_current_phi_block_no_phi:
  EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
  simplify_current_phi_block bb = bb
Proof
  strip_tac >> simp[simplify_current_phi_block_def] >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED

Theorem simplify_current_phis_if_entry_op_seq:
  EVERY (\bb. bb.bb_label = entry ==>
    MAP (\i. i.inst_opcode) bb.bb_instructions = ops) bbs /\
  ~MEM PHI ops ==>
  EVERY (\bb. bb.bb_label = entry ==>
    MAP (\i. i.inst_opcode) bb.bb_instructions = ops)
    (simplify_current_phis_if enabled bbs)
Proof
  Cases_on `enabled` >> simp[simplify_current_phis_if_def] >>
  Cases_on `blocks_have_leading_phi bbs` >> simp[simplify_current_phis_def] >>
  simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >> rename1 `MEM b bbs` >>
  `MAP (\i. i.inst_opcode) b.bb_instructions = ops` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `~MEM PHI ops` mp_tac >>
     qpat_x_assum `MAP _ b.bb_instructions = ops` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> metis_tac[]) >>
  drule simplify_current_phi_block_no_phi >> simp[]
QED

Theorem make_ssa_current_fn_entry_op_seq:
  fn_entry_label fn = SOME entry /\
  make_ssa_current_fn s fn = (fn',s') /\
  (!d fs. ALOOKUP (current_frontier_map fn) d = SOME fs ==> ~MEM entry fs) /\
  EVERY (\bb. bb.bb_label = entry ==>
    MAP (\i. i.inst_opcode) bb.bb_instructions = ops) fn.fn_blocks /\
  ~MEM PHI ops ==>
  EVERY (\bb. bb.bb_label = entry ==>
    MAP (\i. i.inst_opcode) bb.bb_instructions = ops) fn'.fn_blocks
Proof
  strip_tac >> gvs[make_ssa_current_fn_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  irule simplify_current_phis_if_entry_op_seq >> simp[] >>
  drule (CONJUNCT1 rename_current_blocks_entry_op_seq) >> disch_then irule >>
  drule add_phi_nodes_supply_entry_op_seq >> disch_then irule >> simp[] >>
  gvs[current_frontier_map_def] >> metis_tac[]
QED

(* ===== The rows ===== *)

Theorem make_ssa_step_rows:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  (k = 0 \/ k = 4) /\ o1_fn_row k fn ==>
  o1_fn_row (SUC k) out.fpo_function
Proof
  strip_tac >>
  `fmp_sig_no_param fn /\ make_ssa_input_ok fn` by gvs[o1_fn_row_def] >>
  `fmp_sig_no_param out.fpo_function` by
    (drule fn_pass_step_fmp_sig_no_param >> gvs[fn_pass_tag_def]) >>
  `MEM fn observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >> drule lookup_unique_function_member >> simp[]) >>
  `o1_fn_shape observed.cu_context fn` by gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
   first_block_no_phi fn` by gvs[o1_fn_shape_def] >>
  `ir_supply_covers_fn s fn` by
    (gvs[fn_pass_step_def] >> metis_tac[ir_supply_covers_unit_member]) >>
  `make_ssa_current_fn s fn = (out.fpo_function,out.fpo_supply)` by
    (gvs[fn_pass_step_def] >> Cases_on `make_ssa_current_fn s fn` >> gvs[]) >>
  gvs[] >> simp[o1_fn_row_def]
  >~ [`no_raw_fmp_ops _`]
  >- (drule_all make_ssa_current_fn_phis_non_degenerate >> strip_tac >>
      drule_all make_ssa_current_fn_input_ok >> strip_tac >>
      `no_raw_fmp_ops fn` by gvs[o1_fn_row_def] >>
      `no_raw_fmp_ops out.fpo_function` by
        metis_tac[make_ssa_current_fn_no_raw_fmp_ops, pairTheory.FST] >>
      rewrite_tac[make_ssa_input_ok_def] >> asm_rewrite_tac[]) >>
  (* k = 4 *)
  `EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) /\ fn_pseudos_prefix fn /\
   EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks)` by
    gvs[o1_fn_row_def] >>
  `wf_ssa out.fpo_function` by
    (drule_at (Pat `make_ssa_current_fn _ _ = _`) make_ssa_current_fn_wf_ssa >>
     impl_tac >- (fs[make_ssa_input_ok_def] >> metis_tac[]) >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts out.fpo_function)` by
    (drule make_ssa_current_fn_opcodes >>
     disch_then (qspec_then `\lbl op. op <> ALLOCA` mp_tac) >> simp[] >>
     impl_tac
     >- (gvs[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >>
         metis_tac[]) >>
     simp[EVERY_MEM, fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]) >>
  (* the entry block and the rest *)
  `?b0 rest. fn.fn_blocks = b0::rest` by
    (Cases_on `fn.fn_blocks` >> gvs[wf_function_def, fn_has_entry_def]) >>
  `ALL_DISTINCT (b0.bb_label :: MAP (\bb. bb.bb_label) rest)` by
    gvs[wf_function_def, fn_labels_def] >>
  `fn_entry_label fn = SOME b0.bb_label` by
    simp[fn_entry_label_def, entry_block_def] >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  `?b0' rest'. out.fpo_function.fn_blocks = b0'::rest'` by
    (Cases_on `out.fpo_function.fn_blocks` >> gvs[]) >>
  `b0'.bb_label = b0.bb_label /\
   MAP (\bb. bb.bb_label) rest' = MAP (\bb. bb.bb_label) rest` by gvs[] >>
  (* no PARAM outside the entry block *)
  `EVERY (\bb. EVERY (\i. bb.bb_label <> b0.bb_label ==>
     ~is_param_opcode i.inst_opcode) bb.bb_instructions)
     out.fpo_function.fn_blocks` by
    (drule make_ssa_current_fn_opcodes >>
     disch_then (qspec_then
       `\lbl op. lbl <> b0.bb_label ==> ~is_param_opcode op` mp_tac) >>
     simp[is_param_opcode_def] >> disch_then irule >>
     gvs[EVERY_MEM, no_param_insts_def] >> metis_tac[]) >>
  `EVERY (\bb. no_param_insts bb.bb_instructions) rest'` by
    (simp[EVERY_MEM, no_param_insts_def] >> rpt strip_tac >>
     `MEM bb.bb_label (MAP (\bb. bb.bb_label) rest')` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     `MEM bb.bb_label (MAP (\bb. bb.bb_label) rest)` by metis_tac[] >>
     `bb.bb_label <> b0.bb_label` by (strip_tac >> gvs[]) >>
     `MEM bb out.fpo_function.fn_blocks` by
       (qpat_x_assum `out.fpo_function.fn_blocks = _`
          (fn th => simp[th])) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  (* the entry block keeps its opcode sequence *)
  `~MEM PHI (MAP (\i. i.inst_opcode) b0.bb_instructions)` by
    (gvs[first_block_no_phi_def, EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `!d fs. ALOOKUP (current_frontier_map fn) d = SOME fs ==>
          ~MEM b0.bb_label fs` by
    (rpt strip_tac >>
     `MEM d (fn_labels fn)` by metis_tac[current_frontier_key] >>
     drule_all current_frontier_not_entry >> gvs[]) >>
  `EVERY (\bb. bb.bb_label = b0.bb_label ==>
     MAP (\i. i.inst_opcode) bb.bb_instructions =
     MAP (\i. i.inst_opcode) b0.bb_instructions) fn.fn_blocks` by
    (gvs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `EVERY (\bb. bb.bb_label = b0.bb_label ==>
     MAP (\i. i.inst_opcode) bb.bb_instructions =
     MAP (\i. i.inst_opcode) b0.bb_instructions)
     out.fpo_function.fn_blocks` by
    (irule make_ssa_current_fn_entry_op_seq >> metis_tac[]) >>
  `EVERY bb_well_formed out.fpo_function.fn_blocks` by
    (drule make_ssa_current_fn_blocks_well_formed >> impl_tac
     >- (gvs[wf_function_def, EVERY_MEM] >> metis_tac[]) >> simp[]) >>
  `pseudos_prefix b0` by gvs[fn_pseudos_prefix_def] >>
  `fn_pseudos_prefix out.fpo_function` by
    (simp[fn_pseudos_prefix_def] >> rpt strip_tac >>
     Cases_on `bb.bb_label = b0.bb_label`
     >- (irule pseudos_prefix_same_opcodes >> qexists_tac `b0` >>
         fs[EVERY_MEM] >> metis_tac[]) >>
     irule pseudos_prefix_no_params >> gvs[EVERY_MEM, no_param_insts_def] >> metis_tac[]) >>
  gvs[o1_fn_row_def]
QED
