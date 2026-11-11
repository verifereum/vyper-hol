(*
 * DFT's step part of the O1 pass contract: on an SSA function of the O1
 * shape with its pseudo-instructions first, dft_fn keeps the shape, takes
 * no new labels or instruction ids, renames no label and leaves the
 * supply alone.
 *)
Theory o1DftStep
Ancestors
  o1PassContract unitShapeDefs venomPassDispatcher dftStructural dftDefs
  dftLifting dftShape dftCorrectness unitLabelMapIdentity
  venomFnScheduleRunnerProps  o1DftRetpc
  venomWf venomInst venomEffects passSharedDefs dretDesugarDefs list
Libs
  BasicProvers

Theorem dft_shape_instruction_source:
  o1_fn_shape ctx fn /\ MEM i (fn_insts (dft_fn fn)) ==>
  ?j. MEM j (fn_insts fn) /\
      (i = j \/ (i = flip_operands j /\ is_flippable j.inst_opcode))
Proof
  strip_tac >>
  `LIST_REL dftLifting$dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks` by
    (irule dftLiftingTheory.dft_fn_block_rel >> gvs[o1_fn_shape_def, fn_shape_ok_def]) >>
  gvs[fn_insts_MEM] >> drule_all dft_blocks_rel_source >> strip_tac >>
  drule_all dftLiftingTheory.dft_block_rel_source >> strip_tac >> metis_tac[]
QED

Theorem dft_shape_special_source:
  o1_fn_shape ctx fn /\ MEM i (fn_insts (dft_fn fn)) /\
  MEM i.inst_opcode
    [ASSIGN; PHI; GAS; RETPC_PARAM; INVOKE; CALL; STATICCALL;
     RET; RETFMP; DRET; PARAM; FMP_PARAM; STOP; RETURN] ==>
  MEM i (fn_insts fn)
Proof
  strip_tac >> drule_all dft_shape_instruction_source >> strip_tac >> gvs[] >>
  drule flip_operands_special_opcode >> simp[]
QED

Theorem copy_phi_var_mono:
  (!i. MEM i (fn_insts output) /\
       MEM i.inst_opcode [origin; ASSIGN; PHI] ==> MEM i (fn_insts input)) ==>
  !x. copy_phi_var origin output x ==> copy_phi_var origin input x
Proof
  rpt strip_tac >> drule copy_phi_var_special_mono >> disch_then irule >>
  rpt strip_tac >> first_x_assum irule >> gvs[]
QED

Theorem dft_shape_copy_phi_var:
  o1_fn_shape ctx fn /\ MEM origin [GAS; RETPC_PARAM] ==>
  !x. copy_phi_var origin (dft_fn fn) x ==> copy_phi_var origin fn x
Proof
  rpt strip_tac >> irule copy_phi_var_mono >> qexists_tac `dft_fn fn` >>
  simp[] >> rpt strip_tac >>
  irule dft_shape_special_source >> gvs[] >> metis_tac[]
QED

Theorem opaque_use_not_flippable:
  retpc_use_ok i x ==> ~is_flippable i.inst_opcode
Proof
  Cases_on `i.inst_opcode` >>
  simp[retpc_use_ok_def, is_flippable_def,
       is_commutative_def, is_comparator_def]
QED

Theorem dft_shape_opaque_use:
  o1_fn_shape ctx fn ==> opaque_use_ok (dft_fn fn)
Proof
  strip_tac >> simp[opaque_use_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all dft_shape_instruction_source >>
  disch_then (qx_choose_then `j` (CONJUNCTS_THEN assume_tac)) >>
  `MEM (Var x) j.inst_operands` by
    gvs[flip_operands_operand_mem] >>
  `opaque_use_ok fn` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `!origin. MEM origin [GAS; RETPC_PARAM] /\
      copy_phi_var origin (dft_fn fn) x ==> copy_phi_var origin fn x` by
    (rpt strip_tac >> drule_all dft_shape_copy_phi_var >> simp[]) >>
  strip_tac >>
  `retpc_var fn x` by gvs[retpc_var_def] >>
  `retpc_use_ok j x` by metis_tac[opaque_use_ok_retpc_use] >>
  `~is_flippable j.inst_opcode` by metis_tac[opaque_use_not_flippable] >> gvs[]
QED

Theorem dft_shape_first_rel:
  o1_fn_shape ctx fn ==>
  dftLifting$dft_block_rel (HD fn.fn_blocks) (HD (dft_fn fn).fn_blocks)
Proof
  strip_tac >>
  `LIST_REL dftLifting$dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks` by
    (irule dftLiftingTheory.dft_fn_block_rel >> gvs[o1_fn_shape_def, fn_shape_ok_def]) >>
  `fn.fn_blocks <> []` by gvs[o1_fn_shape_def, wf_function_def, fn_has_entry_def] >>
  Cases_on `fn.fn_blocks` >> Cases_on `(dft_fn fn).fn_blocks` >>
  gvs[LIST_REL_def]
QED

Theorem dft_shape_first_no_phi:
  o1_fn_shape ctx fn ==> first_block_no_phi (dft_fn fn)
Proof
  strip_tac >> drule dft_shape_first_rel >> strip_tac >>
  `FILTER (\i. i.inst_opcode = PHI)
     (HD (dft_fn fn).fn_blocks).bb_instructions = []` suffices_by
    simp[first_block_no_phi_def, FILTER_EQ_NIL, EVERY_MEM] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM e (HD (dft_fn fn).fn_blocks).bb_instructions` >>
  `MEM e (FILTER (\i. is_pseudo i.inst_opcode)
     (HD (dft_fn fn).fn_blocks).bb_instructions)` by simp[MEM_FILTER, is_pseudo_def] >>
  `MEM e (HD fn.fn_blocks).bb_instructions` by
    (gvs[dftLiftingTheory.dft_block_rel_def] >> metis_tac[MEM_FILTER]) >>
  gvs[o1_fn_shape_def, first_block_no_phi_def, EVERY_MEM]
QED

Theorem dft_shape_first_no_preds:
  o1_fn_shape ctx fn ==> first_block_no_preds (dft_fn fn)
Proof
  strip_tac >> drule dft_shape_first_rel >> strip_tac >>
  `LIST_REL dftLifting$dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks` by
    (irule dftLiftingTheory.dft_fn_block_rel >> gvs[o1_fn_shape_def, fn_shape_ok_def]) >>
  simp[first_block_no_preds_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all dft_blocks_rel_source >> strip_tac >>
  `bb_succs bb = bb_succs a` by
    (irule dftLiftingTheory.dft_block_rel_succs >> gvs[o1_fn_shape_def, wf_function_def] >> metis_tac[]) >>
  gvs[dftLiftingTheory.dft_block_rel_def, o1_fn_shape_def, first_block_no_preds_def, EVERY_MEM] >>
  metis_tac[]
QED

(* The base's fn_shape_ok also asks for the return-PC shape and checked
   call flags; dft_fn keeps both on an SSA function. *)
Theorem dft_shape_retpc_shape:
  o1_fn_shape ctx fn /\ wf_ssa fn /\ fn_pseudos_prefix fn ==>
  retpc_shape_ok (dft_fn fn)
Proof
  strip_tac >> irule dft_fn_retpc_shape_ok >>
  gvs[o1_fn_shape_def, fn_shape_ok_def]
QED


Theorem dft_shape_fn_shape:
  o1_fn_shape ctx fn /\ wf_ssa fn /\ fn_pseudos_prefix fn ==>
  fn_shape_ok (dft_fn fn)
Proof
  strip_tac >> drule dft_shape_first_rel >> strip_tac >>
  `MAP (\b. b.bb_label) (dft_fn fn).fn_blocks =
   MAP (\b. b.bb_label) fn.fn_blocks` by simp[dft_fn_labels_map] >>
  `fn.fn_blocks <> []` by gvs[o1_fn_shape_def, wf_function_def, fn_has_entry_def] >>
  simp[fn_shape_ok_def] >> rpt conj_tac
  >- (Cases_on `fn.fn_blocks` >> Cases_on `(dft_fn fn).fn_blocks` >>
      gvs[o1_fn_shape_def, fn_shape_ok_def, fn_entry_label_def,
          entry_block_def, dftLiftingTheory.dft_block_rel_def, dft_fn_def] >>
      pairarg_tac >> simp[]) 
  >- metis_tac[dft_shape_opaque_use]
  >- metis_tac[dft_shape_retpc_shape]
  >- (`EVERY (\l. ~reserved_label l) (MAP (\b. b.bb_label) fn.fn_blocks)` by
        gvs[EVERY_MAP, o1_fn_shape_def, fn_shape_ok_def] >>
      `EVERY (\l. ~reserved_label l)
         (MAP (\b. b.bb_label) (dft_fn fn).fn_blocks)` by metis_tac[] >>
      gvs[EVERY_MAP])
  >> irule dft_fn_inst_shape >> gvs[o1_fn_shape_def, fn_shape_ok_def]
QED

Theorem dft_shape_invoke_ok:
  o1_fn_shape ctx fn ==> fn_invoke_ok (ctx_fn_names ctx) (dft_fn fn)
Proof
  strip_tac >> simp[fn_invoke_ok_def] >> rpt strip_tac >>
  `MEM inst (fn_insts fn)` by
    (irule dft_shape_special_source >> simp[] >> metis_tac[]) >>
  gvs[o1_fn_shape_def, fn_invoke_ok_def]
QED

Theorem dft_shape_label_refs_ok:
  o1_fn_shape ctx fn ==> fn_label_refs_ok (dft_fn fn)
Proof
  strip_tac >> simp[fn_label_refs_ok_def] >> rpt strip_tac >>
  drule_all dft_shape_instruction_source >> strip_tac >>
  `MEM (Label l) j.inst_operands /\ j.inst_opcode <> INVOKE` by
    (gvs[flip_operands_operand_mem] >>
     Cases_on `j.inst_opcode` >>
     gvs[is_flippable_def, is_commutative_def, is_comparator_def]) >>
  `MEM l (fn_labels fn) \/ reserved_label l` by
    (gvs[o1_fn_shape_def, fn_label_refs_ok_def] >> metis_tac[]) >>
  gvs[fn_labels_def, dft_fn_labels_map]
QED

Theorem dft_shape_opcode_exclusion:
  o1_fn_shape ctx fn /\
  EVERY (\i. ~MEM i.inst_opcode ops) (fn_insts fn) /\
  (!op. MEM op ops ==> MEM op
    [RET; RETFMP; DRET; PARAM; FMP_PARAM; RETPC_PARAM; STOP; RETURN]) ==>
  EVERY (\i. ~MEM i.inst_opcode ops) (fn_insts (dft_fn fn))
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM i (fn_insts (dft_fn fn))` >>
  `MEM i (fn_insts fn)` by
    (irule dft_shape_special_source >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem dft_shape_no_dret:
  o1_fn_shape ctx fn ==> no_dret (dft_fn fn)
Proof
  rw[no_dret_def] >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (irule dft_shape_special_source >> gvs[] >> metis_tac[]) >>
  gvs[o1_fn_shape_def, no_dret_def] >> metis_tac[]
QED

Theorem flip_operands_not_dalloca:
  is_flippable i.inst_opcode ==> (flip_operands i).inst_opcode <> DALLOCA
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  Cases_on `i.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def, is_comparator_def,
                      flip_comparison_opcode_def]
QED

(* Each block keeps its pseudo-instructions and the flips of the others
   are not parameters, so a block with no parameter instruction keeps
   none. *)
Theorem dft_shape_no_param_tl:
  o1_fn_shape ctx fn /\
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks) ==>
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL (dft_fn fn).fn_blocks)
Proof
  strip_tac >>
  `LIST_REL dftLifting$dft_block_rel fn.fn_blocks (dft_fn fn).fn_blocks` by
    (irule dftLiftingTheory.dft_fn_block_rel >> gvs[o1_fn_shape_def, fn_shape_ok_def]) >>
  `LIST_REL dftLifting$dft_block_rel (TL fn.fn_blocks) (TL (dft_fn fn).fn_blocks)` by
    (Cases_on `fn.fn_blocks` >> Cases_on `(dft_fn fn).fn_blocks` >> gvs[]) >>
  simp[EVERY_MEM, callLayoutDefsTheory.no_param_insts_def] >> rpt strip_tac >>
  rename1 `MEM b' (TL (dft_fn fn).fn_blocks)` >>
  rename1 `MEM i b'.bb_instructions` >>
  `?b. MEM b (TL fn.fn_blocks) /\ dftLifting$dft_block_rel b b'` by
    (gvs[LIST_REL_EL_EQN, MEM_EL] >> metis_tac[]) >>
  drule_all dftLiftingTheory.dft_block_rel_source >> strip_tac >> gvs[]
  >- (gvs[EVERY_MEM, callLayoutDefsTheory.no_param_insts_def] >> metis_tac[]) >>
  drule flip_operands_special_opcode >> gvs[is_param_opcode_iff]
QED

Theorem flip_operands_not_alloca:
  is_flippable i.inst_opcode ==> (flip_operands i).inst_opcode <> ALLOCA
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_flippable_def, is_commutative_def, is_comparator_def] >>
  Cases_on `i.inst_operands` >> simp[flip_operands_def] >>
  Cases_on `t` >> simp[flip_operands_def] >>
  Cases_on `t'` >> simp[flip_operands_def, is_comparator_def,
                      flip_comparison_opcode_def]
QED

(* A DALLOCA output of the schedule is one of the input's, and the
   schedule's GAS and return-PC closures are within the input's. *)
Theorem dft_shape_dalloca:
  o1_fn_shape ctx fn ==>
  !inst x. MEM inst (fn_insts (dft_fn fn)) /\ inst.inst_opcode = DALLOCA /\
           MEM x inst.inst_outputs ==>
           ~gas_var (dft_fn fn) x /\ ~retpc_var (dft_fn fn) x
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (drule_all dft_shape_instruction_source >> strip_tac >> gvs[] >>
     metis_tac[flip_operands_not_dalloca]) >>
  `!x. copy_phi_var GAS (dft_fn fn) x ==> copy_phi_var GAS fn x` by
    (drule dft_shape_copy_phi_var >> disch_then (qspec_then `GAS` mp_tac) >>
     simp[]) >>
  `!x. copy_phi_var RETPC_PARAM (dft_fn fn) x ==>
       copy_phi_var RETPC_PARAM fn x` by
    (drule dft_shape_copy_phi_var >>
     disch_then (qspec_then `RETPC_PARAM` mp_tac) >> simp[]) >>
  gvs[o1_fn_shape_def, gas_var_def, retpc_var_def] >> metis_tac[]
QED

Theorem dft_shape_o1_fn:
  o1_fn_shape ctx fn /\ wf_ssa fn /\ fn_pseudos_prefix fn ==>
  o1_fn_shape ctx (dft_fn fn)
Proof
  strip_tac >>
  `(dft_fn fn).fn_name = fn.fn_name` by
    (simp[dft_fn_def] >> pairarg_tac >> simp[]) >>
  simp[o1_fn_shape_def] >> rpt conj_tac
  >~ [`wf_function _`] >- (irule dft_fn_wf_function >> gvs[o1_fn_shape_def, fn_shape_ok_def])
  >~ [`fn_inst_wf _`] >- (irule dft_fn_inst_wf >> gvs[o1_fn_shape_def, fn_shape_ok_def])
  >~ [`fn_shape_ok _`] >- metis_tac[dft_shape_fn_shape]
  >~ [`first_block_no_preds _`] >- metis_tac[dft_shape_first_no_preds]
  >~ [`first_block_no_phi _`] >- metis_tac[dft_shape_first_no_phi]
  >~ [`fn_invoke_ok _ _`] >- metis_tac[dft_shape_invoke_ok]
  >~ [`fn_label_refs_ok _`] >- metis_tac[dft_shape_label_refs_ok]
  >~ [`no_dret`] >- metis_tac[dft_shape_no_dret]
  >~ [`DALLOCA`] >- metis_tac[dft_shape_dalloca]
  >~ [`_ ==> entry_fn_no_return _ /\ _`]
  >- (strip_tac >> conj_tac
      >- (pure_rewrite_tac[entry_fn_no_return_def] >>
          irule dft_shape_opcode_exclusion >>
          conj_tac >- (simp[] >> metis_tac[]) >>
          conj_tac >- gvs[o1_fn_shape_def, entry_fn_no_return_def] >>
          qexists_tac `ctx` >> simp[]) >>
      `EVERY (\i. ~MEM i.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM])
         (fn_insts (dft_fn fn))` suffices_by
        simp[entry_fn_no_params_def, is_param_opcode_iff] >>
      irule dft_shape_opcode_exclusion >>
      conj_tac >- (simp[] >> metis_tac[]) >>
      conj_tac >- gvs[o1_fn_shape_def, entry_fn_no_params_def, is_param_opcode_iff] >>
      qexists_tac `ctx` >> simp[]) >>
  strip_tac >>
  `EVERY (\i. ~MEM i.inst_opcode [STOP; RETURN]) (fn_insts (dft_fn fn))`
    suffices_by simp[] >>
  irule dft_shape_opcode_exclusion >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  conj_tac >- gvs[o1_fn_shape_def] >>
  qexists_tac `ctx` >> simp[]
QED

(* Proof summary:
   - Without SSA, dft_fn can drop an instruction (a block whose ADD reads
     its own output: nothing reaches it from the entries), but it never
     duplicates one (distinct ids, ds_visited) and every output
     instruction is an input one or its flip_operands
     (dft_block_from_orig, schedule_output_from_block).  So the output
     ids and labels are a subset of the input's (dft_fn_labels_map).
   - The terminator stays last: it has no outputs (inst_wf), so nothing
     depends on it (eda_deps_backward_plain needs only distinct ids); it
     is the last entry, so it is emitted last.  bb_succs reads the last
     instruction, so the CFG facts are unchanged.
   - Pseudos: the output is FILTER is_pseudo ++ schedule, and PHIs are
     already a prefix (bb_well_formed).
   - Flips touch two-operand ADD/MUL/OR/XOR/AND/EQ and GT/LT/SGT/SLT,
     keep arity and opcode class.  ADD [op; Label "code_end"] has at
     most one child, so it is never flipped (the flipped form would fail
     label_positions_ok).
   - The return-PC shape needs SSA (o1DftRetpc). *)
Theorem dft_step_contract_ssa:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  wf_ssa fn /\ fn_pseudos_prefix fn ==>
  o1_fn_shape observed.cu_context out.fpo_function /\
  fresh_names_ok s fn out.fpo_function /\
  label_map_sources_ok fn out.fpo_function out.fpo_label_map /\
  ir_supply_inst_ok out.fpo_supply
Proof
  simp[fn_pass_step_def] >> strip_tac >> gvs[] >>
  `MEM fn observed.cu_context.ctx_functions` by
    metis_tac[lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context fn` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  simp[label_map_sources_ok_def] >> conj_tac
  >- metis_tac[dft_shape_o1_fn] >>
  simp[fresh_names_ok_def, fn_labels_def, dft_fn_labels_map] >>
  metis_tac[dft_fn_ir_inst_ids_subset, o1_fn_shape_def, fn_shape_ok_def]
QED
