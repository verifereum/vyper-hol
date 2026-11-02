Theory concretizeAnalysisSupport
Ancestors concretizeAnalysisRoots concretizeAnalysisBoundary pointerClosure
  ptrDiscipline pointerConfinedDefs basePtrDefs basePtrProofs
  concretizeMemLocDefs cfgNormBase execEquivParamBase list pred_set finite_map venomInst

Definition bp_supported_def:
  bp_supported pv r <=> !v. bp_get_ptrs r v <> [] ==> v IN pv
End

Theorem bp_supported_outside:
  bp_supported pv r /\ v NOTIN pv ==> bp_get_ptrs r v = []
Proof
  metis_tac[bp_supported_def]
QED

Theorem bp_supported_update:
  bp_supported pv r /\ (ps <> [] ==> out IN pv) ==>
  bp_supported pv (r |+ (out, ps))
Proof
  rw[bp_supported_def, bp_get_ptrs_update] >> metis_tac[]
QED

Theorem bp_supported_inst:
  bp_supported pv r /\ MEM inst (fn_insts fn) /\
  alloca_roots fn SUBSET pv /\
  (!i u v. MEM i (fn_insts fn) /\
     is_pointer_preserving_op i.inst_opcode /\
     MEM (Var u) i.inst_operands /\ u IN pv /\
     MEM v i.inst_outputs ==> v IN pv) ==>
  bp_supported pv (SND (bp_handle_inst r inst))
Proof
  strip_tac >>
  Cases_on `inst_output inst`
  >- simp[bp_handle_inst_def] >>
  rename1 `inst_output inst = SOME out` >>
  `MEM out inst.inst_outputs` by
    (gvs[inst_output_def, AllCaseEqs()] >> simp[]) >>
  `!u. MEM (Var u) inst.inst_operands /\ bp_get_ptrs r u <> [] /\
       is_pointer_preserving_op inst.inst_opcode ==> out IN pv` by
    metis_tac[bp_supported_def] >>
  Cases_on `inst.inst_opcode` >>
  simp[bp_handle_inst_def]
  >~ [`is_pointer_preserving_op ALLOCA`] >-
    (irule bp_supported_update >> simp[] >>
     gvs[SUBSET_DEF, alloca_roots_def] >> metis_tac[])
  >~ [`is_pointer_preserving_op PHI`] >-
    (Cases_on `bp_normalize (bp_get_ptrs r out ++
       FLAT (MAP (bp_get_ptrs r) (MAP SND (phi_pairs inst.inst_operands)))) = []`
     >- simp[] >>
     simp[] >> irule bp_supported_update >> simp[] >>
     Cases_on `bp_get_ptrs r out = []`
     >- (gvs[bp_normalize_eq_nil, FLAT_EQ_NIL, EVERY_MAP, EVERY_MEM,
             MEM_MAP, is_pointer_preserving_op_def] >>
         metis_tac[phi_pairs_mem_var, pairTheory.PAIR]) >>
     metis_tac[bp_supported_def]) >>
  all_tac
  >~ [`is_pointer_preserving_op ASSIGN`] >-
    (Cases_on `inst.inst_operands` >> gvs[] >>
     rename1 `inst.inst_operands = h::t` >>
     Cases_on `t` >> gvs[] >> Cases_on `h` >> gvs[] >>
     irule bp_supported_update >>
     gvs[is_pointer_preserving_op_def] >> metis_tac[]) >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = h::t` >>
  Cases_on `t` >> gvs[] >>
  rename1 `inst.inst_operands = h::h2::t2` >>
  Cases_on `t2` >> gvs[] >>
  Cases_on `h` >> Cases_on `h2` >> gvs[] >>
  rpt IF_CASES_TAC >> simp[] >>
  irule bp_supported_update >>
  gvs[is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem bp_supported_fn_inst:
  bp_supported (fn_pv P fn) r /\ MEM inst (fn_insts fn) ==>
  bp_supported (fn_pv P fn) (SND (bp_handle_inst r inst))
Proof
  strip_tac >> irule bp_supported_inst >> simp[] >>
  qexists `fn` >> simp[fn_pv_def] >> conj_tac
  >- metis_tac[pointer_derived_vars_closed, ptr_roots_finite] >>
  irule SUBSET_TRANS >> qexists `ptr_roots P fn` >>
  simp[pointer_derived_vars_roots, ptr_roots_finite, ptr_roots_def, SUBSET_DEF]
QED

Theorem bp_supported_fn_block:
  !insts r. bp_supported (fn_pv P fn) r /\
    EVERY (\i. MEM i (fn_insts fn)) insts ==>
    bp_supported (fn_pv P fn) (SND (bp_process_block r insts))
Proof
  Induct >> simp[bp_process_block_def] >> rpt strip_tac >>
  Cases_on `bp_handle_inst r h` >> simp[] >>
  pairarg_tac >> simp[] >>
  drule_all bp_supported_fn_inst >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem bp_supported_fn_pass_aux:
  !order r. bp_supported (fn_pv P fn) r ==>
    bp_supported (fn_pv P fn) (SND (bp_one_pass_aux fn r order))
Proof
  Induct >> simp[bp_one_pass_aux_def] >> rpt strip_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks`
  >- (simp[] >> first_x_assum irule >> simp[]) >>
  rename1 `_ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[execEquivParamBaseTheory.FIND_MEM] >>
  `EVERY (\i. MEM i (fn_insts fn)) bb.bb_instructions` by
    (simp[EVERY_MEM] >> metis_tac[allocaRemapSSATheory.mem_fn_insts_intro]) >>
  drule_all bp_supported_fn_block >> strip_tac >>
  Cases_on `bp_process_block r bb.bb_instructions` >> gvs[] >>
  pairarg_tac >> simp[] >> first_x_assum drule >> simp[]
QED

Theorem bp_supported_fn_fuel:
  !n r. bp_supported (fn_pv P fn) r ==>
    bp_supported (fn_pv P fn) (bp_iterate_fuel n fn order r)
Proof
  Induct >> simp[bp_iterate_fuel_def] >> rpt strip_tac >>
  `bp_supported (fn_pv P fn) (SND (bp_one_pass fn order r))` by
    simp[bp_one_pass_def, bp_supported_fn_pass_aux] >>
  Cases_on `bp_one_pass fn order r` >> gvs[] >>
  Cases_on `q` >> simp[]
QED

Theorem bp_supported_production:
  bp_supported (fn_pv P fn) (bp_iterate_fuel n fn order FEMPTY)
Proof
  irule bp_supported_fn_fuel >> simp[bp_supported_def, bp_get_ptrs_def]
QED
