(* A straight-line path through a block suffix cannot change an old taint
   lookup when no instruction in the suffix writes that variable. *)
Theory selectedArrayInitTaintFrame
Ancestors
  fragGasPathPtr ptrSafeRun ptrTaintClean ptrDiscipline venomInst venomInstProofs
  fragExec venomState finite_map list arithmetic rich_list algebraicOptCmpBlockProofs

Theorem gas_path_ptr_suffix_taint_frame:
  !is s G tn m H u t.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                 ~MEM x i.inst_outputs) is /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = is /\
    gas_path_ptr D lo ctx fn PG G tn s m H u (OK t) ==>
    FLOOKUP u.t_var x = FLOOKUP tn.t_var x
Proof
  Induct_on `is` >> rpt gen_tac >> strip_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
        (mp_tac o SRULE [Once gas_path_ptr_cases, exit_result_def]) >>
      simp[] >> rpt strip_tac >>
      gvs[gas_path_ptr_edge_def, get_instruction_def]) >>
  fs[EVERY_DEF] >> drule ao_cmp_get_instruction_drop >> strip_tac >>
  qpat_x_assum `gas_path_ptr D lo ctx fn PG G tn s m H u (OK t)`
    (mp_tac o SRULE [Once gas_path_ptr_cases, exit_result_def]) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_path_ptr_edge_def] >> rpt strip_tac >> gvs[exit_result_def] >>
  TRY (qpat_assum `OK _ = step_inst _ _ _ _` (SUBST1_TAC o SYM) >> NO_TAC) >>
  TRY (qpat_x_assum `exit_result _` mp_tac >>
       qpat_assum `OK _ = step_inst _ _ _ _` (SUBST1_TAC o SYM) >>
       simp[exit_result_def] >> NO_TAC) >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  drule_all ghost_step_non_invoke >> strip_tac >>
  gvs[] >>
  qpat_assum `!s'' G' tn' m' H' u' t'. _`
    (fn ih => qpat_assum `gas_path_ptr D lo ctx fn PG (step_prov PG G h _) (step_taint h s _ tn) _ _ H u (OK t)`
      (mp_then (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) mp_tac ih)) >>
  simp[step_taint_def, set_var_taint_lookup]
QED
