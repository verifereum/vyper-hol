(*
 * The generated assembly has the shape the frame simulation needs.
 *
 * TOP-LEVEL:
 *   codegen_assembly_frame_prog_ok
 *)

Theory codegenAsmProgOk
Ancestors
  asmFrameRel codegenEncodingWf codegen unitShapeDefs asmWf asmSem
  symbolResolve stackPlanGen stackPlanOps stackPlanTypes asmIR list rich_list
  arithmetic finite_map planExec venomInst pair

Theorem exec_stack_op_no_data[local]:
  EVERY (\i. ~is_data_inst i) (exec_stack_op fmp op)
Proof
  Cases_on `op` >> simp[exec_stack_op_def, is_data_inst_def, EVERY_REPLICATE] >>
  Cases_on `o'` >> simp[exec_stack_op_def, is_data_inst_def]
QED

Theorem execute_plan_no_data[local]:
  EVERY (\i. ~is_data_inst i) (execute_plan fmp ops)
Proof
  simp[execute_plan_def, EVERY_FLAT, EVERY_MAP, exec_stack_op_no_data]
QED

Theorem data_suffix_all_data[local]:
  EVERY is_data_inst (data_segment_asm segs ++ [AsmDataHeader "code_end"])
Proof
  simp[data_segment_asm_def, data_section_asm_def, EVERY_FLAT, EVERY_MAP,
       is_data_inst_def] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  Cases_on `di` >> simp[is_data_inst_def]
QED

Theorem data_suffix_prefix_indices[local]:
  EVERY (\x. ~is_data_inst x) xs /\ EVERY is_data_inst ys ==>
  !i. i < LENGTH (xs ++ ys) /\ ~is_data_inst (EL i (xs ++ ys)) ==>
  !j. j <= i ==> ~is_data_inst (EL j (xs ++ ys))
Proof
  rpt strip_tac >>
  `i < LENGTH xs` by
    (spose_not_then assume_tac >>
     gvs[EL_APPEND, EVERY_EL] >>
     first_x_assum (qspec_then `i - LENGTH xs` mp_tac) >> simp[]) >>
  `j < LENGTH xs` by decide_tac >>
  gvs[EL_APPEND, EVERY_EL]
QED

Theorem codegen_assembly_frame_prog_ok:
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit ==>
  asm_frame_prog_ok prog
Proof
  strip_tac >>
  `asm_encoding_wf prog` by
    metis_tac[codegen_assembly_asm_encoding_wf] >>
  simp[asm_frame_prog_ok_def] >>
  (qpat_x_assum `codegen_assembly _ _ = _` mp_tac >>
      simp[codegen_assembly_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      qspecl_then [`execute_plan plan.cp_initial_fmp (context_plan_ops plan)`,
        `data_segment_asm unit.cu_data_segment ++ [AsmDataHeader "code_end"]`]
        mp_tac (Q.GENL [`xs`, `ys`] data_suffix_prefix_indices) >>
      simp[execute_plan_no_data, data_suffix_all_data])
QED

(* Every generated context includes the executable revert postamble. *)
Theorem codegen_assembly_nonempty:
  codegen_assembly rpolicy unit = SOME prog ==> assemble prog <> []
Proof
  rw[codegen_assembly_def, AllCaseEqs()] >>
  gvs[context_plan_ops_def, execute_plan_def, MAP_APPEND, FLAT_APPEND,
      revert_postamble_def, exec_stack_op_def] >>
  simp[assemble_def, pairTheory.UNCURRY, MAP_APPEND, FLAT_APPEND, encode_inst_def]
QED
