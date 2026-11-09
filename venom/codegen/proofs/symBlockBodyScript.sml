(*
 * The rest of a function's run from inside one of its blocks, on the
 * symbolic machine: fnBlockBody's block_body_frame_sim with the symbolic
 * premises and conclusions added, over the same n steps.  Shared by the
 * two steps of the symbolic fuel induction (symFnStep).
 *
 * TOP-LEVEL:
 *   sym_body_result           - fnBlockBody's conclusion about a run
 *                               result, with the symbolic run
 *   sym_block_body_frame_sim  - the rest of the run, simulated
 *)
Theory symBlockBody
Ancestors
  symFrameBoundary symFrameControl symFrameInvoke symFrameInst symFnSimSpec
  codegenSymRel fnBlockBody fnBlockBodySteps fnSimSpec asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  venomExecSemantics venomState venomInst

(* block_body_frame_sim's conclusion (fnBlockBodySteps' body_result) with
   the symbolic run from ss over the same n steps: it ends where the
   concrete run halts, reverts or faults, and at an internal return it is
   OK, related, and holds the returned values as words above srest, with
   the memory labels outside the function's closure those of labs0. *)
Definition sym_body_result_def:
  sym_body_result lo o2pc prog env cpl ctx fn mem0 pc_ret rest srest labs0
      as ss res <=>
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\
               sym_steps prog env n ss = SymOK ss' /\
               asm_sym_rel prog env as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))
End

Theorem sym_body_result_error:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss e.
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Error e)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_ok:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss vs.
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (OK vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_halt:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss vs.
  (?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
     venom_asm_terminal_rel vs as' /\
     sym_terminal (sym_steps prog env n ss)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Halt vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_abort:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss a vs.
  (?n as'.
     ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
      (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
     venom_asm_terminal_rel vs as' /\
     sym_terminal (sym_steps prog env n ss)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (Abort a vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_intret:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as ss rv vs.
  (?n as' ss'.
     asm_steps lo o2pc prog n as = AsmOK as' /\
     as'.as_pc = pc_ret /\
     as'.as_stack = REVERSE rv.iret_values ++ rest /\
     context_memory_rel cp vs.vs_memory as'.as_memory /\
     (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          read_byte b as'.as_memory = read_byte b mem0) /\
     shared_state_rel vs as' /\
     sym_steps prog env n ss = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
     ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
     (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
     (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b)) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (IntRet rv vs)
Proof
  simp[sym_body_result_def]
QED

Theorem sym_body_result_prefix:
  !lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0 as as1 ss ss1 n res.
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  sym_steps prog env n ss = SymOK ss1 /\
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as1 ss1 res ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss res
Proof
  rpt gen_tac >> strip_tac >>
  `!m. asm_steps lo o2pc prog (n + m) as =
       asm_steps lo o2pc prog m as1` by
    metis_tac[stackOpSimTheory.asm_steps_add_ok] >>
  `!m. sym_steps prog env (n + m) ss = sym_steps prog env m ss1` by
    simp[sym_steps_add] >>
  gvs[sym_body_result_def] >> rpt conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`n' + n`, `as'`] >> simp[] >> metis_tac[]
QED

Theorem sym_body_result_exec:
  !fuel ctx bb vs lo o2pc prog env cp fn mem0 pc_ret rest srest labs0 as ss.
  (!t. exec_block fuel ctx bb vs <> OK t) /\
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (exec_block fuel ctx bb vs) ==>
  sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
    as ss (block_rest fuel ctx fn bb vs)
Proof
  rpt gen_tac >> strip_tac >> simp[block_rest_def] >>
  Cases_on `exec_block fuel ctx bb vs` >> gvs[]
QED

Theorem sym_frame_inv_plan_transport:
  !ps' ps prog env ctx cp fn ret srest labs0 cs ss.
  ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps cs ss ==>
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps' cs ss
Proof
  simp[sym_frame_inv_def, sym_kinds_ok_def]
QED

Theorem codegen_sym_code_end_label:
  codegen_assembly rpolicy unit = SOME prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "code_end"
Proof
  simp[codegenTheory.codegen_assembly_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> simp[sym_data_label_def]
QED

Theorem data_segment_asm_header:
  !segs ds. MEM ds segs ==>
    MEM (AsmDataHeader ds.ds_label) (data_segment_asm segs)
Proof
  Induct >> simp[asmIRTheory.data_segment_asm_def,
                 asmIRTheory.data_section_asm_def] >>
  metis_tac[asmIRTheory.data_segment_asm_def]
QED

Theorem codegen_sym_runtime_begin_label:
  codegen_assembly rpolicy unit = SOME prog /\
  sym_unit_static_ok unit /\ MEM fn unit.cu_context.ctx_functions /\
  MEM inst (fn_insts fn) /\ MEM (Label "runtime_begin") inst.inst_operands /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) ==>
  sym_data_label prog env "runtime_begin"
Proof
  rpt strip_tac >>
  `EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment` by
    metis_tac[sym_unit_static_ok_def] >>
  gvs[listTheory.EXISTS_MEM] >>
  `MEM (AsmDataHeader "runtime_begin") (data_segment_asm unit.cu_data_segment)` by
    metis_tac[data_segment_asm_header] >>
  gvs[codegenTheory.codegen_assembly_def, AllCaseEqs()] >>
  simp[sym_data_label_def]
QED

Theorem placed_nonentry_sym_code_label:
  !bb fn liveness dfg cfg ps ops ps' prog pc initial_fmp.
  bb <> HD fn.fn_blocks /\
  generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') /\
  asm_block_at prog pc (execute_plan initial_fmp ops) ==>
  MEM (AsmLabel bb.bb_label) prog
Proof
  rpt strip_tac >>
  drule_all fnBlockStepHelpersTheory.generate_block_plan_nonentry >>
  strip_tac >> gvs[] >>
  irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >>
  simp[planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

Theorem placed_revert_sym_code_label:
  asm_block_at prog pc (execute_plan initial_fmp revert_postamble) ==>
  MEM (AsmLabel "revert") prog
Proof
  strip_tac >> irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >>
  simp[stackPlanGenTheory.revert_postamble_def,
       planExecTheory.execute_plan_def, planExecTheory.exec_stack_op_def]
QED

(* body_inv bundles block_body_frame_sim's premises. *)
Theorem sym_block_body_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
   spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs block_ops
   ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv ra pc_ret
   rest mem0 env ret srest labs0 ss.
    gen_fn_sim_at fuel /\ gen_fn_frame_sim_at fuel /\
    sym_fn_sim_at fuel /\ sym_fn_frame_sim_at fuel /\
    body_inv rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
      ra pc_ret rest mem0 /\
    (* ----- The symbolic side ----- *)
    label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
    sym_unit_static_ok unit /\ asm_static_wf prog /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    sym_body_result lo o2pc prog env cp ctx fn mem0 pc_ret rest srest labs0
      as ss (block_rest fuel ctx fn bb vs)
Proof
  cheat
QED
