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
