(* Reached-successor continuation, independent of global frame simulations. *)
Theory symBodySuccessorPointwise
Ancestors
  symBodyAlgebra fnBlockBodySteps fnPlanLineage codegenSymOwnRel
  frameRel contextCodegenRel codegenRel venomExecSemantics

(* Parse-time abbreviations only: exports contain the expanded clauses. *)
val _ = Parse.temp_overload_on ("successor_entry_facts",
  ``\tbb ps_tdfs tops tafter pe ps_after vs1 vs bb t fn liveness dfg cfg ch growth spill_base lbl_ctr prog as1 cpl ctx lo ra rest mem0 Inv.
    pe = ps_tdfs with <| ps_stack := ps_after.ps_stack;
                         ps_spilled := ps_after.ps_spilled |> /\
    ~vs1.vs_halted /\ vs1.vs_labels = vs.vs_labels /\
    vs1.vs_call_ctx = vs.vs_call_ctx /\ vs1.vs_current_bb = t /\
    vs1.vs_prev_bb = SOME bb.bb_label /\ tbb.bb_label = t /\
    lookup_block vs1.vs_current_bb fn.fn_blocks = SOME tbb /\
    tbb <> HD fn.fn_blocks /\ fn_reachable fn tbb.bb_label /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label tbb.bb_label pe /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs1.vs_current_bb ps_tdfs /\
    generate_block_plan liveness dfg cfg fn tbb ps_tdfs = SOME (tops,tafter) /\
    asm_block_at prog as1.as_pc (execute_plan cpl.cp_initial_fmp tops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 pe vs1 as1 /\
    fn_entry_inv Inv ctx fn vs1 /\
    (!at. MEM at pe.ps_stack \/ at IN FDOM pe.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at))``);

val _ = Parse.temp_overload_on ("successor_body_clauses",
  ``\allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0 as ss res.
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps_mode allow_own prog env own n ss)) /\
    (!rv vs'. res = IntRet rv vs' ==>
       ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE rv.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as' /\
               sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
               asm_sym_rel_own lo prog env own as' ss' /\
               ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
               (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cpl b))``);

Theorem sym_body_jump_continue_pointwise:
  body_inv_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs as Inv
    ra pc_ret rest mem0 /\
  k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = inst /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst vs = OK vs1 /\ vs1 = jump_to t vs /\
  MEM t (get_successors inst) /\
  asm_steps lo o2pc prog n as = AsmOK as1 /\
  fn_frame_inv ctx cpl lo fn ra rest mem0 ps_after vs1 as1 /\
  (!at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
    operand_val (frame_view fn ra vs1) lo at =
    operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)) /\
  FLOOKUP lo t = SOME off /\ FLOOKUP o2pc off = SOME as1.as_pc /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  sym_steps_mode allow_own prog env own n ss = SymOK ss1 /\
  sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 ps_after as1 ss1 /\
  (?tbb ps_tdfs tops tafter pe.
    successor_entry_facts tbb ps_tdfs tops tafter pe ps_after vs1 vs bb t fn
      liveness dfg cfg ch growth spill_base lbl_ctr prog as1 cpl ctx lo ra rest mem0 Inv) /\
  (!tbb ps_tdfs tops tafter pe.
    successor_entry_facts tbb ps_tdfs tops tafter pe ps_after vs1 vs bb t fn
      liveness dfg cfg ch growth spill_base lbl_ctr prog as1 cpl ctx lo ra rest mem0 Inv /\
    sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 pe as1 ss1 ==>
    successor_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
      as1 ss1 (run_blocks fuel ctx fn vs1)) ==>
  ~vs1.vs_halted /\
  successor_body_clauses allow_own lo o2pc prog env own cpl ctx fn mem0 pc_ret rest srest labs0
    as ss (run_blocks fuel ctx fn vs1)
Proof
  strip_tac >>
  `sym_frame_inv_own lo prog env own ctx cpl fn ret srest labs0 pe as1 ss1` by
    (irule sym_frame_inv_plan_transport_own >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!tbb ps_tdfs tops tafter pe. _` (drule_all_then strip_assume_tac) >>
  conj_tac >- simp[] >>
  drule_all sym_body_runs_prefix_mode >> disch_then assume_tac >>
  rpt conj_tac >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`n + n'`, `as'`] >> simp[] >> metis_tac[]
QED
