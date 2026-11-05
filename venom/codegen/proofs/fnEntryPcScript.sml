(*
 * The PC of a function's region code is where its entry label resolves,
 * for fnEntryStep$fn_entry_block_step.
 *
 * TOP-LEVEL:
 *   entry_pc_placed - any PC holding region i's code is the one its entry
 *                     label resolves to
 *)

Theory fnEntryPc
Ancestors
  fnPlanPlace fnPlanPlaceFnRegion codegen asmSem symbolResolve planExec
  stackPlanGen

(* fn_region_placed puts region i's code at the PC the entry label
   resolves to; the code starts with AsmLabel of the entry label, which
   asm_symbols_ok (codegen_assembly) makes the only AsmLabel of that name,
   so any PC holding the region's code is that PC. *)
Theorem entry_pc_placed:
  !rpolicy unit cp prog ctx lo o2pc i fn r pc.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    asm_block_at prog pc (execute_plan cp.cp_initial_fmp r.sr_plan) ==>
    ?off. FLOOKUP lo (HD fn.fn_blocks).bb_label = SOME off /\
          FLOOKUP o2pc off = SOME pc
Proof
  cheat
QED
