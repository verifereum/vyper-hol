(*
 * The symbolic machine runs a planner prefix (stack shuffles, spills and
 * restores) without a SymBad, keeping the kinds of the frame's values.
 * Purely symbolic: no Venom state and no concrete assembly state.  The
 * concrete side comes from codegen's own prefix simulation and
 * asm_sym_steps_lockstep.
 *)
Theory symShuffleSim
Ancestors
  codegenSymRel mixedPrefixSim strongPrefixSim prefixExec prefixSim planExec
  contextCodegenRel asmSymSem asmSem stackPlanTypes

(* A prefix of planner ops with no SOPushOfst (codegen emits one only for
   OFFSET, which unit_shape_ok excludes), whose spills write inside the
   byte set R and the context's spill regions, steps symbolically to the
   state the planner predicts, kinds kept and the label bytes outside R
   unchanged. *)
Theorem sym_prefix_ops_sim:
  !ops initial_fmp lo p env cp fn ret srest R ps ss.
    prefix_wf lo (LENGTH ps.ps_stack) ops /\
    prefix_spill_wf initial_fmp lo ops ps /\
    EVERY is_prefix_op ops /\
    EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
    (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
       R b /\ context_spill_byte cp b) /\
    sym_kinds_ok cp fn ret srest ps ss /\
    asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
    ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss =
            SymOK ss' /\
          sym_kinds_ok cp fn ret srest
            (apply_prefix_ops initial_fmp lo ops ps) ss' /\
          ss'.sym_base.as_pc =
            ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
          (!b. ~R b ==>
               FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  cheat
QED
