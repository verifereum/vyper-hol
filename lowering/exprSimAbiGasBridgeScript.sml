(*
 * Counted paths for GAS-free fragments.
 *
 * frag_exec and abi_decode_sim say what running a fragment reaches, as a
 * run_from simulation; the counted expression judgments need an actual
 * gas_marked_path to that state.  For a fragment that runs no GAS, INVOKE
 * or PHI and never jumps back to the block it starts in, the fragment
 * judgment gives such a path, with a count of 0.
 *)

Theory exprSimAbiGasBridge
Ancestors
  fragGasMode fragExec exprLoweringProps abiDecoderLoop

(* The code a fragment emitted: the instructions after sa's position in the
   block it started, every block it finished after that, and the
   instructions of the block it left open. *)
Definition frag_code_def:
  frag_code (sa:compile_state) (sb:compile_state) =
    let new = emitted_blocks sa sb in
    if NULL new then emitted_insts sa sb
    else DROP (LENGTH sa.cs_current_insts) (LAST new).bb_instructions ++
         FLAT (MAP (\bb. bb.bb_instructions) (FRONT new)) ++
         sb.cs_current_insts
End

(* The fragment runs no GAS, INVOKE or PHI, never jumps back to the block
   it starts in, and leaves open a block of a label it did not finish. *)
Definition frag_gas_free_def:
  frag_gas_free (sa:compile_state) (sb:compile_state) <=>
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               i.inst_opcode <> PHI /\
               ~MEM (Label sa.cs_current_bb) i.inst_operands)
          (frag_code sa sb) /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (emitted_blocks sa sb))
End

(* The run_from simulation of frag_exec, taken in a function where the
   fragment's end is followed by STOP, is an actual path in every function
   that has the fragment's code.  Q may not depend on vs_returndata, which
   that STOP clears; R accepts no Halt, so that the STOP is never mistaken
   for an exit of the fragment. *)
Theorem frag_exec_gas_path:
  !ctx sa sb P Q R fn s.
    frag_exec ctx sa sb P Q R /\ cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\ (!h. ~R (Halt h)) /\
    fn_has_code sa sb fn /\ P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  cheat
QED

(* The same for a fragment proved in the abi_decode_sim form, such as the
   ABI encoder and decoder executions. *)
Theorem abi_decode_sim_gas_path:
  !ctx sa sb Q fn s.
    (!fn. fn_has_code sa sb fn ==>
       ?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           abi_decode_sim ctx fn s t) /\
    cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    fn_has_code sa sb fn /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  cheat
QED
