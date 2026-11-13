(* Textual target-only forwarding certificate; no HOL definition. *)
structure lowerDloadForwardingPackageLib =
struct
open HolKernel boolLib bossLib
open lowerDloadTerminalSafetyTheory
val ld_forward = ``\(ctx:venom_context) fn ti t.
  ?bb i j. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ i <= t.vs_inst_idx /\
    t.vs_inst_idx <= j /\ get_instruction bb t.vs_inst_idx = SOME ti /\
    t.vs_alloca_next < dimword (:256)``;
end
