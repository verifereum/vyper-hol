(* Terms shared by the initializer observer and the replay at its cut. *)
structure groupedRejectCutLib =
struct
open HolKernel boolLib bossLib
open compileEnvTheory fragFuelTheory fragGasPathTheory relationTheory
     loweringStateRelDefsTheory venomInstTheory venomStateTheory
open runtimeDefaultRejectSyntaxLib

val row22_stopped = ``\ctx fn cut start.
  RTC (\u v. ~at_point cut u /\ ?n. gas_path_edge ctx fn u n (OK v)) start``;

val row22_opcode_ok = rhs (concl (DEPTH_CONV BETA_CONV
  ``\i:instruction. ^default_opcode i.inst_opcode``));

val row22_cut_facts = ``\ctx fn cut s entry.
  (!u bb i. ^row22_stopped ctx fn cut s u /\ ~at_point cut u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME i ==> ^row22_opcode_ok i) /\
  (!w. ^row22_stopped ctx fn cut s w /\ at_point cut w ==>
    fresh_vars_wrt entry w /\ w.vs_call_ctx = s.vs_call_ctx /\
    (!id e. FLOOKUP w.vs_allocas id = SOME e ==> id < entry.cs_next_id))``;
end
