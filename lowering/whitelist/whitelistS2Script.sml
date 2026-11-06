(* Whitelist removal, S2 leaves: the O1 source-unit shape facts without
   supported_program or raw_shape_free_program.

   lower_vyper_runtime_unit_source_unit_ok_full holds only once the O1 unit
   shape admits what the lowering emits for raw_call, create and calldata
   raw_call (DELEGATECALL, CREATE/CREATE2, DALLOCA; vyper-hol #963): until
   that widening it is false for those programs and stays admitted.
   lower_vyper_runtime_unit_defs_reach_uses_full is the S2b branch's
   theorem; it becomes a one-liner once that branch merges. *)
Theory whitelistS2
Ancestors
  vyperLoweringCorrect whitelistS2Shape whitelistS2RawBaseShape

Theorem lower_vyper_runtime_unit_source_unit_ok_full:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art
    ==> o1_source_unit_ok unit
Proof
  cheat
QED

Theorem lower_vyper_runtime_unit_o1_shape_extras_full:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art
    ==> unit_entry_no_params unit /\ unit_fmp_unsealed unit
Proof
  cheat
QED

Theorem lower_vyper_runtime_unit_defs_reach_uses_full:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit
    ==> unit_defs_reach_uses unit
Proof
  cheat
QED
