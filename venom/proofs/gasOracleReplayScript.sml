(* A finite run can be replayed with an arbitrary unused GAS suffix.
   The consumed prefix includes zero readings after oracle exhaustion. *)
Theory gasOracleReplay
Ancestors
  stateEquiv venomExecSemantics venomState list

Theorem gas_oracle_replay:
  (!fuel ctx inst s.
     ?prefix. !tail.
       lift_result
         (\a b. b = (a with vs_gas_readings := tail))
         (\a b. b = (a with vs_gas_readings := tail))
         (\a b. b = (a with vs_gas_readings := tail))
         (step_inst fuel ctx inst s)
         (step_inst fuel ctx inst
           (s with vs_gas_readings := prefix ++ tail))) /\
  (!fuel ctx bb s.
     ?prefix. !tail.
       lift_result
         (\a b. b = (a with vs_gas_readings := tail))
         (\a b. b = (a with vs_gas_readings := tail))
         (\a b. b = (a with vs_gas_readings := tail))
         (exec_block fuel ctx bb s)
         (exec_block fuel ctx bb
           (s with vs_gas_readings := prefix ++ tail))) /\
  (!fuel ctx func s.
     ?prefix. !tail.
       lift_result
         (\a b. b = (a with vs_gas_readings := tail))
         (\a b. b = (a with vs_gas_readings := tail))
         (\a b. b = (a with vs_gas_readings := tail))
         (run_blocks fuel ctx func s)
         (run_blocks fuel ctx func
           (s with vs_gas_readings := prefix ++ tail)))
Proof
  cheat
QED
