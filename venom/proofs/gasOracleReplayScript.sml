(* A finite run can be replayed with an arbitrary unused GAS suffix.
   The consumed prefix includes zero readings after oracle exhaustion. *)
Theory gasOracleReplay
Ancestors
  stateEquiv venomExecSemantics venomState list

Theorem gas_oracle_replay:
  (!fuel ctx inst s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (step_inst fuel ctx inst s)
         (step_inst fuel ctx inst
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx bb s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (exec_block fuel ctx bb s)
         (exec_block fuel ctx bb
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx func s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (run_blocks fuel ctx func s)
         (run_blocks fuel ctx func
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail)))
Proof
  cheat
QED
