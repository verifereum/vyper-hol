(* Error-post boundary for the extcall falsehood audit. *)
Theory abiExtcallErrorPostProbe
Ancestors
  exprSimDefs

Theorem expr_exit_OK_false[simp]:
  !res s. ~expr_exit res (OK s)
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  rename1 `INR ex` >> Cases_on `ex` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* Sufficient exclusion contract for a full witness (not yet proved here):
   S = eval_expr cx call, start = (es,s0), m = "abi_decode invalid".
   1. !gs. S (es with gas_obs := gs) =
        (INR (Error (RuntimeError m)), ee with gas_obs := gs).
      This source has explicit literal gas and performs no gas reads.
   2. !n a t. ~gas_path ctx func s0 n (Abort a t).
      A successful helper prefix is insufficient: func must include a safe
      tail after the compiled slice. Choose STOP; prove an actual Halt run
      and use gas_path_exit plus fuel_mono to exclude every Abort run.
   3. ~unspecified_behaviour_exempt (cx_tops cx) (RuntimeError m).
      It suffices that tops has no occurs_abi_decode_target witness (e.g. []).
   For every marks, gas_marked_exec_def with tail=[] and (1) pins res to
   the source error. The normal post in expr_sim/expr_vv_sim requires INL,
   so is impossible, and expr_exit requires Abort, ruled out by (2).
   gas_marked_path_exec removes memory-mode wrapping for (2).
   In the exemption disjunct, gas_exempt_cert_execution with tail=[] and
   ignore_bind_def pins err to RuntimeError m; its classified exemption
   contradicts (3), regardless of marks, leaf, finish or focused prefixes.
   This contracts all target tails and both gas_outcome alternatives; no
   finite-prefix success is being advertised as their exclusion. *)
