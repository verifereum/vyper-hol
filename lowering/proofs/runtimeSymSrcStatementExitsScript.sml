Theory runtimeSymSrcStatementExits
Ancestors
  runtimeSymSrcStatementLogs runtimeSymSrcStatementReasons
  runtimeSymSrcStatementReturns

(* Import-only boundary for the statement recursion proof.  The family
   theorems retain their literal primitive contracts and pointwise expression
   hypotheses; this aggregate neither assumes nor discharges those contracts.

   Constructor coverage (theorems are inherited, not duplicated here):
   Log:    runtime_sym_stmt_log
   Return: runtime_sym_return_none, runtime_sym_return_some
   Raise:  runtime_sym_stmt_raise_bare, runtime_sym_stmt_raise_unreachable,
           runtime_sym_stmt_raise_reason
   Assert: runtime_sym_stmt_assert_bare, runtime_sym_stmt_assert_unreachable,
           runtime_sym_stmt_assert_reason

   Supporting boundaries remain in their defining family theories:
   Logs: saving/evaluating arguments, splitting operands, topics and data.
   Reasons: reason-message construction and revert encoding are imported by
     runtimeSymSrcStatementReasons from their independently built theories.
   Returns: tuple loading, DRET operands, MCOPY guards, internal/external
     return dispatch, return unlocking and environment transport.
   In particular, the internal/external return contracts carried by
   runtime_sym_return_some are discharged by the return-family boundaries at
   the downstream join, not replaced by additional aggregate assumptions.
*)
