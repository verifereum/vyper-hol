(* Assembly call completion interface. Reuse the shared oracle contracts;
 * keep tuple normalization and generic list splicing out of consumers.
 * No running/terminal relation is strengthened in TASK041. *)
Theory asmCallOracleProps
Ancestors
  asmSem extCallOracle list rich_list arithmetic pair

(* This single normalization fact transports every untouched record field,
 * including future fields, without a selector-by-selector frame API. *)
Theorem asm_consume_call_outcome_eq:
  asm_consume_call_outcome rq ro rs stk s =
    let outcome = FST (take_outcome rq s.as_outcomes);
        adopted = adopt_outcome rq outcome
          (s.as_accounts, s.as_transient, s.as_logs);
        bytes = TAKE rs outcome.co_returnData
    in AsmOK (asm_next (s with <|
      as_stack := (if outcome.co_success then 1w else 0w) :: stk;
      as_outcomes := SND (take_outcome rq s.as_outcomes);
      as_requests := record_request rq s.as_requests;
      as_accounts := FST adopted;
      as_transient := FST (SND adopted);
      as_logs := SND (SND adopted);
      as_returndata := outcome.co_returnData;
      as_memory := TAKE ro s.as_memory ++ bytes ++
                   DROP (ro + LENGTH bytes) s.as_memory |>))
Proof
  simp[asm_consume_call_outcome_def] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[]
QED

(* Generic byte-list splice contract: no lost/shifting suffix. Applicable
 * to all memory writers, not just CALL or one particular return size. *)
Theorem overwrite_prefix_length_suffix:
  off + LENGTH bytes <= LENGTH mem ==>
  LENGTH (TAKE off mem ++ bytes ++ DROP (off + LENGTH bytes) mem) = LENGTH mem /\
  DROP (off + LENGTH bytes)
    (TAKE off mem ++ bytes ++ DROP (off + LENGTH bytes) mem) =
  DROP (off + LENGTH bytes) mem
Proof
  strip_tac >> simp[LENGTH_TAKE, LENGTH_DROP, DROP_APPEND] >>
  `MIN off (LENGTH mem) = off` by simp[MIN_DEF] >> simp[]
QED

Theorem asm_step_call_staticcall_gas:
  asm_step lo otp (AsmOp "CALL") s = asm_exec_call s.as_call_ctx.cc_static s /\
  asm_step lo otp (AsmOp "STATICCALL") s = asm_exec_staticcall s /\
  asm_step lo otp (AsmOp "GAS") s = asm_gas s
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def]
QED

Theorem asm_calls_ignore_forwarded_gas:
  asm_exec_call is_static
    (s with as_stack := g1::addr::value::ao::asz::ro::rs::stk) =
  asm_exec_call is_static
    (s with as_stack := g2::addr::value::ao::asz::ro::rs::stk) /\
  asm_exec_staticcall
    (s with as_stack := g1::addr::ao::asz::ro::rs::stk) =
  asm_exec_staticcall
    (s with as_stack := g2::addr::ao::asz::ro::rs::stk)
Proof
  simp[asm_exec_call_def, asm_exec_staticcall_def, asm_call_request_def,
       asm_consume_call_outcome_eq]
QED
