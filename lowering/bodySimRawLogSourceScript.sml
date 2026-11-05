(* Forced source action boundary for the counted body simulation. *)
Theory bodySimRawLogSource
Ancestors
  exprSimRawLog gasExemptCert vyperInterpreter vyperState vyperValue
Libs
  pairLib

Theorem raw_log_forced_source_eval:
  LENGTH topics <= n /\ ~cx.txn.is_static ==>
  (do r <- eval_expr cx
      (Call ann RawLog
        [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
         data] dflt);
      read_result cx r
   od) =
  (do vs <- eval_exprs cx topics;
      dv <- (do tv <- eval_expr cx data; read_result cx tv od);
      bs <- lift_option_type (dest_BytesV dv) "raw_log data";
      type_check (LENGTH vs <= 4) "raw_log too many topics";
      push_log (encode_raw_event_values cx.txn.target vs bs);
      return NoneV
   od)
Proof
  strip_tac >>
  `eval_expr cx
      (Call ann RawLog
        [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
         data] dflt) =
   (do vs <- eval_exprs cx topics;
       dv <- (do tv <- eval_expr cx data; read_result cx tv od);
       bs <- lift_option_type (dest_BytesV dv) "raw_log data";
       type_check (LENGTH vs <= 4) "raw_log too many topics";
       push_log (encode_raw_event_values cx.txn.target vs bs);
       return (Value NoneV)
    od)` by simp[FUN_EQ_THM, raw_log_source_eval] >>
  simp[bind_assoc, ignore_bind_def, bind_return, read_result_def]
QED

