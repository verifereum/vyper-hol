(* Static origins of staged memory arguments, independent of execution. *)
Theory bodyIntCallStageOrigin
Ancestors
  exprLowering exprLoweringProps loweringHalt context compileEnv
  list arithmetic
Libs
  monadsyntax

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem stage_intcall_args_length:
  !es flags tys a ops b.
    compile_stage_intcall_args cfn ce es flags tys a = (ops,b) ==>
    LENGTH ops = LENGTH es
Proof
  cheat
QED

(* RESTATED (train 17): 0.5.0b1 per-argument staging *)
Theorem stage_intcall_memory_origin:
  !es flags tys a ops b i.
    (!ce' ty' e' s'. ci_mono s' (SND (cfn ce' ty' e' s'))) /\
    LENGTH es <= LENGTH flags /\ LENGTH es <= LENGTH tys /\
    compile_stage_intcall_args cfn ce es flags tys a = (ops,b) /\
    i < LENGTH es /\ ~EL i flags ==>
    ?pre post buf.
      compile_alloc_buffer (MAX 32 (type_memory_bytes ce (EL i tys))) pre =
        (buf,post) /\
      EL i ops = buf.buf_operand /\
      a.cs_next_id <= pre.cs_next_id /\ pre.cs_next_id < b.cs_next_id
Proof
  cheat
QED


