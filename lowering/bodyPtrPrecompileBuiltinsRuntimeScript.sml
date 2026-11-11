(* Normalize the S1 request-equality interface once for pointer consumers. *)
Theory bodyPtrPrecompileBuiltinsRuntime
Ancestors exprSimPrecompiles venomCallOracleDefs exprLoweringProps exprSimHash
          venomExecSemantics venomInstProofs venomInst venomState finite_map

Theorem computed_static_exec_eq:
  computed_precompile (venom_call_request s addr 0w ai an T) /\
  inst.inst_outputs = [out] ==>
  exec_ext_call inst s gas addr 0w ai an ro rs T =
    OK (update_var out
      (if (FST (take_outcome (venom_call_request s addr 0w ai an T)
              s.vs_outcomes)).co_success then 1w else 0w)
      ((write_memory_with_expansion (w2n ro)
        (TAKE (w2n rs)
          (FST (take_outcome (venom_call_request s addr 0w ai an T)
                 s.vs_outcomes)).co_returnData) s)
       with <|vs_returndata :=
          (FST (take_outcome (venom_call_request s addr 0w ai an T)
                 s.vs_outcomes)).co_returnData;
              vs_outcomes := DROP 1 s.vs_outcomes|>))
Proof
  ACCEPT_TAC (Q.INST [`rq` |-> `venom_call_request s addr 0w ai an T`]
    computed_static_exec |> SIMP_RULE bool_ss [])
QED

Theorem computed_static_exec_ok:
  computed_precompile (venom_call_request s addr 0w ai an T) /\
  inst.inst_outputs = [out] ==>
  ?t. exec_ext_call inst s gas addr 0w ai an ro rs T = OK t
Proof
  strip_tac >> drule_all computed_static_exec_eq >> simp[]
QED

Theorem computed_call_prefix:
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\
  eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s addr 0w wi an T) ==>
  ?t. run_inst_seq
    [mk_inst id GAS [] [gv];
     mk_inst (id+1) STATICCALL
       [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv]] s = OK t
Proof
  strip_tac >> simp[run_inst_seq_def, step_GAS] >>
  qmatch_goalsub_abbrev_tac `step_inst_base ci u` >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    (simp[Abbr `u`, update_var_def, venom_call_request_def] >>
     gvs[venom_call_request_def, read_memory_def]) >>
  `eval_operand (Var src) u = SOME wi /\
   eval_operand (Var dst) u = SOME wo /\
   eval_operand (Var gv) u = SOME (HD (s.vs_gas_readings ++ [0w]))` by
    gvs[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `?t. exec_ext_call ci u (HD (s.vs_gas_readings ++ [0w]))
      addr 0w wi an wo rn T = OK t` by
    (irule computed_static_exec_ok >> simp[Abbr `ci`, mk_inst_def]) >>
  gvs[Abbr `ci`, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]
QED
