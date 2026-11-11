(* Retained fragment code is distinct from execution-local region safety. *)
Theory exprSimAbiEncodeCompatibility
Ancestors
  fragExec fcgDefs venomInst venomExecSemantics venomExecProofs
  list rich_list

Theorem abi_encode_retained_current:
  fn_has_code st st' obs /\ MEM i st'.cs_current_insts ==>
  MEM i (fn_insts obs)
Proof
  rw[fn_has_code_def]
  >> irule lookup_block_fn_insts
  >> goal_assum (drule_at Any)
  >> irule IS_PREFIX_MEM >> metis_tac[]
QED

Theorem abi_encode_retained_block:
  fn_has_code st st' obs /\ MEM bb (emitted_blocks st st') /\
  MEM i bb.bb_instructions ==> MEM i (fn_insts obs)
Proof
  rw[fn_has_code_def] >> irule lookup_block_fn_insts >> metis_tac[]
QED

Theorem abi_encode_retained_invoke:
  fn_has_code st st' obs /\ MEM i st'.cs_current_insts /\
  i.inst_opcode = INVOKE ==>
  ~(!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE)
Proof
  metis_tac[abi_encode_retained_current]
QED

(* Callees need not be registered: only the caller lookup matters. *)
Theorem abi_encode_retained_call_edge:
  fn_has_code st st' obs /\ MEM i st'.cs_current_insts /\
  i.inst_opcode = INVOKE /\ i.inst_operands = Label target :: rest /\
  lookup_function obs.fn_name ctx.ctx_functions = SOME obs ==>
  fn_directly_calls ctx obs.fn_name target
Proof
  strip_tac >> simp[fn_directly_calls_def]
  >> qexistsl_tac [`i`, `rest`]
  >> simp[] >> irule abi_encode_retained_current >> metis_tac[]
QED

Theorem abi_encode_singleton_no_edges:
  ctx.ctx_functions = [obs] ==>
  ((!a b. ~fn_directly_calls ctx a b) <=>
   (!i target rest. MEM i (fn_insts obs) /\ i.inst_opcode = INVOKE ==>
      i.inst_operands <> Label target :: rest))
Proof
  simp[fn_directly_calls_def, lookup_function_def, FIND_thm,
       AllCaseEqs()]
  >> metis_tac[]
QED

Theorem abi_encode_singleton_invoke_edge_probe:
  fn_directly_calls
    (ctx with ctx_functions := [fn with
       <|fn_name := "observer"; fn_blocks :=
         [<|bb_label := "entry"; bb_instructions :=
           [mk_inst 0 INVOKE [Label "callee"] []]|>]|>])
    "observer" "callee"
Proof
  simp[fn_directly_calls_def, lookup_function_def, fn_insts_def,
       fn_insts_blocks_def, mk_inst_def, FIND_thm]
QED
