(* Compilation-side entry data for the transaction-valid fixture. *)
Theory immutableDeployEmptyValidMachine
Ancestors
  immutableDeployEmptyValid immutableDeployEmptySource vyperCompiler stmtLowering

Definition empty_immutable_entry_sa_def:
  empty_immutable_entry_sa = initial_compile_state "entry"
End

Definition empty_immutable_entry_compiled_def:
  empty_immutable_entry_compiled =
    stmt_env empty_immutable_ce NoLoop NoneT
      (Assign (BaseTarget (TopLevelNameTarget (NONE,"dst"))) empty_immutable_expr)
      empty_immutable_entry_sa
End

Theorem empty_immutable_entry_compile_probe:
  (SND empty_immutable_entry_compiled).cs_next_id > 0
Proof
  EVAL_TAC
QED

Theorem empty_immutable_entry_compile_shape:
  SND empty_immutable_entry_compiled =
    <|cs_next_var := 2; cs_next_label := 0; cs_next_id := 3;
      cs_current_bb := "entry";
      cs_current_insts :=
        [<|inst_id := 0; inst_opcode := ALLOCA; inst_operands := [Lit 0w];
           inst_outputs := ["%0"]|>;
         <|inst_id := 1; inst_opcode := MLOAD; inst_operands := [Var "%0"];
           inst_outputs := ["%1"]|>;
         <|inst_id := 2; inst_opcode := ISTORE;
           inst_operands := [Lit 0w; Var "%1"]; inst_outputs := []|>];
      cs_blocks := []; cs_data_sections := []|>
Proof
  EVAL_TAC
QED

Definition empty_immutable_entry_fn_def:
  empty_immutable_entry_fn = mk_raw_function "entry"
    [<|bb_label := "entry";
       bb_instructions := (SND empty_immutable_entry_compiled).cs_current_insts|>]
End

Theorem empty_immutable_entry_code:
  fn_has_code empty_immutable_entry_sa (SND empty_immutable_entry_compiled)
    empty_immutable_entry_fn /\
  fn_inst_ids_distinct empty_immutable_entry_fn /\
  local_ptrs_reserved empty_immutable_ce empty_immutable_entry_sa /\
  (!s. ret_pc_ok empty_immutable_ce empty_immutable_entry_sa s) /\
  ~block_is_terminated empty_immutable_entry_sa
Proof
  EVAL_TAC >> simp[]
QED

Theorem empty_immutable_entry_fn_not_in_unit:
  lookup_function empty_immutable_entry_fn.fn_name
    empty_immutable_unit.cu_context.ctx_functions <> SOME empty_immutable_entry_fn
Proof
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >> EVAL_TAC >> simp[]
QED

Theorem empty_immutable_entry_fn_no_state_rel:
  !ss. ~stmt_state_rel empty_immutable_unit.cu_context empty_immutable_entry_fn
          empty_immutable_ce empty_immutable_valid_cx empty_immutable_es ss
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.alloca_room_def, empty_immutable_entry_fn_not_in_unit]
QED
