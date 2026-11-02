Theory rawCreateContractProbe
Ancestors
  builtinCreate exprLoweringProps vyperCompiler
  venomExecSemantics venomState compileEnv
Libs
  wordsLib

(* The theorem's two explicit operands are defined, and freshness holds,
   but the optional salt is not required to be defined. *)
Theorem raw_create_probe_premises:
  eval_operand (Lit 0w) (init_venom_state "entry") = SOME 0w /\
  fresh_vars_wrt (initial_compile_state "entry") (init_venom_state "entry")
Proof
  simp[eval_operand_def, fresh_vars_wrt_def, initial_compile_state_def,
       init_venom_state_def]
QED

Theorem raw_create_missing_salt_execution:
  let cs = initial_compile_state "entry" in
  let compiled = compile_raw_create_legacy (Lit 0w) (Lit 0w)
                   (SOME (Var "missing_salt")) F NONE cs in
  run_inst_seq (emitted_insts cs (SND compiled))
    (init_venom_state "entry") = Error "undefined operand"
Proof
  EVAL_TAC
QED

(* A complete counterexample to the current universal execution contract. *)
Theorem raw_create_contract_counterexample:
  let cs = initial_compile_state "entry" in
  let ss = init_venom_state "entry" in
  let compiled = compile_raw_create_legacy (Lit 0w) (Lit 0w)
                   (SOME (Var "missing_salt")) F NONE cs in
  compile_raw_create_legacy (Lit 0w) (Lit 0w)
    (SOME (Var "missing_salt")) F NONE cs =
      (FST compiled, SND compiled) /\
  eval_operand (Lit 0w) ss = SOME 0w /\
  eval_operand (Lit 0w) ss = SOME 0w /\
  fresh_vars_wrt cs ss /\
  ~(?ss'. run_inst_seq (emitted_insts cs (SND compiled)) ss = OK ss' \/
          run_inst_seq (emitted_insts cs (SND compiled)) ss =
            Abort Revert_abort ss')
Proof
  simp[LET_THM, raw_create_probe_premises,
       SRULE [LET_THM] raw_create_missing_salt_execution]
QED

(* EVAL's result and the two probe lemmas must be kernel-closed. *)
val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name ^ ": " ^
                   String.concatWith "," (#1 (Tag.dest_tag (Thm.tag th)))))
  (DB.thms "rawCreateContractProbe");
