(* Immutable initcode must be copied from its declared region before CREATE. *)
Theory createImmutableBytecodeTest
Ancestors
  exprLowering exprLoweringProps vyperCompiler venomCallOracleDefs
  venomExecSemantics venomState compileEnv context words list
Libs
  wordsLib

Definition immutable_snapshot_request_ok_def:
  immutable_snapshot_request_ok ctor =
    let cenv = (ARB:compile_env) with
      <|ce_is_ctor := ctor; ce_imm_alloca := SOME (Lit 256w)|> in
    let vv = LocatedValue (BaseT (BytesT (Dynamic 10)))
      (mk_ptr (Lit 0w) LocCode) in
    let cs = initial_compile_state "entry" in
    let (ptr, compiled) = compile_create_snapshot cenv vv
      (BaseT (BytesT (Dynamic 49152))) cs in
    let bytes = REPLICATE 31 0w ++ [2w;96w;0w] ++ REPLICATE 30 0w in
    let initial = (init_venom_state "entry") with
      <|vs_alloca_next := 1024;
        vs_memory := if ctor then REPLICATE 256 0w ++ bytes else [];
        vs_data_section := if ctor then [] else bytes|> in
    case run_inst_seq (emitted_insts cs compiled) initial of
      OK post =>
        eval_operand ptr post = SOME 1024w /\
        mload 1024 post = 2w /\
        (venom_create_request post 0w 1056w (mload 1024 post) NONE).cr_data =
          [96w;0w] /\
        LENGTH post.vs_memory = 1088 /\
        post.vs_alloca_next = 50208
    | _ => F
End

Theorem immutable_creation_snapshot_request:
  immutable_snapshot_request_ok F /\ immutable_snapshot_request_ok T
Proof
  EVAL_TAC
QED

val _ = app (fn (name, th) =>
  if null (List.filter (fn s => s <> "DISK_THM")
             (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail ("Oracle dependency in " ^ name))
  (DB.thms "createImmutableBytecodeTest");
