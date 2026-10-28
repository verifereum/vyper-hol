(* A source-derived, genuinely checked tuple read at the unchanged whitelist
   boundary. This is not an unsupported runtime-op enabling theorem. *)
Theory sourceElaborationSupportTest
Ancestors
  sourceElaborationSupport supportedProgram supportedStmts exprLowering
  sourceExprElaborate vyperTypeSystem integer
  sourceModuleElaborate sourceModuleDefs
  sourceModuleEnv sourceSyntax sourceConstAnnotation sourceConstAST
  vyperTypeContract vyperAST vyperContext finite_map
Libs
  sourceModuleFrontendLib

Theorem source_expr_local_tuple_lowering_index:
  source_expr_elaborate fuel env scopes table constants bindings expected original =
    SC_Value (Subscript ty (Name (TupleT ts) name) index) ==>
  literal_int_index index < LENGTH ts /\
  EL (literal_int_index index) ts = ty
Proof
  strip_tac >> drule source_expr_local_tuple_index >> strip_tac >>
  `~(n < 0)` by intLib.ARITH_TAC >>
  gvs[literal_int_index_def, integerTheory.INT_ABS]
QED

Theorem supported_program_local_tuple_return_rejected:
  ~supported_program
    [FunctionDecl External mut nr rr name args defaults ret
      [Return (SOME (Subscript ty (Name (TupleT ts) local_name) index))]]
Proof
  simp[supported_program_def, supported_declaration_body_def,
       supported_function_body_def, supported_stmt_def,
       supported_local_tuple_read_rejected]
QED

Definition source_support_tuple_program_def:
  source_support_tuple_program = SourceProgram (SourceModule
    [SD_Function "f" [SX_Name "external"]
      [SourceArg "t" (SOME (SCA_Tuple
        [SCA_Name ["bool"]; SCA_Name ["uint256"]]))] []
      (SOME (SCA_Name ["uint256"]))
      [SS_Return (SOME (SX_Subscript (SX_Name "t")
        (SX_Binary SCB_Add (SX_Literal (SCL_Int 0)) (SX_Literal (SCL_Int 1)))))]] ) []
End

Definition source_support_tuple_tops_def:
  source_support_tuple_tops =
    [FunctionDecl External Nonpayable F F "f"
      [("t",TupleT [BaseT BoolT; BaseT (UintT 256)])] [] (BaseT (UintT 256))
      [Return (SOME (Subscript (BaseT (UintT 256))
        (Name (TupleT [BaseT BoolT; BaseT (UintT 256)]) "t")
        (Literal (BaseT (UintT 256)) (IntL 1))))]]
End

Definition source_support_tuple_trust_def:
  source_support_tuple_trust = <| smt_ids := [(["main"],NONE)];
    smt_nominals := []; smt_type_defs := FEMPTY; smt_slots := [] |>
End

val checked_tuple = sourceModuleFrontendLib.check
  {fuel=``30:num``,trust=``source_support_tuple_trust``,
   policies=``[(["main"],SourceModulePolicy F F)]``,keys=``[["main"]]``,
   program=``source_support_tuple_program``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``,address=``0w:address``};
val tuple_elaboration = save_thm ("source_support_tuple_elaboration_phase",
  #equation (#elaboration checked_tuple));
val _ = save_thm ("source_support_tuple_check_phase", #composition checked_tuple);
val tuple_checking = save_thm ("source_support_tuple_checking", #checking checked_tuple);

Theorem source_support_tuple_elaboration:
  source_module_elaborate 30 source_support_tuple_trust
    [(["main"],SourceModulePolicy F F)] [["main"]] source_support_tuple_program =
  SM_Ok (SourceRetained source_support_tuple_program [(NONE,source_support_tuple_tops)])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV tuple_elaboration)) >>
  EVAL_TAC
QED

Theorem source_support_tuple_not_supported:
  ~supported_program source_support_tuple_tops
Proof
  simp[source_support_tuple_tops_def, supported_program_local_tuple_return_rejected]
QED

Theorem source_support_tuple_checked_but_not_supported:
  source_module_elaborate 30 source_support_tuple_trust
    [(["main"],SourceModulePolicy F F)] [["main"]] source_support_tuple_program =
    SM_Ok (SourceRetained source_support_tuple_program [(NONE,source_support_tuple_tops)]) /\
  (?art. check_contract T
    [(0w:address,([]:storage_layout,[]:storage_layout))] (0w:address)
    [(NONE,source_support_tuple_tops)] = SOME art) /\
  ~supported_program source_support_tuple_tops
Proof
  simp[source_support_tuple_elaboration, source_support_tuple_not_supported] >>
  simp[source_support_tuple_tops_def, tuple_checking]
QED

val () = List.app (fn (name,th) => let
    val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail ("source support boundary kernel audit: " ^ name) end)
  (DB.thms "sourceElaborationSupportTest");
