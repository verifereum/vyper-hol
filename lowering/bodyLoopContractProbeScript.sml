(* Concrete hypothesis probes; not a body memory certificate. *)
Theory bodyLoopContractProbe
Ancestors
  supportedStmts supportedTargets vyperTypeSystem vyperInterpreter
  stmtLowering compileEnv finite_map venomExecSemantics fragExec exprSimHyps

Definition loop_probe_body_def:
  loop_probe_body =
    [Assign (BaseTarget (SubscriptTarget (NameTarget "xs")
       (Literal (BaseT (UintT 256)) (IntL 1))))
       (Literal (BaseT (UintT 256)) (IntL 2));
     Assign (BaseTarget (NameTarget "out")) (Name (BaseT (UintT 256)) "i")]
End

Definition loop_probe_stmt_def:
  loop_probe_stmt = For "i" (BaseT (UintT 256))
    (Array (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "xs")) 2
    loop_probe_body
End

Theorem loop_probe_supported:
  supported_stmt []
    [("xs", ArrayT (BaseT (UintT 256)) (Fixed 2));
     ("out", BaseT (UintT 256))] loop_probe_stmt
Proof
  EVAL_TAC
QED

Definition loop_probe_env_def:
  loop_probe_env = <| current_src := NONE;
    var_types := FEMPTY |++ [("xs", ArrayT (BaseT (UintT 256)) (Fixed 2));
                            ("out", BaseT (UintT 256))];
    var_assignable := FEMPTY |++ [("xs", T); ("out", T)];
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY; type_defs := FEMPTY;
    fn_sigs := FEMPTY; flag_members := FEMPTY |>
End

Theorem loop_probe_typed:
  type_stmt loop_probe_env NoneT loop_probe_stmt = SOME loop_probe_env
Proof
  simp[loop_probe_stmt_def, type_stmt_def, well_typed_iterator_def] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition loop_probe_scopes_def:
  loop_probe_scopes = [FEMPTY |++
    [("xs", <| assignable := T;
               type := ArrayTV (BaseTV (UintT 256)) (Fixed 2);
               value := ArrayV (SArrayV [(0, IntV 0); (1, IntV 1)]);
               popped := [] |>);
     ("out", <| assignable := T; type := BaseTV (UintT 256);
                value := IntV 0; popped := [] |> )]]
End

Theorem loop_probe_source_result:
  lookup_scopes_val "out"
    (SND (eval_stmt cx loop_probe_stmt
      (es with scopes := loop_probe_scopes))).scopes = SOME (IntV 1)
Proof
  EVAL_TAC >> simp_tac (srw_ss() ++ wordsLib.SIZES_ss) [wordsTheory.dimword_def] >> EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition loop_probe_cenv_def:
  loop_probe_cenv = (ARB : compile_env) with <|
    ce_vars := FEMPTY |++ [("xs", MemLoc 0 64); ("out", MemLoc 64 32)];
    ce_var_type := (\n. if n = "xs" then
      SOME (ArrayT (BaseT (UintT 256)) (Fixed 2))
      else if n = "out" then SOME (BaseT (UintT 256)) else NONE);
    ce_alloca_locals := T; ce_is_ctor := F |>
End

Definition loop_probe_cs_def:
  loop_probe_cs = <| cs_next_var := 0; cs_next_label := 0;
    cs_next_id := 0; cs_current_bb := "entry"; cs_current_insts := [];
    cs_blocks := []; cs_data_sections := [] |>
End

Definition loop_probe_compiled_def:
  loop_probe_compiled = SND
    (compile_stmt loop_probe_cenv NoLoop NoneT loop_probe_stmt loop_probe_cs)
End

Definition loop_probe_func_def:
  loop_probe_func = mk_raw_function "probe"
    (loop_probe_compiled.cs_blocks ++
     [<| bb_label := loop_probe_compiled.cs_current_bb;
         bb_instructions := loop_probe_compiled.cs_current_insts ++
           [mk_inst 100 STOP [] []] |>])
End

Definition loop_probe_vs_def:
  loop_probe_vs = (mstore 32 1w (init_venom_state "entry")) with
    vs_alloca_next := 96
End

Theorem loop_probe_compiled_result:
  ?s. run_from 30 ctx loop_probe_func loop_probe_vs = Halt s /\
      mload 64 s = 2w
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  EVAL_TAC
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_LOOP_PROBE_KERNEL_AUDIT OK\n"
     else raise Fail "body loop probe inherited admission"
  end) [loop_probe_supported, loop_probe_typed, loop_probe_source_result,
        loop_probe_compiled_result];

(* The first execution probe uses immediate memory locations; the actual
   body contract requires pointer-valued locals. This rejection is specific
   to that initial layout, not to the mutating source program. *)
Theorem loop_probe_immediate_layout_rejected:
  ~expr_sim_inv loop_probe_cenv cx loop_probe_env es
Proof
  strip_tac >>
  fs[expr_sim_inv_def] >>
  qpat_x_assum `!id ty. FLOOKUP loop_probe_env.var_types id = SOME ty ==> ?p sz. _`
    (qspec_then `"xs"` mp_tac) >>
  simp[loop_probe_env_def, loop_probe_cenv_def, FUPDATE_LIST, FLOOKUP_UPDATE]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag loop_probe_immediate_layout_rejected)
  in if null axioms andalso null (Thm.hyp loop_probe_immediate_layout_rejected) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_LOOP_LAYOUT_KERNEL_AUDIT OK\n"
     else raise Fail "body loop layout probe inherited admission"
  end;

Definition loop_probe_ptr_cenv_def:
  loop_probe_ptr_cenv = loop_probe_cenv with ce_vars :=
    FEMPTY |++ [("xs", PtrVar (Var "%0") 64);
                ("out", PtrVar (Var "%1") 32)]
End

Definition loop_probe_ptr_cs_def:
  loop_probe_ptr_cs = loop_probe_cs with cs_next_var := 2
End

Definition loop_probe_ptr_compiled_def:
  loop_probe_ptr_compiled = SND
    (compile_stmt loop_probe_ptr_cenv NoLoop NoneT loop_probe_stmt loop_probe_ptr_cs)
End

Definition loop_probe_ptr_func_def:
  loop_probe_ptr_func = mk_raw_function "probe_ptr"
    (loop_probe_ptr_compiled.cs_blocks ++
     [<| bb_label := loop_probe_ptr_compiled.cs_current_bb;
         bb_instructions := loop_probe_ptr_compiled.cs_current_insts ++
           [mk_inst 100 STOP [] []] |>])
End

Definition loop_probe_ptr_vs_def:
  loop_probe_ptr_vs = (loop_probe_vs with vs_vars :=
    FEMPTY |++ [("%0", 0w); ("%1", 64w)])
End

Theorem loop_probe_ptr_compiled_result:
  ?s. run_from 30 ctx loop_probe_ptr_func loop_probe_ptr_vs = Halt s /\
      mload 64 s = 2w
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  once_rewrite_tac[run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >> simp[] >>
  EVAL_TAC
QED

Theorem loop_probe_ptr_locals_interface:
  (!id ty. FLOOKUP loop_probe_env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP loop_probe_ptr_cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  (!id ty. FLOOKUP loop_probe_env.var_types id = SOME ty ==>
     loop_probe_ptr_cenv.ce_var_type id = SOME ty)
Proof
  simp[loop_probe_env_def, loop_probe_ptr_cenv_def, loop_probe_cenv_def,
       FUPDATE_LIST, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_LOOP_POINTER_KERNEL_AUDIT OK\n"
     else raise Fail "body loop pointer probe inherited admission"
  end) [loop_probe_ptr_compiled_result, loop_probe_ptr_locals_interface];

Theorem loop_probe_none_return_typing:
  IS_SOME (type_stmt env NoneT (Return eo)) <=> eo = NONE
Proof
  Cases_on `eo` >> simp[type_stmt_def]
QED

Theorem loop_probe_none_return_stop:
  cenv.ce_return_pc = NONE /\
  cenv.ce_nonreentrant = (F, nkey, use_transient, is_view) ==>
  compile_stmt cenv lctx NoneT (Return NONE) = emit_inst STOP [] []
Proof
  strip_tac >> simp[Once compile_stmt_def, FUN_EQ_THM,
                   comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_LOOP_RETURN_KERNEL_AUDIT OK\n"
     else raise Fail "body loop return probe inherited admission"
  end) [loop_probe_none_return_typing, loop_probe_none_return_stop];
