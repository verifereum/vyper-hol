(* Static witness for the argument-length producer of a blueprint
 * allocation. None of the equations assert execution of a stage. *)
Theory entryBlueprintCheckedProducer
Ancestors
  entryBlueprintBudgetSite compileVyper exprLowering builtinCreate
  context compileEnv venomExecSemantics venomExecProofs contextCodegenRel
  fragExec arithmetic list rich_list

Definition checked_blueprint_producer_def:
  checked_blueprint_producer a target value salt offset code args_ptr
    args_len rof result b <=>
  ?cfn ce raw salted es target_e value_e rest start ct ca cv cs co.
    es = target_e :: value_e :: rest /\
    (if salted then 1 else 0) + 1 <= LENGTH rest /\
    let suffix = if salted then TL rest else rest in
    let offset_e = origin_fold_value (HD suffix) in
      lower_value cfn ce (expr_type target_e) target_e start = (target,ct) /\
      compile_create_blueprint_args cfn ce raw
        (value_e :: TAKE (if salted then 2 else 1) rest) (TL suffix) ct =
        ((args_ptr,args_len),ca) /\
      lower_value cfn ce (expr_type value_e) value_e ca = (value,cv) /\
      compile_create_salt cfn ce (if salted then SOME (HD rest) else NONE) cv =
        (salt,cs) /\
      (case offset_e of
         Literal _ (IntL i) => comp_return (Lit (i2w i))
       | _ => lower_value cfn ce (expr_type (HD suffix)) (HD suffix)) cs =
        (offset,co) /\
      compile_create_blueprint_check (is_int_literal offset_e) target offset co =
        (code,a) /\
      compile_create_blueprint_append target value salt offset code args_ptr
        args_len rof a = (result,b)
End

Definition checked_blueprint_site_def:
  checked_blueprint_site label prefix chunk k <=>
    k = 1 /\
    ?a d target value salt offset code args_ptr args_len rof result b created.
      label = a.cs_current_bb /\ prefix = a.cs_current_insts /\
      checked_blueprint_producer a target value salt offset code args_ptr
        args_len rof result b /\
      blueprint_append_code target value salt offset code args_ptr args_len a created d chunk /\
      compile_check_create_result created rof d = (result,b)
End

Theorem checked_blueprint_producer_site:
  checked_blueprint_producer a target value salt offset code args_ptr
    args_len rof result b ==>
  ?created d chunk.
    cs_extends a d /\ d.cs_current_bb = a.cs_current_bb /\
    d.cs_current_insts = a.cs_current_insts ++ chunk /\
    checked_blueprint_site a.cs_current_bb a.cs_current_insts chunk 1 /\
    1 < LENGTH chunk /\ (EL 1 chunk).inst_opcode = DALLOCA /\
    (!k. k < LENGTH chunk /\ (EL k chunk).inst_opcode = DALLOCA ==> k = 1) /\
    compile_check_create_result created rof d = (result,b)
Proof
  strip_tac >>
  `compile_create_blueprint_append target value salt offset code args_ptr
     args_len rof a = (result,b)` by
    (fs[checked_blueprint_producer_def, LET_THM]) >>
  drule_then strip_assume_tac blueprint_append_segment_geometry >>
  drule_then strip_assume_tac blueprint_append_code_only_dalloca >>
  `cs_extends a d /\ d.cs_current_bb = a.cs_current_bb /\
   d.cs_current_insts = a.cs_current_insts ++ chunk` by fs[blueprint_append_code_def] >>
  qexistsl_tac [`created`,`d`,`chunk`] >> asm_rewrite_tac[] >>
  simp[checked_blueprint_site_def] >>
  qexistsl_tac [`a`,`d`,`target`,`value`,`salt`,`offset`,`code`,`args_ptr`,
                `args_len`,`rof`,`result`,`b`,`created`] >> simp[]
QED

Theorem checked_blueprint_site_window:
  checked_blueprint_site s.vs_current_bb prefix chunk k /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ chunk ++ rest /\
  s.vs_inst_idx = LENGTH prefix + k ==>
  active_inst fn (EL s.vs_inst_idx bb.bb_instructions) s /\
  entry_blueprint_window fn (EL s.vs_inst_idx bb.bb_instructions) s
Proof
  pure_rewrite_tac[checked_blueprint_site_def, blueprint_append_code_def] >>
  strip_tac >> rename1 `add_inst.inst_opcode = ADD` >>
  rename1 `compile_alloc_dynamic sz m = (alloc_ptr,n)` >>
  `DROP (LENGTH a.cs_current_insts) bb.bb_instructions =
      add_inst :: alloc :: (emitted_insts n c ++ effect :: rest)` by
    (asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >> REFL_TAC) >>
  `s.vs_inst_idx = SUC (LENGTH a.cs_current_insts)` by simp[ADD1] >>
  `DROP s.vs_inst_idx bb.bb_instructions =
      alloc :: (emitted_insts n c ++ effect :: rest)` by metis_tac[DROP_EQ_CONS] >>
  `EL s.vs_inst_idx bb.bb_instructions = alloc` by metis_tac[DROP_EQ_CONS] >>
  pop_assum (fn th => pure_rewrite_tac[th]) >> conj_tac
  >- (simp[active_inst_def] >> qexists_tac `bb` >>
      metis_tac[DROP_EQ_CONS, lookup_block_MEM, lookup_block_label]) >>
  pure_rewrite_tac[entry_blueprint_window_def] >>
  qexistsl_tac [`bb`,`a`,`m`,`n`,`e`,`c`,`add_inst`,`effect`,`rest`,
                `target`,`value`,`salt`,`offset`,`code`,`args_ptr`,`args_len`,
                `sz`,`alloc_ptr`] >>
  asm_rewrite_tac[]
QED
