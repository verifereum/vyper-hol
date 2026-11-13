(* Open expression body: recursive callbacks are assumed only at its children. *)
Theory ctorCallFreeExprBody
Ancestors
  list pair vyperAST compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules ctorCallFreeCallbacks e2eDeployDefs supportedExprTraverse
  exprSimHypsDefs

Theorem call_free_ifexp_body[local]:
  (!st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (lower_value cfn cenv (BaseT BoolT) cond_e st)))) /\
  (!et st. MEM et [then_e;else_e] ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty et st)))) /\
  (!rty aty vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_ifexp_arm cenv rty aty vv st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr_body cfn bfn tfn cenv ty
        (IfExp ety cond_e then_e else_e) st)))
Proof
  strip_tac >> gen_tac >> strip_tac >> simp[compile_expr_body_def] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> simp[] >>
  `JNZ <> RETURNDATACOPY /\ JNZ <> INVOKE /\
   JMP <> RETURNDATACOPY /\ JMP <> INVOKE /\
   ASSIGN <> RETURNDATACOPY /\ ASSIGN <> INVOKE` by simp[] >>
  metis_tac[every_state_insts_fresh_var, every_state_insts_fresh_label,
    every_state_insts_new_block, call_free_emit_inst, SND]
QED

(* Direct helper contracts are guarded by the actual parent constructor;
   callers obtain them from the child-restricted callback interfaces. *)
Theorem call_free_expr_body:
  (!rty lit st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_literal_vv rty lit st)))) /\
  (!rty name st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_name_vv cenv rty name st)))) /\
  (!vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value cenv vv st)))) /\
  (!sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_alloc_buffer sz st)))) /\
  (!rty aty vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_ifexp_arm cenv rty aty vv st)))) /\
  (!ptr ws sz ctor imm loc st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_dynarray_pop ptr ws sz ctor imm loc st)))) /\
  (!rty aty a bty b mty m st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_addmod_names cenv rty aty a bty b mty m st)))) /\
  (!rty aty a bty b mty m st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_mulmod_names cenv rty aty a bty b mty m st)))) /\
  (!rty aty a bty b st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_powmod256_names cenv rty aty a bty b st)))) ==>
  !e.
  ~supported_expr_exists constructor_call_root e /\ ~supported_expr_exists root2 e /\
  (!child ety st. expr_size child < expr_size e /\
      ~supported_expr_exists constructor_call_root child /\ ~supported_expr_exists root2 child ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ety child st)))) /\
  (!ann bi args st. e = Builtin ann bi args ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (bfn cenv ann ty bi args st)))) /\
  (!ann tb rty args st. e = TypeBuiltin ann tb rty args ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (tfn cenv ann ty tb rty args st)))) /\
  (!ann base_e idx_e st. e = Subscript ann base_e idx_e ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_subscript cfn cenv ann ty base_e idx_e st)))) /\
  (!ann base_e fname st. e = Attribute ann base_e fname ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_attribute cfn cenv ann ty base_e fname st)))) /\
  (!ann name fields buf off st. e = StructLit ann name fields ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_struct_lit cfn cenv (StructT name) fields buf off st)))) /\
  (!ann target st. e = Pop ann target ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_get_target_ptr cfn cenv target st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_expr_body cfn bfn tfn cenv ty e st)))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  Cases_on `e` >> gvs[supported_expr_exists_def, constructor_call_root_def] >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (IfExp ann cond_e then_e else_e)`] >-
    (ho_match_mp_tac call_free_ifexp_body >> simp[] >> conj_tac >-
       (ho_match_mp_tac every_state_insts_lower_value >> simp[] >>
        first_x_assum irule >> simp[]) >>
     rpt strip_tac >> gvs[] >> first_x_assum irule >> simp[]) >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (Builtin ann bi args)`] >-
    (Cases_on `names_builtin bi args` >-
       (qpat_x_assum `names_builtin bi args` mp_tac >>
        map_every qid_spec_tac [`args`,`bi`] >>
        recInduct names_builtin_ind >>
        simp[names_builtin_def, compile_expr_body_def, expr_type_def]) >>
     simp[compile_expr_body_builtin_dispatch]) >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (Pop ann target)`] >-
    (simp[compile_expr_body_def] >> rpt strip_tac >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[SND]) >>
  simp[compile_expr_body_def, expr_type_def] >~ [`FLOOKUP cenv.ce_module_vars nsid`] >-
    (rpt gen_tac >> CASE_TAC >> gvs[] >-
       (rpt (pairarg_tac >> gvs[]) >> metis_tac[SRULE [] (Q.INST [`opc` |-> `INVALID`] call_free_emit_inst), SND]) >>
     CASE_TAC >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
     metis_tac[SRULE [] (Q.INST [`opc` |-> `INVALID`] call_free_emit_inst), SND]) >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >> metis_tac[SND]
QED
