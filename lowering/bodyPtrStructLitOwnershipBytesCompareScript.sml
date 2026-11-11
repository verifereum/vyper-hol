Theory bodyPtrStructLitOwnershipBytesCompare
Ancestors bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering
  builtinSimple compileEnv context unitShapeDefs venomInst stackPlanTypes list pair

Theorem alloc_run_compile_bytestring_hash:
  alloc_run fresh_outputs (compile_bytestring_hash ptr_op) (\v s. fresh_outputs s)
Proof
  simp[compile_bytestring_hash_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

(* Shape of the runtime hash of a lowered bytestring operand. *)
Theorem bytestring_hash_shape[local]:
  shape_step F compiler_label (\s. plain_operand s p)
    (compile_bytestring_hash p) (\v s. plain_operand s v)
Proof
  simp[compile_bytestring_hash_def] >> irule shape_step_bind >>
  qexists `\x s. plain_operand s p /\ plain_operand s x` >> reverse conj_tac
  >- (qspecl_then [`F`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s p`, `\s. plain_operand s p`] >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands), plain_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, label_or_plain_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `x` >> simp[] >> irule shape_step_bind >>
  qexists `\y s. plain_operand s x /\ plain_operand s y` >> reverse conj_tac
  >- (qspecl_then [`F`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s x`,
        `\s. plain_operand s p /\ plain_operand s x`] >>
      simp[SRULE [] (Q.SPEC `[x]` shape_stable_plain_operands), plain_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, label_or_plain_def,
        stackPlanTypesTheory.is_label_operand_def]) >>
  qx_gen_tac `y` >> simp[] >>
  qspecl_then [`F`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
  irule_at Any shape_step_emit_op_pre >>
  qexists `\s. plain_operand s x /\ plain_operand s y` >>
  simp[plain_operand_def,
    lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def, label_or_plain_def,
    stackPlanTypesTheory.is_label_operand_def]
QED

Theorem alloc_run_bytestring_hash_frame[local]:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s p)
    (compile_bytestring_hash p) (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`]
    bodyPtrStructLitOwnershipStructFrameTheory.alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_bytestring_hash, bytestring_hash_shape]
QED

(* A comparison operand: a literal's compile-time hash, or the runtime hash
   of the lowered bytestring. *)
Theorem alloc_run_lower_bytestring_hash[local]:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce) (cfn ce t e)
    (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce t e) (\v s. T) /\
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (\st. case bytestring_literal_hash e of
            SOME h => (Lit h, st)
          | NONE => comp_bind (lower_value cfn ce t e) compile_bytestring_hash st)
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v)
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e` >> simp[]
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule alloc_run_bind >>
      qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
      reverse conj_tac
      >- (irule alloc_run_lower_value_frame >> simp[] >> qexists_tac `internal` >> simp[]) >>
      qx_gen_tac `p` >> simp[] >>
      irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. R s /\ cenv_shape_ok s ce`]
        alloc_run_bytestring_hash_frame) >>
      simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  simp[alloc_run_def, alloc_frame_refl, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def]
QED

Theorem alloc_run_uncurry[local]:
  alloc_run P m M /\ (!v. alloc_run (M v) (k v) Q) ==>
  alloc_run P (\st. UNCURRY k (m st)) Q
Proof
  strip_tac >>
  `(\st. UNCURRY k (m st)) = comp_bind m k` by
    (simp[FUN_EQ_THM, comp_bind_def] >> qx_gen_tac `st0` >>
     Cases_on `m st0` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule alloc_run_bind >> qexists_tac `M` >> simp[]
QED

Theorem alloc_run_builtin_bytestring_compare:
  (op = Eq \/ op = NotEq) /\ is_bytestring_type (expr_type (HD args)) /\
  2 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v)) /\
  (!e t. MEM e args ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Bop op) args) (\v s. T)
Proof
  strip_tac >> gvs[] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, GSYM comp_bind_def] >>
  simp[SF ETA_ss] >>
  `MEM (HD args) args /\ MEM (HD (TL args)) args` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  irule alloc_run_uncurry >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. T`] alloc_run_lower_bytestring_hash) >>
      qexists_tac `internal` >> simp[shape_stable_def]) >>
  qx_gen_tac `h1` >> simp[] >>
  irule alloc_run_uncurry >>
  qexists `\v s. shape_state s /\ plain_operand s h1 /\ cenv_shape_ok s ce /\
                 plain_operand s v` >>
  conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. plain_operand s h1`]
        alloc_run_lower_bytestring_hash) >>
      qexists_tac `internal` >>
      simp[SRULE [] (Q.SPEC `[h1]` shape_stable_plain_operands)]) >>
  qx_gen_tac `h2` >> simp[] >> irule alloc_run_conseq >>
  qexistsl [`fresh_outputs`, `\v s. fresh_outputs s`] >>
  simp[shape_state_def, shape_base_fresh_outputs] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    (reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh]) >> gen_tac >> simp[]) >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SRULE [alloc_run_def] alloc_run_emit_op_fresh) >> simp[]
QED
