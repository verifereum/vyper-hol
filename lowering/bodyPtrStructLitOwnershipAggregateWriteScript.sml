Theory bodyPtrStructLitOwnershipAggregateWrite
Ancestors bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs
  loweringShapeRules context compileEnv exprLowering list

Theorem alloc_run_aggregate_write_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s buf /\ value_shape_ok s vv)
    (do dst <- emit_op ADD [buf; Lit (n2w off)];
        v <- unwrap_value ce vv;
        compile_store_memory ce v dst dt st
     od)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\dst s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s buf /\ value_shape_ok s vv /\ plain_operand s dst` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_address_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\ value_shape_ok s vv` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, value_shape_ok_stable,
        SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)]) >>
  qx_gen_tac `dst` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s buf /\ plain_operand s dst /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\ plain_operand s dst` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands),
        SRULE [] (Q.SPEC `[dst]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_store_memory_frame >>
  qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf` >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)]
QED
