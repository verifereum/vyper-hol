(* The post-VV administrative interval of one buffered internal argument. *)
Theory entryIntCallStageBuffer
Ancestors
  entryCreateEffectFocus entryCreatePathScope entryCreateAdminSequence
  createSizeCutCode createSizeCutOpens createSizeLocationCode createSizeTypedCopyCode
  entryCreatePosSnapshotCode exprSimAbiEncodeObliviousCode exprSimAbiGasBridge
  exprLowering compileEnv context emitHelper venomInst fragExec list pair

val buffer_safe = ``\opc. opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2``;
val buffer_gas_safe = ``\opc. opc <> GAS /\ opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE``;

Theorem buffer_admin_action_weaken[local]:
  code_action ^buffer_gas_safe m ==> code_action ^buffer_safe m
Proof
  simp[code_action_def, code_step_def, EVERY_MEM] >> metis_tac[]
QED

Theorem buffer_unwrap_action:
  code_action ^buffer_safe (unwrap_value ce vv)
Proof
  irule buffer_admin_action_weaken >> simp[admin_unwrap_code_action]
QED

Theorem buffer_store_action:
  code_action ^buffer_safe (compile_store_memory ce src dst dt st)
Proof
  irule buffer_admin_action_weaken >> simp[admin_store_code_action]
QED

(* These actions are also used after a saved external-call argument. *)
Theorem saved_value_admin_actions:
  code_action ^buffer_safe (unwrap_value ce vv) /\
  code_action ^buffer_safe (compile_store_memory ce src dst dt st)
Proof
  simp[buffer_unwrap_action, buffer_store_action]
QED

Theorem intcall_stage_buffer_admin_safe:
  compile_alloc_buffer n a = (buf,b) /\
  unwrap_value ce vv b = (op,c) /\
  compile_store_memory ce op buf.buf_operand dt (vv_type vv) c = ((),d) /\
  fn_has_code a d fn /\ body_inv tops ctx ce cx /\ MEM fn ctx.ctx_functions ==>
  create_operand_cut a d explicit ctx fn tops cx st0 source (es,s)
Proof
  strip_tac >>
  `create_cut_code {} a d` by
    (irule create_cut_code_join >> qexists_tac `b` >> conj_tac
     >- metis_tac[create_alloc_buffer_cut_code, SND] >>
     irule create_cut_code_join >> qexists_tac `c` >>
     metis_tac[create_unwrap_cut_code, create_store_memory_cut_code, SND]) >>
  `code_step ^buffer_safe a b` by
    (qpat_assum `compile_alloc_buffer _ _ = _`
       (mp_then (Pat `compile_alloc_buffer _ _ = _`) irule
         (REWRITE_RULE [code_action_def] (Q.SPECL [`^buffer_safe`, `n`] code_action_alloc_buffer))) >> simp[]) >>
  `code_step ^buffer_safe b c` by
    (irule (REWRITE_RULE [code_action_def] buffer_unwrap_action) >> metis_tac[]) >>
  `code_step ^buffer_safe c d` by
    (irule (REWRITE_RULE [code_action_def] buffer_store_action) >> metis_tac[]) >>
  `code_step ^buffer_safe a d` by
    (irule code_step_trans >> qexists_tac `b` >> simp[] >>
     irule code_step_trans >> qexists_tac `c` >> simp[]) >>
  irule create_effect_suffix_cut >> simp[] >> conj_tac
  >- (qpat_x_assum `code_step _ a d` mp_tac >> simp[code_step_def]) >>
  qexists_tac `ce` >> simp[]
QED
