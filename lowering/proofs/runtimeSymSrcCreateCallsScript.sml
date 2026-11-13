Theory runtimeSymSrcCreateCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcCallStaging runtimeSymSrcSystemCreate runtimeSymSrcAbiEncode
  runtimeSymSrcContext runtimeSymSrcContextTypedBase
  exprLowering compileEnv emitHelper list stackPlanTypes supportedExprs

Theorem runtime_sym_create_salt:
  (!e s op s'. salt = SOME e /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce (expr_type e) e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_salt cfn ce salt s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  (!op. out = SOME op ==> ~is_label_operand op)
Proof
  Cases_on `salt`
  >- (simp[compile_create_salt_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[compile_create_salt_def, comp_bind_def] >> disch_tac >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem runtime_sym_create_ctor_tuple:
  (!s vals s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_multi_vvs cfn ce args s = (vals,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ EVERY runtime_sym_value vals) ==>
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_create_ctor_tuple cfn ce args s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  disch_tac >> simp[compile_create_ctor_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  gvs[comp_return_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule_at (Pat `compile_extcall_store_values _ _ _ _ _ = _`)
    runtime_sym_extcall_store_values >> simp[] >>
  disch_then irule >>
  `!es st. LENGTH (FST (compile_multi_vvs cfn ce es st)) = LENGTH es` by
    (Induct >> simp[compile_multi_vvs_def, comp_return_def, comp_bind_def] >>
     rpt gen_tac >> rpt (pairarg_tac >> simp[]) >>
     simp[comp_return_def] >> metis_tac[pairTheory.FST]) >>
  `LENGTH vals = LENGTH (MAP expr_type args)` by metis_tac[pairTheory.FST, LENGTH_MAP] >>
  simp[every_zip_fst]
QED

Theorem runtime_sym_create_blueprint_args:
  (!e s op s'. MEM e args /\ EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce (expr_type e) e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!s op s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_create_ctor_tuple cfn ce args s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  EVERY runtime_sym_inst (state_insts s) /\
  compile_create_blueprint_args cfn ce raw args s = ((p_op,len),s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  ~is_label_operand p_op /\ ~is_label_operand len
Proof
  strip_tac >> Cases_on `raw`
  >- (Cases_on `args` >> simp[compile_create_blueprint_args_def]
      >- (simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
          pairarg_tac >> simp[] >> strip_tac >> gvs[is_label_operand_def] >>
          irule runtime_sym_emit_inst >>
          qexistsl [`0`, `INVALID`, `[]`, `[]`, `s`, `()`] >>
          simp[runtime_sym_ordinary_inst] ) >>
      Cases_on `t` >> simp[compile_create_blueprint_args_def, comp_bind_def,
                               comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
      >- (first_x_assum drule_all >> strip_tac >>
          qpat_x_assum `emit_op MLOAD _ _ = _`
            (mp_then Any mp_tac runtime_sym_emit_op) >>
          (impl_tac >- simp[]) >> strip_tac >>
          qpat_x_assum `emit_op ADD _ _ = _`
            (mp_then Any mp_tac runtime_sym_emit_op) >>
          (impl_tac >- simp[is_label_operand_def]) >> simp[]) >>
      simp[is_label_operand_def] >> irule runtime_sym_emit_inst >>
      qexistsl [`0`, `INVALID`, `[]`, `[]`, `s`, `()`] >>
      simp[runtime_sym_ordinary_inst]) >>
  Cases_on `args = []` >> simp[compile_create_blueprint_args_def, comp_return_def]
  >- (rpt strip_tac >> gvs[is_label_operand_def]) >>
  simp[comp_bind_def] >> rpt (pairarg_tac >> simp[]) >>
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all runtime_sym_abi_encode_to_buf >> simp[]
QED

Theorem runtime_sym_raw_create:
  (!s vv s'. EVERY runtime_sym_inst (state_insts s) /\
     cfn ce (expr_type byte_e) byte_e s = (vv,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value vv) /\
  (!vv bt s op s'. runtime_sym_env ce /\ runtime_sym_value vv /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_create_snapshot ce vv bt s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!s op s'. EVERY runtime_sym_inst (state_insts s) /\
     lower_value cfn ce (expr_type value_e) value_e s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!s op s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_create_ctor_tuple cfn ce ctor_args s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  (!s out s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_create_salt cfn ce salt_e s = (out,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\
     (!op. out = SOME op ==> ~is_label_operand op)) ==>
  runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_raw_create cfn ce byte_e value_e ctor_args salt_e rof s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >>
  simp[compile_raw_create_def, comp_bind_def, comp_ignore_bind_def] >>
  strip_tac >>
  qpat_x_assum `(\(vv,cs'). _) _ = _` mp_tac >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  qpat_x_assum `!s vv s'. _ /\ cfn _ _ _ _ = _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `!vv bt s op s'. _` drule_all >> strip_tac >>
  qpat_x_assum `!s op s'. _ /\ lower_value _ _ _ _ _ = _ ==> _` drule_all >> strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  Cases_on `ctor_args = []` >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def]
  >- (pairarg_tac >> simp[] >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      drule_all runtime_sym_create_dispatch >> simp[]) >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  qpat_x_assum `(\(buf,st). _) _ = _` mp_tac >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  pairarg_tac >> first_assum SUBST1_TAC >> simp[NoAsms] >>
  strip_tac >> gvs[] >> simp[comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule_all runtime_sym_copy_memory_dynamic >> strip_tac >>
  qpat_x_assum `!s op s'. _ /\ compile_create_ctor_tuple _ _ _ _ = _ ==> _`
    drule_all >> strip_tac >>
  qpat_x_assum `emit_op ADD [_; len] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all runtime_sym_abi_encode_to_buf >> strip_tac >>
  qpat_x_assum `emit_op ADD [len; _] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all runtime_sym_create_dispatch >> simp[]
QED

(* The current supported-program whitelist rejects every creation target.
   The callback wrappers above remain independent of that whitelist. *)
Theorem runtime_sym_call_create:
  !tops cfn ce rt ty ck has_salt rof metadata es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\
    supported_expr tops (Call rt (CreateTarget ck has_salt rof metadata) es default) /\
    ~supported_expr_exists is_self_code
       (Call rt (CreateTarget ck has_salt rof metadata) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (CreateTarget ck has_salt rof metadata)
      es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `default` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED
