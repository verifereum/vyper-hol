(* Literal, name and environment compiler boundaries. *)
Theory gasShadowCompileLiteral
Ancestors
  gasShadowCompileArith gasShadowCompileContext gasShadowCompileBase
  gasShadowState gasShadow vyperAST exprLowering compileEnv emitHelper venomInst

Theorem gas_shadow_compiles_store_byte_chunks:
  !data_ptr bs offset.
    gas_shadow_compiles (compile_store_byte_chunks data_ptr bs offset)
      (compile_store_byte_chunks data_ptr bs offset)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  gvs[LET_THM] >>
  once_rewrite_tac[compile_store_byte_chunks_def] >>
  simp[LET_THM, comp_ignore_bind_def, gas_shadow_compiles_return] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_emit_void] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_bytelike_literal:
  gas_shadow_compiles (compile_bytelike_literal bytez max_len)
    (compile_bytelike_literal bytez max_len)
Proof
  simp[compile_bytelike_literal_def, LET_THM, comp_ignore_bind_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[gas_shadow_compiles_alloc_buffer, gas_shadow_compiles_emit_void,
               gas_shadow_compiles_store_byte_chunks]
       >> gen_tac >> BETA_TAC) >> simp[gas_shadow_compiles_return]
QED

Theorem gas_shadow_compiles_env_var:
  gas_shadow_compiles (compile_env_var ev) (compile_env_var ev)
Proof
  Cases_on `ev` >> simp[compile_env_var_def] >>
  rpt (match_mp_tac gas_shadow_compiles_bind >> conj_tac
       >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem gas_shadow_compiles_env_msggas:
  gas_shadow_compiles (compile_env_var MsgGas) (compile_env_var GasPrice)
Proof
  simp[compile_env_var_def, gas_shadow_compiles_emit_op]
QED

Theorem gas_shadow_compiles_literal_vv:
  gas_shadow_compiles (compile_literal_vv ty lit) (compile_literal_vv ty lit)
Proof
  Cases_on `lit`
  >- (rename1 `BoolL flag` >> Cases_on `flag` >>
      simp[compile_literal_vv_def, gas_shadow_compiles_return]) >>
  Cases_on `ty` >>
  simp[compile_literal_vv_def, gas_shadow_compiles_return,
       gas_shadow_compiles_bind, gas_shadow_compiles_bytelike_literal] >>
  rename1 `BaseT base_ty` >> Cases_on `base_ty` >>
  simp[compile_literal_vv_def, gas_shadow_compiles_return,
       gas_shadow_compiles_bind, gas_shadow_compiles_bytelike_literal] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  simp[gas_shadow_compiles_return, gas_shadow_compiles_bind,
       gas_shadow_compiles_bytelike_literal]
QED

Theorem gas_shadow_compiles_name_vv:
  gas_shadow_compiles (compile_name_vv cenv ty id) (compile_name_vv cenv ty id)
Proof
  Cases_on `FLOOKUP cenv.ce_vars id` >>
  simp[compile_name_vv_def, comp_ignore_bind_def, gas_shadow_compiles_return,
       gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst] >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[compile_name_vv_def, comp_ignore_bind_def, gas_shadow_compiles_return,
       gas_shadow_compiles_bind, gas_shadow_compiles_emit_inst]
QED
