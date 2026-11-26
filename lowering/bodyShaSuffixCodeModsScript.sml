(* The real SHA suffix and its matching shadow classify one implicit GAS. *)
Theory bodyShaSuffixCodeMods
Ancestors
  bodyFullHashShaLayout bodyFullHashShaGas exprSimHash
  builtinHashing context emitHelper compileEnv exprLoweringProps
  venomInst list rich_list arithmetic pred_set
  vyperAST vyperTypeSystem gasExplicitSites gasShadowState gasShadowUnit

Theorem sha_fixed_count_no_dalloca[local]:
  compile_sha256_bytesm x m sm = (op,sb) ==>
  LENGTH (emitted_insts sm sb) = 7 /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sm sb)
Proof
  simp[compile_sha256_bytesm_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def]
QED

Theorem sha_memory_count_no_dalloca[local]:
  compile_sha256_bytes x sm = (op,sb) ==>
  LENGTH (emitted_insts sm sb) = 7 /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sm sb)
Proof
  simp[compile_sha256_bytes_def, compile_alloc_buffer_def, emit_op_def,
       emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def]
QED

Theorem sha_implicit_site[local]:
  MEM (mk_inst id GAS [] [gv]) code /\
  MAP (\i. (fn.fn_name,i.inst_id) IN explicit)
    (FILTER (\i. i.inst_opcode = GAS) code) = [F] ==>
  (fn.fn_name,id) NOTIN explicit
Proof
  strip_tac >> strip_tac >>
  `MEM (mk_inst id GAS [] [gv]) (FILTER (\i. i.inst_opcode = GAS) code)`
    by simp[MEM_FILTER, mk_inst_def] >>
  `MEM T (MAP (\i. (fn.fn_name,i.inst_id) IN explicit)
    (FILTER (\i. i.inst_opcode = GAS) code))` by
    (simp[MEM_MAP] >> qexists_tac `mk_inst id GAS [] [gv]` >> simp[mk_inst_def]) >>
  pop_assum mp_tac >> simp[]
QED

Theorem sha_suffix_code_mods:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
        BaseT (BytesT (Fixed n)) => compile_sha256_bytesm x n sm
      | _ => compile_sha256_word x sm) = (op,sb) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x shadow_sm
   else case expr_type e of
        BaseT (BytesT (Fixed n)) => compile_sha256_bytesm x n shadow_sm
      | _ => compile_sha256_word x shadow_sm) = (shadow_op,shadow_sb) /\
  gas_shadow_state sm shadow_sm /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func ==>
  same_blocks sm sb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  LENGTH (emitted_insts sm sb) = 7 /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb) /\
  EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sm sb) /\
  MAP (\i. (func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) = [F] /\
  ?prefix gv code.
    emitted_insts sm sb = prefix ++ mk_inst (sm.cs_next_id+3) GAS [] [gv]::code /\
    EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                ~is_terminator i.inst_opcode) code /\
    (func.fn_name,sm.cs_next_id+3) NOTIN gas_explicit_sites ctx shadow_ctx
Proof
  strip_tac >>
  qpat_x_assum `_ = (shadow_op,shadow_sb)`
    (fn th => drule_all_then strip_assume_tac sha256_typed_suffix_shape >>
              assume_tac th) >>
  `MAP (\i. (func.fn_name,i.inst_id) IN gas_explicit_sites ctx shadow_ctx)
    (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) = [F] /\
   LENGTH (emitted_insts sm sb) = 7 /\
   EVERY (\i. i.inst_opcode <> DALLOCA) (emitted_insts sm sb) /\
   ?prefix gv code.
     emitted_insts sm sb = prefix ++ mk_inst (sm.cs_next_id+3) GAS [] [gv]::code /\
     EVERY (\i. MEM i.inst_opcode [ALLOCA;MSTORE;MLOAD;ADD]) prefix /\
     EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
                 ~is_terminator i.inst_opcode) code` by
    (Cases_on `?n. bty = BytesT (Fixed n)`
     >- (gvs[is_bytestring_type_def] >>
         drule_all_then assume_tac sha_fixed_gas_classified >>
         qpat_x_assum `compile_sha256_bytesm _ _ shadow_sm = _` kall_tac >>
         drule_then strip_assume_tac sha_fixed_count_no_dalloca >>
         drule_then strip_assume_tac sha_fixed_gas_layout >>
         rpt conj_tac
         >- (qpat_assum `MAP _ (FILTER _ _) = [F]` mp_tac >> simp[])
         >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`prefix`,`gv`,`code`] >> gvs[]) >>
     `is_bytestring_type (expr_type e)` by
       (Cases_on `bty` >> gvs[is_bytes_or_string_type_def, is_bytestring_type_def] >>
        rename1 `expr_type e = BaseT (BytesT bd)` >>
        Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
     fs[] >> drule_all_then assume_tac sha_bytes_gas_classified >>
     qpat_x_assum `compile_sha256_bytes _ shadow_sm = _` kall_tac >>
     drule_then strip_assume_tac sha_memory_count_no_dalloca >>
     drule_then strip_assume_tac sha_bytes_gas_layout >>
     rpt conj_tac
     >- (qpat_assum `MAP _ (FILTER _ _) = [F]` mp_tac >> simp[])
     >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`prefix`,`gv`,`code`] >> gvs[]) >>
  `(func.fn_name,sm.cs_next_id+3) NOTIN gas_explicit_sites ctx shadow_ctx` by
    (irule sha_implicit_site >>
     qexistsl_tac [`emitted_insts sm sb`,`gv`] >>
     conj_tac >- first_assum ACCEPT_TAC >> simp[MEM_APPEND]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`prefix`,`gv`,`code`] >> asm_rewrite_tac[]
QED
