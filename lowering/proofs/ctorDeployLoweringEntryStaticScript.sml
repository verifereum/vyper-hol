Theory ctorDeployLoweringEntryStatic
Ancestors
  loweringStateRelDefs
 ctorDeployLoweringDefs ctorDeployLoweringEntryPrefix ctorDeployLoweringFrame
 exprOpenTerminals exprOpenPrimitives moduleLowering emitHelperProps compileEnv venomInst abiEncoder
Libs dep_rewrite

Theorem deploy_ctor_clamp_open:
 !cl v sa u sb. ~block_is_terminated sa /\
 compile_abi_clamp_basetype v cl sa = (u,sb) ==> ~block_is_terminated sb
Proof
 Cases >> simp[abiEncoderTheory.compile_abi_clamp_basetype_def,
   abiEncoderTheory.compile_abi_int_clamp_def,
   abiEncoderTheory.compile_abi_bytes_clamp_def, comp_return_def,
   comp_bind_def, comp_ignore_bind_def] >>
 rpt gen_tac >> rpt (IF_CASES_TAC >> gvs[]) >>
 simp[comp_bind_def, comp_ignore_bind_def] >>
 rpt (pairarg_tac >> gvs[]) >> strip_tac >>
 drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem deploy_ctor_optional_store_open:
 !ce name v sa u sb.
 ~block_is_terminated sa /\
 (case FLOOKUP ce.ce_vars name of
   NONE => comp_return ()
 | SOME loc => case var_location_decode_operand loc of
     NONE => comp_return () | SOME dst => emit_void MSTORE [dst;v]) sa = (u,sb) ==>
 ~block_is_terminated sb
Proof
 rpt gen_tac >> Cases_on `FLOOKUP ce.ce_vars name`
 >- (simp[comp_return_def] >> metis_tac[]) >>
 Cases_on `var_location_decode_operand x`
 >- (simp[comp_return_def] >> metis_tac[]) >>
 simp[] >> strip_tac >> drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem deploy_ctor_decode_args_open:
 !args ce off hi adj sa u sb.
 ~block_is_terminated sa /\
 compile_decode_args ce args off DLOAD hi adj sa = (u,sb) ==>
 ~block_is_terminated sb
Proof
 Induct >- simp[compile_decode_args_def, comp_return_def] >>
 PairCases >> rpt gen_tac >>
 Cases_on `h1` >> Cases_on `h2` >>
 simp[compile_decode_args_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
 Cases_on `FLOOKUP ce.ce_vars h0` >>
 simp[] >>
 TRY (rename1 `SOME loc` >> Cases_on `var_location_decode_operand loc`) >>
 simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
 rpt (pairarg_tac >> gvs[]) >> strip_tac >>
 gvs[AllCaseEqs()] >>
 imp_res_tac emit_op_nonterminator_open >> fs[is_terminator_def] >>
 imp_res_tac compile_abi_decode_to_buf_open >>
 imp_res_tac deploy_ctor_clamp_open >>
 imp_res_tac deploy_ctor_optional_store_open >>
 imp_res_tac emit_void_terminated >> fs[is_terminator_def] >>
 qpat_x_assum `!ce off hi adj sa sb. ~block_is_terminated sa /\
   compile_decode_args ce args off DLOAD hi adj sa = ((),sb) ==> _`
   (fn ih => first_assum (mp_then (Pos last) mp_tac ih)) >>
 simp[]
QED

Theorem deploy_ctor_register_args_open:
 !args ce off size sa ce' sb.
 ~block_is_terminated sa /\
 compile_register_constructor_args ce args off size sa = (ce',sb) ==>
 ~block_is_terminated sb
Proof
 Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
 PairCases >> rpt gen_tac >>
 Cases_on `FLOOKUP ce.ce_vars h0` >>
 simp[Once compile_register_constructor_args_def] >>
 TRY (rename1 `SOME loc` >> Cases_on `var_location_memory_size loc`) >>
 simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
 rpt (pairarg_tac >> gvs[]) >> strip_tac >>
 imp_res_tac compile_alloc_buffer_open >>
 imp_res_tac deploy_ctor_decode_args_open >>
 qpat_x_assum `!ce off size sa ce' sb. _` 
   (fn ih => first_assum (mp_then (Pos last) mp_tac ih)) >> simp[]
QED

Theorem deploy_ctor_body_entry_static:
 !tops rp runtime_bc unit body cenv nr key ut imm lbl sa sb sj se sp sf func.
 deploy_ctor_code tops rp runtime_bc unit
  (body,cenv,nr,key,ut,imm,lbl,sa,sb,sj,se,sp,sf,func) /\ nr = F ==>
 local_ptrs_reserved cenv sa /\ ~block_is_terminated sa
Proof
 rpt gen_tac >> strip_tac >> gvs[] >>
 qpat_x_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
 simp[deploy_ctor_code_def, comp_return_def] >> strip_tac >>
 PairCases_on `cf` >>
 drule_all deploy_ctor_target_reserved_entry >> strip_tac >>
 drule_all deploy_ctor_pre_register_unterminated >> strip_tac >>
 drule_all deploy_ctor_register_args_open >> strip_tac >>
 gvs[fresh_label_def, comp_bind_def, comp_return_def,
     local_ptrs_reserved_def, not_fresh_at_def, block_is_terminated_def] >>
 metis_tac[]
QED
