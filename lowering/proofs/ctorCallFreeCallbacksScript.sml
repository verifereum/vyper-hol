(* Callback boundaries: hypotheses are restricted to the actual children. *)
Theory ctorCallFreeCallbacks
Ancestors
  list pair compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules supportedExprTraverse

Theorem every_state_insts_lower_value:
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ty e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ty e st)))
Proof
  strip_tac >> simp[lower_value_def, every_state_insts_bind]
QED

Theorem every_state_insts_lower_value_with_loc:
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ty e st)))) /\
  (!vv st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (unwrap_value cenv vv st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value_with_loc cfn cenv ty e st)))
Proof
  strip_tac >> simp[lower_value_with_loc_def, every_state_insts_bind,
    every_state_insts_return]
QED

Theorem call_free_multi_exprs:
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_multi_exprs cfn cenv es st)))
Proof
  rpt disch_tac >> Induct >- simp[compile_multi_exprs_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[compile_multi_exprs_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- (ho_match_mp_tac every_state_insts_lower_value >> simp[ ]) >>
  gen_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[] >>
  simp[every_state_insts_return]
QED

Theorem call_free_make_tuple:
  (!ce src dst dty sty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) ==>
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !buf off st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_make_tuple cfn cenv es buf off st)))
Proof
  rpt disch_tac >> Induct >- simp[compile_make_tuple_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_make_tuple_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])])
QED

Theorem call_free_make_array_elems:
  (!ce src dst dty sty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) ==>
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !ety sz len_word buf idx st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_make_array_elems cfn cenv es ety sz len_word buf idx st)))
Proof
  rpt disch_tac >> Induct >- simp[compile_make_array_elems_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_make_array_elems_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])])
QED

Theorem call_free_make_array:
  (!ce src dst dty sty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) /\
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  (!e ty st. MEM e es ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_make_array cfn cenv es ety sz len_word buf st)))
Proof
  strip_tac >> strip_tac >> simp[compile_make_array_def] >> Cases_on `len_word` >> simp[] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_make_array_elems, call_free_emit_void,
      every_state_insts_return])])
QED

Theorem call_free_struct_lit:
  (!ce src dst dty sty st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_store_memory ce src dst dty sty st)))) ==>
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !fields cfn cenv.
  (!name e ty st. MEM (name,e) fields ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !sty buf off st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_struct_lit cfn cenv sty fields buf off st)))
Proof
  rpt disch_tac >> Induct >- simp[compile_struct_lit_def, every_state_insts_return] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >> gvs[] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_struct_lit_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])]) >> metis_tac[]
QED

Theorem call_free_concat:
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !data_op infos off_op st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_concat cfn cenv es data_op infos off_op st)))
Proof
  rpt disch_tac >> Induct >- simp[compile_concat_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >> rpt gen_tac >>
  Cases_on `infos` >> simp[compile_concat_def, every_state_insts_return] >>
  rename1 `compile_concat _ _ _ _ (info::rest) _` >> PairCases_on `info` >>
  Cases_on `info0` >> qid_spec_tac `st` >> simp[compile_concat_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_lower_value >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void, every_state_insts_return])])
QED

Theorem call_free_abi_encode_args:
  (!ce ty vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_materialize_vv ce ty vv st)))) ==>
  (!ce vv st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (unwrap_value ce vv st)))) ==>
  !es cfn cenv.
  (!e ty st. MEM e es ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty e st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_encode_args cfn cenv es st)))
Proof
  rpt disch_tac >> Induct >- simp[compile_abi_encode_args_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >> simp[compile_abi_encode_args_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return])])
QED

Theorem call_free_attribute:
  (!st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (cfn cenv ty base_e st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_attribute cfn cenv ret_ty ty base_e field_name st)))
Proof
  strip_tac >> simp[compile_attribute_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])])
QED

Theorem call_free_acc:
  (!st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (lower_value cfn cenv (BaseT AddressT) addr_e st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_acc cfn cenv addr_e accessor st)))
Proof
  strip_tac >> Cases_on `accessor` >> simp[compile_acc_def] >>
  rpt gen_tac >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  `BALANCE <> RETURNDATACOPY /\ BALANCE <> INVOKE /\
   EXTCODEHASH <> RETURNDATACOPY /\ EXTCODEHASH <> INVOKE /\
   EXTCODESIZE <> RETURNDATACOPY /\ EXTCODESIZE <> INVOKE /\
   GT <> RETURNDATACOPY /\ GT <> INVOKE /\
   INVALID <> RETURNDATACOPY /\ INVALID <> INVOKE` by simp[] >>
  metis_tac[call_free_emit_op, call_free_emit_inst, SND]
QED

Theorem every_state_insts_subscript:
  (!ety st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ety idx_e st)))) /\
  (!st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (cfn cenv ty base_e st)))) /\
  (!v st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_keccak256_key v F st)))) /\
  (!v k st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_mapping_subscript v k st)))) /\
  (!v off st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_tuple_subscript v off st)))) /\
  (!v idx dyn count ws sz signed loc st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_array_subscript v idx dyn count ws sz signed
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st)))) ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_subscript cfn cenv ret_ty ty base_e idx_e st)))
Proof
  strip_tac >> simp[compile_subscript_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> reverse (Cases_on `place_type cenv base_e`) >> simp[]
  >- (rename1 `ValPT bty` >> Cases_on `bty` >> simp[] >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return])])) >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[every_state_insts_return])])
QED

Theorem every_state_insts_get_target_ptr:
  (!e ety st. ~supported_expr_exists R e /\ ~supported_expr_exists root2 e ==>
    EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (lower_value cfn cenv ety e st)))) /\
  (!v st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_keccak256_key v F st)))) /\
  (!v k st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_mapping_subscript v k st)))) /\
  (!ops st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (emit_op ADD ops st)))) /\
  (!v idx dyn count ws sz signed loc st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_array_subscript v idx dyn count ws sz signed
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st)))) ==>
  !target. ~supported_target_exists R target /\ ~supported_target_exists root2 target ==>
  !st. EVERY P (state_insts st) ==>
    EVERY P (state_insts (SND (compile_get_target_ptr cfn cenv target st)))
Proof
  strip_tac >>
  `( !e:expr. T) /\ (!target. ~supported_target_exists R target /\
     ~supported_target_exists root2 target ==> !st. EVERY P (state_insts st) ==>
     EVERY P (state_insts (SND (compile_get_target_ptr cfn cenv target st))))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[supported_expr_exists_def, compile_get_target_ptr_def] >> rpt conj_tac >> rpt gen_tac
  >- (rpt CASE_TAC >> simp[every_state_insts_return])
  >- (rpt CASE_TAC >> simp[every_state_insts_return])
  >- (ntac 2 strip_tac >> ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
      gen_tac >> Cases_on `SND (SND result)` >> simp[] >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return, every_state_insts_bind]),
        CHANGED_TAC (BasicProvers.TOP_CASE_TAC >> simp[])]) >>
      rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
        gen_tac, CHANGED_TAC (simp[every_state_insts_return])])) >>
  strip_tac >> gen_tac >> strip_tac >> gvs[] >> ho_match_mp_tac every_state_insts_bind >> conj_tac >- simp[] >>
  gen_tac >> simp[every_state_insts_bind, every_state_insts_return]
QED

(* Strict subscript prerequisites; allocation remains a cross-family premise. *)
Theorem call_free_mapping_subscript:
  (!sz st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_alloc_buffer sz st)))) ==>
  !base key st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_mapping_subscript base key st)))
Proof
  strip_tac >> rpt gen_tac >> qid_spec_tac `st` >> simp[compile_mapping_subscript_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_keccak256_key:
  !v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_keccak256_key v F st)))
Proof
  gen_tac >> simp[compile_keccak256_key_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op])])
QED

Theorem call_free_tuple_subscript:
  !base off st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_tuple_subscript base off st)))
Proof
  simp[compile_tuple_subscript_def, call_free_emit_op]
QED

Theorem call_free_array_subscript:
  !base idx dyn count ws sz signed loader.
  (!v st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (loader v st)))) ==>
  !st. EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_array_subscript base idx dyn count ws sz signed loader st)))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dyn` >> Cases_on `signed` >> simp[compile_array_subscript_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      every_state_insts_return])])
QED
