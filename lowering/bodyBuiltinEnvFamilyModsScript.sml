(* Linked environment-family dispatcher for scalar builtin expressions. *)
Theory bodyBuiltinEnvFamilyMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyScalarStackVVMods
  bodyMsgGasCaseMods
  bodyEnvReadScalarMods bodyEnvPrevHashMods bodyLenOperandMods bodyLenLoadSuffixMods
  bodyBuiltinArgBranchesMods vyperState
  bodyAccountReadMods bodyIndexedHashReadMods
  bodyMethodIdFixedLiteralMods bodyMethodIdDynamicLiteralMods
  bodyMethodIdRuntimeOperandMods bodyMethodIdRuntimeSuffixMods
  bodyFullShadowBodyInv exprBodyPreProps exprSimHypsDefs
  vyperTypeBuiltins vyperTypeSystem vyperInterpreter vyperAST list

Theorem env_family_full_ok_mods:
  !mods exps cx ty bt es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt <> Len ==>
       body_exprs_full_ok_mods mods exps cx es) /\
    (!s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) /\ bt = Len ==>
       body_expr_full_ok_mods mods exps cx (HD es)) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bt = Env MsgGas`
  >- (qpat_x_assum `bt = Env MsgGas`
        (fn th => rw[th] >> irule body_msg_gas_case_mods))
  >- (simp[body_expr_full_ok_mods_def] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          Cases_on `bt = Len`
          >>> NTH_GOAL
            (gvs[] >>
             mp_tac len_sim_from_load_mods >>
             (impl_tac >- MATCH_ACCEPT_TAC len_load_suffix_mods) >>
             disch_then irule >>
             gvs[type_check_def, vyperStateTheory.assert_def] >>
             metis_tac[]) 1
          >>> NTH_GOAL (gvs[]) 1
          >>> NTH_GOAL
            (irule env_read_scalar_sim_mods >>
             metis_tac[scalar_stack_vv_sim_full_mods]) 1
          >>> NTH_GOAL
            (Cases_on `i = PrevHash`
             >- (gvs[] >> mp_tac prevhash_sim_mods >>
                 (impl_tac >- MATCH_ACCEPT_TAC scalar_stack_vv_sim_full_mods) >>
                 disch_then irule >> metis_tac[])
             >- (gvs[] >> mp_tac env_read_scalar_sim_mods >>
                 (impl_tac >- MATCH_ACCEPT_TAC scalar_stack_vv_sim_full_mods) >>
                 disch_then irule >> metis_tac[])) 1
          >>> NTH_GOAL
            (mp_tac account_read_sim_mods >>
             (impl_tac >- MATCH_ACCEPT_TAC scalar_stack_vv_sim_full_mods) >>
             disch_then irule >>
             gvs[type_check_def, vyperStateTheory.assert_def] >>
             metis_tac[]) 1
          >>> NTH_GOAL
            (mp_tac indexed_hash_read_sim_mods >>
             (impl_tac >- MATCH_ACCEPT_TAC scalar_stack_vv_sim_full_mods) >>
             disch_then irule >>
             gvs[type_check_def, vyperStateTheory.assert_def] >>
             metis_tac[]) 1
          >>> NTH_GOAL
            (mp_tac indexed_hash_read_sim_mods >>
             (impl_tac >- MATCH_ACCEPT_TAC scalar_stack_vv_sim_full_mods) >>
             disch_then irule >>
             gvs[type_check_def, vyperStateTheory.assert_def] >>
             metis_tac[]) 1
          >>> NTH_GOAL
            (gvs[type_check_def, vyperStateTheory.assert_def] >>
             Cases_on `es` >>
             qpat_assum `expr_body_pre_mods mods cenv cx env (Builtin ty MethodId es) es'`
               (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
             simp[Once well_typed_expr_def, well_typed_builtin_app_def,
                  vyperContextTheory.builtin_args_length_ok_def,
                  type_check_def, vyperStateTheory.assert_def] >>
             Cases_on `t` >>
             gvs[vyperContextTheory.builtin_args_length_ok_def, type_check_def,
                 vyperStateTheory.assert_def] >>
             strip_tac >> gvs[] >>
             (Cases_on `method_id_literal h`
              >- (mp_tac method_id_runtime_from_suffix_mods >>
                  (impl_tac >- MATCH_ACCEPT_TAC method_id_runtime_suffix_mods) >>
                  disch_then irule >>
                  gvs[body_exprs_full_ok_mods_def] >> metis_tac[])
              >- (`?la l. h = Literal la l` by
                    (Cases_on `h` >> gvs[exprLoweringTheory.method_id_literal_def] >>
                     metis_tac[]) >>
                  gvs[] >>
                  (rename1 `expr_sim_full_mods _ _ _ _ (Builtin (BaseT (BytesT (Fixed 4))) MethodId _) _ /\ _` >>
                   mp_tac method_id_fixed_literal_sim_mods >>
                   (impl_tac >- MATCH_ACCEPT_TAC scalar_stack_vv_sim_full_mods) >>
                   disch_then irule >> metis_tac[]
                   ORELSE
                   (irule method_id_dynamic_literal_sim_mods >> metis_tac[]))))) 1)
      >- (rpt gen_tac >> strip_tac >> gvs[]))
QED
