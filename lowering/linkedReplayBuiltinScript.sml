Theory linkedReplayBuiltin
Ancestors
  constSubstCorrect constSubstMods vyperTypeContract vyperTypeSystem
  vyperInterpreter vyperContext vyperState vyperAST vyperTypeEvalCaseProofs
  list option alist pair

Theorem linked_replay_builtin_case:
  const_subst_context roots cx env [] mods art /\
  (!e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
       expr_type (subst_consts_expr_mods E e) = expr_type e) /\
  (!xs. EVERY (\e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
      !s. const_cells_agree roots s ==>
        const_computations_related (const_results_related roots cx (expr_type e))
          (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
        (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
          eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) xs ==>
    well_typed_exprs env xs ==> !s. const_cells_agree roots s ==>
      eval_exprs cx xs s = eval_exprs cx (subst_consts_exprs_mods E xs) s) /\
  (!src id r. ALOOKUP E (src,id) = SOME r ==> constant_expr mods r) /\
  EVERY (\e. (well_typed_expr env e \/ IS_SOME (type_place_expr env e)) ==>
    !s. const_cells_agree roots s ==>
      const_computations_related (const_results_related roots cx (expr_type e))
        (eval_expr cx e) (eval_expr cx (subst_consts_expr_mods E e)) s /\
      (!kt vt. type_place_expr env e = SOME (HashMapT kt vt) ==>
        eval_expr cx e s = eval_expr cx (subst_consts_expr_mods E e) s)) es ==>
  (well_typed_expr env (Builtin ty bi es) \/ IS_SOME (type_place_expr env (Builtin ty bi es))) ==>
  !s. const_cells_agree roots s ==>
    const_computations_related (const_results_related roots cx (expr_type (Builtin ty bi es)))
      (eval_expr cx (Builtin ty bi es)) (eval_expr cx (subst_consts_expr_mods E (Builtin ty bi es))) s /\
    (!kt vt. type_place_expr env (Builtin ty bi es) = SOME (HashMapT kt vt) ==>
      eval_expr cx (Builtin ty bi es) s = eval_expr cx (subst_consts_expr_mods E (Builtin ty bi es)) s)
Proof
  simp[frame_place_expr_other] >> strip_tac >>
  simp[Once well_typed_expr_def] >> rpt strip_tac >>
  rename1 `const_cells_agree roots st` >>
  `!xs. subst_consts_exprs_mods E xs = MAP (subst_consts_expr_mods E) xs` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `MAP expr_type (MAP (subst_consts_expr_mods E) es) = MAP expr_type es` by
    (simp[MAP_MAP_o, MAP_EQ_f, combinTheory.o_DEF] >>
     rpt strip_tac >> first_x_assum irule >> disj1_tac >>
     irule frame_well_typed_exprs_member >> metis_tac[]) >>
  (* A replacement cannot introduce the syntax of self or address.code. *)
  `!e. is_self_addr (subst_consts_expr_mods E e) = is_self_addr e` by
    (gen_tac >> Cases_on `e` >> simp[subst_consts_expr_mods_def, is_self_addr_def] >>
     all_tac >~ [`subst_consts_expr_mods E (TopLevelName ty ns)`] >-
       (PairCases_on `ns` >> simp[subst_consts_expr_mods_def, is_self_addr_def] >>
        Cases_on `ALOOKUP E (ns0,ns1)` >> simp[] >>
        `constant_expr mods x` by metis_tac[] >>
        Cases_on `x` >> gvs[constant_expr_def, is_self_addr_def] >>
        rename1 `Builtin ann b args` >> Cases_on `b` >>
        gvs[constant_builtin_def, is_self_addr_def]) >>
     rename1 `is_self_addr (Builtin ann b (MAP (subst_consts_expr_mods E) args))` >>
     Cases_on `b` >> simp[is_self_addr_def] >>
     rename1 `Env op` >> Cases_on `op` >> simp[is_self_addr_def] >>
     Cases_on `args` >> simp[is_self_addr_def]) >>
  `is_self_codesize bi (MAP (subst_consts_expr_mods E) es) =
   is_self_codesize bi es` by
    (Cases_on `bi` >> gvs[is_self_codesize_def] >>
     Cases_on `es` >> gvs[is_self_codesize_def] >>
     Cases_on `t` >> gvs[]) >>
  `!e ct addr'. subst_consts_expr_mods E e = Builtin ct (Acc Code) [addr'] <=>
     ?addr. e = Builtin ct (Acc Code) [addr] /\ addr' = subst_consts_expr_mods E addr` by
    (rpt gen_tac >> Cases_on `e` >>
     simp[subst_consts_expr_mods_def, MAP_EQ_CONS] >>
     all_tac >~ [`subst_consts_expr_mods E (TopLevelName ty ns)`] >-
       (PairCases_on `ns` >> simp[subst_consts_expr_mods_def] >>
        Cases_on `ALOOKUP E (ns0,ns1)` >> simp[] >>
        strip_tac >> first_x_assum drule >> simp[constant_expr_def, constant_builtin_def]) >>
     metis_tac[]) >>
  `code_slice_source bi (MAP (subst_consts_expr_mods E) es) =
   OPTION_MAP (\(ct,addr). (ct,subst_consts_expr_mods E addr)) (code_slice_source bi es)` by
    (Cases_on `code_slice_source bi es`
     >- (Cases_on `code_slice_source bi (MAP (subst_consts_expr_mods E) es)` >> simp[] >>
         PairCases_on `x` >> gvs[code_slice_source_SOME, MAP_EQ_CONS] >>
         rename1 `Builtin ct (Acc Code) [addr'] = subst_consts_expr_mods E hd` >>
         `?addr. hd = Builtin ct (Acc Code) [addr]` by metis_tac[] >> gvs[]) >>
     PairCases_on `x` >> gvs[code_slice_source_SOME] >> simp[subst_consts_expr_mods_def]) >>
  simp_tac bool_ss [subst_consts_expr_mods_def, expr_type_def] >>
  CONV_TAC (RATOR_CONV (RATOR_CONV (RAND_CONV (SIMP_CONV bool_ss [Once evaluate_def])))) >>
  CONV_TAC (RATOR_CONV (RAND_CONV (SIMP_CONV bool_ss [Once evaluate_def]))) >>
  simp[ignore_bind_def] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  `s = st` by gvs[type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[] >> Cases_on `bi = Len`
  >- suspend "len" >>
  Cases_on `bi = Env MsgGas` >> simp[]
  >- (irule const_computations_related_refl >> simp[const_results_related_def]) >>
  Cases_on `code_slice_source bi es`
  >- suspend "ordinary" >>
  suspend "slice"
QED

Resume linked_replay_builtin_case[len]:
  gvs[] >> Cases_on `es` >>
  gvs[well_typed_builtin_app_def, Once well_typed_expr_def] >>
  simp_tac bool_ss [GSYM vyperStateTheory.bind_assoc] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_prefix >> reverse conj_tac
      >- (simp_tac bool_ss [SF ETA_ss] >>
          irule const_computations_related_length >>
          qexistsl [`expr_type h`, `roots`] >> conj_tac
          >- metis_tac[const_subst_context_expr_frame] >>
          metis_tac[]) >>
      rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> irule const_computations_related_refl >>
  simp[const_results_related_def]
QED

Resume linked_replay_builtin_case[ordinary]:
  simp_tac bool_ss [GSYM vyperStateTheory.bind_assoc] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_prefix >> reverse conj_tac
      >- (simp[const_computations_related_eq] >>
          qpat_assum `!xs. EVERY _ xs ==> _` (qspec_then `es` mp_tac) >> simp[]) >>
      rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[const_results_related_def]
QED

Resume linked_replay_builtin_case[slice]:
  PairCases_on `x` >>
  rename1 `code_slice_source bi es = SOME (ct,addr)` >>
  drule_all code_slice_operand_typing >> strip_tac >>
  `?rest. es = Builtin ct (Acc Code) [addr]::rest` by gvs[code_slice_source_SOME] >>
  gvs[EVERY_DEF] >>
  simp_tac bool_ss [vyperStateTheory.bind_assoc] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (simp[const_computations_related_eq] >>
      qpat_assum `!xs. EVERY _ xs ==> _` (qspec_then `rest` mp_tac) >> simp[]) >>
  rpt strip_tac >> BETA_TAC >>
  rename1 `eval_exprs cx rest s = (INL tail_vs,t)` >>
  `const_cells_agree roots t` by (drule_all const_subst_context_exprs_frame >> simp[]) >>
  simp_tac bool_ss [GSYM vyperStateTheory.bind_assoc] >>
  irule const_computations_related_prefix >> reverse conj_tac
  >- (irule const_computations_related_prefix >> reverse conj_tac
      >- (irule const_computations_related_prefix >> reverse conj_tac
          >- suspend "code_source" >>
          rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
      rpt strip_tac >> irule const_computations_related_refl >> simp[]) >>
  rpt strip_tac >> irule const_computations_related_refl >> simp[const_results_related_def]
QED

(* The slice reads its tail before the code source. For non-self code,
   observe the typed code head at that successor state. *)
Resume linked_replay_builtin_case[code_source]:
  simp[const_computations_related_eq] >>
  Cases_on `is_self_addr addr`
  >- (Cases_on `addr` >> gvs[is_self_addr_def] >>
      rename1 `Builtin ann b args` >> Cases_on `b` >>
      gvs[is_self_addr_def] >> rename1 `Env ev` >> Cases_on `ev` >>
      gvs[is_self_addr_def] >> Cases_on `args` >>
      gvs[is_self_addr_def, subst_consts_expr_mods_def]) >>
  `!a. ~is_self_addr a ==>
      bind (eval_exprs cx [a]) (\avs. bind get_accounts (\acc.
        lift_sum (evaluate_code_source cx acc F ct (expr_type a) avs))) =
      bind (eval_expr cx (Builtin ct (Acc Code) [a])) (read_result cx)` by
    (gen_tac >> strip_tac >>
     CONV_TAC (RHS_CONV (LAND_CONV (SIMP_CONV bool_ss [Once evaluate_def]))) >>
     simp[evaluate_code_source_def, builtin_args_length_ok_def, type_check_def,
          assert_def, ignore_bind_def, precompile_call_success_def,
          vyperStateTheory.bind_return] >>
     simp[vyperStateTheory.bind_assoc, vyperStateTheory.bind_return,
          vyperStateTheory.assert_def, read_result_def] >>
     `assert T (Error (TypeError "Builtin args")) = return ()` by
       simp[FUN_EQ_THM, vyperStateTheory.assert_def, return_def] >>
     simp[vyperStateTheory.bind_return] >>
     AP_TERM_TAC >> ABS_TAC >> AP_TERM_TAC >> ABS_TAC >>
     Cases_on `evaluate_builtin cx acc ct (Acc Code) [expr_type a] avs` >>
     simp[FUN_EQ_THM, is_self_codesize_def, bind_def, lift_sum_def, return_def, raise_def]) >>
  simp[] >> rewrite_tac[GSYM const_computations_related_eq] >>
  irule const_computations_related_bind >>
  qexists `const_results_related roots cx ct` >> reverse conj_tac
  >- (qpat_x_assum `!u. const_cells_agree roots u ==> const_computations_related _ _ _ u /\ _`
        (qspec_then `t` mp_tac) >> simp[expr_type_def, subst_consts_expr_mods_def]) >>
  rpt strip_tac >> irule const_computations_related_read >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `eval_expr cx (Builtin _ _ [subst_consts_expr_mods E _]) _ = _` kall_tac >>
  irule const_subst_context_expr_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Finalise linked_replay_builtin_case
