(* Lift the successful SHA machine endpoint to the linked frame. *)
Theory bodyShaSuccessLandingFrameMods
Ancestors
  bodyShaRegisteredFrameMods bodyShaSuffixPhysicalMods bodyShaSuffixLowTaintMods
  exprSimHash builtinHashing vyperInterpreter vyperCallOutcomeProps
  ghostPcTransportPtr bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs
  bodyInvSplit loweringStateRelDefs exprLoweringProps ptrDiscipline
  compileEnv venomState finite_map vyperAST vyperTypeSystem

Theorem sha_success_landing_frame_mods:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
          BaseT (BytesT (Fixed n)) => compile_sha256_bytesm x n sm
        | _ => compile_sha256_word x sm) = (op,sb) /\
  fn_has_code sm sb func /\ LENGTH (emitted_insts sm sb) = 7 /\
  stmt_state_rel H ctx func cenv cx mid s /\ local_ptrs_reserved cenv sm /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
  immutable_frame_mods func cenv cx mid s /\
  run_inst_seq (emitted_insts sm sb) s = OK z /\
  inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sm sb) s Gf tf /\
  ghost_inv_at (DF H) 0 d cenv cx (mid with outcomes := SOME rest) Gf tf
    (z with vs_inst_idx := s.vs_inst_idx + 7) /\
  ghost_kept_at 0 cenv mid sm G tn s Gf tf /\
  (!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s) /\
  pure_frame cenv func mid sm s z ==>
  let ef = SND (take_call_outcome NONE 2w (precompile_input Sha256 [v]) NONE mid);
      t = z with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sm sb) in
    ghost_inv_at_mods (DF H) lo d cenv cx ef Gf tf t /\
    immutable_frame_mods func cenv cx ef t /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> simp[] >>
  drule_all_then strip_assume_tac sha_suffix_physical_mods >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  Q.SUBGOAL_THEN
    `compile_sha256_bytes x sm = (op,sb) \/
     (?n J ce cy es. compile_sha256_bytesm x n sm = (op,sb) /\
        stmt_state_rel J ctx func ce cy es s /\ fn_has_code sm sb func)` assume_tac >-
    (Cases_on `?n. bty = BytesT (Fixed n)`
     >- (disj2_tac >> gvs[is_bytestring_type_def] >>
         qexistsl_tac [`n`,`H`,`cenv`,`cx`,`mid`] >> simp[]) >>
     `is_bytestring_type (expr_type e)` by
       (Cases_on `bty` >> gvs[is_bytes_or_string_type_def, is_bytestring_type_def] >>
        rename1 `expr_type e = BaseT (BytesT bd)` >>
        Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
     fs[]) >>
  `!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem` by
    (drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`) sha_suffix_low_taint_mods >>
     simp[] >> disch_then (qspecl_then [`x`,`op`] mp_tac) >>
     `compile_sha256_bytes x sm = (op,sb) \/
      (?n J ce cy es. compile_sha256_bytesm x n sm = (op,sb) /\
         stmt_state_rel J ctx func ce cy es s)` suffices_by simp[] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> simp[] >>
     disj2_tac >> qexistsl_tac [`n`,`J`,`ce`,`cy`,`es`] >> simp[]) >>
  `ghost_inv_at (DF H) 0 d cenv cx mid Gf tf z` by
    (qpat_assum `ghost_inv_at _ 0 _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ghost_inv_at_inst_idx, ghost_inv_at_def,
                      vyperStateTheory.evaluation_state_accfupds] >>
     disch_then ACCEPT_TAC) >>
  `!p. not_fresh_at sm p ==> lookup_var p z = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)` by
    fs[ghost_kept_at_def] >>
  drule_all_then strip_assume_tac sha_registered_frame_mods >>
  conj_tac
  >- (qpat_assum `ghost_inv_at_mods _ _ _ _ _ mid _ _ z` mp_tac >>
      `return_buf_ptr d cenv Gf tf (z with vs_inst_idx := s.vs_inst_idx + 7) <=>
       return_buf_ptr d cenv Gf tf z` by
        (Cases_on `d` >- simp[return_buf_ptr_def] >>
         rename1 `SOME buf` >> PairCases_on `buf` >>
         simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]) >>
      pop_assum (fn th => pure_rewrite_tac[ghost_inv_at_mods_def, th,
        ptr_covers_def, stor_taint_ok_at_def, lookup_var_def, allocas_from_def,
        venom_state_accfupds, take_call_outcome_preserved_fields]) >>
      disch_then ACCEPT_TAC) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `immutable_frame_mods _ _ _ mid z` mp_tac >>
  pure_rewrite_tac[immutable_frame_mods_def, immutables_rel_mods_def,
       immutables_rel_def, immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       local_region_def, lookup_var_def, venom_state_accfupds,
       take_call_outcome_preserved_fields] >>
  disch_then ACCEPT_TAC
QED
