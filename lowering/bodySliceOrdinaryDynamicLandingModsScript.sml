(* The captured bytes are kept by the original operand's placement. *)
Theory bodySliceOrdinaryDynamicLandingMods
Ancestors
  bodySliceDynamicCaptureMods bodySliceSavedWordsMods bodyFullIfExpReach
  exprSimSliceOrdinaryEntry exprSimSliceMemory stmtSimLogArgs valueCopyBytes
  allocasBelowFmpUpdatesProps bodyPtrBopOperandRetention bodyPtrPrecompileBuiltinsGhost
  exprSimWordArgs exprLoweringProps loweringPosts vyperStorageTrace
  vyperStorageFootprint vyperState vyperTypeValues wordArgsPtr
  exprSimProps exprSimAttributeFields valueEncodingProofs bodyPtrDefs
  bodyExtractSavedDescriptorMods
  venomState ptrDiscipline freshWrites
Libs monadsyntax

Triviality slice_base_clear:
  expr_sim_inv_mods mods cenv cx env es ==>
  log_arg_clear cenv cx (BaseT bt) v
Proof
  strip_tac >> rw[log_arg_clear_def] >>
  drule evaluate_type_BaseT_cases >> strip_tac >> gvs[] >>
  `dynarray_free (BaseTV btv)` by simp[dynarray_free_base] >>
  drule_all extract_local_window_apart >> simp[]
QED

val payload = ``\op bt (tv:type_value) v sa sb es s q bs tn.
  expr_val_at cenv cx (BaseT bt) sa sb es v op s /\
  eval_operand op s = SOME q /\
  mem_bytes_at (w2n q + 32) (LENGTH bs) s.vs_memory = bs /\
  (!j. w2n q + 32 <= j /\ j < w2n q + 32 + LENGTH bs ==> j NOTIN tn.t_mem)``;

Triviality dynamic_window_step:
  ^payload op bt tv v sa a es s q bs tn /\
  is_bytestring_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\
  32 + LENGTH bs <= val_footprint tv v /\
  (!z. op = Var z ==> not_fresh_at a z) /\
  (!l. op <> Label l) /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv a /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  a.cs_next_id <= b.cs_next_id /\
  wb_frame cenv es ee a s t /\
  ghost_kept_at lo cenv es a G tn s G' tn' /\
  log_arg_clear cenv cx (BaseT bt) v ==>
  ^payload op bt tv v sa b ee t q bs tn'
Proof
  BETA_TAC >> strip_tac >>
  conj_tac
  >- (irule log_frame_placement >>
      qpat_assum `stmt_state_rel _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `wb_frame _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  conj_tac
  >- (irule log_frame_operand >> qpat_assum `wb_frame _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `~is_word_type (BaseT bt)` by metis_tac[is_bytestring_word_type] >>
  `log_arg_clear cenv cx (BaseT bt) v` by simp[slice_base_clear] >>
  conj_tac
  >- (drule_all log_argument_footprint_kept >> strip_tac >>
      `mem_bytes_at (w2n q + 32) (LENGTH bs) t.vs_memory =
       mem_bytes_at (w2n q + 32) (LENGTH bs) s.vs_memory` by
        (irule mem_bytes_at_translated_window >> qexists_tac `val_footprint tv v` >> simp[]) >> simp[]) >>
  `ghost_kept cenv es a G tn s G' tn'` by
    (rewrite_tac[ghost_kept_def] >>
     first_assum (ACCEPT_TAC o REWRITE_RULE [ghost_kept_at_def])) >>
  rpt strip_tac >> spose_not_then assume_tac >>
  `w2n q <= j /\ j < w2n q + val_footprint tv v` by decide_tac >>
  drule_all bop_argument_taint_kept >> simp[]
QED

val header = ``\a s G tn lp dp p bs.
  not_fresh_at a lp /\ not_fresh_at a dp /\
  eval_operand (Var lp) s = SOME (n2w (LENGTH bs)) /\
  op_prov G (Var lp) = NONE /\ op_taint tn (Var lp) = {} /\
  lookup_var dp s = SOME p /\ ptr_covers G tn dp s (LENGTH bs) /\
  w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= s.vs_alloca_next``;

Triviality dynamic_header_step:
  ^header a s G tn lp dp p bs /\ wb_frame cenv es ee a s t /\
  ghost_kept_at lo cenv es a G tn s G' tn' /\
  a.cs_next_var <= b.cs_next_var /\ s.vs_alloca_next <= t.vs_alloca_next ==>
  ^header b t G' tn' lp dp p bs
Proof
  BETA_TAC >> strip_tac >>
  `lookup_var lp t = SOME (n2w (LENGTH bs)) /\ lookup_var dp t = SOME p` by
    fs[wb_frame_def,eval_operand_def] >>
  `ghost_kept cenv es a G tn s G' tn'` by
    (rewrite_tac[ghost_kept_def] >>
     first_assum (ACCEPT_TAC o REWRITE_RULE [ghost_kept_at_def])) >>
  `ptr_covers G' tn' dp t (LENGTH bs)` by
    (irule ghost_kept_ptr_covers >>
     qpat_assum `ghost_kept _ _ _ _ _ _ _ _` (irule_at Any) >> simp[eval_operand_def]) >>
  `FLOOKUP G' lp = FLOOKUP G lp /\ op_taint tn' (Var lp) = op_taint tn (Var lp)` by
    fs[ghost_kept_at_def] >>
  simp[eval_operand_def,op_prov_def] >> rpt conj_tac
  >- (irule not_fresh_at_mono >> qexists_tac `a` >> simp[])
  >- (irule not_fresh_at_mono >> qexists_tac `a` >> simp[])
  >> fs[op_prov_def] >> decide_tac
QED

Theorem slice_ordinary_dynamic_landing_mods:
  ^payload op bt tv v sa a es s q bs tn /\
  is_bytestring_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\
  32 + LENGTH bs <= val_footprint tv v /\
  (!z. op = Var z ==> not_fresh_at a z) /\
  (!l. op <> Label l) /\
  stmt_state_rel H ctx func cenv cx es s /\
  local_ptrs_reserved cenv a /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  a.cs_next_id <= b.cs_next_id /\
  wb_frame cenv es ee a s t /\
  ghost_kept_at lo cenv es a G tn s G' tn' /\
  log_arg_clear cenv cx (BaseT bt) v ==>
  ^payload op bt tv v sa b ee t q bs tn'
Proof
  strip_tac >> drule_all dynamic_window_step >> simp[]
QED
