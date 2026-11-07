Theory exprSimPopNestedLocalSuffix
Ancestors
  exprSimPopNestedLocalPost exprSimPopNestedLocalRun exprSimProps
  venomState words arithmetic list exprSimHyps exprSimHypsDefs vyperTypeEnv
  exprSimPopNestedLocalPtrs exprSimWordArgs exprLoweringProps compileEnv
  loweringPosts localPtrsProps exprSimAttributeFields finite_map valueEncoding
  exprSimVVFrame

Theorem memory_pop_result_address:
  vs <> [] /\ LENGTH vs < dimword (:256) /\
  w2n (h:bytes32) = locbase + k /\
  locbase + sz < dimword (:256) /\
  k + 32 + (LENGTH vs - 1) * esz <= sz /\
  lookup_var x u = SOME (h + 32w + (n2w (LENGTH vs) - 1w) * n2w esz) ==>
  eval_operand (Var x) u = SOME (h + 32w + (n2w (LENGTH vs) - 1w) * n2w esz) /\
  w2n (h + 32w + (n2w (LENGTH vs) - 1w) * n2w esz) =
    locbase + k + 32 + (LENGTH vs - 1) * esz
Proof
  strip_tac >> conj_tac >- simp[eval_operand_def] >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `n2w (LENGTH vs) - 1w = n2w (LENGTH vs - 1) : bytes32` by
    simp[GSYM wordsTheory.n2w_sub] >>
  asm_rewrite_tac[] >>
  rewrite_tac[GSYM wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w,
    wordsTheory.WORD_ADD_ASSOC] >>
  `w2n h + (sz - k) < dimword (:256) /\
   32 + (LENGTH vs - 1) * esz <= sz - k` by decide_tac >>
  drule_all buffer_offset_no_wrap >>
  pure_rewrite_tac[GSYM wordsTheory.word_mul_n2w,
    GSYM wordsTheory.WORD_ADD_ASSOC, GSYM wordsTheory.word_add_n2w] >>
  disch_tac >> decide_tac
QED

Theorem pop_array_element_layout:
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (ArrayT ann bd) = SOME (ArrayTV etv bd') ==>
  evaluate_type (get_tenv cx) ann = SOME etv /\
  type_memory_bytes cenv ann = type_memory_size etv
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) ann = SOME etv` by
    gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  simp[] >> irule expr_sim_inv_memory_size >>
  goal_assum (drule_at Any) >> fs[expr_body_pre_def] >> metis_tac[]
QED

Theorem pop_memory_live_suffix_post:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  stmt_state_rel ctx func cenv cx mid s /\
  wb_frame cenv es sa s0 s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM scopes' /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  lookup_scopes id mid.scopes = SOME entry /\
  lookup_scopes id scopes' = SOME (entry with <|value := updated; popped := hist|>) /\
  (!j. j <> id ==> lookup_scopes j scopes' = lookup_scopes j mid.scopes) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME b /\
  local_region cenv mid.scopes s id (w2n b) sz /\ k + 32 <= sz /\
  mutable_place_path entry.type path /\ value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ val_wf entry.type entry.value /\
  val_in_memory entry.type entry.value (w2n b) s.vs_memory /\
  type_memory_size entry.type <= sz /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
  local_path_at cenv cx id k (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  u = s with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|> /\
  u.vs_memory = (mstore (w2n b + k) (n2w (LENGTH vs - 1)) s).vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  read_result cx result (mid with scopes := scopes') =
    (INL (LAST vs),mid with scopes := scopes') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  eval_operand op u = SOME w /\
  w2n w = w2n b + k + 32 + (LENGTH vs - 1) * type_memory_size etv /\
  local_place_at cenv cx id (k + 32 + (LENGTH vs - 1) * type_memory_size etv)
    etv result ==>
  vv_post ctx func cenv cx e es sa sb s0 (mid with scopes := scopes') result
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) (u with vs_inst_idx := idx)
Proof
  pure_rewrite_tac[vv_post_inst_idx] >> strip_tac >>
  `local_ptrs_rel func cenv mid.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `u = _ with <|vs_vars := _; vs_memory := _|>`
      (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!q j sq. FLOOKUP cenv.ce_vars j = SOME (PtrVar (Var q) sq) ==>
     lookup_var q u = lookup_var q s` by
    (rpt strip_tac >> first_x_assum irule >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv scopes' u` by
    (drule_all pop_path_local_ptrs_rel >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with scopes := scopes') u` by
    (drule_all pop_path_stmt_state_rel >> simp[]) >>
  `dynarray_len_at cenv id k` by
    (drule_all local_path_at_dynarray_len_at >> simp[]) >>
  `wb_frame cenv mid sm s u` by
    (irule pop_path_wb_frame >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 u` by
    (drule_all wb_frame_trans >> simp[]) >>
  `local_region cenv scopes' u id (w2n b) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  irule pop_path_vv_post >>
  qpat_assum `mem_path_offset _ _ = _` (irule_at Any) >>
  qpat_assum `evaluate_subscripts _ _ _ = _` (irule_at Any) >>
  qpat_assum `val_in_memory entry.type _ _ s.vs_memory` (irule_at Any) >>
  simp[] >>
  qpat_assum `local_region _ scopes' u _ _ _` (irule_at Any) >>
  simp[] >>
  `k + (type_memory_size etv * (LENGTH vs - 1) + 32) =
   k + 32 + (LENGTH vs - 1) * type_memory_size etv` by simp[] >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED
