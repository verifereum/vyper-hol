(* Shared root and parent coordinate for a reached local-memory place. *)
Theory bodyArrayMemoryReachedRowMods
Ancestors
  bodyFullPostsMods exprSimProps exprBopSimProps exprSimWordArgs
  loweringPosts loweringStateRelDefs stateRelProj nameLoweringProps
  vyperPlaceTyping vyperTypeSystem venomState words finite_map arithmetic

Theorem array_memory_reached_row_mods:
  lookup_scopes id es.scopes = SOME initial /\
  lookup_scopes id mid.scopes = SOME em /\
  lookup_scopes id fin.scopes = SOME entry /\
  em.type = initial.type /\ entry.type = initial.type /\
  ce.ce_var_type id = SOME rt /\
  evaluate_type (get_tenv cx) rt = SOME initial.type /\
  subscripts_type entry.type path = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  stmt_state_rel H ctx fn ce cx es s0 /\
  vv_post_mods H ctx fn ce cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  expr_post H ctx fn ce cx idx mid sm st2 s fin key iop it /\
  p.ptr_location = LocMemory /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  s0.vs_alloca_next <= it.vs_alloca_next ==>
  ?q sz B j a.
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
    lookup_var q s0 = SOME B /\ lookup_var q s = SOME B /\
    lookup_var q it = SOME B /\
    local_region ce es.scopes s0 id (w2n B) sz /\
    local_region ce mid.scopes s id (w2n B) sz /\
    local_region ce fin.scopes it id (w2n B) sz /\
    type_memory_size initial.type <= sz /\
    w2n B + sz <= it.vs_alloca_next /\ w2n B + sz < dimword (:256) /\
    mem_path_offset entry.type path = SOME (j,ArrayTV etv bd) /\
    j + type_memory_size (ArrayTV etv bd) <= sz /\
    a = B + n2w j /\ w2n a = w2n B + j /\
    eval_operand p.ptr_operand s = SOME a /\
    eval_operand p.ptr_operand it = SOME a /\
    vv_place_ptr ce cx fin it (PlaceR (MemoryPlace id path)) (LocatedValue t p) /\
    place_ptr_rel ce cx it (PlaceR (MemoryPlace id path)) a (SOME LocMemory)
      (Type (ArrayT et bd))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac expr_post_frame >>
  qhdtm_x_assum `vv_post_mods`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qhdtm_x_assum `vv_place_ptr_mods`
    (mp_tac o REWRITE_RULE [vv_place_ptr_mods_def, vv_place_ptr_def]) >>
  simp[] >> strip_tac >>
  rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz)` >>
  rename1 `lookup_var q s = SOME B` >>
  `?j. mem_path_offset initial.type path = SOME (j,ArrayTV etv bd) /\
       eval_operand p.ptr_operand s = SOME (B + n2w j) /\
       j + type_memory_size (ArrayTV etv bd) <= type_memory_size initial.type` by
    (gvs[] >> drule_then strip_assume_tac mem_path_offset_sound >> gvs[] >>
     first_assum (irule_at Any) >> simp[]) >>
  pop_assum strip_assume_tac >>
  `local_ptrs_rel fn ce es.scopes s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >> simp[]) >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  `not_fresh_at sa q /\ not_fresh_at sm q` by
    (qpat_assum `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz)` mp_tac >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `lookup_var q s0 = SOME B` by (fs[eval_operand_def] >> metis_tac[optionTheory.SOME_11]) >>
  `lookup_var q it = SOME B` by (fs[wb_frame_def] >> metis_tac[]) >>
  `local_region ce es.scopes s0 id (w2n B) sz` by
    (simp[local_region_def] >> qexistsl_tac [`initial`,`q`,`B`] >> simp[]) >>
  `w2n B + sz < dimword (:256)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_then Any (qspecl_then [`id`,`w2n B`,`sz`] mp_tac o cj 2)
          stmt_state_rel_region_lt) >> simp[]) >>
  `eval_operand p.ptr_operand it = SOME (B + n2w j)` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`sm`,`s`] >> fs[wb_frame_def]) >>
  `w2n (B + n2w j) = w2n B + j` by
    (`j < dimword (:256) /\ w2n B + j < dimword (:256)` by decide_tac >>
     simp[w2n_add_2, w2n_n2w]) >>
  `w2n B + sz <= it.vs_alloca_next` by
    (`w = B` by fs[eval_operand_def] >>
     qpat_x_assum `w = B` SUBST_ALL_TAC >> decide_tac) >>
  `j + type_memory_size (ArrayTV etv bd) <= sz` by decide_tac >>
  qexistsl_tac [`q`,`sz`,`B`,`j`] >> simp[] >>
  conj_tac >- (simp[local_region_def] >> qexistsl_tac [`em`,`q`,`B`] >> simp[]) >>
  conj_tac >- (simp[local_region_def] >> qexistsl_tac [`entry`,`q`,`B`] >> simp[]) >>
  conj_tac
  >- (simp[vv_place_ptr_def] >>
      qexistsl_tac [`q`,`sz`,`B`,`rt`,`initial.type`,`j`,`ArrayTV etv bd`] >> simp[]) >>
  simp[place_ptr_rel_def] >>
  qexistsl_tac [`q`,`sz`,`B`,`rt`,`initial.type`,`j`,`ArrayTV etv bd`,`ArrayT et bd`] >> simp[]
QED
