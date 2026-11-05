(*
 * Expression simulation: pop on a nested target (x.a.pop(), x[i].pop(),
 * self.s.a.pop(), self.m[k].pop()).
 *
 * The lowering takes the array's pointer, location and type from
 * compile_get_target_ptr, as an assignment does, then runs
 * compile_dynarray_pop at that pointer.  The case lemmas take the target's
 * fragment judgment (pop_target_frag, which targetPlaceSimCases'
 * target_place_sim gives from target_sim) and split on the target's root:
 *
 *   pop_nested_storage_pure_sim — a storage or transient root with pure
 *                             indices: the header load and store and the
 *                             element's slots, as exprSimPopStorage's
 *                             compile_pop_storage_sim has them at a
 *                             declared variable's slot.
 *   pop_nested_storage_effectful_sim — RESIDUAL: a storage root with an
 *                             index that pops or calls, which can leave
 *                             the target's header dead.
 *   pop_nested_immutable_runtime_sim — an immutable or constant root at
 *                             runtime: such a target does not type
 *                             (bare_global_assignable is empty at runtime).
 *   pop_nested_immutable_deploy_sim — RESIDUAL: an immutable root in the
 *                             constructor, which Python accepts for a
 *                             member of a complex immutable.
 *   pop_nested_local_sim    — RESIDUAL: a memory local root, whose
 *                             nested length word locals_kept does not
 *                             exempt yet.
 *
 *   pop_nested_expr_target_frag — RESIDUAL: the target's fragment judgment
 *                             at the expression level; target_pre's
 *                             target_env_ok asks for every declaration's
 *                             metadata, where the target needs its root's.
 *)

Theory exprSimPopNested
Ancestors
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* The target's fragment, typed ty, evaluates to a place at the pointer
   (target_place_sim's conclusion, at every start). *)
Definition pop_target_frag_def:
  pop_target_frag ctx func cenv cx env bt es <=>
    !ty sa sb r res es' s0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      eval_target_place cx bt es = (res, es') /\
      ((?p. res = INL p) \/ (?m. res = INR (Error (RuntimeError m))) \/
       (?d. res = INR (Error (RevertData d))) \/
       (?str. res = INR (AssertException str))) /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa ==>
      frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
        (\s. ?p. res = INL p /\
                 target_post ctx func cenv cx es sa sb s0 es' (PlaceR p)
                   (Type ty) r s)
        (expr_exit res)
End

Theorem pop_target_frag_of_sim:
  !ctx func cenv cx env bt es.
    target_sim ctx func cenv cx env bt es ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  simp[pop_target_frag_def] >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_tac >> irule target_place_sim >> metis_tac[]
QED

Definition nested_pop_suffix_def[local]:
  nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6 =
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] [];
     mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
     mk_inst (id+5) (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
     mk_inst (id+6) ADD [hdr; Lit 1w] [x4];
     mk_inst (id+7) MUL [Var x3; Lit (n2w esz)] [x5];
     mk_inst (id+8) ADD [Var x4; Var x5] [x6]]
End

Theorem nested_pop_suffix_shape[local]:
  !hdr tr esz is_ctor imm sa r sb.
    compile_dynarray_pop hdr 1 esz is_ctor imm
      (if tr then LocTransient else LocStorage) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        nested_pop_suffix hdr tr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  rpt gen_tac >> Cases_on `tr` >>
  simp[compile_dynarray_pop_def, contextTheory.compile_ptr_load_def,
       contextTheory.compile_ptr_store_def,
       emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, LET_THM] >>
  rpt strip_tac >> gvs[APPEND_ASSOC] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`,
                `STRING #"%" (toString (sa.cs_next_var + 1))`,
                `STRING #"%" (toString (sa.cs_next_var + 2))`,
                `STRING #"%" (toString (sa.cs_next_var + 3))`,
                `STRING #"%" (toString (sa.cs_next_var + 4))`,
                `STRING #"%" (toString (sa.cs_next_var + 5))`] >>
  simp[ASCIInumbersTheory.toString_11, not_fresh_at_def, APPEND_ASSOC,
       nested_pop_suffix_def]
QED

Theorem nested_pop_step_load[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s =
    OK (update_var out (if tr then tload (THE (eval_operand hdr s)) s
                       else sload (THE (eval_operand hdr s)) s) s)
Proof
  Cases_on `tr` >> Cases_on `eval_operand hdr s` >>
  simp[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

Theorem nested_pop_step_store[local]:
  IS_SOME (eval_operand hdr s) /\ IS_SOME (lookup_var x s) ==>
  step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [hdr; Var x] []) s =
    OK (if tr then tstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s
        else sstore (THE (eval_operand hdr s)) (THE (lookup_var x s)) s)
Proof
  Cases_on `tr` >> Cases_on `eval_operand hdr s` >> Cases_on `lookup_var x s` >>
  simp[step_inst_base_def, exec_write2_def, mk_inst_def, eval_operand_def]
QED

Theorem nested_pop_step_add[local]:
  IS_SOME (eval_operand hdr s) ==>
  step_inst_base (mk_inst id ADD [hdr; Lit 1w] [out]) s =
    OK (update_var out (THE (eval_operand hdr s) + 1w) s)
Proof
  Cases_on `eval_operand hdr s` >> simp[] >>
  irule step_ADD >> simp[eval_operand_def]
QED


Theorem nested_pop_suffix_empty[local]:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a s'. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = Abort a s'
Proof
  Cases_on `hdr` >>
  simp[eval_operand_def] >> strip_tac >>
  fs[nested_pop_suffix_def, run_inst_seq_def, nested_pop_step_load,
     pop_step_ISZERO, pop_step_ASSERT, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]
QED

Theorem nested_pop_suffix_run[local]:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  (if tr then tload slot s else sload slot s) <> 0w ==>
  ?u. run_inst_seq
    (nested_pop_suffix hdr tr id esz x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    u = (if tr then tstore slot (tload slot s - 1w) s
         else sstore slot (sload slot s - 1w) s) with vs_vars := u.vs_vars /\
    (!x. ~MEM x [x0;x1;x2;x3;x4;x5;x6] ==> lookup_var x u = lookup_var x s) /\
    lookup_var x6 u = SOME (slot + 1w +
      ((if tr then tload slot s else sload slot s) - 1w) * n2w esz)
Proof
  Cases_on `hdr` >> simp[eval_operand_def] >> strip_tac >>
  fs[nested_pop_suffix_def, run_inst_seq_def, nested_pop_step_load,
     nested_pop_step_store, nested_pop_step_add,
     pop_step_ISZERO, pop_step_ASSERT, pop_step_SUB_lit,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >>
  Cases_on `tr` >>
  fs[nested_pop_step_store, nested_pop_step_add,
     pop_step_MUL_lit, pop_step_ADD_var, eval_operand_def,
     lookup_var_def, update_var_def, FLOOKUP_UPDATE, sstore_def, tstore_def] >>
  simp[venom_state_component_equality, FLOOKUP_UPDATE] >> rw[] >> gvs[]
QED

(* A storage or transient root whose indices are pure (no pop, no call).
   compile_get_target_ptr hands out the array's header slot with location
   storage (transient), and the source's pop_place pops the StoragePlace
   there, so the run is compile_pop_storage_sim's at that slot: the header
   load, the abort on zero, the store of the length less one, and the last
   element's slot.  The element is past the new length, so its slots are
   dead in the array; storage_holds asks for them to agree
   (storage_range_agree), before the pop by storage_rel and after it since
   only the header slot changed.  Pure indices leave the state alone, so
   the header the target points at stays live. *)
Theorem nested_pop_lookup_frame[local]:
  off + sz <= dimword (:256) /\
  (w2n slot < off \/ off + sz <= w2n slot) ==>
  !i. off <= i /\ i < off + sz ==>
    lookup_storage (n2w i) (update_storage slot u st) =
    lookup_storage (n2w i) st
Proof
  rpt strip_tac >>
  `i < dimword (:256) /\ i <> w2n slot` by decide_tac >>
  `(n2w i:bytes32) <> slot` by
    (strip_tac >> `w2n (n2w i:bytes32) = w2n slot` by simp[] >>
     gvs[wordsTheory.w2n_n2w]) >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem nested_pop_array_offset_frame[local]:
  !(a:num) (k:num) (base:num) (sz:num) (slot:bytes32).
  a <> k /\ base + k * sz <= w2n slot /\
  w2n slot < base + (k + 1) * sz ==>
  w2n slot < base + a * sz \/ base + (a + 1) * sz <= w2n slot
Proof
  rpt strip_tac >> Cases_on `a < k`
  >- (`(a + 1) * sz <= k * sz` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >> decide_tac) >>
  `(k + 1) * sz <= a * sz` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >> decide_tac
QED

Theorem nested_pop_dead_list[local]:
  !tvs i elem off slot u st.
    oEL i tvs = SOME elem /\
    off + type_slot_size_list tvs <= dimword (:256) /\
    off + tuple_prefix_slot_size i tvs <= w2n slot /\
    w2n slot < off + tuple_prefix_slot_size i tvs + type_slot_size elem /\
    (!j b. dead_bytes st (off + tuple_prefix_slot_size i tvs) elem j b ==>
      dead_bytes (update_storage slot u st)
        (off + tuple_prefix_slot_size i tvs) elem j b) ==>
    !j b. dead_bytes_list st off tvs j b ==>
      dead_bytes_list (update_storage slot u st) off tvs j b
Proof
  Induct_on `tvs` >- simp[oEL_def] >>
  Cases_on `i`
  >- (simp[oEL_def, tuple_prefix_slot_size_def,
            vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac
      >- metis_tac[] >>
      disj2_tac >>
      `dead_bytes_list (update_storage slot u st)
         (off + type_slot_size h) tvs j b =
       dead_bytes_list st (off + type_slot_size h) tvs j b` by
        (irule (cj 2 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >> decide_tac) >> simp[])
  >> simp[oEL_def, tuple_prefix_slot_size_def,
          vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac
  >- (disj1_tac >>
      `dead_bytes (update_storage slot u st) off h j b =
       dead_bytes st off h j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >> decide_tac) >> simp[]) >>
  disj2_tac >> first_x_assum irule >> simp[] >>
  qexistsl [`elem`, `n`] >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem nested_pop_dead_fields[local]:
  !fields id delta elem off slot u st.
    struct_field_slot fields id = SOME (delta,elem) /\
    off + type_slot_size (StructTV fields) <= dimword (:256) /\
    off + delta <= w2n slot /\
    w2n slot < off + delta + type_slot_size elem /\
    (!j b. dead_bytes st (off + delta) elem j b ==>
      dead_bytes (update_storage slot u st) (off + delta) elem j b) ==>
    !j b. dead_bytes_fields st off fields j b ==>
      dead_bytes_fields (update_storage slot u st) off fields j b
Proof
  Induct_on `fields` >- simp[struct_field_slot_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC
  >- (simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
      rpt strip_tac >- (gvs[] >> metis_tac[]) >> gvs[] >> disj2_tac >>
      `dead_bytes_fields (update_storage slot u st)
         (off + type_slot_size elem) fields j b =
       dead_bytes_fields st (off + type_slot_size elem) fields j b` by
        (irule (cj 3 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >>
         gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >> simp[]) >>
  Cases_on `struct_field_slot fields id` >> simp[] >>
  Cases_on `x` >>
  simp[vyperValueTheory.type_slot_size_def, dead_bytes_def] >>
  rpt strip_tac
  >- (disj1_tac >>
      `dead_bytes (update_storage slot u st) off h1 j b =
       dead_bytes st off h1 j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >> decide_tac) >> simp[]) >>
  disj2_tac >> first_x_assum irule >>
  simp[vyperValueTheory.type_slot_size_def] >>
  qexistsl [`q`, `r`, `id`] >>
  gvs[] >> pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >>
  metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem nested_pop_dead_bytes_subregion[local]:
  !path root delta etv n off slot st j b.
    storage_subregion root path delta (ArrayTV etv (Dynamic n)) /\
    off + type_slot_size root <= dimword (:256) /\
    w2n slot = off + delta /\
    dead_bytes st off root j b ==>
    dead_bytes (update_storage slot
      (n2w (w2n (lookup_storage slot st) - 1)) st) off root j b
Proof
  Induct_on `path`
  >- (simp[storage_subregion_def] >> rpt strip_tac >> gvs[] >>
      irule dead_bytes_pop_header >> simp[])
  >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `h`)
  >- (Cases_on `root` >> gvs[storage_subregion_def] >>
      drule storage_subregion_bounds >> strip_tac >>
      drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >> strip_tac >>
      `rest < type_slot_size elem` by
        (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
      gvs[Once dead_bytes_def] >>
      pure_once_rewrite_tac[compileEnvTheory.dead_bytes_def] >>
      irule nested_pop_dead_fields >> simp[] >>
      qexistsl [`delta'`, `elem`, `s`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
  Cases_on `v` >> Cases_on `root` >> gvs[storage_subregion_def]
  >~ [`dead_bytes _ _ (TupleTV _) _ _`]
  >- (drule storage_subregion_bounds >> strip_tac >>
      drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >>
      strip_tac >>
      `rest < type_slot_size elem` by
        (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
      gvs[dead_bytes_def, vyperValueTheory.type_slot_size_def] >>
      irule nested_pop_dead_list >> simp[] >>
      qexistsl [`elem`, `Num i`] >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
  rename1 `ArrayTV child bd` >> Cases_on `bd` >> gvs[storage_subregion_def]
  >- (drule storage_subregion_bounds >> strip_tac >>
      gvs[Once dead_bytes_def] >>
      rename1 `a < n'` >> pure_once_rewrite_tac[compileEnvTheory.dead_bytes_def] >>
      qexists `a` >> simp[] >>
      Cases_on `a = Num i`
      >- (gvs[] >> first_x_assum irule >>
          goal_assum (drule_at Any) >>
          simp[] >> conj_tac
          >- (gvs[vyperValueTheory.type_slot_size_def] >>
              `Num i * type_slot_size child + type_slot_size child <=
               n' * type_slot_size child` by
                (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
              decide_tac) >>
          qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
      `w2n slot < off + a * type_slot_size child \/
       off + (a + 1) * type_slot_size child <= w2n slot` by
        (irule nested_pop_array_offset_frame >>
         qexists `Num i` >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.ADD_CLAUSES, arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
      `dead_bytes (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
         (off + a * type_slot_size child) child j b =
       dead_bytes st (off + a * type_slot_size child) child j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >>
         `a * type_slot_size child + type_slot_size child <=
          n' * type_slot_size child` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> simp[])
  >- (drule storage_subregion_bounds >> strip_tac >>
      `off < w2n slot /\ off + 1 <= dimword (:256)` by
        gvs[vyperValueTheory.type_slot_size_def] >>
      `!q. off <= q /\ q < off + 1 ==>
        lookup_storage (n2w q)
          (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) =
        lookup_storage (n2w q) st` by
        (match_mp_tac nested_pop_lookup_frame >> decide_tac) >>
      `lookup_storage (n2w off)
          (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) =
        lookup_storage (n2w off) st` by (first_x_assum irule >> decide_tac) >>
      qpat_x_assum `!q. _` kall_tac >>
      gvs[Once dead_bytes_def] >>
      rename1 `a < n'` >> pure_once_rewrite_tac[compileEnvTheory.dead_bytes_def] >>
      qexists `a` >> simp[] >>
      Cases_on `a < w2n (lookup_storage (n2w off) st)` >> gvs[] >>
      Cases_on `a = Num i`
      >- (gvs[] >> first_x_assum irule >>
          goal_assum (drule_at Any) >> simp[] >> conj_tac
          >- (gvs[vyperValueTheory.type_slot_size_def] >>
              `Num i * type_slot_size child + type_slot_size child <=
               n' * type_slot_size child` by
                (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
              decide_tac) >>
          qexistsl [`rest`, `etv`, `n`] >> simp[]) >>
      `w2n slot < off + 1 + a * type_slot_size child \/
       off + 1 + (a + 1) * type_slot_size child <= w2n slot` by
        (irule nested_pop_array_offset_frame >> qexists `Num i` >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.RIGHT_ADD_DISTRIB]) >>
      `dead_bytes (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
         (off + 1 + a * type_slot_size child) child j b =
       dead_bytes st (off + 1 + a * type_slot_size child) child j b` by
        (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
         match_mp_tac nested_pop_lookup_frame >>
         `a * type_slot_size child + type_slot_size child <=
          n' * type_slot_size child` by
           (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
         gvs[vyperValueTheory.type_slot_size_def,
             arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> gvs[])

QED

Theorem nested_pop_eval_base_pure_state[local]:
  !bt cx st res st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (res,st') ==> st' = st
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >>
      metis_tac[lookup_global_state]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  metis_tac[eval_expr_preserves_state, read_result_state, extend_place_state]
QED

Theorem nested_pop_eval_target_pure_state[local]:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (res,st') ==> st' = st
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def]
QED

Theorem nested_pop_dead_tuple_selected[local]:
  !tvs k elem st off j b.
    oEL k tvs = SOME elem /\ dead_bytes_list st off tvs j b /\
    off + tuple_prefix_slot_size k tvs <= j /\
    j < off + tuple_prefix_slot_size k tvs + type_slot_size elem ==>
    dead_bytes st (off + tuple_prefix_slot_size k tvs) elem j b
Proof
  Induct_on `tvs` >- simp[oEL_def] >>
  Cases_on `k`
  >- (simp[oEL_def, tuple_prefix_slot_size_def] >> rpt strip_tac >>
      gvs[Once dead_bytes_def] >>
      drule (cj 2 accountsRelPropsTheory.dead_bytes_range) >> simp[]) >>
  simp[oEL_def, tuple_prefix_slot_size_def] >> rpt strip_tac >>
  qpat_x_assum `dead_bytes_list _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac
  >- (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> simp[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`st`, `off + type_slot_size h`, `j`, `b`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  pure_rewrite_tac[GSYM arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem nested_pop_live_fixed_element[local]:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Fixed n)) /\ k < n ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem)) elem
Proof
  rpt gen_tac >> strip_tac >>
  `k * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def, wordsTheory.WORD_ADD_0] >> rpt strip_tac >>
      qspec_then `w` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[vyperValueTheory.type_slot_size_def] >> strip_tac >>
  `w2n w + k * type_slot_size elem < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (k * type_slot_size elem)) = w2n w + k * type_slot_size elem` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes st (w2n w) (ArrayTV elem (Fixed n)) j b` by
    (first_x_assum irule >> decide_tac) >>
  gvs[Once dead_bytes_def] >>
  `i = k` suffices_by (strip_tac >> gvs[]) >>
  drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> strip_tac >>
  Cases_on `i < k`
  >- (`(i + 1) * type_slot_size elem <= k * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
  Cases_on `k < i`
  >- (`(k + 1) * type_slot_size elem <= i * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> decide_tac
QED

Theorem nested_pop_live_dynamic_element[local]:
  !cx tr st w elem n k.
    storage_read_live cx tr st w (ArrayTV elem (Dynamic n)) /\
    k < n /\ k < w2n (lookup_storage w st) ==>
    storage_read_live cx tr st (w + n2w (k * type_slot_size elem + 1)) elem
Proof
  rpt gen_tac >> strip_tac >>
  `k * type_slot_size elem + type_slot_size elem <= n * type_slot_size elem` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + 1w` mp_tac wordsTheory.w2n_lt >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >>
  simp[vyperValueTheory.type_slot_size_def] >> strip_tac >>
  `w2n w + (k * type_slot_size elem + 1) < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (k * type_slot_size elem + 1)) =
   w2n w + (k * type_slot_size elem + 1)` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes st (w2n w) (ArrayTV elem (Dynamic n)) j b` by
    (first_x_assum irule >> decide_tac) >>
  gvs[Once dead_bytes_def] >>
  `w2n w + (i * type_slot_size elem + 1) <= j /\
   j < w2n w + ((i + 1) * type_slot_size elem + 1)` by
    (Cases_on `i < w2n (lookup_storage w st)` >> gvs[]
     >- (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >>
         simp[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >>
     gvs[arithmeticTheory.MULT_COMM]) >>
  `i = k` suffices_by (strip_tac >> gvs[]) >>
  Cases_on `i < k`
  >- (`(i + 1) * type_slot_size elem <= k * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >> decide_tac) >>
  Cases_on `k < i`
  >- (`(k + 1) * type_slot_size elem <= i * type_slot_size elem` by
        (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
      gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac) >> decide_tac
QED

Theorem nested_pop_live_tuple_element[local]:
  !cx tr st w tvs k elem.
    storage_read_live cx tr st w (TupleTV tvs) /\ oEL k tvs = SOME elem ==>
    storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size k tvs)) elem
Proof
  rpt gen_tac >> strip_tac >>
  drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >> strip_tac >>
  Cases_on `type_slot_size elem = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + n2w (tuple_prefix_slot_size k tvs)` mp_tac wordsTheory.w2n_lt >>
      decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + tuple_prefix_slot_size k tvs < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (tuple_prefix_slot_size k tvs)) =
   w2n w + tuple_prefix_slot_size k tvs` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) tvs j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def] >> decide_tac) >>
  irule nested_pop_dead_tuple_selected >> simp[] >>
  qexists `k` >> simp[]
QED

Theorem nested_pop_resolve_array_empty[local]:
  resolve_array_element cx tr slot tv [] st = (INL (slot,tv,[]),st)
Proof
  Cases_on `tv` >> simp[resolve_array_element_def, return_def]
QED

Theorem nested_pop_extend_storage_live[local]:
  get_storage_backend cx tr st = (INL raw,st) /\
  storage_read_live cx tr raw slot tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ storage_read_live cx tr raw slot' tv'
Proof
  reverse (Cases_on `sb`)
  >- (Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def] >>
      irule accountsRelPropsTheory.storage_read_live_field >> metis_tac[]) >>
  Cases_on `v` >> Cases_on `tv` >> simp[extend_storage_place_def, raise_def]
  >~ [`storage_read_live _ _ _ _ (TupleTV _)`]
  >- (simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      irule nested_pop_live_tuple_element >> metis_tac[]) >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >>
  simp[resolve_array_element_def, bind_def, ignore_bind_def,
       lift_option_type_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[nested_pop_resolve_array_empty, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, return_def, raise_def, AllCaseEqs()]
  >- (irule nested_pop_live_fixed_element >> metis_tac[]) >>
  irule nested_pop_live_dynamic_element >> metis_tac[]
QED

Definition nested_pop_result_live_def:
  nested_pop_result_live cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       storage_read_live cx tr raw slot tv) /\
  nested_pop_result_live cx st (PlaceR _) = T /\
  nested_pop_result_live cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  nested_pop_result_live cx st (Value _) = T
End

Theorem nested_pop_mapping_leaf_live[local]:
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  storage_read_live cx tr raw slot tv
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  asm_simp_tac bool_ss [vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def,
                       optionTheory.option_case_def, APPEND_NIL] >>
  strip_tac >> drule accountsRelPropsTheory.declared_storage_region_read_live >> simp[]
QED

Theorem nested_pop_lookup_global_live[local]:
  lookup_global cx mid var_name st = (INL pv,st') ==>
  nested_pop_result_live cx st pv
Proof
  Cases_on `pv` >> simp[nested_pop_result_live_def]
  >- (Cases_on `p` >> simp[nested_pop_result_live_def] >> rpt strip_tac >>
      drule lookup_global_storage_region >> strip_tac >>
      drule accountsRelPropsTheory.declared_storage_region_read_live >> simp[]) >>
  strip_tac >> drule lookup_global_mapping_region >> simp[]
QED

Theorem nested_pop_extend_result_live[local]:
  nested_pop_result_live cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  nested_pop_result_live cx st pv'
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def, nested_pop_result_live_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`extend_storage_place _ _ _ _ _ _`]
      >- (drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
          simp[nested_pop_result_live_def] >> rpt strip_tac >>
          gvs[nested_pop_result_live_def] >>
          drule_all nested_pop_extend_storage_live >> simp[]) >>
      simp[extend_memory_place_def, nested_pop_result_live_def]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `v` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[nested_pop_result_live_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v'` assume_tac) >>
  simp[] >> rpt strip_tac >>
  irule nested_pop_mapping_leaf_live >> goal_assum (drule_at Any) >> simp[]
QED

Theorem nested_pop_eval_base_live[local]:
  !bt cx st pv st'.
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    nested_pop_result_live cx st pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      simp[nested_pop_result_live_def] >>
      metis_tac[nested_pop_lookup_global_live]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  simp[nested_pop_result_live_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[]
  >~ [`pure_expr e`]
  >- (drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule_all nested_pop_extend_result_live >> simp[]) >>
  drule_all nested_pop_extend_result_live >> simp[]
QED

Theorem nested_pop_eval_target_live[local]:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  storage_read_live cx tr raw slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_live >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def,
                       nested_pop_result_live_def]
QED

Theorem nested_pop_eval_target_live_post[local]:
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st' = (INL raw,st') ==>
  storage_read_live cx tr raw slot tv
Proof
  rpt strip_tac >>
  drule_all nested_pop_eval_target_pure_state >> strip_tac >> gvs[] >>
  drule_all nested_pop_eval_target_live >> simp[]
QED

Theorem nested_pop_storage_dead_header[local]:
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\ storage_dead cx tr st j b ==>
  storage_dead cx tr
    (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st) j b
Proof
  strip_tac >> fs[storage_dead_def] >>
  rename1 `dead_bytes st (w2n k) tv' j b` >>
  qexistsl [`mid'`, `n'`, `subs'`, `k`, `tv'`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  Cases_on `(k,tv') = (root_slot,root)`
  >- (gvs[] >> irule nested_pop_dead_bytes_subregion >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl [`tv`, `n`, `path`] >> simp[]) >>
  `ranges_disjoint (w2n k) (type_slot_size tv')
                   (w2n root_slot) (type_slot_size root)` by
    (first_x_assum irule >> metis_tac[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `dead_bytes (update_storage slot (n2w (w2n (lookup_storage slot st) - 1)) st)
     (w2n k) tv' j b = dead_bytes st (w2n k) tv' j b` suffices_by simp[] >>
  irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >>
  match_mp_tac nested_pop_lookup_frame >>
  gvs[vyperStorageFrameTheory.ranges_disjoint_def,
      vyperValueTheory.type_slot_size_def] >> decide_tac
QED

Theorem nested_pop_stmt_state_rel_header[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx es tr
      (update_storage slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1))
        (get_storage cx es tr)))
    (if tr then
       tstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s
     else
       sstore slot (n2w (w2n (lookup_storage slot (get_storage cx es tr)) - 1)) s)
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx _ _ _ es1 s1` >>
  `accounts_rel cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`]
     >- (irule accountsRelPropsTheory.accounts_rel_tstore >> simp[] >> qexists `es` >>
         simp[vyperStorageBackendTheory.set_storage_backend_eq, vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def] >>
         rpt strip_tac >> irule nested_pop_storage_dead_header >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     irule accountsRelPropsTheory.accounts_rel_sstore >> simp[] >> qexists `es` >>
     simp[vyperStorageBackendTheory.set_storage_backend_eq, vyperStorageBackendTheory.get_storage_def, vfmStateTheory.lookup_account_def] >>
     rpt strip_tac >> irule nested_pop_storage_dead_header >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by
    (Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]) >>
  drule accountsRelPropsTheory.accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`] >>
     fs[stmt_state_rel_def, state_rel_def, sstore_def, tstore_def, LET_THM,
        vyperStorageBackendTheory.set_storage_def, local_ptrs_rel_def, local_backed_def, local_region_def,
        lookup_var_def, immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, sstore_def, tstore_def, LET_THM,
          vyperStorageBackendTheory.set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, sstore_def, tstore_def, LET_THM, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, sstore_def, tstore_def, LET_THM]
QED

Theorem nested_pop_live_array_agree[local]:
  stmt_state_rel ctx func cenv cx es s /\
  storage_read_live cx tr (vyperStorageBackend$get_storage cx es tr) slot (ArrayTV tv (Dynamic n)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256) ==>
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n))
Proof
  strip_tac >> irule accountsRelPropsTheory.storage_range_agree_of_live >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cx`, `tr`] >> simp[] >>
  Cases_on `tr` >>
  gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
      transient_rel_def, vyperStorageBackendTheory.get_storage_def,
      vfmStateTheory.lookup_account_def]
QED

Theorem nested_pop_array_header_load[local]:
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) slot (ArrayTV tv (Dynamic n)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (vyperStorageBackend$get_storage cx es tr)
Proof
  strip_tac >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by
    simp[vyperValueTheory.type_slot_size_def] >>
  drule_all accountsRelPropsTheory.storage_range_agree_head >>
  Cases_on `tr` >> simp[sload_def, tload_def]
QED

Theorem nested_pop_updated_state_rel[local]:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name subs = SOME (tr,root_slot,root) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  w2n slot = w2n root_slot + delta /\
  local_ptrs_reserved cenv sa /\
  u = (if tr then tstore slot
         (n2w (w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr)) - 1)) s
       else sstore slot
         (n2w (w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr)) - 1)) s)
        with vs_vars := u.vs_vars /\
  (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s) ==>
  stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes slot [(0,n2w (w2n (lookup_storage slot
        (vyperStorageBackend$get_storage cx es tr)) - 1))]
        (vyperStorageBackend$get_storage cx es tr))) u
Proof
  strip_tac >> drule_all nested_pop_stmt_state_rel_header >> strip_tac >>
  qpat_x_assum `w2n slot = _` kall_tac >>
  Cases_on `tr` >> gvs[] >>
  simp[vyperStorageTheory.apply_writes_def] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  irule exprSimPropsTheory.stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  first_x_assum (drule_then mp_tac) >>
  gvs[sstore_def, tstore_def, lookup_var_def, LET_THM]
QED

Theorem nested_pop_positive_holds[local]:
  storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) w (ArrayTV tv (Dynamic n)) /\
  slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic n)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  len = w2n (lookup_storage w (vyperStorageBackend$get_storage cx es tr)) /\ 0 < len /\
  elem = w + n2w (1 + (len - 1) * type_slot_size tv) /\
  u = (if tr then tstore w (n2w (len - 1)) s else sstore w (n2w (len - 1)) s)
        with vs_vars := u.vs_vars ==>
  storage_holds cx tr ann (PlaceR (StoragePlace tr elem tv)) elem
    (vyperStorageBackend$set_storage cx es tr
      (apply_writes w [(0,n2w (len - 1))] (vyperStorageBackend$get_storage cx es tr))) u
Proof
  strip_tac >>
  `len <= n` by metis_tac[pop_array_length_bound] >>
  `w2n w + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by
    fs[accountsRelPropsTheory.storage_range_agree_def] >>
  Q.SUBGOAL_THEN
    `w2n elem + type_slot_size tv <= dimword(:256) /\
     (type_slot_size tv = 0 \/ w2n w < w2n elem)` assume_tac
  >- metis_tac[pop_array_last_bounds] >>
  `slots_in_range (vyperStorageBackend$get_storage cx es tr) (w2n elem) tv` by
    metis_tac[pop_array_last_slots] >>
  `storage_range_agree (vyperStorageBackend$get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) elem tv` by
    metis_tac[storage_range_agree_dyn_last] >>
  irule pop_storage_holds >>
  pure_rewrite_tac[vyperStorageBackendTheory.get_storage_after_set] >>
  conj_tac >- metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[pop_element_slots_frame] >>
  qpat_x_assum `u = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  `storage_range_agree
     (apply_writes w [(0,n2w (len - 1))] (vyperStorageBackend$get_storage cx es tr))
     (apply_writes w [(0,n2w (len - 1))]
       (if tr then contract_transient s else contract_storage s)) elem tv` by
    metis_tac[storage_pop_element_frame] >>
  Cases_on `tr` >>
  gvs[contract_storage_def, contract_transient_def, sstore_def, tstore_def,
      LET_THM, vyperStorageTheory.apply_writes_def, vfmStateTheory.lookup_account_def]
QED

Theorem nested_pop_target_callback_cong[local]:
  !bt f g cenv.
    (!e. MEM e (target_indices bt) ==> !ce t st. f ce t e st = g ce t e st) ==>
    compile_get_target_ptr f cenv bt = compile_get_target_ptr g cenv bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_def] >> rpt strip_tac
  >~ [`compile_get_target_ptr _ _ (NameTarget _)`]
  >- simp[compile_get_target_ptr_def]
  >~ [`compile_get_target_ptr _ _ (TopLevelNameTarget _)`]
  >- simp[compile_get_target_ptr_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  `compile_get_target_ptr f cenv b = compile_get_target_ptr g cenv b` by
    (first_x_assum irule >> metis_tac[]) >>
  pure_rewrite_tac[compile_get_target_ptr_def] >>
  asm_rewrite_tac[] >>
  `f cenv (expr_type e) e = g cenv (expr_type e) e` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  `lower_value f cenv (expr_type e) e = lower_value g cenv (expr_type e) e` by
    simp[lower_value_def, comp_bind_def, FUN_EQ_THM] >>
  asm_rewrite_tac[]
QED

Theorem nested_pop_index_size[local]:
  !bt e. MEM e (target_indices bt) ==> expr_size e < base_assignment_target_size bt
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  simp[target_indices_def, expr_size_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[expr_size_def] >>
  strip_tac >> res_tac >> decide_tac
QED

Theorem nested_pop_target_guard_erasure[local]:
  compile_get_target_ptr
    (expr_child_callback (expr_size (Pop ann bt)) f) cenv bt =
  compile_get_target_ptr f cenv bt
Proof
  irule nested_pop_target_callback_cong >> rpt strip_tac >>
  irule exprCallBoundsTheory.expr_child_callback_valid >>
  drule nested_pop_index_size >> simp[expr_size_def]
QED

Theorem nested_pop_compile_eq[local]:
  compile_expr cenv ty (Pop ann bt) sa =
    (let ((hdr,loc_opt,pt_opt),sm) = compile_get_target_ptr compile_expr cenv bt sa in
     let loc = (case loc_opt of SOME l => l | NONE => LocMemory) in
     let et = (case pt_opt of SOME (ValPT (ArrayT t _)) => t | _ => BaseT (IntT 256)) in
     let (elem,sb) = compile_dynarray_pop hdr (word_scale loc)
       (elem_size_in_location cenv loc et)
       cenv.ce_is_ctor cenv.ce_imm_alloca loc sm in
     (LocatedValue ann (mk_ptr elem loc),sb))
Proof
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def, SRULE [expr_size_def] nested_pop_target_guard_erasure,
       SF ETA_ss] >>
  `compile_get_target_ptr
     (expr_child_callback (base_assignment_target_size bt + (type_size ann + 1)) compile_expr)
       cenv bt = compile_get_target_ptr compile_expr cenv bt` by
    (irule nested_pop_target_callback_cong >> rpt strip_tac >>
     irule exprCallBoundsTheory.expr_child_callback_valid >>
     drule nested_pop_index_size >> simp[]) >>
  asm_rewrite_tac[]
QED

Theorem nested_pop_compile_storage_eq[local]:
  compile_get_target_ptr compile_expr cenv bt sa =
    ((hdr,SOME (if tr then LocTransient else LocStorage),
      SOME (ValPT (ArrayT et (Dynamic n)))),sm) ==>
  compile_expr cenv ty (Pop ann bt) sa =
    (let (elem,sb) = compile_dynarray_pop hdr 1
       (elem_size_in_location cenv (if tr then LocTransient else LocStorage) et)
       cenv.ce_is_ctor cenv.ce_imm_alloca
       (if tr then LocTransient else LocStorage) sm in
     (LocatedValue ann (mk_ptr elem (if tr then LocTransient else LocStorage)),sb))
Proof
  strip_tac >> rewrite_tac[nested_pop_compile_eq] >>
  Cases_on `tr` >> simp[word_scale_def]
QED

Theorem nested_pop_extend_storage_class[local]:
  ((?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
   (?tr slot kt vt. pv = HashMapRef tr slot kt vt)) /\
  extend_place cx pv sb st = (INL next,st') ==>
  (?tr slot tv. next = PlaceR (StoragePlace tr slot tv)) \/
  (?tr slot kt vt. next = HashMapRef tr slot kt vt)
Proof
  strip_tac
  >- (gvs[extend_place_def, bind_def, return_def, AllCaseEqs()] >>
      drule extend_storage_place_subregion >> strip_tac >> gvs[] >> metis_tac[]) >>
  Cases_on `sb` >>
  gvs[extend_place_def, bind_def, return_def, raise_def, lift_option_type_def,
      AllCaseEqs()] >>
  Cases_on `vt` >>
  gvs[extend_place_def, bind_def, return_def, raise_def, lift_option_type_def,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem nested_pop_lookup_storage_class[local]:
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
  lookup_global cx src id st = (INL pv,st') ==>
  (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
  (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  PairCases_on `d` >> Cases_on `d0` >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[return_def, bind_def, lift_option_type_def, raise_def, AllCaseEqs()] >>
  gvs[return_def] >> metis_tac[]
QED

Theorem nested_pop_eval_base_storage_class[local]:
  !bt cx st pv st' src id ts d.
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    eval_base_place cx bt st = (INL pv,st') ==>
    (?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)) \/
    (?tr slot kt vt. pv = HashMapRef tr slot kt vt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_root_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      drule_all nested_pop_lookup_storage_class >> simp[]) >>
  simp[target_root_def, Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_assum_rename_tac `eval_base_place cx child st = (INL child_pv,child_st)` >>
  qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  irule nested_pop_extend_storage_class >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem nested_pop_eval_target_storage_class[local]:
  target_root bt = TopLevelNameTarget (src,id) /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
  eval_target_place cx bt st = (INL p,st') ==>
  ?tr slot tv. p = StoragePlace tr slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_storage_class >> strip_tac >>
  gvs[get_place_def, return_def, raise_def] >> metis_tac[]
QED

Theorem nested_pop_storage_target_metadata[local]:
  target_post ctx func cenv cx es sa sm s0 es' (PlaceR (StoragePlace tr slot vt))
    (Type (ArrayT ann (Dynamic n))) (hdr,loc,pt) t ==>
  ?tv. vt = ArrayTV tv (Dynamic n) /\
    evaluate_type (get_tenv cx) ann = SOME tv /\
    eval_operand hdr t = SOME slot /\ loc = SOME (slot_loc tr) /\
    pt = SOME (ValPT (ArrayT ann (Dynamic n))) /\
    (!x. hdr = Var x ==> not_fresh_at sm x) /\
    stmt_state_rel ctx func cenv cx es' t
Proof
  simp[target_post_def, place_ptr_rel_def, value_type_place_def,
       vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem nested_pop_storage_natural_region[local]:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ==>
  ?mid name keys root root_tv path delta.
    declared_storage_region cx mid name keys = SOME (tr,root,root_tv) /\
    storage_subregion root_tv path delta (ArrayTV tv (Dynamic n)) /\
    slot = root + n2w delta /\ w2n slot = w2n root + delta /\
    w2n root + type_slot_size root_tv <= dimword(:256) /\
    w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)
Proof
  strip_tac >> fs[storage_place_region_def] >>
  drule_all vyperStorageLayoutSafetyTheory.storage_layout_safe_region_nonoverflow >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword(:256)` by
    (fs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `delta < dimword(:256)` by decide_tac >>
  `w2n (n2w delta : bytes32) = delta` by simp[] >>
  `w2n (root + n2w delta : bytes32) = w2n root + delta` by
    simp[wordsTheory.w2n_add_2] >>
  qexistsl [`mid`, `var_name`, `keys`, `root`, `tv'`, `path`, `delta`] >>
  simp[] >> decide_tac
QED

Theorem nested_pop_slots_word_offset[local]:
  slots_in_range raw (w2n (w:bytes32) + off) tv ==>
  slots_in_range raw (w2n (w + n2w off)) tv
Proof
  strip_tac >>
  `slots_in_range raw (w2n w + off) tv =
   slots_in_range raw (w2n (w + n2w off)) tv` by
    (irule (cj 1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     `w + n2w off = n2w (w2n w + off)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     simp[wordsTheory.w2n_n2w]) >> gvs[]
QED

Theorem nested_pop_tuple_slots_index[local]:
  !tvs k off raw.
    tuple_slots_in_range raw off tvs /\ k < LENGTH tvs ==>
    slots_in_range raw (off + tuple_prefix_slot_size k tvs) (EL k tvs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `tuple_slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def] >> strip_tac >>
  Cases_on `k` >> gvs[tuple_prefix_slot_size_def] >>
  first_x_assum drule_all >> rewrite_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem nested_pop_tuple_slots[local]:
  slots_in_range raw (w2n (w:bytes32)) (TupleTV tvs) /\
  oEL k tvs = SOME tv ==>
  slots_in_range raw (w2n (w + n2w (tuple_prefix_slot_size k tvs))) tv
Proof
  strip_tac >> irule nested_pop_slots_word_offset >>
  gvs[listTheory.oEL_EQ_EL] >> irule nested_pop_tuple_slots_index >>
  simp[GSYM vyperLookupStorageTheory.slots_in_range_def]
QED

Theorem nested_pop_fixed_slots[local]:
  slots_in_range raw (w2n (w:bytes32)) (ArrayTV tv (Fixed n)) /\ k < n ==>
  slots_in_range raw (w2n (w + n2w (k * type_slot_size tv))) tv
Proof
  strip_tac >> irule nested_pop_slots_word_offset >>
  gvs[Once vyperLookupStorageTheory.slots_in_range_def,
      vyperLookupStorageTheory.array_slots_in_range_indexed]
QED

Theorem nested_pop_dynamic_slots[local]:
  slots_in_range raw (w2n (w:bytes32)) (ArrayTV tv (Dynamic n)) /\
  k < w2n (lookup_storage w raw) ==>
  slots_in_range raw (w2n (w + n2w (k * type_slot_size tv + 1))) tv
Proof
  strip_tac >> irule nested_pop_slots_word_offset >>
  qpat_x_assum `slots_in_range _ _ _` mp_tac >>
  simp[Once vyperLookupStorageTheory.slots_in_range_def,
       vyperLookupStorageTheory.array_slots_in_range_indexed,
       vyperStorageTheory.read_slot_def] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >>
  simp[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]
QED

Theorem nested_pop_extend_storage_slots[local]:
  get_storage_backend cx tr st = (INL raw,st) /\
  slots_in_range raw (w2n slot) tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' slot' tv'),st') ==>
  tr' = tr /\ slots_in_range raw (w2n slot') tv'
Proof
  reverse (Cases_on `sb`)
  >- (Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[return_def] >>
      irule vyperLookupStorageTheory.storage_field_slots_in_range >> metis_tac[]) >>
  Cases_on `v` >> Cases_on `tv` >> simp[extend_storage_place_def, raise_def]
  >~ [`slots_in_range _ _ (TupleTV _)`]
  >- (simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, check_def, assert_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      irule nested_pop_tuple_slots >> metis_tac[]) >>
  rename1 `ArrayTV elem bd` >> Cases_on `bd` >>
  simp[resolve_array_element_def, bind_def, ignore_bind_def,
       lift_option_type_def, check_def, assert_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[nested_pop_resolve_array_empty, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, return_def, raise_def, AllCaseEqs()]
  >- (irule nested_pop_fixed_slots >> metis_tac[]) >>
  irule nested_pop_dynamic_slots >> metis_tac[]
QED

Definition nested_pop_result_slots_def:
  nested_pop_result_slots cx st (PlaceR (StoragePlace tr slot tv)) =
    (!raw. get_storage_backend cx tr st = (INL raw,st) ==>
       slots_in_range raw (w2n slot) tv) /\
  nested_pop_result_slots cx st (PlaceR _) = T /\
  nested_pop_result_slots cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  nested_pop_result_slots cx st (Value _) = T
End

Theorem nested_pop_mapping_leaf_slots[local]:
  contract_storage_well_formed cx st /\
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  slots_in_range raw (w2n slot) tv
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `slot`, `tv`] mp_tac) >>
  asm_simp_tac bool_ss [vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def,
                       optionTheory.option_case_def, APPEND_NIL] >>
  strip_tac >>
  drule_all vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >> simp[]
QED

Theorem nested_pop_lookup_global_slots[local]:
  contract_storage_well_formed cx st /\
  lookup_global cx mid var_name st = (INL pv,st') ==>
  nested_pop_result_slots cx st pv
Proof
  Cases_on `pv` >> simp[nested_pop_result_slots_def]
  >- (Cases_on `p` >> simp[nested_pop_result_slots_def] >> rpt strip_tac >>
      drule lookup_global_storage_region >> strip_tac >>
      drule_all vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >> simp[]) >>
  strip_tac >> drule lookup_global_mapping_region >> simp[]
QED

Theorem nested_pop_extend_result_slots[local]:
  contract_storage_well_formed cx st /\
  nested_pop_result_slots cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  nested_pop_result_slots cx st pv'
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def, nested_pop_result_slots_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`extend_storage_place _ _ _ _ _ _`]
      >- (drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
          simp[nested_pop_result_slots_def] >> rpt strip_tac >>
          gvs[nested_pop_result_slots_def] >>
          drule_all nested_pop_extend_storage_slots >> simp[]) >>
      simp[extend_memory_place_def, nested_pop_result_slots_def]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `v` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[nested_pop_result_slots_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v'` assume_tac) >>
  simp[] >> rpt strip_tac >>
  irule nested_pop_mapping_leaf_slots >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem nested_pop_eval_base_slots[local]:
  !bt cx st pv st'.
    contract_storage_well_formed cx st /\
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    nested_pop_result_slots cx st pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      simp[nested_pop_result_slots_def] >>
      metis_tac[nested_pop_lookup_global_slots]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  simp[nested_pop_result_slots_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[]
  >~ [`pure_expr e`]
  >- (drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule_all nested_pop_extend_result_slots >> simp[]) >>
  drule_all nested_pop_extend_result_slots >> simp[]
QED

Theorem nested_pop_eval_target_slots[local]:
  contract_storage_well_formed cx st /\
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt st = (INL (StoragePlace tr slot tv),st') /\
  get_storage_backend cx tr st = (INL raw,st) ==>
  slots_in_range raw (w2n slot) tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_slots >> strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def,
                       nested_pop_result_slots_def]
QED

Theorem nested_pop_suffix_vv_post[local]:
  target_post ctx func cenv cx es sa sm s0 es pv vt op t /\
  ci_mono sa sm /\ stmt_state_rel ctx func cenv cx es' u /\
  storage_holds cx tr ann v slot es' u /\ lookup_var x u = SOME slot /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  (!q. not_fresh_at sm q ==> lookup_var q u = lookup_var q t) ==>
  vv_post ctx func cenv cx (Pop ann bt) es sa r s0 es' v
    (LocatedValue ann (mk_ptr (Var x) (if tr then LocTransient else LocStorage))) u
Proof
  strip_tac >>
  `!q. not_fresh_at sa q ==> not_fresh_at sm q` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  Cases_on `tr` >>
  (fs[target_post_def, vv_post_def, vv_holds_def, vv_at_def,
      contextTheory.mk_ptr_def, eval_operand_def, expr_type_def,
      locals_kept_def] >> rpt strip_tac >> gvs[]
   >- (qpat_assum `!aid off sz. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
       simp[] >> metis_tac[]) >>
   metis_tac[])
QED

Theorem nested_pop_storage_suffix_sim[local]:
  expr_sim_inv cenv cx env es /\
  EVERY pure_expr (target_indices bt) /\
  eval_target_place cx bt es = (INL (StoragePlace tr slot (ArrayTV tv (Dynamic n))),es) /\
  target_post ctx func cenv cx es sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic n))))
    (Type (ArrayT ann (Dynamic n))) (hdr,SOME (slot_loc tr),pt) t /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor
    cenv.ce_imm_alloca (if tr then LocTransient else LocStorage) sm = (q,r) /\
  pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic n))) es = (res,es') /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sm ==>
  frag_exec ctx sm r (\s. s = t)
    (\s. ?v. res = INL v /\ vv_post ctx func cenv cx (Pop ann bt) es sa r s0 es' v
      (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) s)
    (expr_exit res)
Proof
  strip_tac >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx es` by
    fs[expr_sim_inv_def] >>
  `storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic n)))` by
    metis_tac[eval_target_place_region] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  `get_storage_backend cx tr es = (INL (vyperStorageBackend$get_storage cx es tr),es)` by
    simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
  drule_all nested_pop_eval_target_slots >> strip_tac >>
  drule_all nested_pop_eval_target_live >> strip_tac >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
  qpat_x_assum `EVERY pure_expr _` kall_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` kall_tac >>
  qpat_x_assum `storage_layout_safe _` kall_tac >>
  qpat_x_assum `contract_storage_well_formed _ _` kall_tac >>
  qpat_x_assum `storage_place_region _ _` kall_tac >>
  qpat_x_assum `storage_read_live _ _ _ _ _` kall_tac >>
  drule nested_pop_suffix_shape >> strip_tac >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, ignore_bind_def, check_def, assert_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq,
       vyperStorageTheory.encode_value_def, vyperStorageTheory.encode_base_to_slot_def,
       integer_wordTheory.i2w_def] >>
  Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr) = 0w` >>
  simp[]
  >- (strip_tac >> gvs[] >> suspend "empty") >>
  `0 < w2n (lookup_storage slot (vyperStorageBackend$get_storage cx es tr))` by
    (Cases_on `lookup_storage slot (vyperStorageBackend$get_storage cx es tr)` >> gvs[]) >>
  simp[] >> strip_tac >> gvs[] >> suspend "positive"
QED

Resume nested_pop_storage_suffix_sim[empty]:
  rpt strip_tac >>
  match_mp_tac frag_exec_run_inst_seq >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[rich_listTheory.IS_PREFIX_APPEND] >>
  conj_tac >- (Cases_on `tr` >>
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
         nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  rpt strip_tac >> gvs[] >> simp[expr_exit_def] >>
  irule nested_pop_suffix_empty >> simp[] >> metis_tac[]
QED

Resume nested_pop_storage_suffix_sim[positive]:
  rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `apply_writes slot [(0,n2w (len - 1))] raw` >>
  match_mp_tac frag_exec_run_inst_seq >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- simp[rich_listTheory.IS_PREFIX_APPEND] >>
  conj_tac >- (Cases_on `tr` >>
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
         nested_pop_suffix_def, mk_inst_def, is_terminator_def]) >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  rpt strip_tac >> gvs[] >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by simp[] >>
  `!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]` by
    (simp[] >> metis_tac[]) >>
  `(if tr then tload slot t else sload slot t) <> 0w` by simp[Abbr `slot`] >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`sm.cs_next_id`, `type_slot_size tv`] strip_assume_tac) >>
  qexists `u` >> simp[] >>
  `lookup_storage slot raw - 1w = n2w (len - 1)` by
    (simp[Abbr `len`] >> Cases_on `lookup_storage slot raw` >>
     gvs[GSYM wordsTheory.n2w_sub]) >>
  `u = (if tr then tstore slot (n2w (len - 1)) t
         else sstore slot (n2w (len - 1)) t) with vs_vars := u.vs_vars` by
    (Cases_on `tr` >> fs[] >> metis_tac[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by
    (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `u = _` mp_tac >> Cases_on `tr` >>
     simp[sstore_def, tstore_def, venom_state_component_equality]) >>
  `lookup_var x6 u = SOME (slot + n2w (type_slot_size tv * (len - 1) + 1))` by
    (fs[] >> Cases_on `tr` >> fs[] >>
     simp[wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w,
          wordsTheory.WORD_ADD_ASSOC, wordsTheory.WORD_ADD_COMM,
          arithmeticTheory.MULT_COMM]) >>
  `stmt_state_rel ctx func cenv cx
    (vyperStorageBackend$set_storage cx es tr (apply_writes slot [(0,n2w (len - 1))] raw)) u` by
    (simp[Abbr `len`, Abbr `raw`] >> irule nested_pop_updated_state_rel >>
     conj_tac
     >- (goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM] >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     qexistsl [`t`, `sa`] >> simp[]) >>
  `storage_holds cx tr ann
    (PlaceR (StoragePlace tr (slot + n2w (type_slot_size tv * (len - 1) + 1)) tv))
    (slot + n2w (type_slot_size tv * (len - 1) + 1))
    (vyperStorageBackend$set_storage cx es tr (apply_writes slot [(0,n2w (len - 1))] raw)) u` by
    (simp[Abbr `raw`] >> irule nested_pop_positive_holds >>
     conj_tac >- simp[] >>
     conj_tac >- simp_tac std_ss [arithmeticTheory.ADD_COMM, arithmeticTheory.MULT_COMM] >>
     conj_tac >- simp[Abbr `len`] >>
     conj_tac >- simp[] >>
     qexistsl [`n`, `t`] >> simp[] >> metis_tac[]) >>
  irule nested_pop_suffix_vv_post >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[]
QED

Finalise nested_pop_storage_suffix_sim

Theorem pop_nested_storage_pure_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Pop ann bt)` by
    fs[expr_body_pre_def] >>
  `?n. type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n)))` by
    fs[well_typed_expr_def] >>
  pop_assum strip_assume_tac >>
  rw[expr_vv_sim_def] >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  PairCases_on `q` >>
  qmatch_asmsub_rename_tac `compile_get_target_ptr _ _ _ _ = ((hdr,loc,pt),sm)` >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rewrite_tac[nested_pop_compile_eq] >> asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >>
  qmatch_goalsub_abbrev_tac
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  Cases_on
    `compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm` >>
  simp[] >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `!h w e c i l s. ci_mono s (SND (compile_dynarray_pop h w e c i l s))` by
    simp[ci_mono_compile_dynarray_pop] >>
  `ci_mono sm r` by metis_tac[pairTheory.SND] >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split, ci_mono_def] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt es` >> rename1 `(target_res,es1)` >>
  Cases_on `target_res` >> simp[]
  >- suspend "target_success" >>
  rpt strip_tac >> gvs[] >>
  rename1 `eval_target_place cx bt es = (INR exc,es')` >>
  `frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
     (\s. F) (expr_exit (INR exc : place + exception))` by
    (qpat_x_assum `pop_target_frag _ _ _ _ _ _ _` mp_tac >>
     simp[pop_target_frag_def] >> disch_then irule >>
     simp[] >> fs[expr_vv_res_ok_def]) >>
  qspec_then `PlaceR` (qspec_then `INR exc` assume_tac) expr_exit_success_map >>
  gvs[] >>
  irule frag_exec_exit_prefix >> qexists `sm` >> fs[ci_mono_def]
QED

Resume pop_nested_storage_pure_sim[target_success]:
  strip_tac >> rename1 `eval_target_place cx bt es = (INL p,es1)` >>
  `es1 = es` by metis_tac[nested_pop_eval_target_pure_state] >> gvs[] >>
  `frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
     (\s. target_post ctx func cenv cx es sa sm s0 es (PlaceR p)
       (Type (ArrayT ann (Dynamic n))) (hdr,loc,pt) s)
     (expr_exit (INL p : place + exception))` by
    (qpat_x_assum `pop_target_frag _ _ _ _ _ _ _` mp_tac >>
     simp[pop_target_frag_def] >> disch_then irule >> simp[]) >>
  `frag_exec ctx sa sm (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
     (\s. target_post ctx func cenv cx es sa sm s0 es (PlaceR p)
       (Type (ArrayT ann (Dynamic n))) (hdr,loc,pt) s) (expr_exit res)` by
    (irule frag_exec_weaken >> goal_assum (drule_at Any) >> simp[]) >>
  irule frag_exec_seq_pointwise >>
  qpat_assum `frag_exec _ sa sm _ _ (expr_exit res)` (irule_at Any) >>
  fs[ci_mono_def] >> rpt strip_tac >>
  drule_all nested_pop_eval_target_storage_class >> strip_tac >> gvs[] >>
  drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  drule_all pop_storage_element_size >>
  disch_then (qspec_then `tr` assume_tac) >>
  fs[GSYM slot_loc_def] >>
  `ws = 1` by
    (Cases_on `tr` >> fs[Abbr `ws`, Abbr `lc`, slot_loc_def, word_scale_def]) >>
  qunabbrev_tac `lc` >> qunabbrev_tac `ws` >>
  gvs[Abbr `esz`] >>
  simp[slot_loc_def] >>
  irule nested_pop_storage_suffix_sim >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  fs[ci_mono_def, slot_loc_def] >> metis_tac[]
QED

Finalise pop_nested_storage_pure_sim


(* RESIDUAL (effectful storage indices): an index that pops or calls can
   shrink an array the target already points into, so the header the pop
   reads can be dead.  Source and Venom read the same raw slot, but
   stmt_state_rel relates only live storage.  Needs raw agreement on slots
   made dead by a pop.  The AugAssign on a storage place with an
   effectful index, and targetPlaceSimCases' target_subscript_case, have
   the same exposure. *)
Theorem pop_nested_storage_effectful_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    ~EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem pop_nested_storage_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `EVERY pure_expr (target_indices bt)`
  >- (irule pop_nested_storage_pure_sim >> metis_tac[]) >>
  irule pop_nested_storage_effectful_sim >> metis_tac[]
QED

Theorem no_storage_root_untyped_runtime[local]:
  !env cx src id.
    env_context_consistent env cx /\ ~cx.in_deploy /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_place_target env (TopLevelNameTarget (src,id))` >> simp[] >>
  gvs[type_place_target_TopLevelNameTarget,
      env_context_consistent_def, bare_global_assignable_complete_def] >>
  Cases_on `x` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  res_tac >> gvs[]
QED

Theorem target_root_untyped[local]:
  !env bt. type_place_target env (target_root bt) = NONE ==>
    type_place_target env bt = NONE
Proof
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> simp[target_root_def] >> rpt strip_tac >>
  first_x_assum (drule_at Any) >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `type_place_target env tgt` >>
  Cases_on `type_place_target env tgt` >> simp[] >>
  gvs[Abbr `tgt`, type_place_target_AttributeTarget,
      type_place_target_SubscriptTarget]
QED

(* An immutable or constant root at runtime: bare_global_assignable is
   empty outside the constructor (bare_global_assignable_complete), so the
   root names a bare global, which type_place_target rejects, and the pop
   does not type. *)
Theorem pop_nested_immutable_runtime_sim:
  !ctx func cenv cx env ann bt ty es src id.
    ~cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt gen_tac >> strip_tac >>
  `env_context_consistent env cx` by
    metis_tac[expr_body_pre_def, expr_sim_inv_def, env_consistent_def] >>
  `type_place_target env (target_root bt) = NONE` by
    metis_tac[no_storage_root_untyped_runtime] >>
  drule target_root_untyped >> strip_tac >>
  `well_typed_expr env (Pop ann bt)` by metis_tac[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr env (Pop ann bt)` mp_tac >>
  simp[Once well_typed_expr_def]
QED

(* RESIDUAL (constructor immutables): pop on a member of an immutable in
   the constructor, which Python's checker accepts for a complex immutable
   (local.py skips the modification count when var_info is None).  The
   lowering loads and stores the length through the immutables buffer
   (compile_ptr_load/compile_ptr_store), and immutable_holds accepts the
   code pointer to the popped element, whose bytes the pop leaves in the
   buffer.  The proof also needs the constructor immutable invariant. *)
Theorem pop_nested_immutable_deploy_sim:
  !ctx func cenv cx env ann bt ty es src id.
    cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* RESIDUAL (nested length words), unprovable under the current frame:
   pop on an array inside a memory local.  The pop writes the array's
   length word inside the local's region, which locals_kept exempts only
   for a root dynamic array, so vv_post's locals_kept fails.  Once
   locals_kept exempts every length word in a local's declared type
   (PR #1040), the run is compile_pop_name_sim's at the target's
   pointer. *)
Theorem pop_nested_local_sim:
  !ctx func cenv cx env ann bt ty es id.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

Theorem target_root_cases[local]:
  !bt. (?id. target_root bt = NameTarget id) \/
       (?src id. target_root bt = TopLevelNameTarget (src,id))
Proof
  `(!e:expr. T) /\
   !bt. (?id. target_root bt = NameTarget id) \/
        (?src id. target_root bt = TopLevelNameTarget (src,id))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  rw[target_root_def] >> Cases_on `p` >> simp[]
QED

(* By the target's root: a local, a storage or transient variable, or a
   module name with no storage declaration (an immutable or a constant). *)
Theorem pop_nested_sim:
  !ctx func cenv cx env ann bt ty es.
    (~immutable_root cx bt ==> pop_target_frag ctx func cenv cx env bt es) /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >>
  qspec_then `bt` strip_assume_tac target_root_cases
  >- (`~immutable_root cx bt` by gvs[immutable_root_def] >>
      irule pop_nested_local_sim >> metis_tac[]) >>
  Cases_on `?ts d. get_module_code cx src = SOME ts /\
                   find_var_decl_by_name id ts = SOME d`
  >- (gvs[] >> `~immutable_root cx bt` by gvs[immutable_root_def] >>
      irule pop_nested_storage_sim >> metis_tac[]) >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  Cases_on `cx.in_deploy`
  >- (irule pop_nested_immutable_deploy_sim >> metis_tac[]) >>
  irule pop_nested_immutable_runtime_sim >> metis_tac[]
QED

(* RESIDUAL (target metadata): the target's fragment judgment at the
   expression level.  targetPlaceSimCases' target_case_all gives target_sim
   from target_pre, whose target_env_ok asks for every storage and mapping
   declaration of every module to have its type in the compile
   environment's tables.  expr_sim_inv gives that for the storage
   variables, and for a mapping only when its type is in toplevel_vtypes
   (place_map_tables_agree_on_defined), which needs a layout slot.  The
   target only reads its root's entry, which typing puts in
   toplevel_vtypes, so a target_env_ok on the root alone would follow from
   expr_sim_inv. *)
Theorem pop_nested_expr_target_frag:
  !cenv ann bt ctx func cx env es.
    expr_sim_below cenv (expr_size (Pop ann bt)) /\
    expr_sim_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  cheat
QED

(* RESIDUAL (target metadata): the target's fragment judgment in the body,
   where an index may make an internal call.  target_case_all gives
   target_sim from body_base_target_ok's index judgments and target_pre,
   whose target_env_ok asks for every module's storage and mapping
   declarations to be in the compile environment's tables, which body_inv
   gives for the main module only (exprSimPopNested's
   pop_nested_expr_target_frag has the same gap). *)
Theorem body_pop_nested_target_frag:
  !cx bt tops ctx func cenv env ann es.
    body_base_target_ok cx bt /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    pop_target_frag ctx func cenv cx env bt es
Proof
  cheat
QED
