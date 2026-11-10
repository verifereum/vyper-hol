(* Current local memory representation for write-side subscripts. *)
Theory targetSubscriptMemory
Ancestors
  fragGasFresh fragGasMode varsExt context emitHelper emitHelperProps venomInst
  exprBopSimProps exprSimUnopProps fragExec exprSimHyps
  targetPlaceSim targetPlaceSimCasesBase exprSimProps exprSimArrayIndex
  exprSimHypsDefs exprLoweringProps freshWrites option vyperPlaceResultTyping
  exprSimAggregateEncoding tupleMemoryLayout exprSimAttributeFields
  vyperTypeExprSoundness vyperTypeInvariants vyperPlaceTyping
  vyperTypeStatePreservation vyperPlaceStatePreservation vyperTyping valueEncoding valueEncodingDefs valueEncodingProofs
  valueEncodingProps loweringPosts exprLowering compileEnv loweringStateRelDefs vyperState vyperInterpreter
  vyperTypeSystem vyperValue vyperValueOperation list rich_list pair
  words arithmetic finite_map venomState venomMemDefs exprSimSubscriptArrayFramed
Libs
  pairLib

Theorem fields_in_memory_mem_field_offset:
  !vals fs off mem id fv k ftv.
    struct_has_type fs vals /\ fields_in_memory vals fs off mem /\
    ALOOKUP vals id = SOME fv /\ mem_field_offset fs id = SOME (k,ftv) ==>
    val_in_memory ftv fv (off + k) mem
Proof
  Induct >> Cases_on `fs` >> simp[value_has_type_def] >>
  PairCases_on `h` >> Cases >>
  rename1 `struct_has_type ((fname,fty)::fts) ((vname,vval)::vrest)` >>
  simp[value_has_type_def, val_in_memory_def, mem_field_offset_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `fname = id` >> gvs[AllCaseEqs()] >>
  rename1 `mem_field_offset fts id = SOME child_offset` >>
  PairCases_on `child_offset` >> gvs[] >>
  first_x_assum drule_all >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem array_index_in_memory:
  !tv av off mem i v k etv.
    value_has_type tv (ArrayV av) /\
    val_in_memory tv (ArrayV av) off mem /\
    array_index tv av i = SOME v /\
    mem_step_offset tv (ValueSubscript (IntV i)) = SOME (k,etv) ==>
    val_in_memory etv v (off + k) mem
Proof
  rpt gen_tac >> Cases_on `tv` >> Cases_on `av` >>
  gvs[value_has_type_def] >>
  TRY (rename1 `ArrayTV _ bd` >> Cases_on `bd` >> gvs[value_has_type_def]) >>
  simp[val_in_memory_def, array_index_def, mem_step_offset_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[oEL_THM, AllCaseEqs()]
  >- (drule values_have_types_length >> strip_tac >>
      drule_all tuple_in_memory_element >> simp[GSYM type_memory_size_list_sum])
  >- (drule_all elems_in_memory_EL >> simp[AC ADD_ASSOC ADD_COMM]) >>
  drule_all kvs_in_memory_lookup >> simp[]
QED

Theorem mem_step_offset_current_value:
  !tv a sb v off mem k etv.
    value_has_type tv a /\ val_in_memory tv a off mem /\
    evaluate_subscripts tv a [sb] = INL v /\
    mem_step_offset tv sb = SOME (k,etv) ==>
    val_in_memory etv v (off + k) mem
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[evaluate_subscripts_def] >>
      Cases_on `a` >> simp[evaluate_subscripts_def, AllCaseEqs()] >>
      rpt strip_tac >> drule_all array_index_in_memory >> simp[]) >>
  Cases_on `tv` >> Cases_on `a` >>
  simp[evaluate_subscripts_def, mem_step_offset_def, value_has_type_def,
       val_in_memory_def, AllCaseEqs()] >>
  rpt strip_tac >> drule_all fields_in_memory_mem_field_offset >> simp[]
QED

Theorem mem_path_offset_current_value:
  !path tv a v off mem k ptv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\
    evaluate_subscripts tv a path = INL v /\
    mem_path_offset tv path = SOME (k,ptv) ==>
    val_in_memory ptv v (off + k) mem
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, evaluate_subscripts_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  rename1 `mem_step_offset tv sb = SOME (delta,etv)` >>
  `mem_path_offset tv [sb] = SOME (delta,etv)` by
    simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> simp[subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `a`] assume_tac) >>
  qpat_x_assum `evaluate_subscripts tv a (sb::path) = INL v` mp_tac >>
  once_asm_rewrite_tac[] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `evaluate_subscripts tv a [sb] = INL child` >>
  `value_has_type etv child` by
    (irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
     simp[subscripts_type_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  drule_all mem_step_offset_current_value >> strip_tac >>
  first_x_assum drule_all >> simp[NoAsms, AC ADD_ASSOC ADD_COMM]
QED

Theorem place_ptr_rel_memory_current:
  !ctx func cenv cx env es s id path entry v w loc ty tv.
    expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    val_in_memory tv v (w2n w) s.vs_memory /\
    value_has_type tv v /\ well_formed_type_value tv /\
    subscripts_type entry.type path = SOME tv
Proof
  rpt gen_tac >> strip_tac >>
  `?ety. FLOOKUP env.var_types id = SOME ety` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[IS_SOME_EXISTS]) >>
  `cenv.ce_var_type id = SOME ety /\
   evaluate_type (get_tenv cx) ety = SOME entry.type` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     metis_tac[]) >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[lookup_scopes_well_typed_value_has_type, lookup_scopes_well_typed_type]) >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  qpat_x_assum `!name entry p sz. _ ==> _` drule_all >> strip_tac >> gvs[] >>
  drule_all mem_path_offset_current_value >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  drule alloca_room_next_lt >> strip_tac >>
  `w2n b + k < dimword (:256)` by decide_tac >>
  `k < dimword (:256)` by decide_tac >>
  simp[w2n_add_2, w2n_n2w, LESS_MOD] >> fs[ADD_COMM] >>
  conj_tac
  >- (irule evaluate_subscripts_type >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all subscripts_type_well_formed >> simp[]
QED

Theorem array_len_ok_memory_current:
  !ctx func cenv cx env es s id path entry vs w loc ty etv cap ptr cnt.
    expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
    place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
    evaluate_type (get_tenv cx) ty = SOME (ArrayTV etv (Dynamic cap)) /\
    eval_operand ptr s = SOME w ==>
    array_len_ok T cnt
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory)
      ptr s (n2w (LENGTH vs))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all place_ptr_rel_memory_current >>
  simp[val_in_memory_def] >> strip_tac >>
  drule array_len_ok_MLOAD >>
  disch_then (qspecl_then [`cenv.ce_is_ctor`, `cenv.ce_imm_alloca`, `cnt`] mp_tac) >>
  simp[GSYM mem_word_at_eq_mload]
QED

Theorem target_post_suffix_frame:
  target_post ctx func cenv cx es sa sm s0 es' pv vt rb t /\
  sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es' u /\
  (?w. eval_operand dst u = SOME w /\ place_ptr_rel cenv cx u pv' w loc vt') /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  place_readable cx es' pv' /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==>
         lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  u.vs_memory = t.vs_memory ==>
  target_post ctx func cenv cx es sa sb s0 es' pv' vt'
    (dst,loc,SOME (value_type_place vt')) u
Proof
  strip_tac >>
  `locals_kept cenv es s0 u` by
    (irule locals_kept_mem_tail >> qexists `t` >> gvs[target_post_def]) >>
  gvs[target_post_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem place_ptr_rel_memory_step:
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  mem_step_offset tv sb = SOME (k,etv) /\
  evaluate_type (get_tenv cx) ety = SOME etv ==>
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id (path ++ [sb])))
    (w + n2w k) loc (Type ety)
Proof
  simp[place_ptr_rel_def] >> strip_tac >> gvs[] >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  simp[place_ptr_rel_def, AC WORD_ADD_ASSOC WORD_ADD_COMM,
       word_add_n2w, ADD_COMM]
QED

Theorem extend_place_memory_live_result:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  subscripts_type entry.type path = SOME tv ==>
  extend_place cx (PlaceR (MemoryPlace id path)) sb es =
    (case evaluate_subscripts tv v [sb] of
     | INL w => (INL (PlaceR (MemoryPlace id (path ++ [sb]))),es)
     | INR err => (INR (Error err),es))
Proof
  rpt strip_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, read_memory_path_def,
       extend_memory_place_def] >>
  Cases_on `evaluate_subscripts tv v [sb]` >>
  simp[lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem place_readable_memory_live:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v ==>
  place_readable cx es (PlaceR (MemoryPlace id path))
Proof
  rpt strip_tac >>
  simp[place_readable_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, read_memory_path_def]
QED

Theorem extend_place_memory_live:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  extend_place cx (PlaceR (MemoryPlace id path)) sb es = (INL pv,es') ==>
  es' = es /\ pv = PlaceR (MemoryPlace id (path ++ [sb])) /\
  ?w. evaluate_subscripts entry.type entry.value (path ++ [sb]) = INL w
Proof
  strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def, read_memory_path_def,
       extend_memory_place_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `subscripts_type entry.type path` >>
  gvs[return_def, raise_def] >>
  rename1 `subscripts_type entry.type path = SOME ptv` >>
  Cases_on `evaluate_subscripts ptv v [sb]` >>
  gvs[return_def, raise_def] >>
  drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` mp_tac) >> simp[]
QED

(* Preserve pointer values that already exist; fresh writes may create new ones. *)
Theorem target_place_ptr_values_frame:
  place_ptr_rel cenv cx s pv w loc vt /\ local_ptrs_reserved cenv sa /\
  (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
         lookup_var x t = SOME v) ==>
  place_ptr_rel cenv cx t pv w loc vt
Proof
  Cases_on `pv` >> simp[place_ptr_rel_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> simp[place_ptr_rel_def] >>
  rpt strip_tac >> gvs[] >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  metis_tac[]
QED

Theorem target_post_memory_step:
  target_post ctx func cenv cx es sa sm s0 es2
    (PlaceR (MemoryPlace id path)) (Type ty) rb t /\
  lookup_scopes id es2.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL v /\
  extend_place cx (PlaceR (MemoryPlace id path)) sub es2 = (INL pv',es3) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  mem_step_offset tv sub = SOME (k,etv) /\
  evaluate_type (get_tenv cx) ety = SOME etv /\
  eval_operand (FST rb) t = SOME w /\
  eval_operand dst u = SOME (w + n2w k) /\
  stmt_state_rel ctx func cenv cx es2 u /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  (!x z. not_fresh_at sm x /\ lookup_var x t = SOME z ==>
         lookup_var x u = SOME z) /\
  (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP u.vs_allocas aid = SOME b) /\
  u.vs_memory = t.vs_memory ==>
  target_post ctx func cenv cx es sa sb s0 es3 pv' (Type ety)
    (dst,SOME LocMemory,SOME (ValPT ety)) u
Proof
  strip_tac >>
  drule_all extend_place_memory_live >> strip_tac >> gvs[] >>
  `place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type ty)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  `place_ptr_rel cenv cx t
     (PlaceR (MemoryPlace id (path ++ [sub]))) (w + n2w k)
     (SOME LocMemory) (Type ety)` by
    (irule place_ptr_rel_memory_step >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `place_ptr_rel cenv cx u
     (PlaceR (MemoryPlace id (path ++ [sub]))) (w + n2w k)
     (SOME LocMemory) (Type ety)` by
    (irule target_place_ptr_values_frame >> qexistsl [`t`, `sm`] >> simp[]) >>
  once_rewrite_tac[GSYM value_type_place_def] >>
  drule_then irule target_post_suffix_frame >> simp[] >>
  irule place_readable_memory_live >> goal_assum (drule_at Any) >> simp[]
QED

Theorem extend_place_memory_array_index:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  subscripts_type entry.type path = SOME (ArrayTV et bd) /\
  value_has_type (ArrayTV et bd) (ArrayV av) ==>
  extend_place cx (PlaceR (MemoryPlace id path))
    (ValueSubscript (IntV i)) es =
  (if 0 <= i /\ Num i < array_length (ArrayTV et bd) av
   then (INL (PlaceR (MemoryPlace id
                (path ++ [ValueSubscript (IntV i)]))),es)
   else (INR (Error (RuntimeError "evaluate_subscripts array_index")),es))
Proof
  strip_tac >>
  drule_all extend_place_memory_live_result >>
  disch_then (qspecl_then [`ValueSubscript (IntV i)`, `cx`] mp_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, evaluate_subscripts_def, array_length_def,
      array_index_def, oEL_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  qmatch_goalsub_rename_tac `ALOOKUP sparse (Num i)` >>
  Cases_on `ALOOKUP sparse (Num i)` >> gvs[]
QED

Theorem target_array_subscript_straight_fresh:
  (!p. straight_fresh (loader p)) ==>
  straight_fresh (compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    loader)
Proof
  strip_tac >> rewrite_tac[compile_array_subscript_split] >>
  match_mp_tac straight_fresh_bind >> conj_tac
  >- (Cases_on `dyn` >> simp[straight_fresh_return]) >>
  simp[straight_fresh_array_check_ptr]
QED


Theorem target_memory_header_load:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op s = SOME w ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (mload (w2n w) s) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  simp[compile_ptr_load_def] >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qexists_tac `update_var out (mload (w2n w) s) s
                with vs_inst_idx := SUC s.vs_inst_idx` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >>
     metis_tac[LESS_EQ_REFL]) >>
  `dst = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt conj_tac
  >- (pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
      qunabbrev_tac `out` >>
      irule emit_op_zero_path >> simp[] >>
      qexistsl [`[base_op]`, `dst`, `MLOAD`, `sb`] >>
      simp[is_terminator_def, step_MLOAD])
  >- simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >> simp[])
  >- (rpt strip_tac >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      metis_tac[lookup_var_def]) >>
  simp[update_var_def]
QED

Theorem target_array_check_ptr_path:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!x. len_op = Var x ==> not_fresh_at sa x) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  eval_operand len_op s = SOME len /\ idx_in_range sgn i len ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t =
        SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
                FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i /\
   eval_operand len_op (drop_fresh sa s) = SOME len` by
    simp[eval_operand_drop_fresh] >>
  drule_at (Pat `comp_ignore_bind _ _ _ = _`) array_check_ptr_run >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem target_array_check_ptr_abort_path:
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (dst,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!x. len_op = Var x ==> not_fresh_at sa x) /\
  eval_operand idx_op s = SOME i /\ eval_operand len_op s = SOME len /\
  ~idx_in_range sgn i len ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `eval_operand idx_op (drop_fresh sa s) = SOME i /\
   eval_operand len_op (drop_fresh sa s) = SOME len` by
    simp[eval_operand_drop_fresh] >>
  drule_at (Pat `comp_ignore_bind _ _ _ = _`) array_check_ptr_oob >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem target_memory_header_compile:
  compile_ptr_load ctor imm LocMemory base_op sa = (dst,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x. dst = Var x ==> not_fresh_at sb x)
Proof
  simp[compile_ptr_load_def, emit_op_def, comp_bind_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[cs_extends_def, not_fresh_at_def, IS_PREFIX_APPEND] >>
  simp[]
QED

Theorem target_memory_dynamic_array_path:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (mload (w2n b) s) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t = SOME (b + n2w ws + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
                FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule target_memory_header_compile >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. idx_op = Var x ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all target_memory_header_load >> strip_tac >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl [`sa`, `s`] >> simp[]) >>
  drule_all target_array_check_ptr_path >> strip_tac >>
  qexists_tac `t'` >>
  conj_tac
  >- (qpat_x_assum `gas_marked_path F ctx func s 0 (OK t)` mp_tac >>
      qpat_x_assum `gas_marked_path F ctx func t 0 (OK t')` mp_tac >>
      metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem target_memory_dynamic_array_abort_path:
  compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (mload (w2n b) s) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  drule target_memory_header_compile >> strip_tac >>
  `!x. idx_op = Var x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  drule_all target_memory_header_load >> strip_tac >>
  `eval_operand idx_op t = SOME i` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`sa`, `s`] >> simp[]) >>
  drule_all target_array_check_ptr_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >>
  qpat_x_assum `gas_marked_path F ctx func s 0 (OK t)` mp_tac >>
  qpat_x_assum `gas_marked_path F ctx func t 0 (Abort Revert_abort t')` mp_tac >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Theorem target_memory_array_path:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
             lookup_var x t = SOME v) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
                FLOOKUP t.vs_allocas aid = SOME a) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_path >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all target_memory_dynamic_array_path >> simp[]
QED

Theorem target_memory_array_abort_path:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if dyn then mload (w2n b) s else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_abort_path >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ _ sa = (len_op,sm)` >>
  drule target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all target_memory_dynamic_array_abort_path >> simp[]
QED

Theorem target_typed_index_range:
  evaluate_type tenv ity = SOME itv /\ value_has_type itv (IntV i) /\
  n < dimword (:256) ==>
  (idx_in_range (is_signed_type ity) (i2w i) (n2w n) <=>
   0 <= i /\ Num i < n)
Proof
  Cases_on `ity`
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[evaluate_type_def, value_has_type_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[value_has_type_def]
      >- (`Num i < dimword (:256)` by
            (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** n'` >>
             simp[dimword_def, bitTheory.TWOEXP_MONO2]) >>
          `i = &Num i` by simp[integerTheory.INT_OF_NUM] >>
          qpat_x_assum `i = &Num i` SUBST1_TAC >>
          simp[idx_in_range_def, is_signed_type_def, integer_wordTheory.i2w_pos,
               w2n_n2w, LESS_MOD]) >>
      `w2i (i2w i : bytes32) = i` by
        metis_tac[vyperArithTheory.w2i_i2w_within_signed] >>
      simp[idx_in_range_def, is_signed_type_def, integer_wordTheory.WORD_LTi, integer_wordTheory.word_0_w2i,
           w2n_n2w, LESS_MOD] >>
      Cases_on `0 <= i`
      >- (`Num i < dimword (:256)` by
            (drule_all vyperArithTheory.within_int_bound_in_word_range >>
             simp[INT_MAX_def, INT_MIN_def, dimword_def] >>
             intLib.ARITH_TAC) >>
          `i = &Num i` by simp[integerTheory.INT_OF_NUM] >>
          qpat_x_assum `i = &Num i` SUBST1_TAC >>
          simp[integer_wordTheory.i2w_pos, w2n_n2w, LESS_MOD]) >>
      intLib.ARITH_TAC) >>
  simp[evaluate_type_def, value_has_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[value_has_type_def]
QED

Theorem target_memory_array_header:
  val_in_memory (ArrayTV etv (Dynamic cnt)) (ArrayV av) (w2n b) s.vs_memory /\
  value_has_type (ArrayTV etv (Dynamic cnt)) (ArrayV av) ==>
  mload (w2n b) s = n2w (array_length (ArrayTV etv (Dynamic cnt)) av)
Proof
  Cases_on `av` >> simp[value_has_type_def, val_in_memory_def,
    array_length_def, GSYM mem_word_at_eq_mload]
QED

Theorem target_memory_array_length_bound:
  evaluate_type tenv (ArrayT ety bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  array_length (ArrayTV etv bd) av < dimword (:256)
Proof
  strip_tac >>
  `bound_length bd < dimword (:256)` by
    (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
     rw[evaluate_type_def, AllCaseEqs()] >> Cases_on `bd` >>
     gvs[type_slot_size_def, vyperASTTheory.bound_length_def] >>
     `n <= n * type_slot_size etv` by
       (Cases_on `type_slot_size etv` >> gvs[MULT_CLAUSES]) >>
     decide_tac) >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[value_has_type_def, array_length_def, vyperASTTheory.bound_length_def] >>
  decide_tac
QED

Theorem target_memory_array_range:
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b loc
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) ==>
  (idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then mload (w2n b) s else n2w cnt) <=>
   0 <= i /\ Num i < array_length (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) av)
Proof
  strip_tac >> drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all target_memory_array_length_bound >> strip_tac >>
  Cases_on `dyn` >> gvs[]
  >- (drule_all target_memory_array_header >> disch_then SUBST1_TAC >>
      metis_tac[target_typed_index_range]) >>
  Cases_on `av` >> gvs[value_has_type_def, array_length_def] >>
  metis_tac[target_typed_index_range]
QED

Theorem target_memory_array_offset:
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  value_has_type (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) (ArrayV av) /\
  0 <= i /\ Num i < array_length (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) av ==>
  ?k. mem_step_offset (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt))
        (ValueSubscript (IntV i)) = SOME (k,etv) /\
      evaluate_type (get_tenv cx) ety = SOME etv /\
      ((if dyn then b + n2w 32 else b) + i2w i * n2w (type_memory_bytes cenv ety) =
       (b : bytes32) + n2w k)
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) ety = SOME etv` by
    (gvs[evaluate_type_def, AllCaseEqs()]) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  `i2w i : bytes32 = n2w (Num i)` by
    (`i = &Num i` by simp[integerTheory.INT_OF_NUM] >>
     qpat_x_assum `i = &Num i` SUBST1_TAC >>
     simp[integer_wordTheory.i2w_pos]) >>
  Cases_on `dyn` >> Cases_on `av` >>
  gvs[value_has_type_def, array_length_def, mem_step_offset_def] >>
  simp[integer_wordTheory.i2w_pos, word_add_n2w, word_mul_n2w,
       WORD_ADD_ASSOC, ADD_COMM] >>
  pure_rewrite_tac[GSYM word_add_n2w] >>
  metis_tac[WORD_ADD_ASSOC, WORD_ADD_COMM]
QED

Theorem target_memory_array_error_suffix:
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INR err,es') ==>
  (?u. gas_marked_path F ctx func s 0 (Abort Revert_abort u)) /\
  err = Error (RuntimeError "evaluate_subscripts array_index") /\ es' = es
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   ?b. eval_operand (FST rb) s = SOME b /\
       place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
         (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))` by
    fs[target_post_def] >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `cx`] assume_tac) >>
  drule_all target_memory_array_range >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all target_memory_array_abort_path >> simp[]
QED

Theorem target_memory_array_suffix:
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (MemoryPlace id path))
    (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))) rb s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)) =
    SOME (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv (IntV i) /\
  eval_operand idx s = SOME (i2w i) /\
  compile_array_subscript (FST rb) idx dyn cnt 32 (type_memory_bytes cenv ety)
    (is_signed_type ity)
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. idx = Var x ==> not_fresh_at sm x) /\
  (!l. idx <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\
  extend_place cx (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL pv',es') ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
      target_post ctx func cenv cx es0 sa sb s0 es' pv' (Type ety)
        (dst,SOME LocMemory,SOME (ValPT ety)) u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es s /\
   (?b. eval_operand (FST rb) s = SOME b /\
        place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) b
          (FST (SND rb)) (Type (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt)))) /\
   (!x. FST rb = Var x ==> not_fresh_at sm x)` by fs[target_post_def] >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all extend_place_memory_array_index >>
  disch_then (qspecl_then [`i`, `cx`] assume_tac) >>
  `0 <= i /\ Num i < array_length (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)) av` by
    (gvs[AllCaseEqs()]) >>
  drule_all target_memory_array_range >> strip_tac >>
  `idx_in_range (is_signed_type ity) (i2w i)
     (if dyn then mload (w2n b) s else n2w cnt)` by metis_tac[] >>
  drule_all target_memory_array_path >> strip_tac >>
  drule_all target_memory_array_offset >>
  disch_then (qspec_then `b` strip_assume_tac) >>
  `eval_operand dst t = SOME (b + n2w k)` by metis_tac[] >>
  drule_all target_post_memory_step >> strip_tac >>
  qexists_tac `t` >> simp[]
QED
