(*
 * Expression simulation: places (#636, Places)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for subscripts,
 * attributes and pop.  Proved: pop on a local (compile_pop_name_case, by
 * exprSimPop's compile_pop_name_sim, for the body simulation too),
 * attributes (exprSimAttribute's compile_attribute_vv_sim), tuple
 * subscripts (exprSimTuple's compile_subscript_tuple_sim), a dispatch that
 * disagrees with the base's type and subscripts of any base but an array, a
 * tuple or a mapping, which do not type.  Cheated, for the later #636 PRs:
 * array and mapping subscripts and pop on any other target, by kind
 * (compile_pop_storage_sim, compile_pop_immutable_sim,
 * compile_pop_nested_sim).  Admitted: an array subscript with a pop
 * (compile_subscript_array_pop_case), with a call in the index of a
 * storage or transient base (compile_subscript_array_storage_call_case),
 * or of an immutable in the constructor or with an effectful index
 * (compile_subscript_array_ctor_code_case).
 *
 * TOP-LEVEL:
 *   compile_subscript_case — static and dynamic arrays with the
 *                           bounds-check abort, hashmaps, tuples (#558),
 *                           Places row 1, over expr_vv_case: by place_type
 *                           of the base, compile_subscript_map_case for a
 *                           mapping, compile_subscript_mismatch_case for a
 *                           dispatch type other than the base's,
 *                           compile_subscript_tuple_sim for a tuple,
 *                           compile_subscript_array_case for an array
 *   compile_subscript_sim — compile_subscript_case with nocalls = T
 *   compile_attribute_sim — struct fields (#558), row 2: by
 *                           compile_attribute_vv_sim
 *   compile_pop_sim       — pop on a dynamic array, with the empty-array
 *                           abort, row 3: compile_pop_name_sim for a local,
 *                           compile_pop_other_sim for the rest
 *
 * The case lemmas take the base's expr_vv_case and the index's
 * expr_sim_case; expr_vv_case describes a base's value_vv, captured memory,
 * storage and transient places included.  It does not cover a hashmap
 * base: that evaluates to a HashMapRef and is typed by type_place_expr, not
 * well_typed_expr, so for a nested mapping (m[a][b]) nothing judges the
 * inner key a.  The mapping lemma's proof needs expr_vv_case to describe a
 * HashMapRef result (the operand holding the mapping's slot), which then
 * carries the inner keys' simulation to the outer subscript.
 *
 * compile_subscript dispatches on place_type of the base, the base's own
 * type for a nested place, and pop takes its target's place from
 * compile_get_target_ptr, so nested subscripts and pops are lowered at
 * their element type.  (compile_attribute finds the struct from the base's
 * type.)
 *)

Theory exprSimPlaces
Ancestors
  list exprSim exprSimHyps exprSimPop exprSimAttribute exprSimTuple
  exprSimArrayIndex exprSimArraySubscript exprLoweringProps fragExec compileEnv
  exprLowering exprCallbackContracts placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* ===== Subscripts ===== *)

(* The case lemmas take the judgments a shared case lemma takes
   (expr_vv_case, expr_sim_case: exprSimHyps), so the body simulation's
   body_subscript_case (bodySimExprCases), where an operand may call an
   internal function, uses them with nocalls = F, as compile_subscript_sim
   does with T. *)

(* ===== Mappings ===== *)

(* A mapping variable: compile_expr's pointer is the mapping's slot, at its
   storage location (compile_toplevel_name_sim in exprSimLeaves is the
   other variables').  Cheated. *)
Theorem compile_toplevel_map_case:
  !nocalls ctx func cenv cx ty id.
    expr_map_case nocalls ctx func cenv cx (TopLevelName ty id)
Proof
  cheat
QED

(* A mapping that is a value of a mapping (m[a] for m : HashMap[K,
   HashMap[...]]): the base's slot, the key lowered after it, and
   compile_mapping_subscript's SHA3 over the two against hashmap_slot slot
   (encode_hashmap_key kt kv), with compile_keccak256_key for a bytes or
   string key.  Cheated. *)
Theorem compile_subscript_map_map_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_map_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

Theorem expr_sim_below_mono[local]:
  !cenv m n. expr_sim_below cenv n /\ m <= n ==> expr_sim_below cenv m
Proof
  rw[expr_sim_below_def]
QED

(* With every smaller expression simulating, an expression naming a
   mapping simulates: its keys are smaller. *)
Theorem expr_map_case_below:
  !obj cenv ctx func cx.
    expr_sim_below cenv (expr_size obj) ==>
    expr_map_case T ctx func cenv cx obj
Proof
  measureInduct_on `expr_size obj` >> rpt strip_tac >>
  Cases_on `obj`
  >~ [`TopLevelName`] >- simp[compile_toplevel_map_case]
  >~ [`Subscript _ _ _`]
  >- (rename1 `Subscript ann obj0 idx` >>
      irule compile_subscript_map_map_case >> conj_tac
      >- (rpt strip_tac >>
          `expr_ok cenv idx` by
            (fs[expr_sim_below_def] >> first_x_assum irule >>
             simp[expr_size_def]) >>
          gvs[expr_ok_case]) >>
      first_x_assum irule >> simp[expr_size_def] >>
      irule expr_sim_below_mono >>
      qexists_tac `expr_size (Subscript ann obj0 idx)` >>
      simp[expr_size_def]) >>
  irule expr_map_case_other >> simp[]
QED

(* A subscript of a mapping (place_type MapPT) whose values are not
   mappings: the leaf's storage place.  Cheated: the base's slot comes from
   its expr_map_case, the key's word is lowered after it, and
   compile_mapping_subscript's SHA3 over the two stored in a 64-byte buffer
   computes hashmap_slot slot (encode_hashmap_key kt kv), with
   compile_keccak256_key for a bytes or string key.  expr_sim_inv's map
   table clauses make MapPT mean a declared mapping.  For a storage or
   transient subscript, here and in compile_subscript_array_case,
   storage_holds also asks that the element's or hashmap leaf's slots are in
   range (slots_in_range); the proof gets that from the base's
   storage_mapping_region and the hashmap regions of
   contract_storage_well_formed, as toplevel_storage_slots_in_range and
   storage_field_slots_in_range do for names and struct fields. *)
Theorem compile_subscript_map_case:
  !nocalls ctx func cenv cx ann obj idx kt vt.
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    place_type cenv obj = MapPT kt vt ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* The compiler's dispatch type disagrees with the base's type: place_type
   says ValPT bt with bt not the base's expr_type.  Unreachable: under
   expr_sim_inv's map table clauses a well-typed base's place_type is its
   own type, and a place-typed base's is that of its vtype. *)
Theorem compile_subscript_mismatch_case:
  !nocalls ctx func cenv cx ann obj idx bt.
    place_type cenv obj = ValPT bt /\ bt <> expr_type obj ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rw[expr_vv_case_def, expr_body_pre_def, expr_sim_inv_def] >>
  gvs[Once well_typed_expr_def]
  >- (drule_all place_type_well_typed_on_defined >> simp[]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  drule type_place_expr_vtype_annotation >>
  Cases_on `vt` >> gvs[value_type_place_def, vtype_annotation_ok_def]
QED

(* A subscript's base whose dispatch type is its own is an array or a
   tuple: subscript_type_ok is false of every other type, and a place-typed
   base whose place_type is ValPT has a value vtype, which subscript_vtype
   indexes only for an array. *)
Theorem subscript_base_array_or_tuple[local]:
  !cenv cx env ann obj idx es.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    place_type cenv obj = ValPT (expr_type obj) ==>
    (?et bd. expr_type obj = ArrayT et bd) \/ (?tys. expr_type obj = TupleT tys)
Proof
  rpt gen_tac >> simp[expr_body_pre_def, expr_sim_inv_def] >>
  simp[Once well_typed_expr_def] >> rpt strip_tac
  >- (Cases_on `expr_type obj` >> gvs[subscript_type_ok_def]) >>
  drule_all place_type_checked_place_on_defined >> strip_tac >>
  Cases_on `vt` >> gvs[value_type_place_def] >>
  Cases_on `expr_type obj` >> gvs[subscript_vtype_def]
QED

Theorem compile_expr_array_subscript[local]:
  !cenv ty ann obj idx et bd st vv st'.
    compile_expr cenv ty (Subscript ann obj idx) st = (vv, st') /\
    place_type cenv obj = ValPT (ArrayT et bd) ==>
    ?bvv st1 iop st2 p.
      compile_expr cenv ty obj st = (bvv, st1) /\
      lower_value compile_expr cenv ty idx st1 = (iop, st2) /\
      compile_array_subscript (vv_operand bvv) iop
        (case bd of Fixed n => F | Dynamic n => T)
        (case bd of Fixed n => n | Dynamic n => 0)
        (word_scale (vv_loc bvv))
        (elem_size_in_location cenv (vv_loc bvv) et)
        (is_signed_type (expr_type idx))
        (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (vv_loc bvv))
        st2 = (p, st') /\
      vv = LocatedValue ann (mk_ptr p (vv_loc bvv))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  pure_rewrite_tac[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[SF ETA_ss, compile_subscript_child_calls] >>
  simp[compile_subscript_def, compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[compileEnvTheory.comp_return_def, vv_loc_def] >>
  Cases_on `bd` >> gvs[]
QED

(* An element of a static or dynamic array, with the bounds-check abort,
   for a subscript with no pop, no call in the index of a storage or
   transient base, and no immutable base in the constructor.  Cheated, for
   the alan run: compile_subscript lowers the index after the base.  Where
   the base points into a local (x[i] for a local x), vv_holds gives the
   base's pointer as the local's place at the base's path (local_place_at),
   which the index's fragment keeps (local_place_at_vars_frame); without a
   pop the index leaves the source locals as they were (a call restores
   the caller's scopes), so the base's path still reads the current value
   and the element is at the base's pointer plus its offset.  The bounds
   check itself, a source RuntimeError for an index out of range against
   compile_array_subscript's ASSERT, which aborts, is in expr_exit's
   allowance (exprSimArrayIndex).  A dynamic array in code (an immutable,
   LocCode) reads its length with compile_ptr_load's compile_imm_load_word
   (ILOAD or DLOAD), for which exprSimArrayIndex has no array_len_ok lemma
   yet. *)
Theorem compile_subscript_array_nopop_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    ~expr_has_pop (Subscript ann obj idx) /\
    (!ty st l. vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
               is_slot_addressed l ==> ~expr_has_effect idx) /\
    (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode ==>
             ~cenv.ce_is_ctor /\ ~expr_has_effect idx) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >> simp[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env obj es` by
    (drule_all expr_body_pre_subscript_array_base >> simp[]) >>
  `nocalls ==> int_calls_expr obj = []` by
    gvs[int_calls_expr_def] >>
  `expr_vv_sim ctx func cenv cx ty obj es` by
    (qpat_x_assum `expr_vv_case _ _ _ _ _ obj` mp_tac >>
     simp[expr_vv_case_def] >> disch_then irule >> simp[] >>
     qexists_tac `env` >> simp[]) >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  rename1 `lower_value compile_expr cenv ty idx sm = (iop,si)` >>
  `ci_mono si sb` by
    metis_tac[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load,
              pairTheory.SND] >>
  drule (cj 1 compile_expr_grows) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >> strip_tac >>
  `cs_extends si sb` by fs[ci_mono_def] >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm si func /\ fn_has_code si sb func` by
    metis_tac[fn_has_code_split] >>
  irule frag_exec_pointwise_control >> rpt strip_tac >> gvs[] >>
  Cases_on `eval_expr cx obj es` >> rename1 `_ = (er,es1)` >>
  `expr_vv_res_ok er` by (drule_all expr_body_pre_vv_res_ok >> simp[]) >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _` mp_tac >>
  simp[expr_vv_sim_def] >> disch_then drule_all >>
  disch_then (qspec_then `s0` assume_tac) >>
  Cases_on `er`
  >- suspend "base_success" >>
  gvs[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def] >>
  irule frag_exec_exit_prefix >> qexists_tac `sm` >> simp[] >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[]
QED

Resume compile_subscript_array_nopop_case[base_success]:
  rename1 `eval_expr cx obj es = (INL btv,es1)` >> gvs[] >>
  `expr_body_pre cenv cx env idx es1` by
    (drule_all expr_body_pre_subscript_array_index_after >> simp[]) >>
  `nocalls ==> int_calls_expr idx = []` by gvs[int_calls_expr_def] >>
  `expr_sim_case nocalls ctx func cenv cx idx` by metis_tac[] >>
  `expr_sim ctx func cenv cx ty idx es1` by
    (drule_all expr_sim_case_apply >> simp[]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\s. vv_post ctx func cenv cx obj es sa sm s0 es1 btv bvv s`, `sm`] >>
  simp[] >> conj_tac
  >- (irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[expr_exit_def]) >>
  irule frag_exec_pointwise >> rpt strip_tac >> gvs[] >>
  rename1 `vv_post _ _ _ _ obj _ _ _ _ _ _ _ q0` >>
  `stmt_state_rel ctx func cenv cx es1 q0` by fs[vv_post_def] >>
  `local_ptrs_reserved cenv sm` by
    (drule_all compile_expr_local_ptrs_reserved >> simp[]) >>
  Cases_on `(do result <- eval_expr cx idx; read_result cx result od) es1` >>
  rename1 `_ = (ir,es2)` >>
  `expr_res_ok ir` by (drule_all expr_body_pre_res_ok >> simp[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ idx _` mp_tac >>
  simp[expr_sim_def] >> disch_then drule_all >>
  disch_then (qspec_then `q0` assume_tac) >>
  Cases_on `eval_expr cx idx es1` >> rename1 `_ = (itr,eit)` >>
  Cases_on `itr`
  >- suspend "index_read" >>
  gvs[vyperStateTheory.bind_def] >>
  gvs[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def] >>
  irule frag_exec_exit_prefix >> qexists_tac `si` >> simp[] >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  gen_tac >> Cases_on `r` >> Cases_on `y` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED
Resume compile_subscript_array_nopop_case[index_read]:
  rename1 `eval_expr cx idx es1 = (INL itv,eit)` >>
  gvs[vyperStateTheory.bind_def] >>
  drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
  Cases_on `ir`
  >- suspend "index_success" >>
  gvs[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def] >>
  irule frag_exec_exit_prefix >> qexists_tac `si` >> simp[] >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  gen_tac >> Cases_on `r` >> rename1 `INR exc` >>
  Cases_on `exc` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED
Resume compile_subscript_array_nopop_case[index_success]:
  rename1 `read_result cx itv eit = (INL iv,eit)` >> gvs[] >>
  irule frag_exec_seq >>
  qexistsl_tac [`expr_post ctx func cenv cx idx es1 sm si q0 eit iv iop`, `si`] >>
  simp[] >> conj_tac
  >- (irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[expr_exit_def]) >>
  irule frag_exec_pointwise >> rpt strip_tac >> gvs[] >>
  rename1 `expr_post _ _ _ _ idx _ _ _ _ _ _ _ q1` >>
  `~expr_has_pop obj /\ ~expr_has_pop idx` by fs[expr_has_pop_def, supportedExprTraverseTheory.supported_expr_exists_def,
      expr_pop_root_def] >>
  `vv_post ctx func cenv cx obj es sa si s0 eit btv bvv q1` by
    (drule_all compile_array_endpoint_post >> simp[]) >>
  qpat_x_assum `frag_exec ctx sa sm _ _ _` kall_tac >>
  qpat_x_assum `frag_exec ctx sm si _ _ _` kall_tac >>
  `expr_sim_inv cenv cx env eit /\
   eval_result_typed (env,cx,eit) itv (Type (expr_type idx))` by
    (drule_all expr_body_pre_eval_result >> simp[]) >>
  `select_result cx (ArrayT et bd) btv (ValueSubscript iv) eit = (res,es')` by
    (qpat_x_assum `eval_expr cx (Subscript _ _ _) es = _` mp_tac >>
     simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def]) >>
  irule compile_array_selection_suffix >>
  qpat_assum `compile_expr cenv ty obj sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> qexists_tac `env` >> simp[] >>
  strip_tac >>
  qpat_x_assum `!ty st. vv_location _ = SOME LocCode ==> _`
    (qspecl_then [`ty`, `sa`] mp_tac) >> simp[]
QED
Finalise compile_subscript_array_nopop_case

(* An element of an array in a subscript with a pop (expr_has_pop,
   exprSimHyps).  ADMITTED (cheat), with target_subscript_pop_case on the
   write side: a pop in the base or the index that pops the base's array
   (x[1][x.pop()]) leaves the source reading the base's path from the
   popped history (read_memory_path), which no invariant relates to memory
   yet, and a nested pop (x[0][x[0].pop()]) writes an inner length word
   that the shared locals_kept frame keeps.  The repair of that frame
   replaces this lemma. *)
Theorem compile_subscript_array_pop_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    expr_has_pop (Subscript ann obj idx) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An element of a storage or transient array whose index has a call
   (expr_has_effect).  ADMITTED (cheat): the call can shrink the array
   (self.a[0][self.f()] with f popping self.a), and the source and the
   lowering then both read the element at the base's slot, past the
   array's new length, but storage_holds asks that the result's bytes are
   live (storage_read_live), which they are not.  A storage judgment that
   allows a dead place read replaces this lemma. *)
Theorem compile_subscript_array_storage_call_case:
  !nocalls ctx func cenv cx ann obj idx et bd ty st l.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
    is_slot_addressed l /\ expr_has_effect idx ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An element of an immutable array in the constructor, or at runtime with
   an index that has an effect.  ADMITTED (cheat).  In the constructor, as
   exprSimBuiltins' compile_len_ctor_code_case is for len: the lowering
   loads the array's length word with ILOAD, but immutables_rel relates
   that word to typed_val_to_w256 of the whole value, not to its length.
   At runtime, the source lets a call in the index write the immutable
   (write_place has no deploy check on an ImmutablePlace, and the type
   system has no immutable rule), so a[f()] with f reassigning a reads the
   new value, while the lowering reads the old one from code.  Vyper
   rejects that program (ImmutableViolation); a type-checker rule that
   immutables are written only in the constructor replaces that half. *)
Theorem compile_subscript_array_ctor_code_case:
  !nocalls ctx func cenv cx ann obj idx et bd ty st.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode /\
    (cenv.ce_is_ctor \/ expr_has_effect idx) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

Theorem compile_subscript_array_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt strip_tac >> Cases_on `expr_has_pop (Subscript ann obj idx)`
  >- metis_tac[compile_subscript_array_pop_case] >>
  Cases_on `?ty st l. vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
                      is_slot_addressed l /\ expr_has_effect idx`
  >- metis_tac[compile_subscript_array_storage_call_case] >>
  Cases_on `(cenv.ce_is_ctor \/ expr_has_effect idx) /\
            ?ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode`
  >- metis_tac[compile_subscript_array_ctor_code_case] >>
  irule compile_subscript_array_nopop_case >> metis_tac[]
QED

(* By place_type of the base: compile_subscript_map_case for a mapping,
   compile_subscript_mismatch_case for a dispatch type other than the
   base's, exprSimTuple's compile_subscript_tuple_sim for a tuple and
   compile_subscript_array_case for an array; no other base types. *)
Theorem compile_subscript_case:
  !nocalls ctx func cenv cx ann obj idx.
    expr_vv_case nocalls ctx func cenv cx obj /\
    expr_map_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt strip_tac >> Cases_on `place_type cenv obj`
  >- metis_tac[compile_subscript_map_case] >>
  rename1 `ValPT bt` >>
  Cases_on `bt <> expr_type obj`
  >- (irule compile_subscript_mismatch_case >> qexists_tac `bt` >> simp[]) >>
  gvs[] >> simp[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  drule_all subscript_base_array_or_tuple >> strip_tac
  >- (`expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)` by
        metis_tac[compile_subscript_array_case] >>
      qpat_x_assum `expr_vv_case _ _ _ _ _ (Subscript _ _ _)` mp_tac >>
      simp[expr_vv_case_def] >>
      disch_then (qspecl_then [`env`, `ty`, `es`] mp_tac) >> fs[]) >>
  `expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)` by
    (irule compile_subscript_tuple_sim >> gvs[]) >>
  qpat_x_assum `expr_vv_case _ _ _ _ _ (Subscript _ _ _)` mp_tac >>
  simp[expr_vv_case_def] >>
  disch_then (qspecl_then [`env`, `ty`, `es`] mp_tac) >> fs[]
QED

Theorem compile_subscript_sim:
  !cenv ann obj idx.
    expr_sim_below cenv (expr_size (Subscript ann obj idx)) ==>
    expr_vv_ok cenv (Subscript ann obj idx)
Proof
  rpt strip_tac >>
  `expr_ok cenv obj /\ expr_ok cenv idx` by
    (fs[expr_sim_below_def] >> rpt strip_tac >> first_x_assum irule >>
     simp[expr_size_def]) >>
  `expr_sim_below cenv (expr_size obj)` by
    (irule expr_sim_below_mono >>
     qexists_tac `expr_size (Subscript ann obj idx)` >> simp[expr_size_def]) >>
  gvs[expr_ok_case, expr_vv_ok_case] >> rpt gen_tac >>
  irule compile_subscript_case >> simp[expr_map_case_below]
QED

(* ===== Attributes ===== *)

Theorem compile_attribute_sim:
  !cenv ann obj fld.
    expr_sim_below cenv (expr_size (Attribute ann obj fld)) ==>
    expr_vv_ok cenv (Attribute ann obj fld)
Proof
  rpt strip_tac >>
  `expr_vv_ok cenv obj` by
    (fs[expr_sim_below_def, expr_ok_def] >> first_x_assum irule >>
     simp[expr_size_def]) >>
  rw[expr_vv_ok_def] >>
  drule_all compile_attribute_vv_sim >> simp[] >> metis_tac[]
QED

(* pop on a local: exprSimPop's compile_pop_name_sim.  Its target has no
   operand that can call, so expr_body_pre is expr_sim_pre here. *)
Theorem compile_pop_name_case:
  !nocalls ctx func cenv cx ann id.
    expr_sim_case nocalls ctx func cenv cx (Pop ann (NameTarget id)) /\
    expr_vv_case nocalls ctx func cenv cx (Pop ann (NameTarget id))
Proof
  rpt gen_tac >>
  `expr_vv_case nocalls ctx func cenv cx (Pop ann (NameTarget id))` by
    (rw[expr_vv_case_def] >> irule compile_pop_name_sim >>
     gvs[expr_sim_pre_body, int_calls_expr_def] >> metis_tac[]) >>
  simp[expr_sim_case_of_vv]
QED

(* pop on a module variable in storage or transient storage.  Cheated:
   the source reads the popped element from its slots (read_storage_slot),
   which raises a RuntimeError where the slots do not decode, while the
   lowering never reads it and hands out the slot; expr_sim_inv's storage
   clauses keep the slots decoding (as in exprSimLeaves's
   compile_toplevel_storage_undecodable_sim), but the proof also needs
   expr_sim_inv to give ce_var_type of the module variable's key, from
   which the lowering reads the element type.
   It also breaks expr_post's frame on the live locals (locals_kept): the
   lowering MSTOREs at the slot's fixed memory address, where an allocation
   holding a local can sit (allocation starts at 0). *)
Theorem compile_pop_storage_sim:
  !cenv ann src id ctx func cx env ty es ts d.
    expr_sim_below cenv (expr_size (Pop ann (TopLevelNameTarget (src,id)))) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  cheat
QED

(* pop on an immutable, in the constructor.  Cheated: the lowering pops at
   LocCode with MLOAD and MSTORE at the immutable's data offset, which is
   not where immutables_rel keeps it, and that offset can hold a live
   local's allocation (locals_kept). *)
Theorem compile_pop_immutable_sim:
  !cenv ann src id ctx func cx env ty es.
    expr_sim_below cenv (expr_size (Pop ann (TopLevelNameTarget (src,id)))) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann (TopLevelNameTarget (src,id))) es
Proof
  cheat
QED

(* pop on a nested target (x.a.pop(), x[i].pop(), self.s.a.pop()).
   Cheated: the lowering takes the array's pointer, location and type from
   compile_get_target_ptr, as an assignment does, but no lemma relates
   compile_get_target_ptr to the source's eval_target_place for a target
   deeper than a name.  The proof needs that target/place judgment: by
   induction on the target, with the hypothesis for the indices, the
   pointer is the place's in memory (with the array bounds abort of each
   index) or its slot in storage (with the mapping slot of each key); the
   subscript lemmas need the same judgment for their bases (this file's
   header).  Given it, a memory target pops as compile_pop_name_sim does at
   the array's pointer, inside the local's region (locals_kept), and a
   storage target as compile_pop_storage_sim does, which waits on the new
   storage statement of #713. *)
Theorem compile_pop_nested_sim:
  !cenv ann tgt.
    (!id. tgt <> NameTarget id) /\ (!nid. tgt <> TopLevelNameTarget nid) /\
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  cheat
QED

(* pop on a target other than a local: compile_pop_storage_sim,
   compile_pop_immutable_sim and compile_pop_nested_sim, by kind. *)
Theorem compile_pop_other_sim:
  !cenv ann tgt.
    (!id. tgt <> NameTarget id) /\ expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  rpt strip_tac >> Cases_on `?src id. tgt = TopLevelNameTarget (src,id)`
  >- (qpat_x_assum `?src id. _` strip_assume_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[expr_vv_ok_def] >> rpt strip_tac >>
      Cases_on `?ts d. get_module_code cx src = SOME ts /\
                       find_var_decl_by_name id ts = SOME d`
      >- (irule compile_pop_storage_sim >> metis_tac[]) >>
      irule compile_pop_immutable_sim >> rpt conj_tac
      >- (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >>
          metis_tac[]) >>
      metis_tac[]) >>
  irule compile_pop_nested_sim >> rw[] >> Cases_on `nid` >> gvs[]
QED

Theorem compile_pop_sim:
  !cenv ann tgt.
    expr_sim_below cenv (expr_size (Pop ann tgt)) ==>
    expr_vv_ok cenv (Pop ann tgt)
Proof
  rpt strip_tac >> Cases_on `?id. tgt = NameTarget id`
  >- (gvs[] >> rw[expr_vv_ok_def] >> irule compile_pop_name_sim >>
      metis_tac[]) >>
  irule compile_pop_other_sim >> gvs[]
QED
