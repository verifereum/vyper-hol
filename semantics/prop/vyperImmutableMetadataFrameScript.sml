Theory vyperImmutableMetadataFrame
Ancestors
  list option pair finite_map alist vyperAST vyperState vyperInterpreter
  vyperCallOutcomeFrame vyperPlaceFrames vyperStatePreservation
  vyperImmutablesPreservation vyperCreate vyperCreateFrame

(* Resolved immutable paths retain their declared type across expression effects.
   Values may change; presence and declared type metadata may not. *)
Definition immutable_metadata_frame_def:
  immutable_metadata_frame (st:evaluation_state) (st':evaluation_state) <=>
    (!addr. IS_SOME (ALOOKUP st.immutables addr) <=>
            IS_SOME (ALOOKUP st'.immutables addr)) /\
    (!addr imms imms' src id.
       ALOOKUP st.immutables addr = SOME imms /\
       ALOOKUP st'.immutables addr = SOME imms' ==>
       OPTION_MAP FST (FLOOKUP (get_source_immutables src imms) id) =
       OPTION_MAP FST (FLOOKUP (get_source_immutables src imms') id))
End

Theorem immutable_metadata_frame_refl[simp]:
  immutable_metadata_frame st st
Proof
  rw[immutable_metadata_frame_def] >> gvs[]
QED

Theorem immutable_metadata_frame_eq:
  st'.immutables = st.immutables ==> immutable_metadata_frame st st'
Proof
  rw[immutable_metadata_frame_def] >> gvs[]
QED

Theorem immutable_metadata_frame_trans:
  immutable_metadata_frame s t /\ immutable_metadata_frame t u ==>
  immutable_metadata_frame s u
Proof
  rw[immutable_metadata_frame_def] >>
  `?middle. ALOOKUP t.immutables addr = SOME middle` by
    (Cases_on `ALOOKUP t.immutables addr` >> gvs[] >>
     qpat_x_assum `!addr. IS_SOME (ALOOKUP t.immutables _) <=> _`
       (qspec_then `addr` mp_tac) >> simp[]) >>
  metis_tac[]
QED

Theorem set_immutable_existing_metadata_frame:
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (tv,old) /\
  set_immutable cx src id tv v st = (res,st') ==>
  immutable_metadata_frame st st'
Proof
  rw[get_immutables_def, get_address_immutables_def, set_immutable_def,
     set_address_immutables_def, bind_def, lift_option_type_def,
     return_def, raise_def, vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  gvs[immutable_metadata_frame_def, get_source_immutables_def,
      set_source_immutables_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rw[ALOOKUP_ADELKEY] >> gvs[ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `src = src'` >> gvs[ALOOKUP_ADELKEY, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[FLOOKUP_UPDATE]
QED

Theorem write_place_immutable_metadata_frame:
  write_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  immutable_metadata_frame st st'
Proof
  simp[write_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  `s'' = st` by metis_tac[vyperStatePreservationTheory.get_immutables_state, SND] >>
  gvs[] >>
  PairCases_on `tva` >> gvs[] >>
  drule_all set_immutable_existing_metadata_frame >> simp[]
QED

Theorem write_place_metadata_frame:
  write_place cx p v st = (res,st') ==> immutable_metadata_frame st st'
Proof
  Cases_on `p`
  >- metis_tac[write_storage_place_immutables, immutable_metadata_frame_eq]
  >- metis_tac[write_memory_place_immutables, immutable_metadata_frame_eq] >>
  metis_tac[write_place_immutable_metadata_frame]
QED

Theorem append_place_metadata_frame:
  !cx p v st res st'.
    append_place cx p v st = (res,st') ==> immutable_metadata_frame st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule immutable_metadata_frame_eq >>
      metis_tac[vyperScopePreservationTheory.append_storage_place_scopes_immutables]) >>
  simp[append_place_def, bind_def, lift_sum_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, lift_sum_def, return_def, raise_def]) >>
  rpt strip_tac >>
  imp_res_tac place_type_value_state >> imp_res_tac read_place_state >>
  gvs[] >> metis_tac[write_place_metadata_frame, immutable_metadata_frame_refl]
QED

Theorem pop_place_metadata_frame:
  !cx p st res st'. pop_place cx p st = (res,st') ==>
    immutable_metadata_frame st st'
Proof
  rpt gen_tac >> Cases_on `p`
  >- (strip_tac >> irule immutable_metadata_frame_eq >>
      metis_tac[vyperScopePreservationTheory.pop_storage_place_scopes_immutables])
  >- (rename1 `MemoryPlace id path` >> strip_tac >>
      Cases_on `find_containing_scope id st.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def, immutable_metadata_frame_refl] >> PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac lift_sum_state >> imp_res_tac lift_option_type_state >>
      gvs[immutable_metadata_frame_refl] >>
      pairarg_tac >> gvs[bind_def, ignore_bind_def, set_scopes_def, return_def] >>
      irule immutable_metadata_frame_eq >> simp[]) >>
  simp[pop_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.sum_CASE_rator, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac get_immutables_state >> gvs[] >>
  PairCases_on `tva` >> gvs[] >>
  drule_all set_immutable_existing_metadata_frame >> simp[]
QED

Theorem metadata_frame_locals[local]:
  !s t. t.scopes = s.scopes /\ t.immutables = s.immutables ==>
    immutable_metadata_frame s t
Proof
  metis_tac[immutable_metadata_frame_eq]
QED

Theorem metadata_frame_state[local]:
  (!st res st'. f st = (res,st') ==> st' = st) ==>
  state_rel_frame immutable_metadata_frame f
Proof
  simp[state_rel_frame_result] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem metadata_frame_eq_op[local]:
  (!st res st'. f st = (res,st') ==> st'.immutables = st.immutables) ==>
  state_rel_frame immutable_metadata_frame f
Proof
  simp[state_rel_frame_result] >> metis_tac[immutable_metadata_frame_eq]
QED

Theorem metadata_frame_bind[local]:
  state_rel_frame immutable_metadata_frame f /\
  (!s v t. f s = (INL v,t) ==> state_rel_frame immutable_metadata_frame (g v)) ==>
  state_rel_frame immutable_metadata_frame (vyperState$bind f g)
Proof
  strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >>
  metis_tac[immutable_metadata_frame_trans]
QED

Theorem metadata_frame_reads[local]:
  state_rel_frame immutable_metadata_frame (read_result cx tv) /\
  state_rel_frame immutable_metadata_frame (select_result cx ann tv sb) /\
  state_rel_frame immutable_metadata_frame (conditional_result cx tv) /\
  state_rel_frame immutable_metadata_frame (lookup_global cx src id) /\
  state_rel_frame immutable_metadata_frame (lookup_flag_mem cx nsid mid) /\
  state_rel_frame immutable_metadata_frame (read_storage_slot cx b slot ty) /\
  state_rel_frame immutable_metadata_frame (result_array_length cx tv) /\
  state_rel_frame immutable_metadata_frame (lift_sum z) /\
  state_rel_frame immutable_metadata_frame (get_immutables cx src) /\
  state_rel_frame immutable_metadata_frame (get_place pv) /\
  state_rel_frame immutable_metadata_frame (read_place cx p) /\
  state_rel_frame immutable_metadata_frame (read_result cx pv) /\
  state_rel_frame immutable_metadata_frame (place_type_value cx p) /\
  state_rel_frame immutable_metadata_frame (extend_place cx pv sb) /\
  state_rel_frame immutable_metadata_frame (resolve_array_element cx b slot ty subs)
Proof
  rpt conj_tac >> irule metadata_frame_state >> rpt strip_tac >>
  FIRST [drule_all read_result_state, drule_all select_result_state,
    drule_all conditional_result_state,
    drule_all lookup_global_state, drule_all lookup_flag_mem_state,
    drule_all read_storage_slot_state,
    drule_all result_array_length_state, drule_all lift_sum_state,
    drule_all get_immutables_state, drule_all get_place_state,
    drule_all read_place_state, drule_all place_type_value_state,
    drule_all extend_place_state,
    drule_all resolve_array_element_state] >> simp[]
QED

Theorem metadata_frame_primitives[local]:
  state_rel_frame immutable_metadata_frame get_scopes /\
  state_rel_frame immutable_metadata_frame (set_scopes scs) /\
  state_rel_frame immutable_metadata_frame push_scope /\
  state_rel_frame immutable_metadata_frame pop_scope /\
  state_rel_frame immutable_metadata_frame (push_scope_with_var nm ty v) /\
  state_rel_frame immutable_metadata_frame (new_variable id ty v) /\
  state_rel_frame immutable_metadata_frame (append_logs ls) /\
  state_rel_frame immutable_metadata_frame (push_log lg) /\
  state_rel_frame immutable_metadata_frame get_pending_deletions /\
  state_rel_frame immutable_metadata_frame (update_pending_deletions fp) /\
  state_rel_frame immutable_metadata_frame (transfer_value sender target amount) /\
  state_rel_frame immutable_metadata_frame (acquire_nonreentrant_lock target lock view) /\
  state_rel_frame immutable_metadata_frame (release_nonreentrant_lock target lock) /\
  state_rel_frame immutable_metadata_frame (push_function fn sc cx) /\
  state_rel_frame immutable_metadata_frame (pop_function scs)
Proof
  rpt conj_tac >> irule metadata_frame_eq_op >>
  simp[get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
    push_scope_with_var_def, new_variable_def, append_logs_def, push_log_def,
    get_pending_deletions_def, update_pending_deletions_def,
    transfer_value_def, get_accounts_def, update_accounts_def,
    acquire_nonreentrant_lock_def, release_nonreentrant_lock_def,
    get_transient_storage_def, update_transient_def,
    push_function_def, pop_function_def, bind_def, ignore_bind_def,
    return_def, raise_def, lift_option_type_def, type_check_def,
    assert_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[set_scopes_def, return_def, raise_def, bind_def, ignore_bind_def,
        get_accounts_def, update_accounts_def, check_def, type_check_def,
        assert_def, get_transient_storage_def, update_transient_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
    gvs[set_scopes_def, return_def, raise_def, bind_def, ignore_bind_def,
        get_accounts_def, update_accounts_def, check_def, type_check_def,
        assert_def, get_transient_storage_def, update_transient_def])
QED

Theorem metadata_frame_storage[local]:
  state_rel_frame immutable_metadata_frame (write_storage_slot cx b slot ty v) /\
  state_rel_frame immutable_metadata_frame (set_global cx src nm v)
Proof
  rpt conj_tac >> irule metadata_frame_eq_op >>
  metis_tac[write_storage_slot_immutables, set_global_immutables]
QED

Theorem metadata_frame_write[local]:
  state_rel_frame immutable_metadata_frame (write_place cx p v)
Proof
  simp[state_rel_frame_result] >> metis_tac[write_place_metadata_frame]
QED

Theorem metadata_frame_mutations[local]:
  state_rel_frame immutable_metadata_frame (append_place cx p v) /\
  state_rel_frame immutable_metadata_frame (pop_place cx p)
Proof
  simp[state_rel_frame_result] >>
  metis_tac[append_place_metadata_frame, pop_place_metadata_frame]
QED

Theorem metadata_frame_try[local]:
  state_rel_frame immutable_metadata_frame f /\
  (!e. state_rel_frame immutable_metadata_frame (h e)) ==>
  state_rel_frame immutable_metadata_frame (try f h)
Proof
  simp[state_rel_frame_def, try_def] >> rpt strip_tac >>
  qpat_x_assum `!st. immutable_metadata_frame st (SND (f st))`
    (qspec_then `st` assume_tac) >>
  Cases_on `f st` >> Cases_on `q` >> gvs[] >>
  irule immutable_metadata_frame_trans >> first_assum (irule_at Any) >> simp[]
QED

Theorem metadata_frame_finally[local]:
  state_rel_frame immutable_metadata_frame f /\
  state_rel_frame immutable_metadata_frame g ==>
  state_rel_frame immutable_metadata_frame (finally f g)
Proof
  simp[state_rel_frame_def, finally_def] >> rpt strip_tac >>
  qpat_x_assum `!st. immutable_metadata_frame st (SND (f st))`
    (qspec_then `st` assume_tac) >>
  Cases_on `f st` >>
  qpat_x_assum `!st. immutable_metadata_frame st (SND (g st))`
    (qspec_then `r` assume_tac) >>
  Cases_on `g r` >> Cases_on `q'` >> Cases_on `q` >>
  gvs[ignore_bind_def, bind_def, return_def, raise_def] >>
  metis_tac[immutable_metadata_frame_trans]
QED

Theorem metadata_frame_handlers[local]:
  state_rel_frame immutable_metadata_frame (handle_loop_exception e) /\
  state_rel_frame immutable_metadata_frame (handle_function e)
Proof
  Cases_on `e` >> simp[handle_loop_exception_def, handle_function_def,
    state_rel_frame_def, return_def, raise_def]
QED

val METADATA_LOCALS = MATCH_MP state_rel_frame_locals_primitives metadata_frame_locals;
val METADATA_TAKE = MATCH_MP state_rel_frame_locals_take metadata_frame_locals;

(* Index only the exposed operation, never continuation arguments. *)
val metadata_frame_net =
  let
    val rules = [metadata_frame_bind, metadata_frame_try, metadata_frame_finally]
    val leaves = metadata_frame_reads :: metadata_frame_primitives ::
      metadata_frame_storage :: metadata_frame_mutations :: metadata_frame_write ::
      metadata_frame_handlers :: METADATA_LOCALS :: [METADATA_TAKE]
    val structural = List.foldl (fn (th,net) => Net.insert
      (snd (dest_imp (concl th)), MATCH_MP_TAC th >> conj_tac) net)
      Net.empty (map SPEC_ALL rules)
  in List.foldl (fn (th,net) =>
      Net.insert (concl th, MATCH_ACCEPT_TAC th) net) structural
      (List.concat (map (CONJUNCTS o SPEC_ALL) leaves)) end;

val metadata_head_conv =
  let
    val case_rules = List.concat (List.map
      (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
      (LET_THM :: COND_CLAUSES ::
       List.mapPartial (total TypeBasePure.case_def_of) (TypeBase.elts ())))
    val cases = List.foldl (fn (th,net) =>
      Net.insert (lhs (concl th), REWR_CONV th) net) Net.empty case_rules
    fun root tm = FIRST_CONV (Net.match tm cases) tm
    fun head tm = (BETA_CONV ORELSEC root ORELSEC
      REWR_CONV UNCURRY ORELSEC RATOR_CONV head) tm
  in head end;

fun METADATA_CASE_TAC (g as (old,_)) =
  let fun simplify (asl,w) =
    let val fresh = List.filter (fn a => not (is_forall a) andalso
      not (List.exists (aconv a) old)) asl
    in simp_tac bool_ss (map ASSUME fresh) (asl,w) end
  in (BasicProvers.PURE_TOP_CASE_TAC >> simplify) g end;

fun METADATA_IH_TAC (asl,w) =
  let
    fun terminal tm =
      if is_forall tm then terminal (snd (dest_forall tm))
      else if is_imp tm then terminal (snd (dest_imp tm)) else tm
    val candidates = List.mapPartial
      (total (fn a => PART_MATCH terminal (ASSUME a) w)) asl
    val _ = if null candidates then print ("NO CANDIDATES: " ^ term_to_string w ^ "\n") else ()
    val normalise = SIMP_RULE bool_ss
      [oneTheory.one, ignore_bind_def, FST, SND, pair_case_thm, UNCURRY]
    fun close candidate g =
      let
        val facts = List.concat (map (CONJUNCTS o normalise o ASSUME)
          (List.filter (not o is_forall) asl))
        fun discharge raw =
          let val th = normalise raw in
            if is_imp (snd (strip_forall (concl th))) then
              discharge (tryfind (MATCH_MP th) facts handle HOL_ERR _ =>
                let val guard = fst (dest_imp (snd (strip_forall (concl th)))) in
                  print ("FAILED GUARD: " ^ term_to_string guard ^ "\n");
                  (MATCH_MP th (REFL (lhs guard)) handle HOL_ERR _ =>
                   (MATCH_MP th (REFL (rhs guard)) handle HOL_ERR e =>
                    (print ("METADATA unmet guard: " ^ term_to_string guard ^ "\n");
                     raise HOL_ERR e))) end)
            else th
          end
      in (ACCEPT_TAC (discharge
        (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] (normalise candidate))) g
        handle e => (print ("CLOSE FAILURE: " ^ General.exnMessage e ^ "\n"); raise e)) end
  in (FIRST (map close candidates) (asl,w) handle HOL_ERR e =>
    (print ("METADATA candidates " ^ Int.toString (length candidates) ^
      " goal " ^ term_to_string w ^ "\n"); raise HOL_ERR e)) end;

val METADATA_FRAME_STEP = FIRST [
  first_assum ACCEPT_TAC,
  (fn g as (_,w) => FIRST (Net.match w metadata_frame_net) g),
  CONV_TAC (HO_REWR_CONV FORALL_PROD),
  CONV_TAC (RAND_CONV (CHANGED_CONV metadata_head_conv)),
  gen_tac, strip_tac, conj_tac,
  CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
  CONV_TAC (RAND_CONV ETA_CONV),
  CHANGED_TAC (fn (asl,w) => simp_tac bool_ss
    (pair_case_thm :: UNCURRY :: List.map ASSUME (List.filter is_eq asl)) (asl,w)),
  METADATA_CASE_TAC, METADATA_IH_TAC];
val METADATA_FRAME_TAC = rpt METADATA_FRAME_STEP;

Theorem metadata_frame_create[local]:
  state_rel_frame immutable_metadata_frame (eval_create cx kind salt rof tys vs blueprint_size)
Proof
  simp[state_rel_frame_result] >>
  metis_tac[eval_create_preserves_scopes_immutables, immutable_metadata_frame_eq]
QED

Theorem metadata_frame_call_helpers[local]:
  state_rel_frame immutable_metadata_frame (eval_send cx has_gas vs) /\
  state_rel_frame immutable_metadata_frame (eval_ext_call cx static skip_check sig opts vs) /\
  state_rel_frame immutable_metadata_frame (check_create_blueprint has_salt vs)
Proof
  simp[state_rel_frame_result] >> rpt conj_tac >> rpt strip_tac >>
  irule immutable_metadata_frame_eq >>
  metis_tac[eval_send_preserves_non_accounts, eval_ext_call_preserves_non_accounts,
            check_create_blueprint_result_state]
QED

Theorem metadata_frame_raw_call[local]:
  state_rel_frame immutable_metadata_frame (eval_raw_call cx flags target data amount)
Proof
  simp_tac bool_ss [eval_raw_call_def, LET_THM] >> METADATA_FRAME_TAC
QED

Theorem metadata_frame_at[local]:
  state_rel_frame immutable_metadata_frame f /\ f st = (res,st') ==>
  immutable_metadata_frame st st'
Proof
  simp[state_rel_frame_result]
QED

val METADATA_EVAL_STEP = FIRST [
  MATCH_ACCEPT_TAC metadata_frame_create,
  FIRST (map MATCH_ACCEPT_TAC (CONJUNCTS metadata_frame_call_helpers)),
  MATCH_ACCEPT_TAC metadata_frame_raw_call,
  CONV_TAC (RAND_CONV (REWR_CONV switch_BoolV_def)),
  CHANGED_TAC (CONV_TAC (RAND_CONV (DEPTH_CONV BETA_CONV))),
  METADATA_FRAME_STEP];

Theorem eval_metadata_frame_mutual:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx it st res st'. eval_iterator cx it st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> immutable_metadata_frame st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> immutable_metadata_frame st st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac >>
  qpat_assum `_ = (res,st')` (fn th =>
    let val result = #1 (pairSyntax.dest_pair (rhs (concl th))) in
      irule (INST_TYPE [alpha |-> type_of result] metadata_frame_at) >>
      exists_tac (rator (lhs (concl th))) >> exists_tac result
    end) >> asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [Once evaluate_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [GSYM state_rel_frame_result]) >>
  TRY (rename1 `CreateTarget kind has_salt rof` >>
       Cases_on `kind` >> Cases_on `has_salt` >>
       simp_tac bool_ss [COND_CLAUSES] >>
       RULE_ASSUM_TAC (SIMP_RULE bool_ss
         [create_kind_11, create_kind_distinct, COND_CLAUSES])) >>
  rpt METADATA_EVAL_STEP >> suspend "IntCallFrames"
QED

Resume eval_metadata_frame_mutual[IntCallFrames]:
  markerLib.RESUME_TAC >>
  (fn g as (asl,w) =>
    let
      fun terminal tm = if is_forall tm then terminal (snd (dest_forall tm))
        else if is_imp tm then terminal (snd (dest_imp tm)) else tm
      val candidates = List.mapPartial
        (total (fn a => PART_MATCH terminal (ASSUME a) w)) (List.filter is_forall asl)
    in FIRST (map (irule o SIMP_RULE bool_ss
      [oneTheory.one, FST, SND, pair_case_thm, UNCURRY, ignore_bind_def]) candidates) g end) >>
  (fn (asl,w) => simp_tac (bool_ss ++ SFY_ss ++ CONJ_ss)
    (oneTheory.one :: FST :: SND :: pair_case_thm :: UNCURRY ::
     List.map ASSUME (List.filter (not o is_forall) asl)) (asl,w)) >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (not o is_forall o concl)) >>
  fs[oneTheory.one, FST, SND, ignore_bind_def] >>
  rpt conj_tac >>
  simp[SF SFY_ss] >>
  FIRST [metis_tac[],
    rename1 `type_check (LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH es + LENGTH dflts) _ _ = _` >>
    qexistsl [`args`,`dflts`] >> simp[SF SFY_ss]]
QED

Finalise eval_metadata_frame_mutual

Theorem eval_expr_immutable_metadata_frame:
  eval_expr cx e st = (res,st') ==> immutable_metadata_frame st st'
Proof
  metis_tac[eval_metadata_frame_mutual]
QED

Theorem immutable_metadata_frame_lookup:
  immutable_metadata_frame st st' /\
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (tv,v) ==>
  ?imms' v'. get_immutables cx src st' = (INL imms',st') /\
    FLOOKUP imms' id = SOME (tv,v')
Proof
  rpt strip_tac >>
  qpat_x_assum `get_immutables _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [get_immutables_def, get_address_immutables_def, bind_def,
       lift_option_type_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  strip_tac >> fs[] >>
  `?imms'. ALOOKUP st'.immutables cx.txn.target = SOME imms'` by
    (fs[immutable_metadata_frame_def] >>
     qpat_x_assum `!addr. IS_SOME _ <=> _`
       (qspec_then `cx.txn.target` mp_tac) >>
     Cases_on `ALOOKUP st'.immutables cx.txn.target` >> simp[]) >>
  gvs[] >>
  fs[immutable_metadata_frame_def] >>
  first_x_assum (drule_all_then (qspecl_then [`src`,`id`] mp_tac)) >>
  simp[] >> strip_tac >> PairCases_on `z` >> gvs[] >> metis_tac[]
QED
