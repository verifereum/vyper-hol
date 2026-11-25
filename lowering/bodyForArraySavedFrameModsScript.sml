(* Frames for the saved Array iterator operand across one reached body. *)
Theory bodyForArraySavedFrameMods
Ancestors
  bodyForArrayHeaderMods bodyForArrayRouteMods bodyLoopImmutableFrame
  immutableIteratorPrefixWrite vyperLiveObservationFrame whitelistForIterMem
  immutableRegionFrameProps bodyFullForArray vyperBareGlobalName
  vyperTypeContract vyperTypeSystem vyperCallOutcomeFrame vyperContext
  vyperInterpreter vyperState finite_map alist list
  targetSubscriptMemory stateRelProj vyperTypeEnv logValueFramePtr
  abiCanonicalHeadSize exprBopSimProps fragGasOriginPtr abiDecodeStaticProps
  bodyFullShadowBodyInv stmtSimDefs vyperStorageTrace words arithmetic
  bodyFullPostsMods bodyInvSplit loweringPosts loweringStateRelDefs
  forNestedArrayCapture exprSimProps vyperTypeInvariants vyperPlaceStatePreservation
  exprSimCopy ptrDiscipline venomState

val _ = Parse.hide "body";

Theorem saved_iterator_writes[local]:
  MEM p (expr_places e) /\ iterator_unmodified (Array e) body ==>
  stmts_writes_ok (\w. ~place_contains w p) body
Proof
  simp[iterator_unmodified_def,EVERY_MEM]
QED

Theorem saved_iterator_place[local]:
  !e p. loop_iterator_place e = SOME p ==> MEM p (expr_places e)
Proof
  measureInduct_on `expr_size e` >>
  Cases_on `e` >> simp[loop_iterator_place_def,expr_places_def,AllCaseEqs(),MEM_MAP] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem saved_iterator_global_guard[local]:
  FST (place_access p []) = TopLevelNameTarget nid ==>
  callee_write_ok p = (\w. ~place_contains w p)
Proof
  simp[FUN_EQ_THM,callee_write_ok_def] >> strip_tac >> gen_tac >>
  Cases_on `FST (place_access w [])` >> simp[place_contains_def]
QED

val selected_prefix = ``\(st:evaluation_state).
  ?root. lookup_immutable cx0 st src name = SOME (rt,root) /\
         evaluate_subscripts rt root (MAP AttrSubscript attrs) = INL (ArrayV cap)``;
val prefix_frame = rhs (concl (DEPTH_CONV BETA_CONV
  ``\s t. ^selected_prefix s ==> ^selected_prefix t``));

Theorem saved_immutable_mutations[local]:
  place_access p [] = (TopLevelNameTarget (src,name),attrs) ==>
  !cx target s pl mid. cx.txn.target = cx0.txn.target /\
    callee_write_ok p target /\ eval_target_place cx target s = (INL pl,mid) /\
    ^selected_prefix s /\ ^selected_prefix mid ==>
    (!v. state_rel_frame ^prefix_frame (write_place cx pl v)) /\
    (!v. state_rel_frame ^prefix_frame (append_place cx pl v)) /\
    state_rel_frame ^prefix_frame (pop_place cx pl)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!s. lookup_immutable cx s src name = lookup_immutable cx0 s src name` by
    simp[lookup_immutable_def] >>
  drule_all immutable_guarded_prefix_mutation >> simp[]
QED

Theorem saved_immutable_body_prefix[local]:
  ALOOKUP cx0.sources cx0.txn.target = SOME mods /\
  loop_iterator_place e = SOME p /\
  place_access p [] = (TopLevelNameTarget (src,name),attrs) /\
  iterator_unmodified (Array e) body /\
  stmt_loop_calls_ok mods (For id et (Array e) bound body) /\
  ^selected_prefix st /\ eval_stmts cx0 body st = (res,fin) ==>
  ^selected_prefix fin
Proof
  BETA_TAC >> strip_tac >>
  `EVERY (callee_writes_ok mods p) (int_calls_stmts body)` by
    (qpat_x_assum `stmt_loop_calls_ok _ _` mp_tac >>
     simp[stmt_loop_calls_ok_def]) >>
  drule loop_calls_reachable_writes >> strip_tac >>
  `stmts_writes_ok (callee_write_ok p) body` by
    (`callee_write_ok p = (\w. ~place_contains w p)` by
       (irule saved_iterator_global_guard >> simp[]) >>
     simp[] >> irule saved_iterator_writes >>
     drule saved_iterator_place >> simp[] >> metis_tac[]) >>
  `state_rel_frame ^prefix_frame (eval_stmts cx0 body)` by
    (mp_tac (Q.INST [`P` |-> `reached`, `M` |-> `ALOOKUP mods`,
      `G` |-> `callee_write_ok p`, `addr` |-> `cx0.txn.target`,
      `deploy` |-> `cx0.in_deploy`,
      `obs` |-> `\imm. ^selected_prefix (st with immutables := imm)`]
      live_guarded_list_observation_frames) >>
     simp_tac (srw_ss()) [lookup_immutable_def] >>
     (impl_tac >-
       (conj_tac >- (rpt gen_tac >> first_assum MATCH_ACCEPT_TAC) >>
        mp_tac (Q.INST [`cx0` |-> `cx0`, `rt` |-> `rt`, `cap` |-> `cap`,
          `src` |-> `src`, `name` |-> `name`, `p` |-> `p`, `attrs` |-> `attrs`]
          (SPEC_ALL saved_immutable_mutations)) >> simp[lookup_immutable_def])) >>
     strip_tac >> first_x_assum irule >> simp[FUN_EQ_THM,get_module_code_def]) >>
  drule_all state_rel_frame_at >> simp[]
QED

Theorem saved_immutable_body_observation[local]:
  ALOOKUP cx0.sources cx0.txn.target = SOME mods /\
  loop_iterator_place e = SOME p /\
  place_access p [] = (TopLevelNameTarget (src,name),attrs) /\
  iterator_unmodified (Array e) body /\
  stmt_loop_calls_ok mods (For id et (Array e) bound body) /\
  lookup_immutable cx0 st src name = SOME (rt,old) /\
  evaluate_subscripts rt old (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
  evaluate_subscripts rt old (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
  eval_stmts cx0 body st = (res,fin) /\ ep.immutables = fin.immutables ==>
  ?root. lookup_immutable cx0 ep src name = SOME (rt,root) /\
         evaluate_subscripts rt root (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
         evaluate_subscripts rt root (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av)
Proof
  strip_tac >>
  `^selected_prefix st` by (BETA_TAC >> qexists `old` >> simp[]) >>
  drule_all saved_immutable_body_prefix >> BETA_TAC >> strip_tac >>
  qexists `root` >> conj_tac
  >- fs[lookup_immutable_def] >>
  `evaluate_subscripts rt old (MAP AttrSubscript attrs ++ tail) =
   evaluate_subscripts rt root (MAP AttrSubscript attrs ++ tail)` by
    (irule evaluate_subscripts_prefix_agree >> qexists `ArrayV cap` >> simp[]) >>
  fs[]
QED

(* The protective syntactic prefix has no dynamic indices.  Obtain the
   current value at that prefix below the pushed scope, then read the suffix. *)
Theorem saved_memory_body_observation[local]:
  place_access p [] = (NameTarget name,attrs) /\ MEM p (expr_places e) /\
  well_typed_expr benv e /\ expr_type e = ArrayT et bd /\
  name IN FDOM benv.var_types /\ type_stmts benv ret_ty body = SOME env' /\
  iterator_unmodified (Array e) body /\
  st.scopes = top::ee.scopes /\ name NOTIN FDOM top /\
  eval_stmts cx body st = (res,fin) /\ ep.scopes = TL fin.scopes /\
  lookup_scopes name ee.scopes = SOME old /\
  evaluate_subscripts old.type old.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) ==>
  ?entry. lookup_scopes name ep.scopes = SOME entry /\ entry.type = old.type /\
    evaluate_subscripts entry.type entry.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av)
Proof
  strip_tac >> drule_all saved_iterator_writes >> strip_tac >>
  `st.scopes <> []` by simp[] >>
  drule_all typed_stmts_place_frame >> strip_tac >>
  qabbrev_tac `project = \e. (e.type,evaluate_subscripts e.type e.value (MAP AttrSubscript attrs))` >>
  qspecl_then [`fin.scopes`,`top`,`ee.scopes`,`name`,`project`,`old`]
    mp_tac scope_projection_lookup_below >>
  (impl_tac >- fs[Abbr `project`]) >>
  simp[Abbr `project`] >> strip_tac >>
  rename1 `lookup_scopes name rest = SOME current` >>
  qexists `current` >> fs[] >>
  qpat_assum `current.type = old.type` (once_rewrite_tac o single) >>
  `evaluate_subscripts old.type old.value (MAP AttrSubscript attrs ++ tail) =
   evaluate_subscripts old.type current.value (MAP AttrSubscript attrs ++ tail)` by
    (irule evaluate_subscripts_prefix_agree >>
     drule evaluate_subscripts_append_prefix >> strip_tac >> qexists `x` >>
     qpat_x_assum `current.type = old.type` (RULE_ASSUM_TAC o ONCE_REWRITE_RULE o single) >>
     simp[]) >>
  fs[]
QED

Theorem saved_memory_current_bytes[local]:
  FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\
  lookup_var root t = SOME rw /\ bw = rw + n2w delta /\
  w2n rw + delta < dimword (:256) /\
  ghost_inv_at_mods D lo d c cx ep G tn t /\
  EVERY scope_well_typed ep.scopes /\ lookup_scopes name ep.scopes = SOME entry /\
  mem_path_offset entry.type path = SOME (delta,rt) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) ==>
  read_result cx (PlaceR (MemoryPlace name path)) ep = (INL (ArrayV av),ep) /\
  ptr_covers G tn root t sz /\
  !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory rt (ArrayV av) (w2n bw) mem
Proof
  strip_tac >> conj_tac
  >- simp[read_result_def,read_place_def,read_memory_path_def,get_scopes_def,
          bind_def,lift_option_type_def,lift_sum_def,return_def] >>
  drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[] >>
  gen_tac >> disch_tac >>
  `val_in_memory entry.type entry.value (w2n rw) mem` by
    first_x_assum (drule_all_then ACCEPT_TAC) >>
  drule_all mem_path_offset_current_value >>
  simp[abiDecodeStaticPropsTheory.w2n_add_n2w_lt]
QED

Theorem saved_owned_current_bytes[local]:
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ep tn t /\
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ aid < saExpr.cs_next_id /\
  (!nm lb lsz. local_region c em.scopes u nm lb lsz ==>
               b + sz <= lb \/ lb + lsz <= b) /\
  b <= w2n bw /\ w2n bw + val_footprint rt (ArrayV av) <= b + sz /\
  val_wf rt (ArrayV av) /\
  (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
         val_in_memory rt (ArrayV av) (w2n bw) mem) ==>
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  (!nm lb lsz. local_region c ep.scopes t nm lb lsz ==>
               b + sz <= lb \/ lb + lsz <= b) /\
  !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
         val_in_memory rt (ArrayV av) (w2n bw) mem
Proof
  simp[for_array_capture_frame_mods_def] >> strip_tac >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _`
    (drule_all_then strip_assume_tac o REWRITE_RULE [alloca_frame_def]) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  ho_match_mp_tac robust_val_in_memory_footprint_frame >>
  qexistsl [`tu.t_mem`,`u.vs_memory`] >>
  simp[] >> conj_tac
  >- (`w2n bw - b + val_footprint rt (ArrayV av) <= sz` by decide_tac >>
      `b + (w2n bw - b) = w2n bw` by decide_tac >>
      metis_tac[Q.SPEC `b` mem_bytes_at_window]) >>
  rpt strip_tac >>
  `b <= i /\ i < b + sz` by decide_tac >>
  first_x_assum (drule_all_then ACCEPT_TAC)
QED

Theorem saved_storage_body_observation[local]:
  eval_stmts cx body st = (res,fin) /\ st.storage_trace = ee.storage_trace /\
  ep.storage_trace = fin.storage_trace /\ MEM root ee.storage_trace ==>
  MEM root ep.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (eval_stmts cx body)` by simp[evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> strip_tac >> fs[MEM_APPEND]
QED

(* Rebuild the qualified view from the current root and selected path.  The
   root can have changed outside that path. *)
Theorem saved_immutable_current_holds[local]:
  ALOOKUP c.ce_modules src = SOME tops /\
  FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  ALOOKUP ep.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) name = SOME (itv,root) /\
  off + type_memory_size itv < dimword (:256) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  mem_path_offset itv path = SOME (delta,ArrayTV tv bd) /\
  evaluate_subscripts itv root path = INL (ArrayV av) /\
  value_has_type itv root /\ well_formed_type_value itv ==>
  immutable_holds_mods c cx (ArrayT et bd) (Value (ArrayV av)) (n2w (off+delta)) ep t
Proof
  strip_tac >> rewrite_tac[immutable_holds_mods_def] >> qexistsl [`src`,`tops`] >>
  simp[immutable_holds_def] >> qexistsl [`name`,`off`,`itv`,`root`,`delta`] >>
  simp[read_result_def,return_def,sub_layout_def] >>
  drule mem_path_offset_sound >> strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule mem_path_offset_current_value >>
      qpat_assum `mem_path_offset _ _ = _` (irule_at Any) >> qexists `root` >> simp[]) >>
  irule evaluate_subscripts_type >>
  qpat_assum `evaluate_subscripts _ _ _ = _` (irule_at Any) >> simp[]
QED

Theorem saved_immutable_ctor_bytes[local]:
  contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env ep /\
  dead_lo_ok_mods H D lo c cx /\ ghost_inv_at_mods D lo d c cx ep G tn t /\
  immutables_rel_mods c cx.txn.target c.ce_is_ctor ep t /\
  ALOOKUP c.ce_modules src = SOME tops /\
  FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  ALOOKUP ep.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) name = SOME (itv,root) /\
  mem_path_offset itv path = SOME (delta,rt) /\
  evaluate_subscripts itv root path = INL v /\
  off + type_memory_size itv < dimword (:256) /\
  value_has_type itv root /\ well_formed_type_value itv /\ c.ce_is_ctor ==>
  w2n (n2w (off+delta):bytes32) + type_memory_size rt <= lo /\
  !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory rt v (w2n (n2w (off+delta):bytes32)) mem
Proof
  strip_tac >>
  `off + type_memory_size itv <= lo /\
   (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory itv root off mem)` by
    (irule qualified_immutable_ctor_frame_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ _` (irule_at Any) >>
     qpat_assum `dead_lo_ok_mods _ _ _ _ _` (irule_at Any) >>
     qpat_assum `FLOOKUP (get_source_immutables _ _) _ = _` (irule_at Any) >>
     qpat_assum `ALOOKUP c.ce_modules _ = _` (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `off + delta < dimword (:256) /\ off + delta + type_memory_size rt <= lo` by decide_tac >>
  simp[w2n_n2w,LESS_MOD] >> rpt strip_tac >>
  `val_in_memory itv root off mem` by simp[] >>
  drule_all mem_path_offset_current_value >> simp[ADD_COMM]
QED

Theorem saved_immutable_runtime_bytes[local]:
  immutables_rel c cx.txn.target src F ep t /\
  FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  ALOOKUP ep.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) name = SOME (itv,root) /\
  mem_path_offset itv path = SOME (delta,rt) /\
  evaluate_subscripts itv root path = INL v /\
  off + type_memory_size itv < dimword (:256) /\
  value_has_type itv root /\ well_formed_type_value itv ==>
  w2n (n2w (off+delta):bytes32) + type_memory_size rt <= LENGTH t.vs_data_section /\
  val_in_memory rt v (w2n (n2w (off+delta):bytes32)) t.vs_data_section
Proof
  strip_tac >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` (mp_tac o REWRITE_RULE [immutables_rel_def]) >>
  simp[] >> disch_then (qspecl_then [`name`,`itv`,`root`,`off`] mp_tac) >> simp[] >> strip_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `off + delta < dimword (:256) /\ off + delta + type_memory_size rt <= LENGTH t.vs_data_section`
    by decide_tac >>
  simp[w2n_n2w,LESS_MOD] >>
  drule_all mem_path_offset_current_value >> simp[ADD_COMM]
QED

Theorem saved_immutable_current_bytes[local]:
  contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env ep /\
  dead_lo_ok_mods H D lo c cx /\ ghost_inv_at_mods D lo d c cx ep G tn t /\
  immutable_frame_mods func c cx ep t /\
  ALOOKUP c.ce_modules src = SOME tops /\
  FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  lookup_immutable cx ep src name = SOME (itv,root) /\
  mem_path_offset itv path = SOME (delta,ArrayTV tv bd) /\
  evaluate_subscripts itv root path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) ==>
  read_result cx (PlaceR (ImmutablePlace src name path)) ep = (INL (ArrayV av),ep) /\
  immutable_holds_mods c cx (ArrayT et bd) (Value (ArrayV av)) (n2w (off+delta)) ep t /\
  (c.ce_is_ctor ==>
     w2n (n2w (off+delta):bytes32) + type_memory_size (ArrayTV tv bd) <= lo /\
     !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n (n2w (off+delta):bytes32)) mem) /\
  (~c.ce_is_ctor ==>
     w2n (n2w (off+delta):bytes32) + type_memory_size (ArrayTV tv bd) <= LENGTH t.vs_data_section /\
     val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n (n2w (off+delta):bytes32)) t.vs_data_section)
Proof
  strip_tac >> conj_tac >- (simp[read_result_immutable_place] >> qexistsl [`itv`,`root`] >> simp[]) >>
  `state_well_typed ep` by fs[exprSimHypsDefsTheory.expr_sim_inv_mods_def] >>
  Cases_on `ALOOKUP ep.immutables cx.txn.target` >> fs[lookup_immutable_def] >>
  drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
  drule_all imms_well_typed_get_source_immutables >> strip_tac >>
  conj_tac >- (drule_all saved_immutable_current_holds >> simp[]) >>
  fs[immutable_frame_mods_def] >> Cases_on `c.ce_is_ctor` >> simp[]
  >- (drule_all saved_immutable_ctor_bytes >> simp[]) >>
  `immutables_rel c cx.txn.target src F ep t` by fs[immutables_rel_mods_def] >>
  drule_all saved_immutable_runtime_bytes >> simp[]
QED

(* Restrict the register frame to the saved operand, rather than the
   younger item pointer or a cursor that might be overwritten next round. *)
Theorem saved_base_operand[local]:
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ep tn t /\
  copy_old_operand saLen op /\ (!lbl. op <> Label lbl) /\
  eval_operand op u = SOME bw /\
  (!x. not_fresh_at saLen x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  eval_operand op t = SOME bw /\ op_prov G op = op_prov G0 op /\
  op_taint tn op = op_taint tn0 op
Proof
  strip_tac >> qpat_x_assum `for_array_capture_frame_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [for_array_capture_frame_mods_def]) >>
  conj_tac
  >- (irule eval_operand_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`saLen`,`u`] >> fs[copy_old_operand_def]) >>
  Cases_on `op` >> fs[copy_old_operand_def,op_prov_def,op_taint_def]
QED

(* All four routes use the same replay and popped endpoint.  The local and
   immutable cases project their selected paths, the owned case projects
   the older allocation, and the storage case retains only its observation. *)
Theorem for_array_saved_after_body_mods:
  push_scope_with_var id dtv v ee = (INL (),eb) /\
  st = eb with gas_obs := obs /\ eval_stmts cx body st = (res,fin) /\
  ep = fin with scopes := TL fin.scopes /\
  for_array_capture_frame_mods c (em,saExpr,saLen,u,tu) ep tn t /\
  copy_old_operand saLen base_op /\ (!lbl. base_op <> Label lbl) /\
  eval_operand base_op u = SOME bw /\
  (!x. not_fresh_at saLen x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  eval_operand base_op t = SOME bw /\ op_prov G base_op = op_prov G0 base_op /\
  op_taint tn base_op = op_taint tn0 base_op /\
  (!root. MEM root ee.storage_trace ==> MEM root ep.storage_trace) /\
  (!aid b sz rt av.
     FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ aid < saExpr.cs_next_id /\
     (!nm lb lsz. local_region c em.scopes u nm lb lsz ==> b+sz <= lb \/ lb+lsz <= b) /\
     b <= w2n bw /\ w2n bw + val_footprint rt (ArrayV av) <= b+sz /\ val_wf rt (ArrayV av) /\
     (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
            val_in_memory rt (ArrayV av) (w2n bw) mem) ==>
     FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
     (!nm lb lsz. local_region c ep.scopes t nm lb lsz ==> b+sz <= lb \/ lb+lsz <= b) /\
     !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           val_in_memory rt (ArrayV av) (w2n bw) mem) /\
  (!name attrs p tail old root sz rw delta av e et bd benv env' ret_ty mods env D lo d.
     name <> id /\ place_access p [] = (NameTarget name,attrs) /\ MEM p (expr_places e) /\
     well_typed_expr benv e /\ expr_type e = ArrayT et bd /\ name IN FDOM benv.var_types /\
     type_stmts benv ret_ty body = SOME env' /\ iterator_unmodified (Array e) body /\
     lookup_scopes name ee.scopes = SOME old /\
     evaluate_subscripts old.type old.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
     expr_sim_inv_mods mods c cx env ep /\ ghost_inv_at_mods D lo d c cx ep G tn t /\
     FLOOKUP c.ce_vars name = SOME (PtrVar (Var root) sz) /\
     not_fresh_at saLen root /\ lookup_var root u = SOME rw /\ bw = rw + n2w delta /\
     w2n rw + delta < dimword (:256) /\
     mem_path_offset old.type (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv bd) ==>
     read_result cx (PlaceR (MemoryPlace name (MAP AttrSubscript attrs ++ tail))) ep = (INL (ArrayV av),ep) /\
     lookup_var root t = SOME rw /\ ptr_covers G tn root t sz /\
     (?entry. lookup_scopes name ep.scopes = SOME entry /\ entry.type = old.type /\
        evaluate_subscripts entry.type entry.value (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av)) /\
     !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
           val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem) /\
  (!src name tops off delta itv old attrs p tail cap av mods exps ctx func env H D lo d e et bd bound fty.
     ALOOKUP cx.sources cx.txn.target = SOME mods /\ loop_iterator_place e = SOME p /\
     place_access p [] = (TopLevelNameTarget (src,name),attrs) /\ iterator_unmodified (Array e) body /\
     stmt_loop_calls_ok mods (For id fty (Array e) bound body) /\
     lookup_immutable cx ee src name = SOME (itv,old) /\
     evaluate_subscripts itv old (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
     evaluate_subscripts itv old (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av) /\
     contract_inv mods exps ctx c cx /\ expr_sim_inv_mods mods c cx env ep /\
     dead_lo_ok_mods H D lo c cx /\ ghost_inv_at_mods D lo d c cx ep G tn t /\
     immutable_frame_mods func c cx ep t /\ ALOOKUP c.ce_modules src = SOME tops /\
     FLOOKUP c.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
     off + type_memory_size itv < dimword (:256) /\ bw = n2w (off+delta) /\
     mem_path_offset itv (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv bd) /\
     evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) ==>
     (?now. lookup_immutable cx ep src name = SOME (itv,now) /\
        evaluate_subscripts itv now (MAP AttrSubscript attrs) = INL (ArrayV cap) /\
        evaluate_subscripts itv now (MAP AttrSubscript attrs ++ tail) = INL (ArrayV av)) /\
     read_result cx (PlaceR (ImmutablePlace src name (MAP AttrSubscript attrs ++ tail))) ep = (INL (ArrayV av),ep) /\
     immutable_holds_mods c cx (ArrayT et bd) (Value (ArrayV av)) bw ep t /\
     (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo /\
        !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) mem) /\
     (~c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= LENGTH t.vs_data_section /\
        val_in_memory (ArrayTV tv bd) (ArrayV av) (w2n bw) t.vs_data_section))
Proof
  strip_tac >> drule_all saved_base_operand >> strip_tac >>
  `st.storage_trace = ee.storage_trace /\ st.immutables = ee.immutables /\
   ?top. st.scopes = top::ee.scopes /\ !name. name <> id ==> name NOTIN FDOM top` by
    (qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
     simp[push_scope_with_var_def,return_def] >> disch_then (SUBST_ALL_TAC o SYM) >> simp[]) >>
  `ep.storage_trace = fin.storage_trace /\ ep.immutables = fin.immutables /\
   ep.scopes = TL fin.scopes` by simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (gen_tac >> strip_tac >> irule saved_storage_body_observation >>
    qpat_assum `eval_stmts _ _ _ = _` (irule_at Any) >> qexists `ee` >> simp[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> drule_all_then strip_assume_tac saved_owned_current_bytes >>
               rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "memory" >>
  suspend "immutable"
QED

Resume for_array_saved_after_body_mods[memory]:
  rpt gen_tac >> strip_tac >>
  `name NOTIN FDOM top` by simp[] >>
  drule_all saved_memory_body_observation >> strip_tac >>
  `lookup_var root t = SOME rw /\ EVERY scope_well_typed ep.scopes` by
    fs[for_array_capture_frame_mods_def,exprSimHypsDefsTheory.expr_sim_inv_mods_def,state_well_typed_def] >>
  `mem_path_offset entry.type (MAP AttrSubscript attrs ++ tail) = SOME (delta,ArrayTV tv bd)` by fs[] >>
  drule_all saved_memory_current_bytes >> strip_tac >> simp[] >>
  qexists `entry` >> simp[]
QED

Resume for_array_saved_after_body_mods[immutable]:
  rpt gen_tac >> strip_tac >>
  `lookup_immutable cx st src name = SOME (itv,old)` by fs[lookup_immutable_def] >>
  drule_all saved_immutable_body_observation >> strip_tac >>
  conj_tac >- (qexists `root` >> simp[]) >>
  drule_all saved_immutable_current_bytes >> simp[]
QED

Finalise for_array_saved_after_body_mods
