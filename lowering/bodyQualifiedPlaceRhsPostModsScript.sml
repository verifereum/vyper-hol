(* The saved RHS of a qualified Assign, at the target fragment's entry. *)
Theory bodyQualifiedPlaceRhsPostMods
Ancestors
  bodyAssignQualifiedStageJoinMods bodyWriteTargetStageMods bodyFullPredsMods
  exprSimMemDefs bodyPtrDefs loweringPosts contextRawReachable valueEncoding
  vyperStorageFootprint words bodyAssignLocalPlaceRoutesMods
  gasShadowCompileStmtBase compileEnv

(* These fields do not depend on which storage horizon is used to
   inspect the fixed endpoint. *)
val rhs_entry =
  ``expr_sim_inv_mods mods cenv cx env mid /\
    body_const_cells_agree_mods mods cx env mid /\
    value_runtime_typed env (expr_type e) v /\
    wb_frame cenv es mid sa s0 u /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 (Gu : string |-> (num # num)) tu /\
    ~u.vs_halted /\ u.vs_current_bb = sr.cs_current_bb /\
    u.vs_inst_idx = LENGTH sr.cs_current_insts /\
    local_ptrs_reserved cenv sr /\ return_buf_frame d cenv sr u /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t)``;

val rhs_at_horizon =
  ``\(H : (bool # bytes32 # type_value) list # num list).
    stmt_state_rel H ctx func cenv cx mid u /\
    immutable_frame_mods func cenv cx mid u /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid Gu tu u``;

(* The source default is the one for the destination's actual evaluated
   type. Only RHS code is skipped; its source read still returns v. *)
val rhs_empty =
  ``mid = (es with gas_obs := mid.gas_obs) /\
    (u : venom_state) = s0 /\ (Gu : string |-> (num # num)) = G0 /\ (tu : taint) = tn0 /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> v = default_value dtv)``;

(* An open value records the original successful read, not the read at
   the later target endpoint. Nothing here executes its delayed unwrap. *)
val rhs_raw =
  ``\vv (H : (bool # bytes32 # type_value) list # num list). (?gs pv.
      eval_expr cx e (es with gas_obs := gs) = (INL pv,mid) /\
      read_result cx pv mid = (INL v,mid) /\
      vv_post_mods H ctx func cenv cx e es sa sr s0 mid pv vv u /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) mid pv vv u /\
      ptr_vv_ok cx (post_value_type cenv e) pv vv mid Gu tu u /\
      (!v0. pv = Value v0 /\ ~is_word_type (post_value_type cenv e) /\
            ~is_bytestring_type (post_value_type cenv e) ==>
        vv_own cenv cx (post_value_type cenv e) sa sr mid pv vv u /\
        (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
               eval_operand (vv_operand vv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
      (!t op. vv = StackValue t op /\ ~is_word_type (post_value_type cenv e) ==>
        ptr_buf_ok cenv e op Gu u) /\
      (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv e p.ptr_operand Gu u)) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sr x)``;

val rhs_snapshot =
  ``\vv. ?tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type (lowered_value_type cenv e) then
       ?op. vv = StackValue (lowered_value_type cenv e) op /\
         eval_operand op u = SOME (typed_val_to_w256 tv v) /\
         ptr_val_ok cx (lowered_value_type cenv e) v op Gu tu u /\
         (!x. op = Var x ==> not_fresh_at sr x)
     else
       ?x aid b. vv = LocatedValue (lowered_value_type cenv e) (mk_ptr (Var x) LocMemory) /\
         FLOOKUP u.vs_allocas aid = SOME (b,type_memory_size tv) /\ aid < sr.cs_next_id /\
         lo <= b /\ b + type_memory_size tv < dimword (:256) /\
         b + type_memory_size tv <= u.vs_alloca_next /\
         (!n off len. local_region cenv mid.scopes u n off len ==>
            loweringStateRelDefs$regions_disjoint b (type_memory_size tv) off len) /\
         not_fresh_at sr x /\ lookup_var x u = SOME (n2w b) /\
         ptr_covers Gu tu x u (type_memory_size tv) /\
         (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==> val_in_memory tv v b mem))``;

Definition qualified_place_rhs_post_mods_def[nocompute]:
  qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
    es sa shadow_sa sr shadow_sr saved s0 G0 tn0 H v mid Gu tu u <=>
    assign_place_rhs_code_mods cenv bt e sa = (saved,sr) /\
    assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
      (gas_shadow_expr e) shadow_sa = (saved,shadow_sr) /\
    gas_shadow_state sr shadow_sr /\ ^rhs_entry /\ (^rhs_at_horizon H) /\
    (case saved of
       NONE => ^rhs_empty
     | SOME vv => if expr_can_mutate cenv (target_to_expr bt) then ^rhs_snapshot vv
                  else ^rhs_raw vv H)
End

val rhs_post =
  ``qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr saved s0 G0 tn0``;

Theorem qualified_place_rhs_entry_view_mods:
  qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post marks v mid Gu tu u ==>
  gas_shadow_state sr shadow_sr /\ ^rhs_entry /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ^rhs_at_horizon H)
Proof
  rewrite_tac[qualified_assign_rhs_reached_mods_def] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [qualified_place_rhs_post_mods_def])) >>
  simp[] >> rpt strip_tac
  >- (first_x_assum drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then
      (strip_assume_tac o BETA_RULE o REWRITE_RULE [qualified_place_rhs_post_mods_def]))) >>
  first_assum ACCEPT_TAC
QED

(* Match the payload at the selected horizon to the actual code choice. *)
Theorem qualified_place_rhs_saved_view_mods:
  ^rhs_post H v mid Gu tu u ==>
  (has_length_word (expr_type e) /\ is_empty_value_expr e /\
   saved = NONE /\ sr = sa /\ shadow_sr = shadow_sa /\ ^rhs_empty) \/
  (~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
   ?vv raw sm. saved = SOME vv /\ compile_expr cenv (expr_type e) e sa = (raw,sm) /\
     (if expr_can_mutate cenv (target_to_expr bt) then
        compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm = (vv,sr) /\
        ^rhs_snapshot vv
      else vv = raw /\ sr = sm /\ ^rhs_raw vv H))
Proof
  rewrite_tac[qualified_place_rhs_post_mods_def] >> strip_tac >>
  qpat_x_assum `assign_place_rhs_code_mods (gas_shadow_env _ _) _ _ _ = _`
    (mk_asm "shadow_rhs") >>
  drule_then strip_assume_tac qualified_assign_rhs_code_view_mods
  >- (asm_x "shadow_rhs" mp_tac >>
      gvs[assign_place_rhs_code_mods_def, gas_shadow_is_empty_value_expr, comp_return_def]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`vv`,`raw`,`sm`] >>
  Cases_on `expr_can_mutate cenv (target_to_expr bt)` >> gvs[] >>
  qexistsl_tac [`gs`,`pv`] >> simp[]
QED
