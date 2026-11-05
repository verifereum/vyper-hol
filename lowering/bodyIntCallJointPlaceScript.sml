(* A bounded place-interface probe, not a producer theorem. *)
Theory bodyIntCallJointPlace
Ancestors
  bodyIntCallJointInduction loweringPosts placeTypingProps
  vyperTypeExprResult exprSimHypsDefs gasOutcome gasContext

(* compile_subscript consumes vv_operand and vv_location of its base.
   This is the complete mapping-specific meaning of those two projections;
   it does not require a read_result of a HashMapRef. *)
Theorem joint_mapping_operand_boundary:
  (?w. eval_operand (vv_operand vv) s = SOME w /\
       place_ptr_rel ce cx s (HashMapRef tr slot kt vt)
         w (vv_location vv) (HashMapT kt vt)) <=>
  eval_operand (vv_operand vv) s = SOME slot /\
  vv_location vv = SOME (slot_loc tr)
Proof
  simp[place_ptr_rel_def]
QED

(* Checked separation from the ordinary typed-expression interface. *)
Theorem joint_mapping_base_not_expr_pre:
  type_place_expr env e = SOME (HashMapT kt vt) ==>
  ~expr_sim_pre ce cx env e es
Proof
  strip_tac >> simp[expr_sim_pre_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

(* PROPOSED Pp, ML quotation only. The domain extends the pure precondition
   by a place-typed branch; a separate admissibility relation is essential.
   Success is a disjoint mapping post or the ordinary vv_post, never a
   blanket place_ptr_rel (which excludes Value and ImmutablePlace).
   Compiler requested ty remains arbitrary. *)
val joint_place_candidate = ``\tops e.
  !ctx func ce cx env es ty sa sb vv s0 hs.
  cx_tops cx = tops /\
  expr_sim_inv ce cx env es /\
  (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
  byte_widths_expr e /\ alloc_limits_expr ce e /\
  int_calls_expr e = [] /\ call_evaluation_safe cx (int_calls_expr e) /\
  ~expr_has_evm_run e /\
  (!target. supported_expr_exists (expr_abi_decode_target_root target) e ==>
            occurs_abi_decode_target target (cx_tops cx)) /\
  (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
            is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) /\
  supported_place_expr tops e /\
  compile_expr ce ty e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e)
    (\r. expr_vv_res_ok r \/ ?tr slot kt vt. r = INL (HashMapRef tr slot kt vt)) es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\(off,len).
    (?aid b sz. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
      b <= off /\ off + len <= b + sz) \/
    (?name b sz. local_region ce es.scopes s0 name b sz /\
      b <= off /\ off + len <= b + sz)) hs ==>
  gas_outcome F tops (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee u. ?pv. res = INL pv /\
      ((?tr slot kt vt w.
          pv = HashMapRef tr slot kt vt /\
          type_place_expr env e = SOME (HashMapT kt vt) /\
          eval_operand (vv_operand vv) u = SOME w /\
          place_ptr_rel ce cx u pv w (vv_location vv) (HashMapT kt vt)) \/
       (~is_HashMapRef pv /\ vv_post ctx func ce cx e es sa sb s0 ee pv vv u)) /\
      stmt_state_rel ctx func ce cx ee u /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x u = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
      EVERY (\(off,len). mem_bytes_at off len u.vs_memory =
                            mem_bytes_at off len s0.vs_memory) hs /\
      (ce.ce_is_ctor ==> !name tv0 v off.
        FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
          NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
          name = SOME (tv0,v) ==>
        mem_bytes_at off (type_memory_size tv0) u.vs_memory =
        mem_bytes_at off (type_memory_size tv0) s0.vs_memory))
    (\res ee r. expr_exit res r)
``;

(* Outstanding, not asserted:
   (1) Pe e ==> Pp e for the same-expression fallback. Value/PlaceR use
       the ordinary vv_post disjunct. The mapping alternative is impossible
       for well_typed_expr by well_typed_expr_not_hashmap_place, but one still
       needs raw result typing to exclude HashMapRef from an ordinary run,
       and must reconcile the candidate's weaker admissibility premise
       with Pe's expr_vv_res_ok premise. That premise cannot be strengthened
       without a theorem that applies at every gas-observation sequence.
   (2) Mapping-base entry: outer Subscript pre implies this place branch's
       type_place_expr and non-typing clauses; invariant propagation for
       eval_expr on place-typed bases and key entry at its actual endpoint.
       eval_scc_type_sound_results_mutual exports the place-typing soundness
       arm (vyperTypeEvalSoundness); its many context premises must match
       expr_sim_inv. No ready expr_sim_pre transfer for HashMapRef exists.
   (3) The mapping disjunct alone is not a frame proof: common resources,
       source frame and actual endpoint PC still require the producer.
       target_post uses a different compiler result (operand,location,pt),
       not value_vv; its pointer relation can be reused, not its whole API.
   No shared local lemmas or definitions have been copied or changed. *)
