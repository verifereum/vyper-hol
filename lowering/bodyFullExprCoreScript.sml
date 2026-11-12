(*
 * The expression core of the full body induction, as direct joint proofs
 * over bodySimFull's finite-horizon judgments: the leaf expressions (names,
 * top-level names, flag members, literals) and the binary operators, by
 * the operand families exprSimOperators' compile_bop_case splits on.
 *
 * TOP-LEVEL:
 *   name_expr_full_ok, toplevel_name_expr_full_ok, flag_member_expr_full_ok,
 *   literal_expr_full_ok -- the leaves bodyFullCases' body_expr_full_ok_leaf
 *     joins
 *   bop_word_sim_full, bop_bytes_eq_sim_full, bop_bytestring_eqne_sim_full,
 *   bop_rest_word_sim_full, bop_in_literal_word_sim_full -- the operator
 *     families bodyFullCases' bop_expr_full_ok and bop_in_expr_full_ok join
 *)
Theory bodyFullExprCore
Ancestors
  gasOutcomeFullCompose exprSimProps exprSimSource exprLoweringProps
  exprLowering vyperTyping vyperTypeSystem loweringPosts valueEncoding vyperValueOperation
  exprSimMemDefs bodyPtrDefs gasShadow fragGasOriginPtr ptrDiscipline loweringSlice
  bodyFullPreds bodySimFull bodySim exprSimHypsDefs compileEnv
  vyperContext vyperAST vyperInterpreter vyperState vyperValue venomState list

val _ = Parse.hide "body";

(* ===== Leaves ===== *)

Theorem name_expr_full_ok:
  !cx ann id. body_expr_full_ok cx (Name ann id)
Proof
  cheat
QED

Theorem toplevel_name_expr_full_ok:
  !cx ann nsid. body_expr_full_ok cx (TopLevelName ann nsid)
Proof
  cheat
QED

(* A flag member compiles to StackValue (Lit _) and emits no instruction
   (compile_expr_def), in runtime and constructor frames alike; the source
   side is exprSimFlagWord's. *)
Theorem flag_member_value_full[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_sim_full_def] >> PairCases_on `nsid` >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0,nsid1)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[gas_shadow_expr_def] >>
  qpat_x_assum `lower_value _ _ _ _ sa = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
       unwrap_value_def] >> strip_tac >> gvs[] >>
  irule gas_outcome_full_pure >>
  qexistsl_tac [`G0`, `es`,
    `INL (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid))`,
    `s0`, `tn0`] >>
  simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, expr_store_bound_def,
       expr_type_def, is_word_type_def, ptr_val_ok_def, op_taint_def,
       ghost_inv_at_def, ghost_kept_at_def] >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       is_word_type_def, typed_val_to_w256_word_value, word_value_def,
       val_to_w256_def, eval_operand_def, locals_kept_def] >>
  gvs[ghost_inv_at_def, vyperStorageFootprintTheory.storage_well_formed_on_def]
  >- (rpt gen_tac >>
      qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
      Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def])
  >- (gvs[op_taint_def] >> metis_tac[]) >>
  gvs[expr_type_def, is_word_type_def]
QED

Theorem flag_member_vv_full[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_vv_sim_full_def] >> PairCases_on `nsid` >>
  `gas_admissible (bind (eval_expr cx (FlagMember ann (nsid0,nsid1) mid))
     (read_result cx)) expr_res_ok es` by
    (irule exprSimStackTheory.eval_expr_force_admissible >> simp[] >>
     rpt gen_tac >> simp[Once evaluate_def, lookup_flag_mem_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]) >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0,nsid1)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[gas_shadow_expr_def] >>
  qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
  simp[compile_expr_def, comp_return_def] >> strip_tac >> gvs[] >>
  irule gas_outcome_full_pure >>
  qexistsl_tac [`G0`, `es`,
    `INL (Value (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid)))`,
    `s0`, `tn0`] >>
  conj_tac >- simp[Once evaluate_def, lookup_flag_mem_def, return_def] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, vv_store_bound_def, contextTheory.vv_location_def,
       expr_type_def, is_word_type_def, ptr_vv_ok_def, ptr_val_ok_def,
       read_result_def, return_def, op_taint_def,
       ghost_inv_at_def, ghost_kept_at_def] >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_storage_live_def,
       read_result_def, return_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, is_word_type_def, typed_val_to_w256_word_value,
       word_value_def, val_to_w256_def, eval_operand_def, locals_kept_def] >>
  gvs[ghost_inv_at_def, vyperStorageFootprintTheory.storage_well_formed_on_def]
  >- (rpt gen_tac >>
      qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
      Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def])
  >- (gvs[op_taint_def] >> metis_tac[]) >>
  gvs[expr_type_def, is_word_type_def] >>
  gvs[contextTheory.vv_location_def]
QED

Theorem flag_member_expr_full_ok:
  !cx ann nsid mid. body_expr_full_ok cx (FlagMember ann nsid mid)
Proof
  simp[body_expr_full_ok_def] >> rpt strip_tac >>
  metis_tac[flag_member_value_full, flag_member_vv_full]
QED

Theorem literal_expr_full_ok:
  !cx ann l. body_expr_full_ok cx (Literal ann l)
Proof
  cheat
QED

(* ===== Binary operators =====
   Each family is a binary operator lowered to a StackValue
   (exprSimOperators' compile_bop_stack), so only the value judgment is
   stated; the vv judgment follows from it. *)

(* Both operands of word_value_type. *)
Theorem bop_word_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

(* == and != on address and bytesN. *)
Theorem bop_bytes_eq_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\
    (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

(* == and != on bytestrings: keccak256 of each operand's bytes. *)
Theorem bop_bytestring_eqne_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

(* The rest, as exprSimBopRestWord's compile_bop_rest_word_case leaves it:
   in and not in on an array of words that is not a literal. *)
Theorem bop_rest_word_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
    ~((bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

(* in and not in on an array literal of words, which the lowering unrolls
   to a comparison with each element, so it takes the elements'
   judgments where e1 evaluates and is read. *)
Theorem bop_in_literal_word_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 a t n elems es.
    (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
    body_expr_full_ok cx e1 /\
    ((?s0 tv s1 s2 v s3. eval_expr cx e1 s0 = (INL tv, s1) /\
                         read_result cx tv s2 = (INL v, s3)) ==>
     builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
     body_exprs_full_ok cx elems) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
      es
Proof
  cheat
QED
