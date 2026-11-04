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
 *)

Theory exprSimPopNested
Ancestors
  list fragExec exprSim exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr

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
  !hdr tr esz sa r sb.
    compile_dynarray_pop hdr 1 esz
      (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = (r,sb) ==>
    ?x0 x1 x2 x3 x4 x5 x6.
      ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\
      EVERY (\x. ~not_fresh_at sa x) [x0;x1;x2;x3;x4;x5;x6] /\
      r = Var x6 /\
      sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
      sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
      sb.cs_current_insts = sa.cs_current_insts ++
        nested_pop_suffix hdr tr sa.cs_next_id esz x0 x1 x2 x3 x4 x5 x6
Proof
  simp[compile_dynarray_pop_def, emit_op_def, emit_void_def, fresh_id_def,
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
Theorem pop_nested_storage_pure_sim:
  !ctx func cenv cx env ann bt ty es src id ts d.
    pop_target_frag ctx func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = SOME d /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* RESIDUAL (effectful storage indices): an index that pops or calls can
   shrink an array the target already points into, so the header the pop
   reads can be dead.  Source and Venom read the same raw slot, but
   stmt_state_rel relates only live storage.  Needs raw agreement on slots
   made dead by a pop; body_augassign_place_effectful_storage and
   targetPlaceSimCases' target_subscript_case have the same exposure. *)
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

(* An immutable or constant root at runtime: bare_global_assignable is
   empty outside the constructor (bare_global_assignable_complete), so the
   root names a bare global, which type_place_target rejects, and the pop
   does not type. *)
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
   the constructor.  Python's checker accepts it for a complex immutable
   (local.py skips the modification count when var_info is None), and the
   lowering pops at the immutable's deploy-time memory.  Needs the
   constructor immutable invariant relating that memory to the source's
   immutables. *)
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

(* RESIDUAL (nested length words): pop on an array inside a memory local.
   The pop writes the array's length word inside the local's region, which
   locals_kept does not exempt for a nested array, only for a root one.
   Once it does (local_path_at_dynarray_len_at), the run is
   compile_pop_name_sim's at the target's pointer. *)
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
