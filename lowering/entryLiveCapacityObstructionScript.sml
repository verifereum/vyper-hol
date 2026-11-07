Theory entryLiveCapacityObstruction
Ancestors exprLoweringProps compileEnv entryNaturalCapacityProbe words
  moduleLowering context loweringHalt finite_map compileVyper
  vyperInterpreter vyperScopePreservation vyperState

Theorem live_parameter_capacity_below_dimword:
  stmt_state_rel ctx func cenv ec es ss /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  sz < dimword (:256)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes ss /\ alloca_room ctx func ss` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  fs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  fs[alloca_room_def] >> decide_tac
QED

Theorem oversized_live_parameter_excludes_body_state:
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  dimword (:256) <= sz ==>
  ~stmt_state_rel ctx func cenv ec es ss
Proof
  strip_tac >> strip_tac >>
  drule_all live_parameter_capacity_below_dimword >> decide_tac
QED

Theorem oversized_singleton_registration_excludes_body_state:
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv0.ce_vars name = SOME (MemLoc off sz) /\
  compile_register_positional_args cenv0 [(name, prim, dyn, abi_sz, dinfo)]
    cd_off st = (cenv, sa) /\ dimword (:256) <= sz ==>
  ~stmt_state_rel ctx func cenv ec es ss
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[compile_register_positional_args_def, var_location_memory_size_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer sz st` >>
  Cases_on `compile_decode_args
    (cenv0 with ce_vars updated_by (\m. m |+ (name, PtrVar q.buf_operand sz)))
    [(name, prim, dyn, abi_sz, dinfo)] cd_off CALLDATALOAD (Lit 0w) 4 r` >>
  simp[] >> strip_tac >> gvs[] >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  irule oversized_live_parameter_excludes_body_state >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem natural_capacity_packaged_registration_impossible:
  package_external_fn tops use_trans nkey_map
    (mut, nr, rr, fname,
     [("a", ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))],
     dflts, ret, fbody) =
    (lbl, cenv0, pos_args, min_cds, pay, nr', key, ut, iv, fbody_out, rt) /\
  compile_register_positional_args cenv0 pos_args cd_off st = (cenv, sa) /\
  lookup_scopes "a" es.scopes = SOME entry ==>
  ~stmt_state_rel ctx func cenv ec es ss
Proof
  strip_tac >>
  `?off. FLOOKUP cenv0.ce_vars "a" = SOME (MemLoc off (dimword (:256)))` by
    (drule natural_capacity_package_location >> simp[]) >>
  `pos_args = build_positional_args cenv0
     [("a", ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))]` by
    gvs[package_external_fn_def] >>
  gvs[build_positional_args_def, build_positional_arg_def] >>
  irule oversized_singleton_registration_excludes_body_state >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

Theorem natural_capacity_call_value_scope:
  bind_arguments tenv
    [("a", ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1)))]
    [ArrayV (DynArrayV [])] = SOME env /\
  send_call_value mut ec
    (initial_state am [env] with
      <| outcomes := SOME outcomes; requests := [] |>) = (INL (), es0) ==>
  lookup_scopes "a" es0.scopes = SOME
    <| assignable := T;
       type := ArrayTV (BaseTV (UintT 256)) (Dynamic (2 ** 251 - 1));
       value := ArrayV (DynArrayV []); popped := [] |>
Proof
  simp[natural_capacity_binding] >> strip_tac >>
  `es0.scopes = [env]` by
    (qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
     rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
        assert_def, return_def, raise_def] >>
     gvs[AllCaseEqs(), initial_state_def] >>
     imp_res_tac transfer_value_scopes >> gvs[initial_state_def]) >>
  simp[lookup_scopes_def, FLOOKUP_UPDATE]
QED
