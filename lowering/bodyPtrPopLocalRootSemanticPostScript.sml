Theory bodyPtrPopLocalRootSemanticPost
Ancestors
  bodyPtrPopLocalRootSource exprSimPop exprSimProps loweringPosts
  compileEnv context venomState words finite_map list
  exprSimMemorySource exprSimWordArgs stmtFragPtr bodyPtrDefs

Theorem pop_local_vv_post_cursor:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_rel func cenv es.scopes s /\
  popped_keys_indexed es.scopes /\
  find_containing_scope id es.scopes = SOME (pre, envs, entry, rest) /\
  cenv.ce_var_type id = SOME (ArrayT ann (Dynamic n)) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\ local_backed func p s (w2n w) sz /\
  w2n w + sz <= s.vs_alloca_next /\
  entry.type = ArrayTV etv (Dynamic n) /\ vs <> [] /\
  LENGTH vs <= n /\ elems_val_wf vs etv /\
  32 + n * type_memory_size etv <= sz /\
  elems_in_memory vs (w2n w + 32) etv s.vs_memory /\
  t.vs_memory = (mstore (w2n w) (n2w (LENGTH vs) - 1w) s).vs_memory /\
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
               vs_inst_idx := t.vs_inst_idx|> /\
  (!q n' sq. FLOOKUP cenv.ce_vars n' = SOME (PtrVar (Var q) sq) ==>
             lookup_var q t = lookup_var q s) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!q. cenv.ce_imm_alloca = SOME (Var q) ==> lookup_var q t = lookup_var q s) /\
  lookup_var out t =
    SOME (w + 32w + (n2w (LENGTH vs) - 1w) * n2w (type_memory_size etv)) /\
  EVERY (value_has_type etv) vs /\
  evaluate_type (get_tenv cx) ann = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT ann (Dynamic n)) =
    SOME (ArrayTV etv (Dynamic n)) ==>
  vv_post ctx func cenv cx (Pop ann (NameTarget id)) es sa sb s
    (es with scopes := pre ++ envs |+ (id, pop_name_entry entry vs) :: rest)
    (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))]))
    (LocatedValue ann (mk_ptr (Var out) LocMemory)) t
Proof
  strip_tac >>
  `t = (t with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx := t.vs_inst_idx`
    by simp[] >>
  pop_assum SUBST1_TAC >> irule pop_vv_post >>
  fs[lookup_var_def]
  >~ [`t with vs_inst_idx := _ = _`]
  >- (qpat_x_assum `t = s with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|>`
        SUBST1_TAC >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem pop_local_read_gas_obs:
  read_result cx tv (ee with gas_obs := gs) = (INL v, ee with gas_obs := gs) <=>
  read_result cx tv ee = (INL v, ee)
Proof
  eq_tac >> strip_tac
  >- (drule read_result_gas_obs >>
      disch_then (qspec_then `ee.gas_obs` mp_tac) >> simp[]) >>
  drule read_result_gas_obs >> simp[]
QED

Theorem pop_local_locals_kept_gas_obs:
  locals_kept cenv es (ee with gas_obs := gs) s0 t <=> locals_kept cenv es ee s0 t
Proof
  simp[locals_kept_def, popped_kept_def]
QED

Theorem pop_local_memory_post_gas_obs:
  vv_post ctx func cenv cx (Pop ann bt) es sa sb s0 ee tv
    (LocatedValue ann (mk_ptr op LocMemory)) t ==>
  vv_post ctx func cenv cx (Pop ann bt) es sa sb s0 (ee with gas_obs := gs) tv
    (LocatedValue ann (mk_ptr op LocMemory)) t
Proof
  simp[vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def,
       pop_local_read_gas_obs, pop_local_locals_kept_gas_obs] >> metis_tac[]
QED

Theorem pop_local_memory_ptr_gas_obs:
  ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr op LocMemory))
    (ee with gas_obs := gs) G tn t <=>
  ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr op LocMemory)) ee G tn t
Proof
  simp[ptr_vv_ok_def, mk_ptr_def, pop_local_read_gas_obs]
QED
