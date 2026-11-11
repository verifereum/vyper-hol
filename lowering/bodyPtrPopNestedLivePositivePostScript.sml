Theory bodyPtrPopNestedLivePositivePost
Ancestors
  bodyPtrPopNestedLiveEndpoint bodyPtrPopNestedLiveValuePost bodyPtrPopNestedLiveResult
  appendStorageGhostPtr exprPtrUnwrapPostFrames exprSimProps
  bodyPtrDefs compileEnv venomState finite_map

(* All clauses refer to the counted suffix's own endpoint. *)
Theorem pop_positive_framed_posts:
  expr_has_effect e /\
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  stmt_state_rel ctx func cenv cx mid s /\
  wb_frame cenv es mid sa s0 s /\
  ghost_inv d cenv cx mid G tn s /\
  local_ptrs_rel func cenv mid.scopes s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM scopes' /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  popped_keys_indexed mid.scopes /\
  lookup_scopes id mid.scopes = SOME entry /\
  lookup_scopes id scopes' =
    SOME (entry with <|value := updated;
            popped := (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))], LAST vs)
                      :: entry.popped|>) /\
  (!j. j <> id ==> lookup_scopes j scopes' = lookup_scopes j mid.scopes) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME b /\
  local_region cenv mid.scopes s id (w2n b) sz /\ k+32 <= sz /\
  mutable_place_path entry.type path /\ value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ val_wf entry.type entry.value /\
  type_memory_size entry.type <= sz /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
  local_path_at cenv cx id k (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  (!i. w2n b+k <= i /\ i < w2n b+k+32 ==> i NOTIN tn.t_mem) /\
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
    vs_inst_idx := t.vs_inst_idx|> /\
  t.vs_memory = (mstore (w2n b+k) (n2w (LENGTH vs-1)) s).vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  read_result cx result (mid with scopes := scopes') =
    (INL (LAST vs),mid with scopes := scopes') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  post_value_type cenv e = expr_type e /\
  lookup_var out t = SOME w /\
  w2n w = w2n b+k+32+(LENGTH vs-1)*type_memory_size etv /\
  local_place_at cenv cx id (k + 32 + (LENGTH vs - 1) * type_memory_size etv)
    etv result /\
  ptr_covers H tf out t (type_memory_size etv) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_size etv ==>
  vv_post ctx func cenv cx e es sa sb s0 (mid with scopes := scopes') result
    (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory)) t /\
  ghost_inv d cenv cx (mid with scopes := scopes') H tf t /\
  ptr_vv_ok cx (expr_type e) result
    (LocatedValue (expr_type e) (mk_ptr (Var out) LocMemory))
    (mid with scopes := scopes') H tf t /\
  ptr_buf_ok cenv e (Var out) H t /\
  ghost_kept cenv mid sm G tn s H tf
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n b) mem` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  `val_in_memory entry.type entry.value (w2n b) s.vs_memory` by
    metis_tac[mem_agree_outside_def] >>
  conj_tac
  >- (match_mp_tac pop_framed_memory_live_vv_post >>
      asm_simp_tac bool_ss [eval_operand_def] >> metis_tac[]) >>
  `stor_taint_ok cx tf t` by
    (irule copy_stor_taint_frame >>
     qexistsl_tac [`s`, `tn`] >>
     qpat_x_assum `t = s with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac[th]) >>
     fs[ghost_inv_def]) >>
  conj_tac
  >- (drule_all pop_live_path_ghost_post >> simp[]) >>
  conj_tac
  >- (drule_all pop_path_result_ptr_post >> simp[]) >>
  conj_tac
  >- (drule_all pop_result_ptr_buf_ok >> simp[]) >>
  irule ghost_kept_old_transport >> simp[]
QED
