Theory bodyPtrPopNestedLiveValuePost
Ancestors
  bodyPtrPopNestedLiveSuffixFrame exprSimPopNestedLocalSuffix
  exprSimPopNestedLocalRun exprSimDefs compileEnv venomState finite_map ghostPcTransportPtr

(* S1's local suffix post on the actual counted-path witness, not a separately
   chosen erased execution.  Only the administrative index is normalized. *)
Theorem pop_framed_memory_live_vv_post:
  expr_sim_inv cenv cx env es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  stmt_state_rel ctx func cenv cx mid s /\
  wb_frame cenv es sa s0 s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM scopes' /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  lookup_scopes id mid.scopes = SOME entry /\
  lookup_scopes id scopes' = SOME (entry with <|value := updated; popped := hist|>) /\
  (!j. j <> id ==> lookup_scopes j scopes' = lookup_scopes j mid.scopes) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME b /\
  local_region cenv mid.scopes s id (w2n b) sz /\ k+32 <= sz /\
  mutable_place_path entry.type path /\ value_has_type entry.type entry.value /\
  well_formed_type_value entry.type /\ val_wf entry.type entry.value /\
  val_in_memory entry.type entry.value (w2n b) s.vs_memory /\
  type_memory_size entry.type <= sz /\
  mem_path_offset entry.type path = SOME (k,ArrayTV etv (Dynamic n)) /\
  local_path_at cenv cx id k (ArrayTV etv (Dynamic n)) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
    vs_inst_idx := t.vs_inst_idx|> /\
  t.vs_memory = (mstore (w2n b+k) (n2w (LENGTH vs-1)) s).vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  read_result cx result (mid with scopes := scopes') =
    (INL (LAST vs),mid with scopes := scopes') /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  post_value_type cenv e = expr_type e /\
  eval_operand op t = SOME w /\
  w2n w = w2n b+k+32+(LENGTH vs-1)*type_memory_size etv ==>
  vv_post ctx func cenv cx e es sa sb s0 (mid with scopes := scopes') result
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) t
Proof
  strip_tac >>
  `t = (t with vs_inst_idx := s.vs_inst_idx) with vs_inst_idx := t.vs_inst_idx` by
    simp[] >>
  qpat_x_assum `t = (_ with vs_inst_idx := _) with vs_inst_idx := _`
    (fn th => once_rewrite_tac[th]) >>
  match_mp_tac pop_memory_live_suffix_post >>
  asm_simp_tac bool_ss [venom_state_accfupds, eval_operand_inst_idx] >>
  conj_tac
  >- (drule pop_suffix_frame_normalize >>
      asm_simp_tac bool_ss []) >>
  fs[lookup_var_def]
QED
