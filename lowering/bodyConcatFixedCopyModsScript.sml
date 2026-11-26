(* Fixed-width Concat copy at the reached child endpoint. *)
Theory bodyConcatFixedCopyMods
Ancestors
  bodyConcatCutsMods bodyFullBuiltinConcatHead bodyFullPostsMods stateRelProj
  exprSimFullBundleProps bodyPtrDefs loweringPosts loweringStateRelDefs
  compileEnv context exprSimDefs exprLowering vyperInterpreter vyperState
  vyperValue vyperTyping venomState venomInst finite_map pred_set words list pair
Libs monadsyntax

Theorem concat_fixed_type_mods[local]:
  evaluate_type tenv (BaseT (BytesT (Fixed m))) = SOME tv ==>
  m <= 32 /\ tv = BaseTV (BytesT (Fixed m))
Proof
  Cases_on `m <= 32` >> simp[evaluate_type_def]
QED

Theorem concat_fixed_word_mods[local]:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  value_has_type tv v /\
  expr_val_rel cx (BaseT (BytesT (Fixed m))) v op s ==>
  ?bytes. v = BytesV bytes /\ LENGTH bytes = m /\ m <= 32 /\
    eval_operand op s = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bytes))
Proof
  strip_tac >>
  drule concat_fixed_type_mods >> strip_tac >>
  Cases_on `v` >>
  gvs[value_has_type_def,expr_val_rel_def,is_word_type_def,
      valueEncodingTheory.typed_val_to_w256_def,evaluate_type_def]
QED

Theorem concat_fixed_copy_bound_mods[local]:
  k <= P /\ 32 + concat_data_bound P (BaseT (BytesT (Fixed m))::tys) <= bsz ==>
  32 + k + 32 <= bsz
Proof
  simp[concat_data_bound_def,is_bytestring_type_def,arithmeticTheory.MAX_DEF] >>
  rw[] >> decide_tac
QED

Theorem concat_fixed_copy_cut_mods:
  (do offset_op <- emit_op MLOAD [Var ov];
      dst <- emit_op ADD [Var dv;offset_op];
      emit_void MSTORE [dst;op];
      new_offset <- emit_op ADD [offset_op;Lit (n2w m)];
      emit_void MSTORE [Var ov;new_offset]
   od) sc = ((),sb) /\
  fn_has_code sc sb func /\ fn_inst_ids_distinct func /\
  concat_live_mods (func,cenv,lo) (dv,ov,ow,binst,oinst,B,bsz)
    (ee,sc,s,G,tn) prefix /\
  local_ptrs_reserved cenv sc /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sc z) /\
  (!z. op = Var z ==> not_fresh_at sc z) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  expr_post_mods H ctx func cenv cx e es sa sc s0 ee v op s /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  LENGTH prefix <= P /\ 32 + concat_data_bound P (expr_type e::tys) <= bsz ==>
  ?u G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG : (num # num) option list)
      (s,G,tn) [] (OK u,G',tn')) /\
    concat_copy_effect_mods (ctx,func,cenv,cx,lo,d) (dv,ov,ow,binst,oinst,B,bsz)
      (ee,sc,s,G,tn) (sb,u,G',tn') prefix (concat_payload_mods v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv` by
    (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule concat_fixed_type_mods >> strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  `expr_val_rel cx (BaseT (BytesT (Fixed m))) v op s /\
   stmt_state_rel H ctx func cenv cx ee s` by
    fs[expr_post_mods_def,expr_post_def] >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `?bytes. v = BytesV bytes /\ LENGTH bytes = m /\ m <= 32 /\
    eval_operand op s = SOME (word_of_bytes_be (PAD_RIGHT 0w 32 bytes))` by
    (irule concat_fixed_word_mods >> qexistsl_tac [`cx`,`tv`] >> simp[]) >>
  `32 + LENGTH prefix + 32 <= bsz` by
    (irule concat_fixed_copy_bound_mods >> qexistsl_tac [`P`,`m`,`tys`] >>
     qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >> simp[]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  qpat_x_assum `concat_live_mods _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [concat_live_mods_def]) >>
  `lookup_var ov s = SOME (n2w (w2n ow))` by simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:256``] concat_head_fixed_uniform) >>
  disch_then (qspecl_then [`explicit`,`d`,`cx`,`PG`] strip_assume_tac) >>
  `u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_immutables = s.vs_immutables /\
   u.vs_data_section = s.vs_data_section` by
    (qpat_assum `u = _` SUBST1_TAC >>
     simp_tac bool_ss [mstore_def,LET_THM,venom_state_accessors,
                      venom_state_accfupds,combinTheory.K_THM]) >>
  `!z. not_fresh_at sc z ==> lookup_var z u = lookup_var z s` by
    (rpt strip_tac >> qpat_x_assum `u = _` SUBST1_TAC >>
     simp_tac pure_ss [lookup_var_def,mstore_def,LET_THM,
                      venom_state_accessors,venom_state_accfupds] >>
     first_assum drule >> simp[]) >>
  qpat_x_assum `u = _` kall_tac >>
  `!i. B+32+LENGTH prefix <= i /\ i < B+32+LENGTH prefix+m ==> i NOTIN tn'.t_mem` by
    (gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!i. B+32+LENGTH prefix <= i /\ _ ==> i NOTIN tn'.t_mem`
       (qspec_then `i` irule) >> decide_tac) >>
  `concat_payload_mods v = bytes` by simp[concat_payload_mods_def] >>
  qexistsl_tac [`u`,`G'`,`tn'`] >>
  asm_simp_tac bool_ss [concat_copy_effect_mods_def,expr_sim_full_endpoint_def,
                        arithmeticTheory.LESS_EQ_REFL] >>
  first_assum ACCEPT_TAC
QED
