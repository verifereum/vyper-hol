(* Rebuild a borrowed code row using only the selected source observation. *)
Theory bodyAbiEncodeSuffixCodeRowMods
Ancestors
  bodyAbiEncodePackedPostMods bodyFullExtCallSavedOperand bodyExtSavedCtorReadMods
  exprLoweringProps bodyFullPostsMods loweringPosts vyperState
  exprLowering exprSimMemDefs context bodyPtrDefs ptrDiscipline venomState arithmetic

Theorem abi_encode_suffix_code_row_mods:
  contract_inv mods exps ctx cenv cx /\
  dead_lo_ok_mods H (DF H) lo cenv cx /\
  abi_encode_saved_row_mods lo cenv cx sa ss e sv v si sm ss vv copy H mid Gm tm m /\
  compile_abi_encode_args compile_expr cenv xs ss = (svs,sb) /\
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    xs svs ss sb mid m Gm tm H (INL vs) ee G tn t /\
  ~copy /\ sv = LocatedValue ty p /\ ty = lowered_value_type cenv e /\
  p.ptr_location = LocCode /\ t.vs_labels = m.vs_labels /\
  (!w. eval_operand p.ptr_operand m = SOME w ==>
       immutable_holds_mods cenv cx ty (Value v) w ee t) ==>
  abi_encode_saved_row_mods lo cenv cx sa sb e sv v si sm ss vv copy H ee G tn t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `sv = LocatedValue _ _` SUBST_ALL_TAC >>
  qpat_x_assum `ty = lowered_value_type _ _` SUBST_ALL_TAC >>
  qhdtm_x_assum `abi_encode_saved_row_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  qhdtm_x_assum `abi_encode_packed_post_mods`
    (qx_choose_then `vs'` (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE [abi_encode_packed_post_mods_def]) >>
  qpat_x_assum `LIST_REL _ _ _` kall_tac >>
  `ss.cs_next_var <= sb.cs_next_var /\ ss.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.INST [`f` |-> `compile_expr`, `st` |-> `ss`,
                      `args` |-> `xs`, `cenv` |-> `cenv`]
               ci_mono_compile_abi_encode_args) >>
     simp[cj 1 compile_expr_ci_mono,ci_mono_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at ss x` by
    (rpt strip_tac >>
     `vv_operand (LocatedValue (lowered_value_type cenv e) p) = Var x` by
       simp[vv_operand_def] >>
     drule_all extcall_saved_operand_not_fresh >> simp[]) >>
  qpat_assum `?raw. read_result cx raw mid = _ /\ _`
    (qx_choose_then `old` (map_every assume_tac o CONJUNCTS)) >>
  `?w. eval_operand p.ptr_operand m = SOME w` by
    (qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     simp[vv_holds_mods_def] >> disch_then (qx_choose_then `w` strip_assume_tac) >>
     qexists `w` >> simp[]) >>
  `eval_operand p.ptr_operand t = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def]) >>
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >>
     gvs[ghost_kept_at_def,ptr_vv_ok_def,op_taint_def,op_prov_def] >> metis_tac[]) >>
  `vv_holds_mods cenv cx (lowered_value_type cenv e) (Value v)
      (LocatedValue (lowered_value_type cenv e) p) ee t` by
    simp[vv_holds_mods_def] >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  conj_tac
  >- (qexists `Value v` >>
      simp[read_result_def,return_def,vv_at_def,ptr_vv_ok_def,vv_store_bound_def]) >>
  qpat_assum `p.ptr_location = LocCode`
    (fn code => simp[NoAsms,code,vv_location_def,vv_operand_def]) >>
  disch_tac >> pure_once_rewrite_tac[ADD_COMM] >>
  (* The final source state is its own entry for the constructor read. *)
  match_mp_tac (Q.INST [`D` |-> `DF H`, `entry` |-> `ee`] ext_saved_ctor_read_linked) >>
  simp[] >> qexists `Value v` >> simp[read_result_def,return_def]
QED
