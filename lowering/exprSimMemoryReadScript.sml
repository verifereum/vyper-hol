(* Full-post counted read suffix for memory-located values. *)
Theory exprSimMemoryRead
Ancestors
  exprSimMemorySource exprSimMemoryPath exprSimUnwrapProps exprSimProps
  exprLoweringProps loweringPosts gasSummary fragGasMode fragGasPath
  valueEncodingProps venomState compileEnv vyperState valueCopyBytes

Theorem unwrap_memory_marked_read:
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `(is_word_type t ==> t = post_value_type cenv e) /\
   ?w v. eval_operand p.ptr_operand s = SOME w /\
     read_result cx tv ee = (INL v,ee) /\
     (!tvt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME tvt ==>
       val_in_memory tvt v (w2n w) s.vs_memory /\
       (is_word_type (post_value_type cenv e) ==>
        mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v))` by
    gvs[vv_post_def, vv_holds_def, is_bytestring_word_type] >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue t p) s` by
    metis_tac[vv_post_read_result] >>
  `!u. gas_marked_path F ctx func s 0 (OK u) ==>
       gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s) [] (INL v) ee (OK u)` by
    (simp[gas_marked_exec_def] >> metis_tac[read_result_gas_obs]) >>
  Cases_on `is_word_type t`
  >- (gvs[unwrap_memory_compile] >>
      qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var))
         (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
      `eval_operand op u = SOME (mload (w2n w) s) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts /\
       (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
          lookup_var x u = SOME w') /\
       u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
        (qunabbrev_tac `u` >> irule emit_mload_endpoint >>
         simp[] >> qexists_tac `p.ptr_operand` >> simp[]) >>
      qexistsl_tac [`v`, `u`] >> conj_tac
      >- (first_x_assum irule >>
          drule_all emit_mload_marked_path >> simp[Abbr `u`]) >>
      simp[] >> irule expr_post_of_vv_post_load_physical >>
      goal_assum (drule_at Any) >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> fs[GSYM mem_word_at_eq_mload]) >>
      conj_tac
      >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
          irule stmt_state_rel_update_var >>
          `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
          simp[] >> irule local_ptrs_reserved_fresh >>
          qexists_tac `sm` >> simp[]) >>
      qexistsl_tac [`p`, `s`, `sm`, `post_value_type cenv e`] >> simp[]) >>
  gvs[unwrap_memory_compile, comp_return_def] >>
  qexistsl_tac [`v`, `s`] >> simp[] >> conj_tac
  >- (first_x_assum irule >> simp[gas_marked_path_def] >>
      irule (cj 1 gas_path_rules) >> simp[]) >>
  irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `t` >> simp[]
QED
