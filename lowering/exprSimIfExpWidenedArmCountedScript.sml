Theory exprSimIfExpWidenedArmCounted
Ancestors
  exprSimIfExpWidenedCounted exprSimIfExpWidenedBytesCounted
  exprSimIfExpWidenedNoCopy exprSimLayoutTransport exprSimHyps
  exprSimHypsDefs exprSimProps exprOperandVar exprLowering context
  compileEnv loweringPosts vyperState vyperAST vyperTypeSystem exprLoweringProps fragGasPath fragGasMode

Theorem compile_nocopy_ifexp_post_path:
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,ee) /\
  read_result cx tvv ee = (INL v,ee) /\
  (is_word_type (expr_type e) \/ same_memory_layout ce (lowered_value_type ce e) (expr_type e)) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  vv_post ctx func ce cx e es origin sa s0 ee tvv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `unwrap_value ce vv sa = (op,sb)` by
    (qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[compile_ifexp_arm_def]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[bind_def] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
    ~is_word_type (post_value_type ce e) ==>
    type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
    type_memory_size tvt < 2 ** 64` by
    (drule nocopy_ifexp_physical_bound >> simp[] >>
     disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  `post_value_type ce e <> expr_type e ==>
    ((?t op. vv = StackValue t op) \/
     (?t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory /\ ~is_word_type t))` by
    (strip_tac >> irule compile_changed_physical_unwrap_shape >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >>
     `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
       metis_tac[post_value_type_word, post_value_type_bytestring] >>
     `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
       (spose_not_then assume_tac >>
        `post_value_type ce e = expr_type e` by
          (irule post_value_type_not_int_call >> metis_tac[]) >> gvs[]) >>
     gvs[expr_type_def] >> drule_all ifexp_intcall_copy_source >> strip_tac >>
     fs[type_widens_to_def] >> metis_tac[compatible_word_type]) >>
  drule_all unwrap_value_physical_path >> strip_tac >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (irule nocopy_ifexp_post_annotated >> metis_tac[]) >>
  fs[gas_marked_path_def] >> metis_tac[cj 1 gas_path_normal]
QED
