Theory bodyPtrIfExpRuntimeOffset
Ancestors bodyPtrAttributeAdd exprSimCopy context emitHelperProps
  fragGasPathPtr ptrDiscipline venomState finite_map words compileEnv
  exprLoweringProps venomInst arithmetic bodyPtrDefs

(* Literal and zero offsets emit no edge; variable offsets use the existing
   counted ADD boundary.  Source cleanliness does not erase provenance. *)
Theorem ifexp_runtime_offset_path:
  compile_lit_byte_offset op off sa = (dst,sb) /\
  copy_old_operand sa op /\ eval_operand op s = SOME a /\
  op_taint tn op = {} /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    copy_runtime_frame sa s sb (t with vs_inst_idx := s.vs_inst_idx) /\
    eval_operand dst t = SOME (a+n2w off) /\
    op_prov G' dst = op_prov G op /\ op_taint tn' dst = {} /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `off = 0`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[copy_runtime_frame_refl, gas_path_ptr_rules, WORD_ADD_0] >>
      qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[copy_runtime_frame_refl]) >>
  Cases_on `?w. op = Lit w`
  >- (gvs[compile_lit_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[copy_runtime_frame_refl, gas_path_ptr_rules, op_prov_def,
           op_taint_def, eval_operand_def] >> gvs[eval_operand_def] >>
      qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[copy_runtime_frame_refl]) >>
  `emit_op ADD [op;Lit (n2w off)] sa = (dst,sb)` by
    (Cases_on `op` >> gvs[compile_lit_byte_offset_def]) >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (attribute_emit_binop_path_ptr |> SPEC_ALL |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `out = STRING #"%" (toString sa.cs_next_var)` by
    (qpat_x_assum `dst = Var out` mp_tac >> simp[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `copy_runtime_frame sa s sb (update_var out (a+n2w off) s)` by
    (drule_all copy_runtime_offset >> strip_tac >>
     gvs[copy_runtime_frame_def, run_inst_seq_def, mk_inst_def,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def]) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qpat_x_assum `copy_runtime_frame _ _ _ _` mp_tac >>
  qpat_x_assum `op_taint _ (Var out) = {}` mp_tac >>
  simp[attribute_add_provenance, op_prov_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[] >> metis_tac[]
QED

(* Unlike a clean code address, a destination offset must retain its site.
   The explicit nonwrap bound is needed even when only a suffix is covered. *)
Theorem ifexp_runtime_offset_covers:
  compile_lit_byte_offset (Var root) off sa = (dst,sb) /\
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off+n <= capacity /\ w2n a+off < dimword (:256) /\
  eval_operand dst t = SOME (a+n2w off) /\
  op_prov H dst = op_prov G (Var root) /\ op_taint tt dst = {} ==>
  ?q. dst = Var q /\ ptr_covers H tt q t n
Proof
  strip_tac >>
  `?q. dst = Var q` by
    (Cases_on `off = 0` >>
     gvs[compile_lit_byte_offset_def, comp_return_def] >>
     drule emitted_insts_emit_op >> simp[]) >>
  qexists_tac `q` >> simp[] >>
  `off < dimword (:256)` by decide_tac >>
  gvs[ptr_covers_def, eval_operand_def, op_prov_def] >>
  simp[ptr_covers_def, w2n_add_2, w2n_n2w, LESS_MOD] >>
  decide_tac
QED
