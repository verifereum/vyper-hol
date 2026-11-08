(* The final selector ADD consumes a computed displacement, not a literal. *)
Theory bodyPtrSubscriptCountedAdd
Ancestors
  bodyPtrSubscriptReadOnly bodyPtrSubscriptTupleSuffix bodyPtrAttributeAdd
  typedCopyPtr emitHelperProps exprLoweringProps words finite_map
  bodyPtrDefs ptrDiscipline venomState venomInst emitHelper compileEnv
  bodyPtrSubscriptBounds bodyPtrSubscriptNamedTuplePostBoundary loweringPosts

Theorem add_displacement_coverage:
  ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  off + child_sz <= parent_sz /\ w2n a + off < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var p;disp] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var p;disp] [out]) s
      (update_var out (a + n2w off) s) tn)
    out (update_var out (a + n2w off) s with vs_inst_idx := n) child_sz
Proof
  strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var p;disp] [out]) s
     (update_var out (a + n2w off) s) tn) (Var out) = {}` by
    simp[copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >> `off < dimword (:256)` by decide_tac >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def,
       w2n_add_2, w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem emit_add_displacement_counted:
  emit_op ADD [Var p;disp] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ not_fresh_at sa p /\
  ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  eval_operand disp s = SOME (n2w off) /\ op_taint tn disp = {} /\
  op_prov G disp = NONE /\ off < dimword (:256) /\
  off + child_sz <= parent_sz /\ w2n a + off < dimword (:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w off) /\ ptr_covers Gf tnf out sf child_sz /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_fmp = s.vs_fmp /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    sf.vs_requests = s.vs_requests /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
      stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `op_taint tn (Var p) = {}` by gvs[ptr_covers_def] >>
  `eval_operand (Var p) s = SOME a` by simp[eval_operand_def] >>
  drule_all (attribute_emit_binop_path_ptr |>
    Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  simp[] >> strip_tac >>
  drule emitted_operand_reserved >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf)` >>
  `ptr_covers Gf tnf out sf child_sz` by
    (unabbrev_all_tac >> irule add_displacement_coverage >> simp[] >>
     qexists_tac `parent_sz` >> simp[]) >>
  `!cenv cx es. stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
     stmt_state_rel ctx func cenv cx es sf` by
    (rpt strip_tac >> simp[Abbr `sf`] >> irule fresh_add_stmt_state_rel >>
     simp[] >> qexists_tac `sa` >> simp[] >> fs[not_fresh_at_def]) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  simp[Abbr `sf`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED
