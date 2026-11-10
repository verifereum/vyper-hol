(* Counted constant-offset address selection; containment covers the whole child. *)
Theory bodyPtrSubscriptTupleSuffix
Ancestors
  bodyPtrSubscriptAddress bodyPtrSubscriptNamedIndex typedCopyPtr
  bodyPtrSubscriptNamedTuplePostBoundary
  fragGasSeqPtr emitHelperProps exprSimMemoryPath fragGasPathPtr fragExec
  emitHelper compileEnv loweringStateRelDefs ptrDiscipline ptrSafeRun bodyPtrDefs finite_map
  venomInstProofs venomExecSemantics venomState venomInst exprLowering

Theorem add_offset_counted_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var p; Lit (n2w off)] [out]) /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  lookup_var p s = SOME a ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst id ADD [Var p; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    (OK ((update_var out (a + n2w off) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx func G tn
    (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[op_taint_def]) >>
  `step_inst_base (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s =
    OK (update_var out (a + n2w off) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  `(mk_inst id ADD [Var p; Lit (n2w off)] [out]).inst_opcode <> INVOKE /\
   ~is_terminator (mk_inst id ADD [Var p; Lit (n2w off)] [out]).inst_opcode`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[mk_inst_def, is_terminator_def] >>
  strip_tac >>
  `~(update_var out (a + n2w off) s with
      vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by simp[update_var_def] >>
  metis_tac[cj 1 gas_path_ptr_rules, cj 2 gas_path_ptr_rules,
            arithmeticTheory.ADD_CLAUSES]
QED

Theorem add_offset_coverage:
  ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  off + child_sz <= parent_sz /\ w2n a + off < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var p; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var p; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out ((update_var out (a + n2w off) s)
      with vs_inst_idx := SUC s.vs_inst_idx) child_sz
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  `off < dimword (:256)` by decide_tac >>
  simp[ptr_covers_def, step_prov_def, out_prov_def, first_prov_def,
       set_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       mk_inst_def, op_prov_def, op_taint_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD, eval_operand_def] >> decide_tac
QED

Theorem compile_tuple_subscript_counted:
  compile_tuple_subscript (Var p) off sa = (op,sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ not_fresh_at sa p /\
  ptr_covers G tn p s parent_sz /\ lookup_var p s = SOME a /\
  off + child_sz <= parent_sz /\ w2n a + off < dimword (:256) ==>
  ?out Gf tnf sf.
    op = Var out /\ gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (a + n2w off) /\
    ptr_covers Gf tnf out sf child_sz /\
    sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!q. not_fresh_at sa q ==>
      lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    (!cenv cx es. stmt_state_rel ctx func cenv cx es s /\
      local_ptrs_reserved cenv sa ==> stmt_state_rel ctx func cenv cx es sf)
Proof
  strip_tac >>
  `?out. op = Var out /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var p; Lit (n2w off)] [out]] /\
   (!q. not_fresh_at sa q ==> q <> out)` by
    (gvs[compile_tuple_subscript_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >> gvs[] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
   SOME (mk_inst sa.cs_next_id ADD [Var p; Lit (n2w off)] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id ADD [Var p; Lit (n2w off)] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id ADD [Var p; Lit (n2w off)] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (unabbrev_all_tac >> irule add_offset_counted_edge >>
      simp[] >> gvs[ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers Gf tnf out (t with vs_inst_idx := SUC s.vs_inst_idx) child_sz` by
    (unabbrev_all_tac >> irule add_offset_coverage >> simp[] >>
     qexists_tac `parent_sz` >> simp[]) >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `tnf.t_imm = tn.t_imm` by
    (simp[Abbr `tnf`, step_taint_def, mk_inst_def, imm_taint_def]) >>
  unabbrev_all_tac >> simp[copy_len_binop_ghost_frame] >>
  conj_tac
  >- (rpt strip_tac >> `q <> out` by metis_tac[] >>
      simp[copy_len_binop_ghost_frame]) >>
  rpt strip_tac >> drule_all fresh_add_stmt_state_rel >>
  disch_then (qspecl_then [`a + n2w off`, `SUC (LENGTH sa.cs_current_insts)`] mp_tac) >>
  simp[update_var_def]
QED
