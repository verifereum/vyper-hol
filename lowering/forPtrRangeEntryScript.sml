(* Literal range initialization uses the checked scalar instruction interface.
   The second endpoint is emitted as ADD of two literals, not ASSIGN. *)
Theory forPtrRangeEntry
Ancestors forPtrAllocation forPtrRangeLoop forPtrControl forPtrAdmin emitHelperProps
  stmtSimForParts venomExecProofs ptrDiscipline finite_map
  venomState venomInst venomExecSemantics ptrSafeRun fragGasPathPtr
  contextCodegenRel forPtrRangePrepare stmtFragPtr bodyPtrDefs
  loweringSlice stmtSimDeclPath allocationPtr

Theorem for_add_literals_ghost:
  step_prov PG G (mk_inst id ADD [Lit a; Lit b] [out])
    (update_var out (a+b) s) = DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id ADD [Lit a; Lit b] [out]) s
    (update_var out (a+b) s) tn = tn with t_var := tn.t_var |+ (out,{})
Proof
  `new_site_bytes s (update_var out (a+b) s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       op_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, mk_inst_def, taint_component_equality,
       eval_operand_def]
QED

Theorem for_add_literals_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Lit a; Lit b] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Lit a; Lit b] [out]) s =
    OK (update_var out (a+b) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) copy_len_binop_zero_path_ptr >>
  simp[op_taint_def, for_add_literals_ghost]
QED

Theorem for_range_jump_path_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
     (mk_inst id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gasCountTheory.gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem for_range_literal_entry_path_ptr:
  lookup_block lbl fn.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions :=
      [mk_inst i1 ASSIGN [Lit a] [cv];
       mk_inst i2 ADD [Lit a; Lit b] [ev];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (ev,{}))
    (OK (jump_to cond_lbl (update_var ev (a+b) (update_var cv a s))))
Proof
  strip_tac >>
  qpat_x_assum `s.vs_current_bb = lbl` (SUBST_ALL_TAC o SYM) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {cv}))
    (tn with t_var := tn.t_var |+ (cv,{}))
    (OK ((update_var cv a s) with vs_inst_idx := 1))` by
    (`get_instruction
        <|bb_label := s.vs_current_bb; bb_instructions :=
          [mk_inst i1 ASSIGN [Lit a] [cv];
           mk_inst i2 ADD [Lit a; Lit b] [ev];
           mk_inst i3 JMP [Label cond_lbl] []]|> s.vs_inst_idx =
        SOME (mk_inst i1 ASSIGN [Lit a] [cv])` by
        simp[get_instruction_def] >>
     drule_all assign_literal_zero_path_ptr >>
     simp[assign_literal_scalar_ghost]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    ((update_var cv a s) with vs_inst_idx := 1) 0
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (ev,{}))
    (OK ((update_var ev (a+b) (update_var cv a s)) with vs_inst_idx := 2))` by
    (simp[update_var_def] >>
     irule (SRULE [update_var_def]
       (Q.INST [`s` |-> `(update_var cv a s) with vs_inst_idx := 1`,
                `G` |-> `DRESTRICT G (COMPL {cv})`,
                `tn` |-> `tn with t_var := tn.t_var |+ (cv,{})`]
         (SPEC_ALL for_add_literals_path_ptr))) >>
     simp[get_instruction_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (ev,{}))
    ((update_var ev (a+b) (update_var cv a s)) with vs_inst_idx := 2) 0
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (ev,{}))
    (OK (jump_to cond_lbl
      ((update_var ev (a+b) (update_var cv a s)) with vs_inst_idx := 2)))` by
    (irule for_range_jump_path_ptr >>
     simp[update_var_def, get_instruction_def] >> metis_tac[]) >>
  rev_dxrule gas_path_ptr_then >> disch_then dxrule >> simp[] >> strip_tac >>
  gvs[] >>
  dxrule gas_path_ptr_then >> disch_then drule >> simp[jump_to_def]
QED

Theorem for_range_literal_entry_ghost:
  ghost_inv d cenv cx es G tn s /\
  not_local_ptr cenv es.scopes cv /\ not_local_ptr cenv es.scopes ev /\
  (!q. cenv.ce_return_buf <> SOME (PtrVar (Var cv) q)) /\
  (!q. cenv.ce_return_buf <> SOME (PtrVar (Var ev) q)) ==>
  ghost_inv d cenv cx es
    (DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}))
    (tn with t_var := (tn.t_var |+ (cv,{})) |+ (ev,{}))
    (jump_to cond_lbl (update_var ev b (update_var cv a s)))
Proof
  strip_tac >> pure_rewrite_tac[jump_to_def, ghost_inv_jump_to] >>
  `ghost_inv d cenv cx es (DRESTRICT G (COMPL {cv}))
     (tn with t_var := tn.t_var |+ (cv,{})) (update_var cv a s)` by
     (irule for_scalar_overwrite_ghost >> simp[]) >>
  simp[] >> irule (SRULE [] (Q.INST
    [`G` |-> `DRESTRICT G (COMPL {cv})`,
     `tn` |-> `tn with t_var := tn.t_var |+ (cv,{})`]
    (SPEC_ALL for_scalar_overwrite_ghost))) >> simp[]
QED

Theorem for_range_literal_entry_frame:
  sf = jump_to cond_lbl (update_var ev b (update_var cv a s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {cv})) (COMPL {ev}) /\
  tf = (tn with t_var := (tn.t_var |+ (cv,{})) |+ (ev,{})) /\
  cv <> ev /\ p <> cv /\ p <> ev /\ ptr_covers G tn p s sz ==>
  lookup_var cv sf = SOME a /\ lookup_var ev sf = SOME b /\
  FLOOKUP Gf cv = NONE /\ FLOOKUP Gf ev = NONE /\
  op_taint tf (Var cv) = {} /\ op_taint tf (Var ev) = {} /\
  ptr_covers Gf tf p sf sz /\
  (!x. x <> cv /\ x <> ev ==>
    lookup_var x sf = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  gvs[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE,
      FLOOKUP_DRESTRICT, op_taint_def, ptr_covers_def]
QED

(* S1's analogous state fact is local to stmtSimFor.  This public boundary
   specializes the existing allocation preservation and frame interfaces. *)
Theorem for_range_alloca_state:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\ ~s.vs_halted ==>
  ?u a. step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\ lookup_var out u = SOME a /\
    FLOOKUP u.vs_allocas id = SOME (w2n a,n) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
    ~u.vs_halted /\ (!x. x <> out ==> lookup_var x u = lookup_var x s) /\
    (!aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
       FLOOKUP u.vs_allocas aid = SOME site)
Proof
  strip_tac >>
  `?u. exec_alloca (mk_inst id ALLOCA [Lit (n2w n)] [out]) s (n2w n : bytes32) = OK u` by
    (Cases_on `FLOOKUP s.vs_allocas id` >- simp[exec_alloca_def, mk_inst_def] >>
     rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
     simp[exec_alloca_def, mk_inst_def]) >>
  `stmt_state_rel ctx fn cenv cx es u /\
    ?a. lookup_var out u = SOME a /\
        FLOOKUP u.vs_allocas id = SOME (w2n a,n)` by
    (drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
     simp[mk_inst_def] >> simp[GSYM mk_inst_def] >>
     disch_then drule_all >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
    ~u.vs_halted` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def, AllCaseEqs()]) >>
  drule_at (Pat `exec_alloca _ _ _ = _`) exec_alloca_frames >>
  simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`u`, `a`] >> simp[] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >> simp[GSYM mk_inst_def]
QED

Theorem for_range_alloca_entry_path_ptr:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) ==>
  ?u a.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\ lookup_var out u = SOME a /\
    FLOOKUP u.vs_allocas id = SOME (w2n a,n) /\
    u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
    ~u.vs_halted /\
    gas_path_ptr D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) out u n /\
    (!name lo sz. local_region cenv es.scopes s name lo sz ==>
       regions_disjoint (w2n a) n lo sz) /\
    (!x. x <> out ==> lookup_var x u = lookup_var x s /\
      FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) x =
        FLOOKUP G x /\
      op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
        (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all for_range_alloca_state >> strip_tac >>
  qexistsl_tac [`u`, `a`] >> simp[] >> conj_tac
  >- (irule alloca_zero_path_ptr >> simp[]) >> conj_tac
  >- (irule alloca_step_ptr_covers >> simp[] >> metis_tac[]) >> conj_tac
  >- (rpt strip_tac >> irule for_alloca_outer_local_disjoint >>
      simp[] >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  drule_all alloca_old_variable_ghost_frame >> simp[]
QED
