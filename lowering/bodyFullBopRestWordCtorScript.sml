Theory bodyFullBopRestWordCtor
Ancestors
  bodyPtrBopInBoundedLayout bodyPtrBopInElementLoad bodyPtrBopInLoopLayout
  bodyPtrBopInLoopContract fragExec fragGasSeqPtr
  fragGasOriginPtr instMemFrontier memSafeRun ptrSafeRun ptrDiscipline memLocDefs exprLowering compileEnv
  contextCodegenRel codegenRel venomExecSemantics venomInst venomState
  finite_map words list rich_list

Theorem rest_word_membership_ctor_body_prefix:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load T imm LocCode) bound_opt is_in sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
     fn.fn_blocks = SOME bb /\
    isPREFIX
      ([mk_inst (sa.cs_next_id+6+(case bound_opt of NONE => 0 | SOME cap => 3)) MUL
        [Var ("%" ++ toString (sa.cs_next_var+1)); Lit (n2w stride)]
        ["%" ++ toString (sa.cs_next_var+3+(case bound_opt of NONE => 0 | SOME cap => 2))]] ++
       (if 0 < skip then
         [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)) ADD
           [Lit (n2w skip); Var ("%" ++ toString (sa.cs_next_var+3+(case bound_opt of NONE => 0 | SOME cap => 2)))]
           ["%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2))]] else []) ++
       [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)+(if 0 < skip then 1 else 0)) ADD
         [arr; Var (if 0 < skip then "%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2))
                   else "%" ++ toString (sa.cs_next_var+3+(case bound_opt of NONE => 0 | SOME cap => 2)))]
         ["%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0))]] ++
       (case imm of NONE =>
         [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+(if 0 < skip then 1 else 0)) ILOAD
           [Var ("%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0)))]
           ["%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0)+(if IS_SOME imm then 2 else 1))]]
        | SOME ib =>
         [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+(if 0 < skip then 1 else 0)) ADD
           [Var ("%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0))); ib]
           ["%" ++ toString (sa.cs_next_var+5+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0))];
          mk_inst (sa.cs_next_id+9+(case bound_opt of NONE => 0 | SOME cap => 3)+(if 0 < skip then 1 else 0)) ILOAD
           [Var ("%" ++ toString (sa.cs_next_var+5+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0)))]
           ["%" ++ toString (sa.cs_next_var+4+(case bound_opt of NONE => 0 | SOME cap => 2)+(if 0 < skip then 1 else 0)+(if IS_SOME imm then 2 else 1))]])) bb.bb_instructions
Proof
  strip_tac >> Cases_on `bound_opt`
  >- (gvs[SRULE [] membership_loop_layout] >>
      fs[fn_has_code_def, emitted_blocks_def] >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
            Cases_on `imm` >> Cases_on `0 < skip` >> simp[]) >>
  gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    Cases_on `imm` >> Cases_on `0 < skip` >> simp[]
QED

Theorem rest_word_membership_ctor_prefix_checked:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load T imm LocCode) bound_opt is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  (!ib x. imm = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
  q = (case bound_opt of NONE => 0 | SOME cap => 2) /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if IS_SOME imm then 2 else 1) /\
  dst = "%" ++ toString (sa.cs_next_var+4+q+delta+width) /\
  (!i. addr i = bw + n2w (skip+stride*i)) /\
  code = [mk_inst (sa.cs_next_id+6+(case bound_opt of NONE => 0 | SOME cap => 3)) MUL
    [Var ("%" ++ toString (sa.cs_next_var+1)); Lit (n2w stride)]
    ["%" ++ toString (sa.cs_next_var+3+q)]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)) ADD
      [Lit (n2w skip); Var ("%" ++ toString (sa.cs_next_var+3+q))]
      ["%" ++ toString (sa.cs_next_var+4+q)]] else []) ++
    [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
      [arr; Var (if 0 < skip then "%" ++ toString (sa.cs_next_var+4+q)
                 else "%" ++ toString (sa.cs_next_var+3+q))]
      ["%" ++ toString (sa.cs_next_var+4+q+delta)]] ++
    (case imm of NONE =>
      [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ILOAD
        [Var ("%" ++ toString (sa.cs_next_var+4+q+delta))] [dst]]
    | SOME ib =>
      [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
        [Var ("%" ++ toString (sa.cs_next_var+4+q+delta));ib]
        ["%" ++ toString (sa.cs_next_var+5+q+delta)];
       mk_inst (sa.cs_next_id+9+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ILOAD
        [Var ("%" ++ toString (sa.cs_next_var+5+q+delta))] [dst]]) /\
  ~s0.vs_halted /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
  eval_operand arr s0 = SOME bw /\ op_prov G0 arr = NONE /\ op_taint T0 arr = {} /\
  (!ib. imm = SOME ib ==> eval_operand ib s0 = SOME 0w /\
    op_prov G0 ib = NONE /\ op_taint T0 ib = {}) /\
  (!j. j < LENGTH ws ==> w2n (addr j)+32 <= lo /\
    mem_word_taint T0.t_mem (w2n (addr j)) = {} /\ mload (w2n (addr j)) s0 = EL j ws) /\
  i < LENGTH ws /\ membership_loop_frame sa G0 T0 s0 Gs Ts s /\
  membership_loop_registers sa i 0w Gs Ts s /\
  ~s.vs_halted /\ allocas_from lo s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\ s.vs_inst_idx = 0 ==>
  ?u g tn. run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s /\
    g = FOLDL (\g x. DRESTRICT g (COMPL {x})) Gs
      (["%" ++ toString (sa.cs_next_var+3+q)] ++
       (if 0 < skip then ["%" ++ toString (sa.cs_next_var+4+q)] else []) ++
       ["%" ++ toString (sa.cs_next_var+4+q+delta)] ++
       (if IS_SOME imm then ["%" ++ toString (sa.cs_next_var+5+q+delta)] else []) ++
       [dst]) /\
    tn = Ts with t_var := FOLDL (\m x. m |+ (x,{})) Ts.t_var
      (["%" ++ toString (sa.cs_next_var+3+q)] ++
       (if 0 < skip then ["%" ++ toString (sa.cs_next_var+4+q)] else []) ++
       ["%" ++ toString (sa.cs_next_var+4+q+delta)] ++
       (if IS_SOME imm then ["%" ++ toString (sa.cs_next_var+5+q+delta)] else []) ++
       [dst]) /\
    inst_seq_ptr D lo ctx fn PG Gs Ts code s g tn /\
    membership_loop_frame sa G0 T0 s0 g tn (u with vs_inst_idx := 2+delta+width) /\
    membership_loop_registers sa i 0w g tn (u with vs_inst_idx := 2+delta+width) /\
    ~u.vs_halted /\ allocas_from lo u /\
    u.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    eval_operand (Var dst) u = SOME (EL i ws) /\
    op_prov g (Var dst) = NONE /\ op_taint tn (Var dst) = {}
Proof
  strip_tac >>
  `eval_operand arr s = SOME bw /\
   (!ib. imm = SOME ib ==> eval_operand ib s = SOME 0w) /\
   lookup_var ("%" ++ toString (sa.cs_next_var+1)) s = SOME (n2w i) /\
   mload (w2n (addr i)) s = EL i ws` by suspend "inputs" >>
  `!k w v. sa.cs_next_var <= k ==> eval_operand arr
     (update_var (STRING #"%" (toString k)) w v) = eval_operand arr v` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!ib k w v. imm = SOME ib /\ sa.cs_next_var <= k ==>
     eval_operand ib (update_var (STRING #"%" (toString k)) w v) = eval_operand ib v` by
    (rpt strip_tac >> irule exprSimWordBuiltinsTheory.eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `?u. run_inst_seq code s = OK u` by suspend "run" >>
  `run_inst_seq_mem_ok code s` by suspend "memory" >>
  qexists_tac `u` >>
  qpat_assum `run_inst_seq code s = OK u`
    (fn th => pure_rewrite_tac[th, AND_CLAUSES]) >>
  qpat_assum `run_inst_seq_mem_ok code s`
    (fn th => pure_rewrite_tac[th, AND_CLAUSES]) >>
  suspend "stages"
QED

Resume rest_word_membership_ctor_prefix_checked[inputs]:
  conj_tac
  >- (drule_all (cj 1 membership_loop_frame_operand) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `!x. ib = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all (cj 1 membership_loop_frame_operand) >> simp[]) >>
  conj_tac
  >- fs[membership_loop_registers_def] >>
  drule membership_frame_memory >> strip_tac >>
  simp[]
QED

Resume rest_word_membership_ctor_prefix_checked[run]:
  fs[lookup_var_def] >>
  Cases_on `imm` >> fs[] >> Cases_on `0 < skip` >>
  simp[exprLoweringPropsTheory.run_inst_seq_def, mk_inst_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
    eval_operands_def, eval_operand_def,
    emitHelperPropsTheory.lookup_var_update_var,
    (Q.SPEC `sa` exprSimWordBuiltinsTheory.eval_operand_update_not_fresh),
    lookup_var_def, FLOOKUP_UPDATE] >>
  simp[update_var_def, FLOOKUP_UPDATE]
QED

Resume rest_word_membership_ctor_prefix_checked[memory]:
  `lo <= s.vs_alloca_next` by
    (qpat_x_assum `membership_loop_frame _ _ _ _ _ _ _` mp_tac >>
     simp[membership_loop_frame_def] >> strip_tac >>
     qpat_x_assum `s = _` (mp_tac o Q.AP_TERM `\v. v.vs_alloca_next`) >> simp[]) >>
  fs[lookup_var_def] >>
  Cases_on `imm` >> fs[] >> Cases_on `0 < skip` >>
  simp[fragExecMemTheory.run_inst_seq_mem_ok_def,
    mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_base_opcode_eqs, exec_pure2_def, exec_read1_def,
    eval_operands_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `!j. j < LENGTH ws ==> _` (qspec_then `i` mp_tac) >>
  simp[GSYM word_add_n2w, GSYM word_mul_n2w] >>
  strip_tac >> gvs[arithmeticTheory.NOT_LESS, update_var_def, WORD_ADD_0] >> decide_tac
QED

Resume rest_word_membership_ctor_prefix_checked[stages]:
  `op_prov Gs arr = NONE /\ op_taint Ts arr = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  `!ib. imm = SOME ib ==> op_prov Gs ib = NONE /\ op_taint Ts ib = {}` by
    (rpt strip_tac >>
     `!x. ib = Var x ==> not_fresh_at sa x` by simp[] >>
     drule_all membership_loop_frame_operand >> simp[]) >>
  qabbrev_tac `p = "%" ++ toString (sa.cs_next_var+3+
    (case bound_opt of NONE => 0 | SOME cap => 2))` >>
  qabbrev_tac `mulins = mk_inst (sa.cs_next_id+6+
    (case bound_opt of NONE => 0 | SOME cap => 3)) MUL
    [Var ("%" ++ toString (sa.cs_next_var+1));Lit (n2w stride)] [p]` >>
  qabbrev_tac `sm = update_var p (n2w i * n2w stride) s` >>
  qabbrev_tac `gm = DRESTRICT Gs (COMPL {p})` >>
  qabbrev_tac `tm = Ts with t_var := Ts.t_var |+ (p,{})` >>
  `step_inst_base mulins s = OK sm` by
    (simp[Abbr `mulins`, Abbr `sm`, membership_address_binop_step,
      eval_operand_def]) >>
  `step_prov PG Gs mulins sm = gm /\
   step_taint mulins s sm Ts = tm` by
    (simp[Abbr `mulins`, Abbr `sm`, Abbr `gm`, Abbr `tm`] >>
     irule typedCopyLoopHeaderPtrTheory.typed_copy_loop_arith_ghost_clean >>
     fs[membership_loop_registers_def, update_var_def, op_taint_def] >>
     rpt strip_tac >> gvs[]) >>
  `ptr_inst_ok D lo 0 ctx fn Gs Ts mulins s` by
    (simp[Abbr `mulins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
      mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, eval_operand_def, op_taint_def,
      Abbr `sm`, update_var_def] >>
     rpt strip_tac >> gvs[membership_loop_registers_def, op_taint_def]) >>
  `!x. not_fresh_at sa x ==> x <> p` by
    (simp[Abbr `p`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `3+
       (case bound_opt of NONE => 0 | SOME cap => 2)` mp_tac) >> simp[]) >>
  `p <> "%" ++ toString (sa.cs_next_var+1) /\
   p <> "%" ++ toString sa.cs_next_var` by
    simp[Abbr `p`] >>
  `!x. x <> p ==> FLOOKUP gm x = FLOOKUP Gs x /\
    op_taint tm (Var x) = op_taint Ts (Var x)` by
    simp[Abbr `gm`, Abbr `tm`, FLOOKUP_DRESTRICT,
      pred_setTheory.COMPL_DEF, op_taint_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 gm tm
      (sm with vs_inst_idx := 1) /\
   membership_loop_registers sa i 0w gm tm
      (sm with vs_inst_idx := 1)` by
    (conj_tac
     >- (simp[Abbr `sm`] >> irule membership_frame_scalar_update >>
         conj_tac >- (qpat_assum `!x. not_fresh_at sa x ==> x <> p` ACCEPT_TAC) >>
         qexistsl_tac [`Gs`, `Ts`] >> simp[Abbr `tm`] >> metis_tac[]) >>
     simp[Abbr `sm`] >> irule membership_registers_scalar_update >>
     simp[] >> qexistsl_tac [`Gs`, `Ts`] >> simp[]) >>
  suspend "offset_stage"
QED

Resume rest_word_membership_ctor_prefix_checked[offset_stage]:
  qabbrev_tac `sc = sm with vs_inst_idx := 1` >>
  qabbrev_tac `offname = "%" ++ toString (sa.cs_next_var+4+
    (case bound_opt of NONE => 0 | SOME cap => 2))` >>
  qabbrev_tac `skipins = mk_inst (sa.cs_next_id+7+
    (case bound_opt of NONE => 0 | SOME cap => 3)) ADD
    [Lit (n2w skip); Var p] [offname]` >>
  qabbrev_tac `sk = update_var offname (n2w skip+n2w i*n2w stride) sc` >>
  qabbrev_tac `gk = DRESTRICT gm (COMPL {offname})` >>
  qabbrev_tac `tk = tm with t_var := tm.t_var |+ (offname,{})` >>
  `eval_operand (Var p) sc = SOME (n2w i*n2w stride) /\
   op_prov gm (Var p) = NONE /\ op_taint tm (Var p) = {}` by
    simp[Abbr `sc`, Abbr `sm`, Abbr `gm`, Abbr `tm`,
      eval_operand_def, lookup_var_def, update_var_def,
      op_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      pred_setTheory.COMPL_DEF] >>
  `step_inst_base skipins sc = OK sk` by
    (simp[Abbr `skipins`, Abbr `sk`, membership_address_binop_step,
      eval_operand_def]) >>
  `step_prov PG gm skipins sk = gk` by
    simp[Abbr `skipins`, Abbr `gk`, step_prov_def, out_prov_def,
      set_prov_def, first_prov_def, op_prov_def] >>
  `step_taint skipins sc sk tm = tk` by
    (simp[Abbr `skipins`, Abbr `sk`, Abbr `tk`] >>
     irule stmtAppendStorageRunPtrTheory.scalar_add_taint >> simp[update_var_def]) >>
  `allocas_from lo sc` by
    (simp[Abbr `sc`, Abbr `sm`, update_var_def, allocas_from_def] >>
     qpat_x_assum `allocas_from lo s` mp_tac >> simp[allocas_from_def]) >>
  `!op'. MEM op' [Lit (n2w skip); Var p] ==> op_taint tm op' = {}` by
    (gen_tac >> simp[] >> strip_tac >> gvs[op_taint_def]) >>
  `ptr_inst_ok D lo 0 ctx fn gm tm skipins sc` by
    (simp[Abbr `skipins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
      mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, Abbr `sk`, update_var_def] >>
     fs[allocas_from_def, op_taint_def] >>
     rpt strip_tac >>
     Cases_on `op' = Lit (n2w skip)` >> simp[] >>
     Cases_on `op' = Var p` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> offname` by
    (simp[Abbr `offname`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `4+
       (case bound_opt of NONE => 0 | SOME cap => 2)` mp_tac) >> simp[]) >>
  `offname <> "%" ++ toString (sa.cs_next_var+1) /\
   offname <> "%" ++ toString sa.cs_next_var` by simp[Abbr `offname`] >>
  `!x. x <> offname ==> FLOOKUP gk x = FLOOKUP gm x /\
    op_taint tk (Var x) = op_taint tm (Var x)` by
    simp[Abbr `gk`, Abbr `tk`, FLOOKUP_DRESTRICT,
      pred_setTheory.COMPL_DEF, op_taint_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 gk tk
      (sk with vs_inst_idx := 2) /\
   membership_loop_registers sa i 0w gk tk
      (sk with vs_inst_idx := 2)` by
    (conj_tac
     >- (simp[Abbr `sk`] >> irule membership_frame_scalar_update >>
         conj_tac >- (qpat_assum `!x. not_fresh_at sa x ==> x <> offname` ACCEPT_TAC) >>
         qexistsl_tac [`gm`, `tm`] >> simp[Abbr `tk`, Abbr `sc`] >> metis_tac[]) >>
     simp[Abbr `sk`] >> irule membership_registers_scalar_update >>
     simp[] >> qexistsl_tac [`gm`, `tm`] >> simp[Abbr `sc`]) >>
  qabbrev_tac `so = if 0 < skip then sk with vs_inst_idx := 2 else sc` >>
  qabbrev_tac `go = if 0 < skip then gk else gm` >>
  qabbrev_tac `to = if 0 < skip then tk else tm` >>
  qabbrev_tac `oname = if 0 < skip then offname else p` >>
  `membership_loop_frame sa G0 T0 s0 go to so /\
   membership_loop_registers sa i 0w go to so` by
    (Cases_on `0 < skip` >> simp[Abbr `so`, Abbr `go`, Abbr `to`]) >>
  `eval_operand (Var oname) so = SOME (n2w (skip+i*stride)) /\
   op_prov go (Var oname) = NONE /\ op_taint to (Var oname) = {}` by
    (Cases_on `0 < skip` >>
     simp[Abbr `so`, Abbr `go`, Abbr `to`, Abbr `oname`, Abbr `sk`,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `gk`, Abbr `tk`, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
       pred_setTheory.COMPL_DEF, wordsTheory.word_add_n2w, wordsTheory.word_mul_n2w] >>
     fs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def,
       wordsTheory.word_mul_n2w]) >>
  suspend "address_stage"
QED

Resume rest_word_membership_ctor_prefix_checked[address_stage]:
  `eval_operand arr so = SOME bw /\ op_prov go arr = NONE /\
   op_taint to arr = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  qabbrev_tac `aname = "%" ++ toString (sa.cs_next_var+4+q+delta)` >>
  qabbrev_tac `addins = mk_inst (sa.cs_next_id+7+
    (case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
    [arr; Var oname] [aname]` >>
  qabbrev_tac `ss = update_var aname (bw+n2w (skip+i*stride)) so` >>
  qabbrev_tac `ga = DRESTRICT go (COMPL {aname})` >>
  qabbrev_tac `ta = to with t_var := to.t_var |+ (aname,{})` >>
  `step_inst_base addins so = OK ss` by
    simp[Abbr `addins`, Abbr `ss`, membership_address_binop_step] >>
  `step_prov PG go addins ss = ga` by
    simp[Abbr `addins`, Abbr `ga`, step_prov_def, out_prov_def,
      set_prov_def, first_prov_def] >>
  `step_taint addins so ss to = ta` by
    (simp[Abbr `addins`, Abbr `ss`, Abbr `ta`] >>
     irule stmtAppendStorageRunPtrTheory.scalar_add_taint >> simp[update_var_def]) >>
  `allocas_from lo so` by
    (Cases_on `0 < skip` >>
     simp[Abbr `so`, Abbr `sk`, update_var_def, allocas_from_def] >>
     fs[allocas_from_def]) >>
  `ptr_inst_ok D lo 0 ctx fn go to addins so` by
    (simp[Abbr `addins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
      mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, Abbr `ss`, update_var_def] >>
     fs[allocas_from_def] >> gen_tac >>
     Cases_on `op' = arr` >> simp[] >>
     Cases_on `op' = Var oname` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> aname` by
    (simp[Abbr `aname`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `4+q+delta` mp_tac) >> simp[]) >>
  `aname <> "%" ++ toString (sa.cs_next_var+1) /\
   aname <> "%" ++ toString sa.cs_next_var` by simp[Abbr `aname`] >>
  `!x. x <> aname ==> FLOOKUP ga x = FLOOKUP go x /\
    op_taint ta (Var x) = op_taint to (Var x)` by
    simp[Abbr `ga`, Abbr `ta`, FLOOKUP_DRESTRICT,
      pred_setTheory.COMPL_DEF, op_taint_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 ga ta
      (ss with vs_inst_idx := 2+delta) /\
   membership_loop_registers sa i 0w ga ta
      (ss with vs_inst_idx := 2+delta)` by
    (conj_tac
     >- (simp[Abbr `ss`] >> irule membership_frame_scalar_update >>
         conj_tac >- (qpat_assum `!x. not_fresh_at sa x ==> x <> aname` ACCEPT_TAC) >>
         qexistsl_tac [`go`, `to`] >> simp[Abbr `ta`] >> metis_tac[]) >>
     simp[Abbr `ss`] >> irule membership_registers_scalar_update >>
     simp[] >> qexistsl_tac [`go`, `to`] >> simp[]) >>
  suspend "immutable_stage"
QED

Resume rest_word_membership_ctor_prefix_checked[immutable_stage]:
  qabbrev_tac `sx = ss with vs_inst_idx := 2+delta` >>
  qabbrev_tac `ib = case imm of NONE => Lit 0w | SOME v => v` >>
  `eval_operand ib sx = SOME 0w /\ op_prov ga ib = NONE /\
   op_taint ta ib = {}` by
    (`!x. ib = Var x ==> not_fresh_at sa x` by
       (Cases_on `imm` >> fs[Abbr `ib`]) >>
     `eval_operand ib sx = eval_operand ib s0 /\
      op_prov ga ib = op_prov G0 ib /\
      op_taint ta ib = op_taint T0 ib` by
       (irule membership_loop_frame_operand >> qexists_tac `sa` >> simp[Abbr `sx`]) >>
     Cases_on `imm` >> fs[Abbr `ib`, eval_operand_def, op_prov_def, op_taint_def]) >>
  qabbrev_tac `iname = "%" ++ toString (sa.cs_next_var+5+q+delta)` >>
  qabbrev_tac `immins = mk_inst (sa.cs_next_id+8+
    (case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
    [Var aname; ib] [iname]` >>
  `eval_operand (Var aname) sx = SOME (bw+n2w (skip+i*stride)) /\
   op_prov ga (Var aname) = NONE /\ op_taint ta (Var aname) = {}` by
    simp[Abbr `sx`, Abbr `ss`, Abbr `ga`, Abbr `ta`, eval_operand_def,
      lookup_var_def, update_var_def, op_prov_def, op_taint_def,
      FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, pred_setTheory.COMPL_DEF] >>
  qabbrev_tac `si = update_var iname (bw+n2w (skip+i*stride)) sx` >>
  qabbrev_tac `gi = DRESTRICT ga (COMPL {iname})` >>
  qabbrev_tac `ti = ta with t_var := ta.t_var |+ (iname,{})` >>
  `step_inst_base immins sx = OK si` by
    (`step_inst_base immins sx =
        OK (update_var iname ((bw+n2w (skip+i*stride))+0w) sx)` by
       (simp[Abbr `immins`] >> irule membership_address_binop_step >> simp[]) >>
     fs[Abbr `si`, wordsTheory.WORD_ADD_0]) >>
  `step_prov PG ga immins si = gi` by
    simp[Abbr `immins`, Abbr `gi`, step_prov_def, out_prov_def,
      set_prov_def, first_prov_def] >>
  `step_taint immins sx si ta = ti` by
    (simp[Abbr `immins`, Abbr `si`, Abbr `ti`] >>
     irule stmtAppendStorageRunPtrTheory.scalar_add_taint >> simp[update_var_def]) >>
  `allocas_from lo sx` by
    (simp[Abbr `sx`, Abbr `ss`, update_var_def, allocas_from_def] >>
     fs[allocas_from_def]) >>
  `ptr_inst_ok D lo 0 ctx fn ga ta immins sx` by
    (simp[Abbr `immins`, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def,
      mem_read_ops_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_pure2_def, eval_operands_def, Abbr `si`, update_var_def,
      wordsTheory.WORD_ADD_0] >>
     fs[allocas_from_def] >> gen_tac >>
     Cases_on `op' = Var aname` >> simp[] >>
     Cases_on `op' = ib` >> simp[]) >>
  `!x. not_fresh_at sa x ==> x <> iname` by
    (simp[Abbr `iname`, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `5+q+delta` mp_tac) >> simp[]) >>
  `iname <> "%" ++ toString (sa.cs_next_var+1) /\
   iname <> "%" ++ toString sa.cs_next_var` by simp[Abbr `iname`] >>
  `!x. x <> iname ==> FLOOKUP gi x = FLOOKUP ga x /\
    op_taint ti (Var x) = op_taint ta (Var x)` by
    simp[Abbr `gi`, Abbr `ti`, FLOOKUP_DRESTRICT,
      pred_setTheory.COMPL_DEF, op_taint_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 gi ti
      (si with vs_inst_idx := 3+delta) /\
   membership_loop_registers sa i 0w gi ti
      (si with vs_inst_idx := 3+delta)` by
    (conj_tac
     >- (simp[Abbr `si`] >> irule membership_frame_scalar_update >>
         conj_tac >- (qpat_assum `!x. not_fresh_at sa x ==> x <> iname` ACCEPT_TAC) >>
         qexistsl_tac [`ga`, `ta`] >> simp[Abbr `ti`] >> metis_tac[]) >>
     simp[Abbr `si`] >> irule membership_registers_scalar_update >>
     simp[] >> qexistsl_tac [`ga`, `ta`] >> simp[]) >>
  suspend "load_stage"
QED

Resume rest_word_membership_ctor_prefix_checked[load_stage]:
  qabbrev_tac `sl = if IS_SOME imm then si with vs_inst_idx := 3+delta else sx` >>
  qabbrev_tac `gl = if IS_SOME imm then gi else ga` >>
  qabbrev_tac `tl = if IS_SOME imm then ti else ta` >>
  qabbrev_tac `lname = if IS_SOME imm then iname else aname` >>
  `membership_loop_frame sa G0 T0 s0 gl tl sl /\
   membership_loop_registers sa i 0w gl tl sl` by
    (Cases_on `IS_SOME imm` >> gvs[Abbr `sl`, Abbr `gl`, Abbr `tl`]) >>
  `eval_operand (Var lname) sl = SOME (addr i) /\
   op_prov gl (Var lname) = NONE /\ op_taint tl (Var lname) = {}` by
    (Cases_on `IS_SOME imm`
     >- simp[Abbr `sl`, Abbr `gl`, Abbr `tl`, Abbr `lname`, Abbr `si`,
          Abbr `gi`, Abbr `ti`, eval_operand_def, lookup_var_def, update_var_def,
          op_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
          pred_setTheory.COMPL_DEF, arithmeticTheory.MULT_COMM] >>
     simp[Abbr `sl`, Abbr `gl`, Abbr `tl`, Abbr `lname`,
       arithmeticTheory.MULT_COMM]) >>
  `mem_word_taint tl.t_mem (w2n (addr i)) = {} /\
   mload (w2n (addr i)) sl = EL i ws` by
    (`tl.t_mem = T0.t_mem /\ sl.vs_memory = s0.vs_memory` by
       (qpat_assum `membership_loop_frame sa _ _ s0 gl tl sl` mp_tac >>
        rewrite_tac[membership_loop_frame_def] >> disch_then strip_assume_tac >>
        conj_tac >- simp[] >>
        qpat_x_assum `sl = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     simp[mload_def] >>
     qpat_x_assum `!j. j < LENGTH ws ==> _ /\ _ /\ _`
       (qspec_then `i` mp_tac) >>
     simp[mload_def, arithmeticTheory.MULT_COMM]) >>
  qabbrev_tac `loadins = mk_inst (sa.cs_next_id+8+
    (case bound_opt of NONE => 0 | SOME cap => 3)+delta+
    (if IS_SOME imm then 1 else 0)) ILOAD [Var lname] [dst]` >>
  qabbrev_tac `sv = update_var dst (EL i ws) sl` >>
  `mload (w2n (bw+n2w (skip+i*stride))) sl = EL i ws` by
    metis_tac[arithmeticTheory.MULT_COMM] >>
  `step_inst_base loadins sl = OK sv` by
    simp[Abbr `loadins`, Abbr `sv`, mk_inst_def,
      step_inst_base_opcode_eqs, exec_read1_def] >>
  qabbrev_tac `gv = DRESTRICT gl (COMPL {dst})` >>
  qabbrev_tac `tv = tl with t_var := tl.t_var |+ (dst,{})` >>
  `step_prov PG gl loadins sv = gv` by
    simp[Abbr `loadins`, Abbr `gv`, mk_inst_def, step_prov_def,
      out_prov_def, set_prov_def] >>
  `mem_word_taint tl.t_mem (w2n (bw+n2w (skip+i*stride))) = {}` by
    metis_tac[arithmeticTheory.MULT_COMM] >>
  `step_taint loadins sl sv tl = tv` by
    (simp[Abbr `loadins`, Abbr `tv`, mk_inst_def, step_taint_def,
      mem_taint_def, out_taint_def, set_var_taint_def, store_taint_def,
      adopt_reset_def, imm_taint_def, new_site_bytes_def, step_writes_def,
      written_taint_def, range_bytes_def, Abbr `sv`, update_var_def,
      source_memory_write_ranges_def, FLOOKUP_DEF, SF CONJ_ss,
      pred_setTheory.GSPEC_F, taint_component_equality]) >>
  `w2n (bw+n2w (skip+i*stride))+32 <= lo` by
    metis_tac[arithmeticTheory.MULT_COMM] >>
  `allocas_from lo sl` by
    (Cases_on `IS_SOME imm` >>
     simp[Abbr `sl`, Abbr `si`, update_var_def, allocas_from_def] >>
     fs[allocas_from_def]) >>
  `ptr_inst_ok D lo 0 ctx fn gl tl loadins sl` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
      Abbr `loadins`, mk_inst_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def] >>
     conj_tac >- simp[mem_read_ops_def] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_read1_def,
       update_var_def]) >>
  `!x. not_fresh_at sa x ==> x <> dst` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> first_x_assum (qspec_then `4+q+delta+width` mp_tac) >> simp[]) >>
  `dst <> "%" ++ toString (sa.cs_next_var+1) /\
   dst <> "%" ++ toString sa.cs_next_var` by
    (Cases_on `IS_SOME imm` >> Cases_on `0 < skip` >>
     Cases_on `bound_opt` >> simp[]) >>
  `!x. x <> dst ==> FLOOKUP gv x = FLOOKUP gl x /\
    op_taint tv (Var x) = op_taint tl (Var x)` by
    simp[Abbr `gv`, Abbr `tv`, FLOOKUP_DRESTRICT,
      pred_setTheory.COMPL_DEF, op_taint_def, FLOOKUP_UPDATE] >>
  `membership_loop_frame sa G0 T0 s0 gv tv
      (sv with vs_inst_idx := 2+delta+width) /\
   membership_loop_registers sa i 0w gv tv
      (sv with vs_inst_idx := 2+delta+width)` by
    (conj_tac
     >- (simp[Abbr `sv`] >> irule membership_frame_scalar_update >>
         conj_tac >- (qpat_assum `!x. not_fresh_at sa x ==> x <> dst` mp_tac >> simp[]) >>
         qexistsl_tac [`gl`, `tl`] >> simp[Abbr `tv`] >> metis_tac[]) >>
     simp[Abbr `sv`] >> irule membership_registers_scalar_update >>
     Cases_on `IS_SOME imm` >> Cases_on `0 < skip` >>
     Cases_on `bound_opt` >> simp[] >>
     qexistsl_tac [`gl`, `tl`] >> simp[]) >>
  suspend "spine"
QED

Resume rest_word_membership_ctor_prefix_checked[spine]:
  `code = [mulins] ++ (if 0 < skip then [skipins] else []) ++
     [addins] ++ (if IS_SOME imm then [immins] else []) ++ [loadins]` by
    (Cases_on `imm` >> Cases_on `0 < skip` >>
     simp[Abbr `mulins`, Abbr `p`, Abbr `skipins`, Abbr `addins`, Abbr `immins`,
       Abbr `loadins`, Abbr `ib`, Abbr `lname`, Abbr `aname`,
       Abbr `iname`, Abbr `oname`, Abbr `offname`]) >>
  `inst_seq_ptr D lo ctx fn PG Gs Ts code s gv tv` by
    (qpat_x_assum `code = _` (fn th => rewrite_tac[th]) >>
     Cases_on `0 < skip` >> Cases_on `IS_SOME imm` >>
     fs[Abbr `so`, Abbr `go`, Abbr `to`, Abbr `sl`, Abbr `gl`, Abbr `tl`,
       Abbr `sx`, Abbr `sc`] >>
     qpat_x_assum `delta = _` SUBST_ALL_TAC >>
     qpat_x_assum `width = _` SUBST_ALL_TAC >>
     fs[] >> simp[inst_seq_ptr_def]) >>
  `!j. step_inst_base skipins (sc with vs_inst_idx := j) =
        OK (sk with vs_inst_idx := j)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def,
      Abbr `skipins`, mk_inst_def, is_terminator_def] >>
  `!j. step_inst_base addins (so with vs_inst_idx := j) =
        OK (ss with vs_inst_idx := j)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def,
      Abbr `addins`, mk_inst_def, is_terminator_def] >>
  `!j. step_inst_base immins (sx with vs_inst_idx := j) =
        OK (si with vs_inst_idx := j)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def,
      Abbr `immins`, mk_inst_def, is_terminator_def] >>
  `!j. step_inst_base loadins (sl with vs_inst_idx := j) =
        OK (sv with vs_inst_idx := j)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, instIdxIndepTheory.exec_result_map_def,
      Abbr `loadins`, mk_inst_def, is_terminator_def] >>
  `sv with vs_inst_idx := 0 = u` by
    (qpat_x_assum `run_inst_seq code s = OK u` mp_tac >>
     qpat_x_assum `code = _` (fn th => rewrite_tac[th]) >>
     Cases_on `0 < skip` >> Cases_on `IS_SOME imm` >>
     fs[Abbr `so`, Abbr `sl`, Abbr `sx`, Abbr `sc`] >>
     `sm with vs_inst_idx := 0 = sm` by
       (simp[Abbr `sm`, update_var_def, venom_state_component_equality]) >>
     qpat_assum `!j. step_inst_base skipins _ = _` (qspec_then `0` assume_tac) >>
     qpat_assum `!j. step_inst_base addins _ = _` (qspec_then `0` assume_tac) >>
     qpat_assum `!j. step_inst_base immins _ = _` (qspec_then `0` assume_tac) >>
     qpat_assum `!j. step_inst_base loadins _ = _` (qspec_then `0` assume_tac) >>
     qpat_assum `sm with vs_inst_idx := 0 = sm`
       (fn eq =>
         (qpat_x_assum `step_inst_base skipins (sm with vs_inst_idx := 0) = _`
            (assume_tac o PURE_REWRITE_RULE [eq]) >>
          qpat_x_assum `step_inst_base addins (_ with vs_inst_idx := 0) = _`
            (assume_tac o PURE_REWRITE_RULE [eq]))) >>
     simp[exprLoweringPropsTheory.run_inst_seq_def]) >>
  qexistsl_tac [`gv`, `tv`] >>
  qpat_x_assum `sv with vs_inst_idx := 0 = u` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- REFL_TAC >>
  conj_tac >-
    (Cases_on `0 < skip` >> Cases_on `IS_SOME imm` >>
     simp[Abbr `gv`, Abbr `gl`, Abbr `gi`, Abbr `ga`, Abbr `go`,
       Abbr `gk`, Abbr `gm`, Abbr `p`, Abbr `offname`, Abbr `aname`, Abbr `iname`,
       pred_setTheory.INTER_ASSOC]) >>
  conj_tac >-
    (Cases_on `0 < skip` >> Cases_on `IS_SOME imm` >>
     simp[Abbr `tv`, Abbr `tl`, Abbr `ti`, Abbr `ta`, Abbr `to`,
       Abbr `tk`, Abbr `tm`, Abbr `p`, Abbr `offname`, Abbr `aname`, Abbr `iname`,
       taint_component_equality]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `membership_loop_frame _ _ _ _ gv tv _` mp_tac >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `membership_loop_registers _ _ _ gv tv _` mp_tac >> simp[]) >>
  simp[Abbr `sv`, update_var_def, allocas_from_def,
    eval_operand_def, lookup_var_def, Abbr `gv`, Abbr `tv`,
    op_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
    pred_setTheory.COMPL_DEF] >>
  simp[Abbr `sl`, Abbr `si`, Abbr `sx`, Abbr `ss`, Abbr `so`,
    Abbr `sk`, Abbr `sc`, Abbr `sm`, update_var_def] >>
  Cases_on `IS_SOME imm` >> Cases_on `0 < skip` >>
  simp[update_var_def, allocas_from_def] >>
  qpat_assum `allocas_from lo s` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])
QED

Finalise rest_word_membership_ctor_prefix_checked


Theorem rest_word_membership_ctor_load_joint_indexed:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load T imm LocCode) bound_opt is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  (!ib x. imm = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
  q = (case bound_opt of NONE => 0 | SOME cap => 2) /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if IS_SOME imm then 2 else 1) /\
  dst = "%" ++ toString (sa.cs_next_var+4+q+delta+width) /\
  (!i. addr i = bw + n2w (skip+stride*i)) /\
  (!H:'h. guard H ==>
    ~s0.vs_halted /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
    eval_operand arr s0 = SOME bw /\ op_prov (G0 H) arr = NONE /\
    op_taint (T0 H) arr = {} /\
    (!ib. imm = SOME ib ==>
      eval_operand ib s0 = SOME 0w /\ op_prov (G0 H) ib = NONE /\
      op_taint (T0 H) ib = {}) /\
    (!i. i < LENGTH ws ==>
      w2n (addr i) + 32 <= lo /\
      mem_word_taint (T0 H).t_mem (w2n (addr i)) = {} /\
      mload (w2n (addr i)) s0 = EL i ws)) ==>
  !i s Gs Ts. i < LENGTH ws /\
    (!H:'h. guard H ==>
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gs H) (Ts H) s /\
      membership_loop_registers sa i 0w (Gs H) (Ts H) s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs H,Ts H) [] (OK t,Gt H,Tt H) /\
      membership_loop_frame sa (G0 H) (T0 H) s0 (Gt H) (Tt H) t /\
      membership_loop_registers sa i 0w (Gt H) (Tt H) t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+delta+width /\
      eval_operand (Var dst) t = SOME (EL i ws) /\
      op_prov (Gt H) (Var dst) = NONE /\
      op_taint (Tt H) (Var dst) = {}
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all rest_word_membership_ctor_body_prefix >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bb.bb_instructions` >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta+width | _ => s` >>
  simp[GSYM SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] >>
  gen_tac >> Cases_on `guard H` >> simp[] >>
  qpat_x_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!H. guard H ==> ~s0.vs_halted /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `code = [mk_inst (sa.cs_next_id+6+(case bound_opt of NONE => 0 | SOME cap => 3)) MUL
    [Var ("%" ++ toString (sa.cs_next_var+1)); Lit (n2w stride)]
    ["%" ++ toString (sa.cs_next_var+3+q)]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)) ADD
      [Lit (n2w skip); Var ("%" ++ toString (sa.cs_next_var+3+q))]
      ["%" ++ toString (sa.cs_next_var+4+q)]] else []) ++
    [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
      [arr; Var (if 0 < skip then "%" ++ toString (sa.cs_next_var+4+q)
                 else "%" ++ toString (sa.cs_next_var+3+q))]
      ["%" ++ toString (sa.cs_next_var+4+q+delta)]] ++
    (case imm of NONE =>
      [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ILOAD
        [Var ("%" ++ toString (sa.cs_next_var+4+q+delta))] [dst]]
    | SOME ib =>
      [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
        [Var ("%" ++ toString (sa.cs_next_var+4+q+delta));ib]
        ["%" ++ toString (sa.cs_next_var+5+q+delta)];
       mk_inst (sa.cs_next_id+9+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ILOAD
        [Var ("%" ++ toString (sa.cs_next_var+5+q+delta))] [dst]])` by
    (Cases_on `0 < skip` >> simp[Abbr `code`]) >>
  `!j. j < LENGTH ws ==> w2n (addr j)+32 <= lo /\
    mem_word_taint (T0 H).t_mem (w2n (addr j)) = {} /\
    mload (w2n (addr j)) s0 = EL j ws` by simp[] >>
  drule_all rest_word_membership_ctor_prefix_checked >>
  disch_then (qspecl_then [`PG`, `DF H`] strip_assume_tac) >>
  qexistsl_tac [`g`, `tn`] >> simp[] >>
  conj_tac
  >- (`LENGTH code = 2+delta+width /\
       EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) code /\
       FILTER (\ins. ins.inst_opcode = GAS) code = []` by
        (Cases_on `imm` >> Cases_on `0 < skip` >>
         simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
        (conj_tac >- simp[] >>
         qpat_assum `s.vs_inst_idx = 0` (fn th => pure_rewrite_tac[th, DROP_0]) >>
         first_assum ACCEPT_TAC) >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  gvs[eval_operand_def, lookup_var_def, allocas_from_def] >>
  qpat_assum `!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==> lo <= b` ACCEPT_TAC
QED

Theorem rest_word_membership_ctor_load_joint_const:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load T imm LocCode) bound_opt is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr = Var x ==> not_fresh_at sa x) /\
  (!ib x. imm = SOME ib /\ ib = Var x ==> not_fresh_at sa x) /\
  q = (case bound_opt of NONE => 0 | SOME cap => 2) /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if IS_SOME imm then 2 else 1) /\
  dst = "%" ++ toString (sa.cs_next_var+4+q+delta+width) /\
  (!i. addr i = bw + n2w (skip+stride*i)) /\
  (!H:'h. guard H ==>
    ~s0.vs_halted /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
    eval_operand arr s0 = SOME bw /\ op_prov G0 arr = NONE /\
    op_taint T0 arr = {} /\
    (!ib. imm = SOME ib ==>
      eval_operand ib s0 = SOME 0w /\ op_prov G0 ib = NONE /\
      op_taint T0 ib = {}) /\
    (!i. i < LENGTH ws ==>
      w2n (addr i) + 32 <= lo /\
      mem_word_taint T0.t_mem (w2n (addr i)) = {} /\
      mload (w2n (addr i)) s0 = EL i ws)) ==>
  !i s Gs Ts. i < LENGTH ws /\
    (!H:'h. guard H ==>
      membership_loop_frame sa G0 T0 s0 Gs Ts s /\
      membership_loop_registers sa i 0w Gs Ts s /\
      ~s.vs_halted /\ allocas_from lo s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0) ==>
    ?t Gt Tt. !H:'h. guard H ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
        (s,Gs,Ts) [] (OK t,Gt,Tt) /\
      membership_loop_frame sa G0 T0 s0 Gt Tt t /\
      membership_loop_registers sa i 0w Gt Tt t /\
      ~t.vs_halted /\ allocas_from lo t /\
      t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      t.vs_inst_idx = 2+delta+width /\
      eval_operand (Var dst) t = SOME (EL i ws) /\
      op_prov Gt (Var dst) = NONE /\ op_taint Tt (Var dst) = {}
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all rest_word_membership_ctor_body_prefix >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bb.bb_instructions` >>
  qexists_tac `case run_inst_seq code s of
    OK u => u with vs_inst_idx := 2+delta+width | _ => s` >>
  qexistsl_tac [
    `FOLDL (\g x. DRESTRICT g (COMPL {x})) Gs
      (["%" ++ toString (sa.cs_next_var+3+q)] ++
       (if 0 < skip then ["%" ++ toString (sa.cs_next_var+4+q)] else []) ++
       ["%" ++ toString (sa.cs_next_var+4+q+delta)] ++
       (if IS_SOME imm then ["%" ++ toString (sa.cs_next_var+5+q+delta)] else []) ++
       [dst])`,
    `Ts with t_var := FOLDL (\m x. m |+ (x,{})) Ts.t_var
      (["%" ++ toString (sa.cs_next_var+3+q)] ++
       (if 0 < skip then ["%" ++ toString (sa.cs_next_var+4+q)] else []) ++
       ["%" ++ toString (sa.cs_next_var+4+q+delta)] ++
       (if IS_SOME imm then ["%" ++ toString (sa.cs_next_var+5+q+delta)] else []) ++
       [dst])`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. guard H ==> membership_loop_frame _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!H. guard H ==> ~s0.vs_halted /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `code = [mk_inst (sa.cs_next_id+6+(case bound_opt of NONE => 0 | SOME cap => 3)) MUL
    [Var ("%" ++ toString (sa.cs_next_var+1)); Lit (n2w stride)]
    ["%" ++ toString (sa.cs_next_var+3+q)]] ++
    (if 0 < skip then [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)) ADD
      [Lit (n2w skip); Var ("%" ++ toString (sa.cs_next_var+3+q))]
      ["%" ++ toString (sa.cs_next_var+4+q)]] else []) ++
    [mk_inst (sa.cs_next_id+7+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
      [arr; Var (if 0 < skip then "%" ++ toString (sa.cs_next_var+4+q)
                 else "%" ++ toString (sa.cs_next_var+3+q))]
      ["%" ++ toString (sa.cs_next_var+4+q+delta)]] ++
    (case imm of NONE =>
      [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ILOAD
        [Var ("%" ++ toString (sa.cs_next_var+4+q+delta))] [dst]]
    | SOME ib =>
      [mk_inst (sa.cs_next_id+8+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ADD
        [Var ("%" ++ toString (sa.cs_next_var+4+q+delta));ib]
        ["%" ++ toString (sa.cs_next_var+5+q+delta)];
       mk_inst (sa.cs_next_id+9+(case bound_opt of NONE => 0 | SOME cap => 3)+delta) ILOAD
        [Var ("%" ++ toString (sa.cs_next_var+5+q+delta))] [dst]])` by
    (Cases_on `0 < skip` >> simp[Abbr `code`]) >>
  `!j. j < LENGTH ws ==> w2n (addr j)+32 <= lo /\
    mem_word_taint T0.t_mem (w2n (addr j)) = {} /\
    mload (w2n (addr j)) s0 = EL j ws` by simp[] >>
  drule_all rest_word_membership_ctor_prefix_checked >>
  disch_then (qspecl_then [`PG`, `DF H`] strip_assume_tac) >>
  simp[] >>
  conj_tac
  >- (`LENGTH code = 2+delta+width /\
       EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode) code /\
       FILTER (\ins. ins.inst_opcode = GAS) code = []` by
        (Cases_on `imm` >> Cases_on `0 < skip` >>
         simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
      `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
        (conj_tac >- simp[] >>
         qpat_assum `s.vs_inst_idx = 0` (fn th => pure_rewrite_tac[th, DROP_0]) >>
         first_assum ACCEPT_TAC) >>
      drule_all run_inst_seq_gas_origin_ptr_path >> simp[]) >>
  gvs[eval_operand_def, lookup_var_def, allocas_from_def] >>
  qpat_assum `!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==> lo <= b` ACCEPT_TAC
QED
