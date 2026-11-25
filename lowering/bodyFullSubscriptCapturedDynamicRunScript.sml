(* Counted suffix for a captured dynamic array in memory. *)
Theory bodyFullSubscriptCapturedDynamicRun
Ancestors
  bodyFullTargetArraySuffix bodyFullTargetArrayLoad fragGasOriginPtrDead
  fragGasOriginPtrLoop exprSimSubscriptArraySuffix bodyBinopFragMemory
  exprLowering exprLoweringProps exprSimArrayIndex freshWrites fragExec
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics ptrDiscipline memLocDefs contextCodegenRel codegenRel
  unitTransformDefs loweringStateRelDefs finite_map rich_list words
  typedCopyLayoutPtr exprSimSubscriptArraySource stmtReasonLitFragMemory
  abiDecodeStaticProps overflowElimHelpers

(* Expose the load, bounds check, and address calculation at their actual
   emitted code cuts. No feasibility hypothesis about the source index. *)
Theorem captured_dynamic_emission_cut[local]:
  compile_array_subscript bop iop T cnt ws esz sgn (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn ==>
  ?len sl sc. emit_op MLOAD [bop] sn = (len,sl) /\
    array_bounds_check iop len sgn sl = ((),sc) /\
    array_elem_ptr bop iop T ws esz sc = (dst,sb) /\
    same_blocks sn sl /\ same_blocks sl sc /\ same_blocks sc sb /\
    sl.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sl /\
    sc.cs_current_insts = sl.cs_current_insts ++ emitted_insts sl sc /\
    sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
    fn_has_code sn sl fn /\ fn_has_code sl sc fn /\ fn_has_code sc sb fn /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sl sc) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
    EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sb)
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sl = (unit,sc)` >>
  Cases_on `unit` >> gvs[] >>
  drule_then strip_assume_tac emit_op_extends >>
  `EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sl)` by
    (drule_then strip_assume_tac emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `same_blocks sl sc /\
   sc.cs_current_insts = sl.cs_current_insts ++ emitted_insts sl sc /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sl sc) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sl sc)` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     simp[array_bounds_valid_def, comp_bind_def] >>
     Cases_on `sgn` >> simp[comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2, APPEND_ASSOC, mk_inst_def, is_terminator_def]) >>
  `same_blocks sc sb /\
   sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sc sb)` by
    (qpat_x_assum `sc.cs_current_insts = sl.cs_current_insts ++ _` kall_tac >>
     qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     simp[array_elem_ptr_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, DROP_APPEND2, APPEND_ASSOC, mk_inst_def, is_terminator_def]) >>
  `cs_extends sn sl /\ cs_extends sl sc /\ cs_extends sc sb` by
    fs[cs_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  `cs_extends sl sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sn sl fn /\ fn_has_code sl sb fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code sl sc fn /\ fn_has_code sc sb fn` by metis_tac[fn_has_code_split] >>
  `emitted_insts sn sc = emitted_insts sn sl ++ emitted_insts sl sc` by
    metis_tac[emitted_insts_append] >>
  `sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc` by
    simp[APPEND_ASSOC] >>
  `emitted_insts sn sb = emitted_insts sn sc ++ emitted_insts sc sb` by
    metis_tac[emitted_insts_append] >>
  simp[listTheory.EVERY_APPEND]
QED

(* Only the current header word is read, from its retained provenance row. *)
Theorem captured_dynamic_load_safety[local]:
  emit_op MLOAD [bop] sn = (Var out,sl) /\
  eval_operand bop u = SOME a /\ op_prov G bop = SOME (pbase,sz) /\
  pbase <= w2n a /\ w2n a + 32 <= pbase + sz /\
  w2n a + 32 <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) ==>
  array_length_step_ok lo ctx fn MLOAD [bop] (mload (w2n a) u)
    sn out sl u G tn /\
  op_prov (step_prov PG G (mk_inst sn.cs_next_id MLOAD [bop] [out])
    (update_var out (mload (w2n a) u) u)) (Var out) = NONE /\
  op_taint (step_taint (mk_inst sn.cs_next_id MLOAD [bop] [out]) u
    (update_var out (mload (w2n a) u) u) tn) (Var out) = {}
Proof
  strip_tac >> conj_tac
  >- (simp[array_length_step_ok_def] >>
      rpt conj_tac
      >- simp[mk_inst_def, step_inst_base_def, exec_read1_def]
      >- (Cases_on `bop` >>
          gvs[mk_inst_def, access_ok_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, op_prov_def, mem_read_ops_def,
              mem_write_ops_def] >> metis_tac[])
      >- simp[mk_inst_def, taint_ok_def, mem_taint_def, mem_read_ops_def,
              mem_write_ops_def]
      >> simp[mk_inst_def, inst_mem_below_frontier_def,
              source_memory_read_ranges_def, source_memory_write_ranges_def])
  >> conj_tac
  >- simp[op_prov_def, step_prov_def, mk_inst_def, set_prov_def,
          out_prov_def, FLOOKUP_DRESTRICT]
  >> simp[op_taint_def, step_taint_def, mk_inst_def, set_var_taint_def,
          FLOOKUP_UPDATE, mem_taint_def, mem_read_ops_def, mem_write_ops_def,
          out_taint_def] >>
  Cases_on `bop` >> gvs[op_taint_def]
QED

(* The concrete loader packet fixes the load endpoint independently of D. *)
Theorem captured_dynamic_load[local]:
  emit_op MLOAD [bop] sn = (len,sl) /\ fn_has_code sn sl fn /\
  eval_operand bop u = SOME a /\ op_prov G bop = SOME (pbase,sz) /\
  pbase <= w2n a /\ w2n a + 32 <= pbase + sz /\
  w2n a + 32 <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ mem_word_taint tn.t_mem (w2n a) = {} /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?ul Gl tl.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) [] (OK ul,Gl,tl)) /\
    eval_operand len ul = SOME (mload (w2n a) u) /\
    op_prov Gl len = NONE /\ op_taint tl len = {} /\
    (!x. len = Var x ==> not_fresh_at sl x) /\
    sn.cs_next_var <= sl.cs_next_var /\
    ~ul.vs_halted /\ ul.vs_current_bb = sl.cs_current_bb /\
    ul.vs_inst_idx = LENGTH sl.cs_current_insts /\
    array_length_frame sn u G tn ul Gl tl /\
    (?raw. run_inst_seq (emitted_insts sn sl) u = OK raw /\
           ul = raw with vs_inst_idx := LENGTH sl.cs_current_insts)
Proof
  strip_tac >>
  drule_then strip_assume_tac emitted_insts_emit_op >>
  qabbrev_tac `out = STRING #"%" (toString sn.cs_next_var)` >>
  qpat_x_assum `len = Var out` SUBST_ALL_TAC >>
  drule_then strip_assume_tac emit_op_extends >>
  drule_all_then strip_assume_tac captured_dynamic_load_safety >>
  `?ul Gl tl. array_length_loader_ok F NONE LocMemory bop (mload (w2n a) u)
      sn (Var out) sl lo ctx fn PG u G tn ul Gl tl` by
    (simp[array_length_loader_ok_def, compile_ptr_load_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`dyn` |-> `T`, `ctor` |-> `F`, `imm` |-> `NONE`,
                  `loc` |-> `LocMemory`, `sa` |-> `sn`, `sb` |-> `sl`,
                  `p` |-> `Var out`, `s` |-> `u`, `func` |-> `fn`,
                  `w` |-> `mload (w2n (a:bytes32)) u`,
                  `D` |-> `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
                 array_length_joint) >>
  simp[compile_ptr_load_def] >>
  (impl_tac >- (qexistsl [`ul`,`Gl`,`tl`] >> simp[])) >> strip_tac >>
  `not_fresh_at sl out` by simp[not_fresh_at_def, Abbr `out`, ASCIInumbersTheory.toString_inj] >>
  qexistsl [`t`,`G'`,`tn'`] >> simp[] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_from_no_dead] >>
  qpat_x_assum `array_length_loader_ok F NONE LocMemory _ _ _ _ _ _ _ _ _ _ _ _ t G' tn'` mp_tac >>
  simp[array_length_loader_ok_def, compile_ptr_load_def] >>
  disch_then (qx_choose_then `opc`
    (CONJUNCTS_THEN2 (fn th => assume_tac (Q.AP_THM th `sn`))
      (CONJUNCTS_THEN2 kall_tac strip_assume_tac))) >>
  `opc = MLOAD` by
    (`emit_op opc [bop] sn = (Var out,sl)` by metis_tac[] >>
     qpat_assum `emit_op opc [bop] sn = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[mk_inst_def]) >>
  qpat_x_assum `opc = MLOAD` SUBST_ALL_TAC >>
  qpat_assum `!fn PG. _` (qspecl_then [`fn`,`PG`] mp_tac) >>
  simp[run_inst_seq_def] >>
  fs[array_length_step_ok_def]
QED

(* The scalar observation is made inside the scalar runner's existential,
   so it refers to the very same state and ghosts as its semantic facts. *)
Definition captured_dynamic_scalar_rule_def:
  captured_dynamic_scalar_rule tail_obs <=>
  !idx len sgn sa sc bop esz p sb s b iw nw tn G lo ctx fn explicit PG.
    array_bounds_check idx len sgn sa = ((),sc) /\
    array_elem_ptr bop idx T 32 esz sc = (p,sb) /\
    eval_operand bop s = SOME b /\ eval_operand idx s = SOME iw /\
    eval_operand len s = SOME nw /\
    (!x. bop = Var x ==> not_fresh_at sa x) /\
    (!x. idx = Var x ==> not_fresh_at sa x) /\
    (!x. len = Var x ==> not_fresh_at sa x) /\
    op_taint tn bop = {} /\ op_taint tn idx = {} /\ op_taint tn len = {} /\
    op_prov G idx = NONE /\ op_prov G len = NONE /\
    allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    same_blocks sa sc /\ same_blocks sc sb /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
    fn_has_code sa sc fn /\ fn_has_code sc sb fn /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sa sc) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t H tm.
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
        (if idx_in_range sgn iw nw then OK t else Abort Revert_abort t,H,tm)) /\
      tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
      tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        FLOOKUP H x = FLOOKUP G x /\ FLOOKUP tm.t_var x = FLOOKUP tn.t_var x /\
        FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x) /\
      (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) =
        (if idx_in_range sgn iw nw then s else revert_state (set_returndata [] s)) /\
      (idx_in_range sgn iw nw ==>
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        eval_operand p t = SOME (b + 32w + iw * n2w esz) /\
        op_prov H p = op_prov G bop /\ op_taint tm p = {}) /\
      tail_obs sa sc sb (idx_in_range sgn iw nw) (s,G,tn) (t,H,tm)
End

Theorem captured_dynamic_scalar_rule_trivial:
  captured_dynamic_scalar_rule (\_ _ _ _ _ _. T)
Proof
  simp[captured_dynamic_scalar_rule_def] >> rpt gen_tac >> strip_tac >>
  drule_all (Q.INST [`dyn` |-> `T`] array_tail_scalar_uniform) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`t`,`H`,`tm`] >> simp[] >>
  qpat_assum `s.vs_inst_idx = _` (once_rewrite_tac o single o GSYM) >>
  first_assum ACCEPT_TAC
QED

(* The installed MLOAD ends at ul; the scalar run starts at that state,
   with its actual length operand and without guessing the check result. *)
Definition captured_dynamic_itinerary_def:
  captured_dynamic_itinerary tail_obs fn bop iop dst esz sgn iw nw sn sb
      (u,G,tn) (q,H,tm) <=>
    ?len sl sc raw ul Gl tl.
      emit_op MLOAD [bop] sn = (len,sl) /\
      array_bounds_check iop len sgn sl = ((),sc) /\
      array_elem_ptr bop iop T 32 esz sc = (dst,sb) /\
      same_blocks sn sl /\ same_blocks sl sc /\ same_blocks sc sb /\
      sl.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sl /\
      sc.cs_current_insts = sl.cs_current_insts ++ emitted_insts sl sc /\
      sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
      fn_has_code sn sl fn /\ fn_has_code sl sc fn /\ fn_has_code sc sb fn /\
      run_inst_seq (emitted_insts sn sl) u = OK raw /\
      ul = raw with vs_inst_idx := LENGTH sl.cs_current_insts /\
      eval_operand len ul = SOME nw /\
      array_length_frame sn u G tn ul Gl tl /\
      tail_obs sl sc sb (idx_in_range sgn iw nw) (ul,Gl,tl) (q,H,tm)
End

(* The frame at the original compiler cut survives both readonly stages. *)
Theorem captured_dynamic_scalar_run[local]:
  captured_dynamic_scalar_rule tail_obs /\
  compile_array_subscript bop iop T cnt 32 esz sgn (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  op_prov G bop = SOME (pbase,sz) /\ op_prov G iop = NONE /\
  pbase <= w2n a /\ w2n a + 32 <= pbase + sz /\
  w2n a + 32 <= u.vs_alloca_next /\ mload (w2n a) u = nw /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?q H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw nw then OK q else Abort Revert_abort q,H,tm)) /\
    EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sb) /\
    same_blocks sn sb /\
    sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
    captured_dynamic_itinerary tail_obs fn bop iop dst esz sgn iw nw sn sb
      (u,G,tn) (q,H,tm) /\
    (idx_in_range sgn iw nw ==>
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      eval_operand dst q = SOME (a + 32w + iw * n2w esz) /\
      op_prov H dst = SOME (pbase,sz) /\ op_taint tm dst = {} /\
      array_length_frame sn u G tn q H tm)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac captured_dynamic_emission_cut >>
  drule_all captured_dynamic_load >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `eval_operand bop ul = SOME a /\ eval_operand iop ul = SOME iw /\
   op_prov Gl bop = SOME (pbase,sz) /\ op_prov Gl iop = NONE /\
   op_taint tl bop = {} /\ op_taint tl iop = {}` by
    (Cases_on `bop` >> Cases_on `iop` >>
     gvs[array_length_frame_def, eval_operand_def, op_prov_def, op_taint_def] >>
     qpat_x_assum `ul with <|vs_vars := _; vs_inst_idx := _|> = u` mp_tac >> simp[venom_state_component_equality]) >>
  `(!x. bop = Var x ==> not_fresh_at sl x) /\
   (!x. iop = Var x ==> not_fresh_at sl x)` by metis_tac[not_fresh_at_mono] >>
  `ul.vs_allocas = u.vs_allocas` by
    (qpat_assum `array_length_frame sn u G tn ul Gl tl`
       (mp_tac o Q.AP_TERM `(\s:venom_state. s.vs_allocas)` o CONJUNCT1 o REWRITE_RULE [array_length_frame_def]) >>
     simp[]) >>
  `allocas_from lo ul` by (simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  `eval_operand len ul = SOME nw` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ul` by
    (qpat_assum `array_length_frame _ u _ _ ul _ _`
       (strip_assume_tac o SRULE [] o Q.AP_TERM `\st. (st.vs_allocas, st.vs_initial_fmp, st.vs_fmp)` o
        cj 1 o REWRITE_RULE [array_length_frame_def]) >>
     strip_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` drule >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  qpat_x_assum `captured_dynamic_scalar_rule tail_obs`
    (drule_all o REWRITE_RULE [captured_dynamic_scalar_rule_def]) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `captured_dynamic_itinerary tail_obs fn bop iop dst esz sgn iw nw sn sb
      (u,G,tn) (t,H,tm)` by
    (pure_rewrite_tac[captured_dynamic_itinerary_def] >>
     qexistsl [`len`,`sl`,`sc`,`raw`,`ul`,`Gl`,`tl`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `same_blocks sn sb /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb` by
    (`emitted_insts sn sc = emitted_insts sn sl ++ emitted_insts sl sc` by
       metis_tac[emitted_insts_append] >>
     `sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc` by simp[APPEND_ASSOC] >>
     `emitted_insts sn sb = emitted_insts sn sc ++ emitted_insts sc sb` by
       metis_tac[emitted_insts_append] >>
     fs[same_blocks_def, APPEND_ASSOC]) >>
  qexistsl [`t`,`H`,`tm`] >> simp[] >>
  conj_tac >- metis_tac[gas_origin_ptr_path_trans] >>
  strip_tac >>
  fs[array_length_frame_def, lookup_var_def] >>
  conj_tac
  >- gvs[venom_state_component_equality] >>
  rpt strip_tac >>
  `not_fresh_at sl x` by metis_tac[not_fresh_at_mono] >>
  qpat_assum `!y. not_fresh_at sl y ==> _` (qspec_then `x` mp_tac) >>
  qpat_assum `!y. not_fresh_at sn y ==> _` (qspec_then `x` mp_tac) >>
  simp[] >> metis_tac[]
QED

(* The scalar test and source selection agree even at length zero. *)
Theorem captured_dynamic_selection[local]:
  LENGTH vs < dimword (:256) /\ i = (if sgn then w2i iw else &(w2n iw)) ==>
  (if idx_in_range sgn iw (n2w (LENGTH vs)) then
     0 <= i /\ Num i < LENGTH vs /\ iw = n2w (Num i) /\
     evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
       [ValueSubscript (IntV i)] = INL (EL (Num i) vs)
   else
     evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
       [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index"))
Proof
  strip_tac >>
  `idx_in_range sgn iw (n2w (LENGTH vs)) <=> 0 <= i /\ i < &(LENGTH vs)` by
    (drule idx_in_range_integer >>
     disch_then (qspecl_then [`iw`,`sgn`] mp_tac) >> simp[]) >>
  `0 <= i ==> (Num i < LENGTH vs <=> i < &(LENGTH vs))` by
    (rpt (pop_assum kall_tac) >> intLib.COOPER_TAC) >>
  `0 <= i ==> iw = n2w (Num i)` by
    (Cases_on `sgn` >> fs[] >>
     disch_then (mp_tac o MATCH_MP overflowElimHelpersTheory.nonneg_w2i_eq_w2n) >>
     disch_then (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  Cases_on `idx_in_range sgn iw (n2w (LENGTH vs))`
  >- (`0 <= i /\ i < &(LENGTH vs)` by metis_tac[] >>
      simp[evaluate_array_subscript_result, vyperValueOperationTheory.array_index_def,
           listTheory.oEL_THM, IgnAsm `i = if _ then _ else _`]) >>
  Cases_on `0 <= i` >>
  simp[evaluate_array_subscript_result, vyperValueOperationTheory.array_index_def,
       listTheory.oEL_THM, IgnAsm `i = if _ then _ else _`] >>
  `~(i < &(LENGTH vs))` by metis_tac[] >>
  simp[IgnAsm `i = if _ then _ else _`]
QED

(* The compiler interval contains no allocations, and the successful
   endpoint differs only in its cursor and fresh registers. *)
Theorem captured_dynamic_history[local]:
  fn_has_code sn sb fn /\ same_blocks sn sb /\
  sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
  EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sb) /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn u /\
  array_length_frame sn u G tn q H tm ==>
  alloca_history fn q
Proof
  strip_tac >>
  `q.vs_allocas = u.vs_allocas /\ q.vs_current_bb = u.vs_current_bb` by
    (qpat_assum `array_length_frame sn u G tn q H tm`
      (mp_tac o CONJUNCT1 o REWRITE_RULE [array_length_frame_def]) >>
     simp[venom_state_component_equality]) >>
  `sb.cs_current_bb = sn.cs_current_bb` by fs[same_blocks_def] >>
  drule_all_then strip_assume_tac fn_has_code_code >>
  fs[IS_PREFIX_APPEND] >>
  `q.vs_inst_idx = u.vs_inst_idx + LENGTH (emitted_insts sn sb)` by simp[] >>
  `alloca_history fn (q with vs_inst_idx := q.vs_inst_idx)` suffices_by simp[] >>
  qpat_assum `q.vs_inst_idx = u.vs_inst_idx + _` SUBST1_TAC >>
  irule alloca_history_no_alloca_slice >> simp[] >> qexistsl [`bb`,`l`] >> simp[]
QED

(* This suffix uses the retained representation, whether the caller
   obtained it by reading a popped place or by keeping an owned value. *)
Theorem subscript_captured_dynamic_execution_observed:
  captured_dynamic_scalar_rule tail_obs /\
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv) sgn
    (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (pbase,sz) /\ op_prov G iop = NONE /\
  pbase <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= pbase + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + 32 <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?q H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw (n2w (LENGTH vs)) then OK q else Abort Revert_abort q,H,tm)) /\
    captured_dynamic_itinerary tail_obs fn bop iop dst (type_memory_size tv) sgn iw
      (n2w (LENGTH vs)) sn sb (u,G,tn) (q,H,tm) /\
    (if idx_in_range sgn iw (n2w (LENGTH vs)) then
       0 <= i /\ Num i < LENGTH vs /\
       evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
         [ValueSubscript (IntV i)] = INL (EL (Num i) vs) /\
       value_has_type tv (EL (Num i) vs) /\
       ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
       q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
       eval_operand dst q = SOME (a + 32w + iw * n2w (type_memory_size tv)) /\
       w2n (a + 32w + iw * n2w (type_memory_size tv)) =
         w2n a + 32 + Num i * type_memory_size tv /\
       op_prov H dst = SOME (pbase,sz) /\ op_taint tm dst = {} /\
       w2n a + 32 + Num i * type_memory_size tv + type_memory_size tv <= pbase + sz /\
       array_length_frame sn u G tn q H tm /\
       (!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
         val_in_memory tv (EL (Num i) vs) (w2n a + 32 + Num i * type_memory_size tv) m)
     else
       evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
         [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index"))
Proof
  strip_tac >>
  `mload (w2n a) u = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `u.vs_memory` mp_tac) >>
     simp[bodyPtrDefsTheory.mem_agree_outside_def, valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `w2n a + 32 <= pbase + sz` by decide_tac >>
  drule_all captured_dynamic_scalar_run >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_all captured_dynamic_selection >>
  disch_then (qspecl_then [`tv`,`cap`] assume_tac) >>
  qexistsl [`q`,`H`,`tm`] >>
  reverse (Cases_on `idx_in_range sgn iw (n2w (LENGTH vs))`)
  >- fs[IgnAsm `i = if _ then _ else _`] >>
  fs[IgnAsm `i = if _ then _ else _`, IgnAsm `iw = n2w (Num i)`] >>
  `LENGTH vs <= cap /\ value_has_type tv (EL (Num i) vs)` by
    fs[vyperTypingTheory.value_has_type_def, vyperTypingTheory.all_have_type_EVERY, listTheory.EVERY_EL] >>
  `SUC (Num i) * type_memory_size tv <= cap * type_memory_size tv` by
    (irule arithmeticTheory.LESS_MONO_MULT >> decide_tac) >>
  `Num i * type_memory_size tv + type_memory_size tv <= cap * type_memory_size tv` by
    (qpat_assum `SUC (Num i) * _ <= _` mp_tac >>
     rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `w2n a + (32 + Num i * type_memory_size tv) < dimword (:256)` by decide_tac >>
  `alloca_history fn q` by metis_tac[captured_dynamic_history] >>
  `q.vs_memory = u.vs_memory /\ tm.t_mem = tn.t_mem` by
    (fs[array_length_frame_def] >>
     qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_memory`) >> simp[]) >>
  `w2n (a + 32w + iw * n2w (type_memory_size tv)) =
     w2n a + (32 + Num i * type_memory_size tv)` by
    (qpat_assum `iw = n2w (Num i)` SUBST1_TAC >>
     rewrite_tac[word_mul_n2w, GSYM WORD_ADD_ASSOC, word_add_n2w] >>
     irule abiDecodeStaticPropsTheory.w2n_add_n2w_lt >> decide_tac) >>
  `w2n a + 32 + Num i * type_memory_size tv + type_memory_size tv <= pbase + sz` by
    decide_tac >>
  `!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
       val_in_memory tv (EL (Num i) vs) (w2n a + 32 + Num i * type_memory_size tv) m` by
    metis_tac[dynarray_in_memory_robust_element] >>
  simp[] >>
  qpat_x_assum `!m. _ ==> val_in_memory tv _ _ m` mp_tac >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

(* Ordinary clients do not ask for the scalar itinerary. *)
Theorem subscript_captured_dynamic_execution:
  compile_array_subscript bop iop T cnt 32 (type_memory_size tv) sgn
    (\op. emit_op MLOAD [op]) sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\ eval_operand iop u = SOME iw /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  LENGTH vs < dimword (:256) /\
  (!m. mem_agree_outside tn.t_mem u.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
  op_prov G bop = SOME (pbase,sz) /\ op_prov G iop = NONE /\
  pbase <= w2n a /\
  w2n a + (32 + cap * type_memory_size tv) <= pbase + sz /\
  w2n a + (32 + cap * type_memory_size tv) < dimword (:256) /\
  w2n a + 32 <= u.vs_alloca_next /\
  op_taint tn bop = {} /\ op_taint tn iop = {} /\
  mem_word_taint tn.t_mem (w2n a) = {} /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\ alloca_history fn u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?q H tm.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw (n2w (LENGTH vs)) then OK q else Abort Revert_abort q,H,tm)) /\
    (if idx_in_range sgn iw (n2w (LENGTH vs)) then
       0 <= i /\ Num i < LENGTH vs /\
       evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
         [ValueSubscript (IntV i)] = INL (EL (Num i) vs) /\
       value_has_type tv (EL (Num i) vs) /\
       ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
       q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
       eval_operand dst q = SOME (a + 32w + iw * n2w (type_memory_size tv)) /\
       w2n (a + 32w + iw * n2w (type_memory_size tv)) =
         w2n a + 32 + Num i * type_memory_size tv /\
       op_prov H dst = SOME (pbase,sz) /\ op_taint tm dst = {} /\
       w2n a + 32 + Num i * type_memory_size tv + type_memory_size tv <= pbase + sz /\
       array_length_frame sn u G tn q H tm /\
       (!m. mem_agree_outside tm.t_mem q.vs_memory m ==>
         val_in_memory tv (EL (Num i) vs) (w2n a + 32 + Num i * type_memory_size tv) m)
     else
       evaluate_subscripts (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs))
         [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index"))
Proof
  strip_tac >>
  assume_tac captured_dynamic_scalar_rule_trivial >>
  drule_all subscript_captured_dynamic_execution_observed >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl [`q`,`H`,`tm`] >> simp[]
QED
