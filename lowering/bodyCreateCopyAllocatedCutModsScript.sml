(* The copy guard either reverts or reserves the writer's FMP window. *)
Theory bodyCreateCopyAllocatedCutMods
Ancestors
  bodyFullCreateHeld[qualified,ignore_grammar] bodyFullDynamicBuffer
  bodyPtrMakeArrayEmission[qualified] fragGasOriginPtrLoop stmtFragPtr
  compileEnv emitHelper fragExec ptrDiscipline loweringStateRelDefs
  venomState venomInst venomExecSemantics venomLayout words arithmetic list
Libs
  wordsLib

Theorem copy_guard_operand_frame[local]:
  (!x. not_fresh_at a x ==>
       lookup_var x t = lookup_var x s /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
  t.vs_labels = s.vs_labels /\ (!x. opr = Var x ==> not_fresh_at a x) ==>
  eval_operand opr t = eval_operand opr s /\ op_taint tt opr = op_taint tn opr
Proof
  Cases_on `opr` >> simp[eval_operand_def,op_taint_def] >> metis_tac[]
QED

Theorem create_copy_allocated_cut_mods:
  emit_op EXTCODESIZE [target] sm = (code_op,a1) /\
  emit_void ASSERT [code_op] a1 = ((),a2) /\
  emit_op SHL [Lit 56w;code_op] a2 = (shift,a3) /\
  emit_op OR [Lit 0x620000003d81600b3d39f3w;shift] a3 = (preamble,a4) /\
  emit_op ADD [code_op;Lit 32w] a4 = (req,a5) /\
  emit_op DALLOCA [req] a5 = (Var p,a6) /\
  fn_has_code sm a2 func /\ fn_has_code a2 a5 func /\ fn_has_code a5 a6 func /\
  MEM func ctx.ctx_functions /\ ctx_has_dalloca ctx /\ sm.cs_next_var <= a5.cs_next_var /\
  (!x. code_op = Var x \/ preamble = Var x ==> not_fresh_at a5 x) /\
  (!x. target = Var x ==> not_fresh_at sm x) /\
  eval_operand target s = SOME aw /\ op_taint tn target = {} /\
  (lookup_account (w2w aw) s.vs_accounts).code = code /\ LENGTH code <= 24576 /\
  allocas_from lo s /\ allocas_below_fmp s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  w2n s.vs_initial_fmp <= B /\ B = w2n s.vs_fmp /\
  (!pre Ga ta bb i.
    gas_origin_ptr_path (D0,lo,explicit0,ctx,func,PG) (s,G,tn) [] (OK pre,Ga,ta) /\
    lookup_block pre.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb pre.vs_inst_idx = SOME i /\ i.inst_opcode = DALLOCA ==>
    w2n pre.vs_fmp + venomLayout$ceil32 (LENGTH code + 32) < dimword (:256)) ==>
  if code = [] then
    ?q. code_op = Var q /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (Abort Revert_abort (revert_state (set_returndata []
           (update_var q 0w s with vs_inst_idx := SUC s.vs_inst_idx))),
         G \\ q, tn with t_var := tn.t_var |+ (q,{}))
  else
    ?al Gb tb.
      (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK al,Gb,tb)) /\
      ~al.vs_halted /\ al.vs_current_bb = a6.cs_current_bb /\
      al.vs_inst_idx = LENGTH a6.cs_current_insts /\
      allocas_from lo al /\ allocas_below_fmp al /\
      eval_operand target al = SOME aw /\
      (lookup_account (w2w aw) al.vs_accounts).code = code /\
      eval_operand code_op al = SOME (n2w (LENGTH code)) /\
      eval_operand preamble al = SOME
        (0x620000003d81600b3d39f3w || (n2w (LENGTH code) << 56)) /\
      op_taint tb target = {} /\ op_taint tb code_op = {} /\
      op_taint tb preamble = {} /\ op_taint tb (Var p) = {} /\
      lookup_var p al = SOME (n2w B) /\
      FLOOKUP Gb p = SOME (B,venomLayout$ceil32 (LENGTH code + 32)) /\
      ptr_covers Gb tb p al (LENGTH code + 32) /\
      w2n al.vs_initial_fmp <= B /\ B + venomLayout$ceil32 (LENGTH code + 32) = w2n al.vs_fmp /\
      (al with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx; vs_fmp := s.vs_fmp|>) = s /\
      al.vs_memory = s.vs_memory /\
      (!x. not_fresh_at sm x ==> lookup_var x al = lookup_var x s /\
        FLOOKUP Gb x = FLOOKUP G x /\ op_taint tb (Var x) = op_taint tn (Var x)) /\
      tb.t_mem = tn.t_mem UNION {i | B <= i /\ i < w2n al.vs_fmp} /\
      tb.t_stor = tn.t_stor /\ tb.t_trans = tn.t_trans /\ tb.t_imm = tn.t_imm
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all bodyFullCreateHeldTheory.create_copy_prealloc_path >>
  disch_then (qspecl_then [`PG`, `G`] mp_tac) >>
  Cases_on `code = []` >> asm_rewrite_tac[] >> disch_tac >>
  qpat_x_assum `?t Gt tt. _` (qx_choosel_then [`pre`,`Ga`,`ta`] strip_assume_tac) >>
  suspend "allocate"
QED

Resume create_copy_allocated_cut_mods[allocate]:
  `pre = s with <|vs_vars := pre.vs_vars; vs_inst_idx := pre.vs_inst_idx|>` by
    (qpat_assum `pre with <|vs_vars := _; vs_inst_idx := _|> = s`
       (mp_tac o AP_TERM ``\z. z with <|vs_vars := pre.vs_vars; vs_inst_idx := pre.vs_inst_idx|>``) >>
     simp[NoAsms]) >>
  `allocas_from lo pre /\ allocas_below_fmp pre` by
    (qpat_assum `pre:venom_state = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `allocas_below_fmp s`
       (strip_assume_tac o REWRITE_RULE [allocas_below_fmp_def]) >>
     simp[allocas_from_def,allocas_below_fmp_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `w2n (n2w (LENGTH code + 32):bytes32) = LENGTH code + 32` by
    (simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >> decide_tac) >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >>
  disch_then (qx_choosel_then [`out`,`bb`] strip_assume_tac) >>
  qpat_x_assum `out = STRING _ _` kall_tac >>
  `out = p` by metis_tac[operand_11] >>
  qpat_x_assum `out = p` SUBST_ALL_TAC >>
  qabbrev_tac `inst = mk_inst a5.cs_next_id DALLOCA [req] [p]` >>
  `get_instruction bb pre.vs_inst_idx = SOME inst /\ inst.inst_opcode = DALLOCA /\
   inst.inst_operands = [req] /\ inst.inst_outputs = [p]` by simp[Abbr `inst`,mk_inst_def] >>
  `w2n pre.vs_fmp + venomLayout$ceil32 (w2n (n2w (LENGTH code+32):bytes32)) < dimword (:256)` by
    (qpat_assum `w2n (n2w (LENGTH code + 32):bytes32) = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `!pre Ga ta bb i. _` irule >>
     conj_tac >- (qexistsl_tac [`bb`,`inst`] >> simp[]) >>
     qexistsl_tac [`Ga`,`ta`] >> simp[]) >>
  drule_all dalloca_origin_region_exact >>
  disch_then (qspecl_then [`PG`,`Ga`] (qx_choosel_then [`al`,`Gb`,`tb`] strip_assume_tac)) >>
  suspend "pack"
QED

Resume create_copy_allocated_cut_mods[pack]:
  `!x. not_fresh_at a5 x ==> lookup_var x al = lookup_var x pre /\
       FLOOKUP Gb x = FLOOKUP Ga x /\ op_taint tb (Var x) = op_taint ta (Var x)` by metis_tac[] >>
  `!x. not_fresh_at sm x ==> lookup_var x al = lookup_var x s /\
       FLOOKUP Gb x = FLOOKUP G x /\ op_taint tb (Var x) = op_taint tn (Var x)` by
    (gen_tac >> strip_tac >>
     `not_fresh_at a5 x` by (irule not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
     first_assum drule >> qpat_assum `!x. not_fresh_at sm x ==> lookup_var x pre = _ /\ _` drule >>
     simp[NoAsms] >> metis_tac[]) >>
  `pre.vs_labels = s.vs_labels /\ pre.vs_fmp = s.vs_fmp /\
   pre.vs_accounts = s.vs_accounts /\ pre.vs_initial_fmp = s.vs_initial_fmp /\
   pre.vs_memory = s.vs_memory` by
    (qpat_assum `pre:venom_state = _` (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  `eval_operand target al = eval_operand target s /\ op_taint tb target = op_taint tn target` by
    (irule copy_guard_operand_frame >> conj_tac
     >- (qexists_tac `sm` >> conj_tac >- first_assum ACCEPT_TAC >>
         gen_tac >> strip_tac >>
         qpat_assum `!x. not_fresh_at sm x ==> lookup_var x al = _ /\ _` drule >> simp[]) >>
     simp[]) >>
  `!opr. MEM opr [code_op;preamble] ==>
    eval_operand opr al = eval_operand opr pre /\ op_taint tb opr = op_taint ta opr` by
    (gen_tac >> strip_tac >> irule copy_guard_operand_frame >> reverse conj_tac
     >- first_assum ACCEPT_TAC >>
     qexists_tac `a5` >> conj_tac
     >- (gen_tac >> disch_tac >>
         qpat_assum `!x. code_op = Var x \/ preamble = Var x ==> _` irule >>
         qpat_x_assum `MEM opr _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
         gvs[]) >>
     gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at a5 x ==> lookup_var x al = _ /\ _`
       (drule_then strip_assume_tac) >> conj_tac >> first_assum ACCEPT_TAC) >>
  `al with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx; vs_fmp := s.vs_fmp|> = s` by
    (map_every (fn pat => qpat_assum pat (PURE_ONCE_REWRITE_TAC o single))
      [`al = update_var _ _ _ with vs_inst_idx := _`, `pre:venom_state = _`] >>
     simp[update_var_def,venom_state_component_equality]) >>
  qpat_x_assum `al = update_var _ _ _ with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `pre = s with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  `allocas_from lo al` by
    (PURE_REWRITE_TAC [allocas_from_def] >>
     qpat_assum `al.vs_allocas = _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `allocas_from lo pre` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  qexistsl_tac [`al`,`Gb`,`tb`] >> conj_tac
  >- (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Ga`,`pre`,`ta`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[wordsTheory.n2w_w2n] >> metis_tac[]
QED

Finalise create_copy_allocated_cut_mods
