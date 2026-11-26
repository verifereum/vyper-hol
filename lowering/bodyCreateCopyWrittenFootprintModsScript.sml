Theory bodyCreateCopyWrittenFootprintMods
Ancestors
  bodyFullCreateHeld[qualified] fragGasOriginPtrLoop[qualified]
  stmtFragPtr[qualified] allocasBelowFmpUpdatesProps[qualified]
  venomMemProps[qualified] valueEncodingProps[qualified] venomLayout[qualified]
  arithmetic words pred_set list finite_map
  vyperCreate venomState venomMemDefs venomInst venomExecSemantics
  ptrDiscipline bodyPtrDefs memLocDefs codegenRel emitHelper fragExec
  valueEncodingDefs fragGasOriginPtr
Libs
  dep_rewrite

(* Materialization preserves bytes and taint below the operand landing's FMP.
   The written interval is clean; no claim is made about reservation padding. *)
Theorem create_copy_written_footprint_mods:
  emit_void MSTORE [Var p;pre] a6 = ((),a7) /\
  emit_op ADD [Var p;Lit 32w] a7 = (dst,a8) /\
  emit_void EXTCODECOPY [target;dst;Lit 0w;sz] a8 = ((),a9) /\
  emit_op ADD [Var p;Lit 21w] a9 = (buf,a10) /\
  emit_op ADD [sz;Lit 11w] a10 = (len,sc) /\
  fn_has_code a6 a7 func /\ fn_has_code a7 a8 func /\ fn_has_code a8 a9 func /\
  fn_has_code a9 a10 func /\ fn_has_code a10 sc func /\
  (!x. MEM (Var x) [Var p;target;sz] ==> not_fresh_at a6 x) /\
  0 < LENGTH code /\ LENGTH code <= 24576 /\
  eval_operand target al = SOME aw /\ (lookup_account (w2w aw) al.vs_accounts).code = code /\
  eval_operand sz al = SOME (n2w (LENGTH code)) /\
  eval_operand pre al = SOME (0x620000003d81600b3d39f3w || (n2w (LENGTH code) << 56)) /\
  op_taint tb target = {} /\ op_taint tb sz = {} /\ op_taint tb pre = {} /\
  lookup_var p al = SOME (n2w B) /\ op_taint tb (Var p) = {} /\
  FLOOKUP Gb p = SOME (B,venomLayout$ceil32 (LENGTH code+32)) /\
  ctx_has_dalloca ctx /\ w2n al.vs_initial_fmp <= B /\
  B + venomLayout$ceil32 (LENGTH code+32) = w2n al.vs_fmp /\
  allocas_below_fmp al /\ allocas_from lo al /\ ~al.vs_halted /\
  al.vs_current_bb = a6.cs_current_bb /\ al.vs_inst_idx = LENGTH a6.cs_current_insts /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK al,Gb,tb)) /\
  (al with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx; vs_fmp := s.vs_fmp|>) = s /\
  (!x. not_fresh_at sm x ==> lookup_var x al = lookup_var x s /\
       FLOOKUP Gb x = FLOOKUP G x /\ op_taint tb (Var x) = op_taint tn (Var x)) /\
  tb.t_mem = tn.t_mem UNION {i | B <= i /\ i < w2n al.vs_fmp} /\
  tb.t_stor = tn.t_stor /\ tb.t_trans = tn.t_trans /\ tb.t_imm = tn.t_imm /\
  B = w2n s.vs_fmp /\ sm.cs_next_var <= a6.cs_next_var ==>
  ?q t Gmat tt.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gmat,tt)) /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\ allocas_below_fmp t /\
    buf = Var q /\ eval_operand buf t = SOME (n2w (B+21)) /\
    eval_operand len t = SOME (n2w (LENGTH code+11)) /\
    w2n (n2w (B+21):bytes32) = B+21 /\
    w2n (n2w (LENGTH code+11):bytes32) = LENGTH code+11 /\
    op_taint tt buf = {} /\ op_taint tt len = {} /\ ptr_covers Gmat tt q t (LENGTH code+11) /\
    read_memory (B+21) (LENGTH code+11) t = create_copy_initcode code /\
    w2n t.vs_initial_fmp <= B+21 /\ B+21+(LENGTH code+11) <= w2n t.vs_fmp /\
    (!i. B+21 <= i /\ i < B+21+(LENGTH code+11) ==> i NOTIN tt.t_mem) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
    w2n t.vs_fmp = B + venomLayout$ceil32 (LENGTH code+32) /\
    B+(LENGTH code+32) <= LENGTH t.vs_memory /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP Gmat x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)) /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!b k. b+k <= B ==> mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory) /\
    (!i. i < B /\ i IN tt.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  drule_all (REWRITE_RULE []
    (Q.INST [`n` |-> `LENGTH code`] bodyFullCreateHeldTheory.create_copy_written_path)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `ptr_covers Gmat tt q t (LENGTH code+11)` >>
  `t = al with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                 vs_memory := t.vs_memory|>` by
    (qpat_assum `t with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|> = al`
      (mp_tac o AP_TERM ``\z. z with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                                      vs_memory := t.vs_memory|>``) >> simp[NoAsms]) >>
  `t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
            vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|> = s` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
      (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `al with <|vs_vars := _; vs_inst_idx := _; vs_fmp := _|> = s`
       (fn th => simp[NoAsms,th])) >>
  `al.vs_memory = s.vs_memory` by
    (qpat_assum `al with <|vs_vars := _; vs_inst_idx := _; vs_fmp := _|> = s`
      (mp_tac o AP_TERM ``\z:venom_state. z.vs_memory``) >> simp[NoAsms]) >>
  suspend "finish"
QED

Resume create_copy_written_footprint_mods[finish]:
  `allocas_below_fmp t` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
      (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocasBelowFmpUpdatesPropsTheory.allocas_below_fmp_updates]) >>
  `t.vs_fmp = al.vs_fmp /\ t.vs_initial_fmp = al.vs_initial_fmp` by
    (qpat_assum `t = _ with <|vs_vars := _; vs_inst_idx := _; vs_memory := _|>`
      (PURE_ONCE_REWRITE_TAC o single) >> simp[NoAsms]) >>
  `w2n t.vs_fmp = B + venomLayout$ceil32 (LENGTH code+32)` by
    (qpat_assum `t.vs_fmp = _` SUBST1_TAC >> sym_tac >> first_assum ACCEPT_TAC) >>
  `B+21+(LENGTH code+11) <= w2n t.vs_fmp /\ w2n t.vs_initial_fmp <= B+21` by
    (qspec_then `LENGTH code+32` assume_tac (GEN_ALL venomLayoutTheory.ceil32_ge) >>
     fs[] >> decide_tac) >>
  `w2n (n2w (B+21):bytes32) = B+21 /\
   w2n (n2w (LENGTH code+11):bytes32) = LENGTH code+11` by
    (qspec_then `t.vs_fmp` assume_tac w2n_lt >>
     PURE_REWRITE_TAC [w2n_n2w] >> conj_tac >> irule LESS_MOD >> decide_tac) >>
  `B+(LENGTH code+32) <= LENGTH t.vs_memory /\ LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (qpat_assum `t.vs_memory = _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[venomMemPropsTheory.LENGTH_write_memory_with_expansion,
          venomMemPropsTheory.LENGTH_mstore_eq,MAX_DEF] >> decide_tac) >>
  `!b k. b+k <= B ==> mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `t.vs_memory = _` (PURE_ONCE_REWRITE_TAC o single) >>
     dep_rewrite.DEP_ONCE_REWRITE_TAC [valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint] >>
     conj_tac >- decide_tac >>
     dep_rewrite.DEP_ONCE_REWRITE_TAC [valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint] >>
     conj_tac >- decide_tac >> simp[]) >>
  `!i. B+21 <= i /\ i < B+21+(LENGTH code+11) ==> i NOTIN tt.t_mem` by
    (qpat_assum `tt.t_mem = _` SUBST1_TAC >> simp[NoAsms,IN_DIFF] >>
     rpt strip_tac >> decide_tac) >>
  `!i. i < B /\ i IN tt.t_mem ==> i IN tn.t_mem` by
    (qpat_assum `tt.t_mem = _` SUBST1_TAC >> qpat_assum `tb.t_mem = _` SUBST1_TAC >>
     simp[NoAsms,IN_DIFF,IN_UNION] >> rpt strip_tac >> decide_tac) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP Gmat x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `not_fresh_at a6 x` by (irule stmtFragPtrTheory.not_fresh_at_mono >> qexists `sm` >> simp[]) >>
     qpat_assum `!x. _ ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. _ ==> lookup_var x al = _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gmat,tt)` by
    (rpt gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gb`,`al`,`tb`] >> conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  `tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm` by simp[] >>
  qexistsl_tac [`q`,`t`,`Gmat`,`tt`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise create_copy_written_footprint_mods
