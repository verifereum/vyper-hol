(* Only the reached read inputs are transported: the header may introduce
   fresh registers and move the instruction cursor. *)
Theory bodyMembershipHeaderReadFrameMods
Ancestors
  bodyPtrBopInLoopContract builtinProps compileEnv venomState ptrDiscipline
  finite_map words


Theorem membership_header_read_fields[local]:
  membership_loop_frame sm Gu Tu u Gh Th sh ==>
  sh.vs_alloca_next = u.vs_alloca_next /\
  sh.vs_data_section = u.vs_data_section /\
  Th.t_mem = Tu.t_mem /\ Th.t_stor = Tu.t_stor /\ Th.t_trans = Tu.t_trans /\
  !ctor loc addr. ptr_load_val ctor loc addr sh = ptr_load_val ctor loc addr u
Proof
  simp[membership_loop_frame_def] >> strip_tac >>
  qpat_x_assum `sh = _` (fn th => once_rewrite_tac[th]) >>
  simp[] >> rpt gen_tac >> Cases_on `loc` >> Cases_on `ctor` >>
  simp[ptr_load_val_def, mload_def, sload_def, contract_storage_def,
       tload_def, contract_transient_def]
QED

Theorem membership_header_read_frame_mods:
  membership_loop_frame sm Gu Tu u Gh Th sh /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sm x) /\
  eval_operand (vv_operand vv) u = SOME w /\ op_taint Tu (vv_operand vv) = {} /\
  (!i. i < LENGTH ws ==>
    let addr = w + n2w (word_scale loc + elem_size_in_location cenv loc ety * i) in
    ptr_load_val cenv.ce_is_ctor loc addr u = EL i ws /\
    (loc = LocMemory ==>
      w2n addr + 32 <= u.vs_alloca_next /\ mem_word_taint Tu.t_mem (w2n addr) = {} /\
      !x p Gp Tp. lookup_var x p = SOME addr /\ FLOOKUP Gp x = op_prov Gu (vv_operand vv) /\
        op_taint Tp (Var x) = {} ==> ptr_covers Gp Tp x p 32) /\
    (loc = LocStorage ==> key_taint Tu.t_stor addr = {}) /\
    (loc = LocTransient ==> key_taint Tu.t_trans addr = {}) /\
    (loc = LocCode /\ ~cenv.ce_is_ctor ==> w2n addr <= LENGTH u.vs_data_section) /\
    (loc = LocCode /\ cenv.ce_is_ctor ==>
      w2n addr + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n addr) = {})) /\
  (cenv.ce_is_ctor /\ loc = LocCode ==>
    op_prov Gu (vv_operand vv) = NONE /\
    !ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib u = SOME 0w /\ op_prov Gu ib = NONE /\ op_taint Tu ib = {}) /\
  lo <= u.vs_alloca_next ==>
  eval_operand (vv_operand vv) sh = SOME w /\ op_taint Th (vv_operand vv) = {} /\
  (!i. i < LENGTH ws ==>
    let addr = w + n2w (word_scale loc + elem_size_in_location cenv loc ety * i) in
    ptr_load_val cenv.ce_is_ctor loc addr sh = EL i ws /\
    (loc = LocMemory ==>
      w2n addr + 32 <= sh.vs_alloca_next /\ mem_word_taint Th.t_mem (w2n addr) = {} /\
      !x p Gp Tp. lookup_var x p = SOME addr /\ FLOOKUP Gp x = op_prov Gh (vv_operand vv) /\
        op_taint Tp (Var x) = {} ==> ptr_covers Gp Tp x p 32) /\
    (loc = LocStorage ==> key_taint Th.t_stor addr = {}) /\
    (loc = LocTransient ==> key_taint Th.t_trans addr = {}) /\
    (loc = LocCode /\ ~cenv.ce_is_ctor ==> w2n addr <= LENGTH sh.vs_data_section) /\
    (loc = LocCode /\ cenv.ce_is_ctor ==>
      w2n addr + 32 <= lo /\ mem_word_taint Th.t_mem (w2n addr) = {})) /\
  (cenv.ce_is_ctor /\ loc = LocCode ==>
    op_prov Gh (vv_operand vv) = NONE /\
    !ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib sh = SOME 0w /\ op_prov Gh ib = NONE /\ op_taint Th ib = {}) /\
  lo <= sh.vs_alloca_next
Proof
  pure_rewrite_tac[LET_THM] >> strip_tac >>
  drule_then strip_assume_tac membership_header_read_fields >>
  drule membership_loop_frame_operand >>
  disch_then (qspec_then `vv_operand vv` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac
  >- (qx_gen_tac `i` >> disch_tac >>
      qpat_x_assum `!i. i < LENGTH ws ==> _` (qspec_then `i` mp_tac) >>
      PURE_ASM_REWRITE_TAC[] >> simp[]) >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  disch_tac >>
  qpat_x_assum `cenv.ce_is_ctor /\ loc = LocCode ==> _` mp_tac >>
  PURE_ASM_REWRITE_TAC[] >> simp[SimpLHS] >> strip_tac >>
  qx_gen_tac `ib` >> disch_tac >>
  drule membership_loop_frame_operand >>
  disch_then (qspec_then `ib` mp_tac) >>
  `!x. ib = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  simp[] >>
  qpat_x_assum `!ib. cenv.ce_imm_alloca = SOME ib ==> _`
    (qspec_then `ib` mp_tac) >> simp[]
QED
