(* Constructor-code loads read the staged bytes below the allocation floor. *)
Theory bodyMembershipCtorReadInputsMods
Ancestors
  abiDecodeStaticProps builtinProps bodyPtrDefs ptrDiscipline compileEnv
  exprLowering context words list arithmetic

Theorem membership_ctor_read_inputs_mods:
  cenv.ce_is_ctor /\ vv_location vv = SOME LocCode /\
  elem_size_in_location cenv LocCode ety = 32 /\
  lo <= u.vs_alloca_next /\ u.vs_alloca_next < dimword (:256) /\
  (!ib. cenv.ce_imm_alloca = SOME ib ==>
    eval_operand ib u = SOME 0w /\
    (!x. ib = Var x ==> not_fresh_at sm x) /\
    (lo <> 0 ==> op_prov Gu ib = NONE /\ op_taint Tu ib = {})) /\
  eval_operand (vv_operand vv) u = SOME w /\
  op_prov Gu (vv_operand vv) = NONE /\ op_taint Tu (vv_operand vv) = {} /\
  (!i. i < LENGTH ws ==>
    w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <= lo /\
    mem_word_taint Tu.t_mem
      (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) = {} /\
    mload (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) u = EL i ws) /\
  (!cap. bd = Dynamic cap ==>
    w2n w + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
    mload (w2n w) u = n2w (LENGTH ws)) ==>
  eval_operand (vv_operand vv) u = SOME w /\ op_taint Tu (vv_operand vv) = {} /\
  (!ib x. cenv.ce_imm_alloca = SOME ib /\ ib = Var x ==> not_fresh_at sm x) /\
  (!i. i < LENGTH ws ==>
    let addr = w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => word_scale LocCode) +
                         elem_size_in_location cenv LocCode ety * i) in
    ptr_load_val cenv.ce_is_ctor LocCode addr u = EL i ws /\
    w2n addr + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n addr) = {}) /\
  (!cap. bd = Dynamic cap ==>
    lo <= u.vs_alloca_next /\ op_prov Gu (vv_operand vv) = NONE /\
    w2n w + 32 <= lo /\ mem_word_taint Tu.t_mem (w2n w) = {} /\
    mload (w2n w) u = n2w (LENGTH ws) /\
    (!ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib u = SOME 0w /\ op_prov Gu ib = NONE /\ op_taint Tu ib = {})) /\
  ((0 < LENGTH ws \/ (?cap. bd = Dynamic cap)) ==>
    op_prov Gu (vv_operand vv) = NONE /\
    (!ib. cenv.ce_imm_alloca = SOME ib ==>
      eval_operand ib u = SOME 0w /\ op_prov Gu ib = NONE /\ op_taint Tu ib = {}))
Proof
  strip_tac >> conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qpat_assum `!ib. cenv.ce_imm_alloca = SOME ib ==> _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!j. j < LENGTH ws ==> _` (drule_then strip_assume_tac) >>
      simp[word_scale_def, ptr_load_val_def] >>
      qabbrev_tac `off = case bd of Fixed _ => 0 | Dynamic _ => 32` >>
      `w2n (w + n2w (32 * i + off)) = w2n w + off + i * 32` by
        (`w2n w + (off + 32 * i) < dimword (:256)` by decide_tac >>
         drule w2n_add_n2w_lt >> simp[] >> decide_tac) >>
      gs[]) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!cap. bd = Dynamic cap ==> _` (drule_then strip_assume_tac) >>
      `lo <> 0` by decide_tac >>
      simp[] >> gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  disch_tac >>
  `lo <> 0` suffices_by
    (strip_tac >> simp[] >> gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `0 < LENGTH ws \/ (?cap. bd = Dynamic cap)` strip_assume_tac
  >- (qpat_assum `!j. j < LENGTH ws ==> _`
        (qspec_then `0` (drule_then strip_assume_tac)) >> decide_tac) >>
  qpat_assum `!cap. bd = Dynamic cap ==> _` (drule_then strip_assume_tac) >>
  decide_tac
QED
