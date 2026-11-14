(* RawLog header/payload preparation: the explicit endpoint frame. *)
Theory bodyFullRawLogDynamicPrepareFrame
Ancestors
  bodyFullRawLogDynamicData bodyFullGhostFrame bodyPtrDefs
  ptrDiscipline venomState finite_map words list arithmetic
  loweringStateRelDefs exprSimProps

Theorem raw_log_dynamic_prepare_frame:
  l <> p /\
  (!x. not_fresh_at sm x ==> x <> l /\ x <> p) /\
  not_fresh_at sm src /\ FLOOKUP G src = SOME (site,cap) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sm x) /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  eval_operand (Var src) s = SOME (n2w b) /\
  b+32 < dimword (:256) /\
  ptr_covers G tn src s (32+32*word_size (LENGTH bs)) /\
  (!i. b<=i /\ i<b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  eval_operands ops s = SOME topics /\
  EVERY (\op. op_taint tn op = {}) ops ==>
  let t = update_var p (n2w (b+32)) (update_var l (n2w (LENGTH bs)) s);
      G2 = DRESTRICT G (COMPL {l}) |+ (p,(site,cap));
      tn2 = tn with t_var := tn.t_var |+ (l,{}) |+ (p,{})
  in
    eval_operands ops t = SOME topics /\
    EVERY (\op. op_taint tn2 op = {}) (Var p::Var l::ops) /\
    (LENGTH bs <> 0 ==> ptr_covers G2 tn2 p t (LENGTH bs)) /\
    (!i. b+32<=i /\ i<b+32+LENGTH bs ==> i NOTIN tn2.t_mem) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    ghost_inv_at D lo d cenv cx ee G2 tn2 t /\
    ghost_kept_at lo cenv ee sm G tn s G2 tn2
Proof
  strip_tac >> pure_rewrite_tac [LET_THM] >>
  qabbrev_tac `t = update_var p (n2w (b+32)) (update_var l (n2w (LENGTH bs)) s)` >>
  qabbrev_tac `G2 = DRESTRICT G (COMPL {l}) |+ (p,(site,cap))` >>
  qabbrev_tac `tn2 = tn with t_var := tn.t_var |+ (l,{}) |+ (p,{})` >>
  `!x. not_fresh_at sm x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> l /\ x <> p` by metis_tac[] >>
     simp[Abbr `t`, Abbr `G2`, Abbr `tn2`, lookup_var_def,
          update_var_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  BETA_TAC >>
  conj_tac >- suspend "topics" >>
  conj_tac >- suspend "taints" >>
  conj_tac >- suspend "coverage" >>
  conj_tac >- (simp[Abbr `tn2`] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac >- simp[Abbr `t`, update_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "invariant" >>
  suspend "kept"
QED

Resume raw_log_dynamic_prepare_frame[topics]:
  `!op. MEM op ops ==> eval_operand op t = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >>
     fs[EVERY_MEM, eval_operand_def, Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `eval_operands ops t = eval_operands ops s` suffices_by simp[] >>
  qpat_x_assum `eval_operands ops s = _` kall_tac >>
  Induct_on `ops` >> simp[eval_operands_def] >> metis_tac[MEM]
QED
Resume raw_log_dynamic_prepare_frame[taints]:
  simp[EVERY_DEF] >> conj_tac
  >- simp[Abbr `tn2`, op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- simp[Abbr `tn2`, op_taint_def, FLOOKUP_UPDATE] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM op ops` >>
  `op_taint tn op = {}` by metis_tac[] >>
  Cases_on `op` >> fs[op_taint_def] >>
  first_x_assum (qspec_then `Var s'` mp_tac) >> simp[] >> strip_tac >>
  `s' <> l /\ s' <> p` by metis_tac[] >>
  fs[Abbr `tn2`, op_taint_def, FLOOKUP_UPDATE]
QED
Resume raw_log_dynamic_prepare_frame[coverage]:
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `LENGTH bs <= 32 * word_size (LENGTH bs)` by simp[le_word_size_mul] >>
  fs[ptr_covers_def, eval_operand_def] >>
  simp[ptr_covers_def, Abbr `G2`, Abbr `tn2`, Abbr `t`,
       op_taint_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       w2n_n2w, LESS_MOD] >>
  gvs[lookup_var_def, w2n_n2w, LESS_MOD] >> decide_tac
QED
Resume raw_log_dynamic_prepare_frame[invariant]:
  irule ghost_inv_at_exterior_frame >>
  qexistsl [`G`, `ee`, `s`, `sm`, `tn`] >>
  simp[Abbr `t`, Abbr `tn2`, update_var_def] >> metis_tac[]
QED
Resume raw_log_dynamic_prepare_frame[kept]:
  simp[ghost_kept_at_def, Abbr `tn2`] >> metis_tac[]
QED
Finalise raw_log_dynamic_prepare_frame
