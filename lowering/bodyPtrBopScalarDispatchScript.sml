Theory bodyPtrBopScalarDispatch
Ancestors
  bodyPtrBopPowerCompile bodyPtrBopArithmeticCompile bodyPtrBopScalarCompile
  bodyPtrBopScalarDynamic bodyPtrBopScalarSeq exprLowering exprLoweringProps
  vyperTypeSystem compileEnv freshWrites pred_set list ptrDiscipline
  fragGasPathPtr finite_map venomState venomInst

Theorem bop_scalar_compile_binop:
  bop <> In /\ bop <> NotIn /\ bop <> ExpMod /\
  compile_binop bop x y ty bl el st = (v, st') /\
  x IN A /\ y IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv; And; Or; XOr;
                    ShL; ShR; Eq; NotEq; Lt; LtE; Gt; GtE; Min; Max]`
  >- (drule_all bop_scalar_compile_binop_elementary >> simp[]) >>
  Cases_on `bop` >> gvs[compile_binop_def] >>
  Cases_on `is_decimal_type ty` >> gvs[] >>
  FIRST [
    (drule bop_scalar_compile_safe_add >> simp[]),
    (drule bop_scalar_compile_safe_sub >> simp[]),
    (drule bop_scalar_compile_safe_mul >> simp[]),
    (drule bop_scalar_compile_safe_decimal_div >> simp[]),
    (drule bop_scalar_compile_safe_div >> simp[]),
    (drule bop_scalar_compile_safe_mod >> simp[]),
    (drule bop_scalar_compile_safe_pow >> simp[])]
QED

Theorem bop_scalar_compile_binop_typed:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el st = (v, st') /\
  x IN A /\ y IN A /\ (!w. Lit w IN A) /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> `bop <> ExpMod` by (strip_tac >> gvs[well_typed_binop_def]) >>
  drule_all bop_scalar_compile_binop >> simp[]
QED

Theorem bop_scalar_binop_certificate:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el st = (v, st') /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. bop_scalar_seq R ({x; y} UNION IMAGE Lit UNIV)
        (emitted_insts st st') B /\ v IN B
Proof
  strip_tac >> drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)
    bop_scalar_compile_binop_typed >>
  disch_then (drule_at (Pat `well_typed_binop _ _ _ _`)) >>
  disch_then (qspecl_then [`R`, `{x; y} UNION IMAGE Lit UNIV`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem bop_scalar_binop_input_clean[local]:
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} ==>
  !op. op IN ({x; y} UNION IMAGE Lit UNIV) ==>
    op_prov G op = NONE /\ op_taint tn op = {}
Proof
  simp[op_prov_def, op_taint_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >> gvs[]
QED

Theorem bop_scalar_binop_success_path:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el st = (v, st') /\
  (!z. z IN R ==> not_fresh_at st z) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts st st') s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. z IN R ==> FLOOKUP G' z = FLOOKUP G z /\
                      FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z)
Proof
  strip_tac >> drule_all bop_scalar_binop_certificate >>
  strip_tac >>
  `!op. op IN ({x; y} UNION IMAGE Lit UNIV) ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    metis_tac[bop_scalar_binop_input_clean] >>
  irule bop_scalar_certificate_result_path >>
  simp[] >> qexists_tac `{x; y} UNION IMAGE Lit UNIV` >>
  simp[] >> qexists_tac `B` >> simp[]
QED

Theorem bop_scalar_binop_abort_path:
  bop <> In /\ bop <> NotIn /\ well_typed_binop ann bop t1 t2 /\
  compile_binop bop x y ty bl el st = (v, st') /\
  (!z. z IN R ==> not_fresh_at st z) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts st st') s = Abort a t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn' n j. gas_path_ptr D 0 ctx fn PG G tn s n G' tn'
      (Abort a (t with vs_inst_idx := j)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. z IN R ==> FLOOKUP G' z = FLOOKUP G z /\
                      FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z)
Proof
  strip_tac >> drule_all bop_scalar_binop_certificate >> strip_tac >>
  `!op. op IN ({x; y} UNION IMAGE Lit UNIV) ==>
     op_prov G op = NONE /\ op_taint tn op = {}` by
    metis_tac[bop_scalar_binop_input_clean] >>
  drule_all bop_scalar_seq_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED
