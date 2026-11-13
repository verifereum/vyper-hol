Theory runtimeSymSrcAssignTuple
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv
  context venomInst stackPlanTypes exprSimStorageCopy

(* Assignment-value and store-at-location are discharged by C1.1.5.2's
   join. The selected target implication is discharged there with the
   guarded target-pointer contract (C1.1.3); it is not global target safety. *)
Theorem runtime_sym_tuple_store_all:
  (!d l v p sl dt st di n s u s'.
    ~is_label_operand d /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_assign_value ce d l v p sl dt st di n s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!d v loc s u s'. ~is_label_operand d /\ ~is_label_operand v /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_store_at_loc ce.ce_imm_alloca d v loc s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !tys targets vals s u s'.
    (!bt s op loc pt s'. MEM (BaseTarget bt) targets /\
      EVERY runtime_sym_inst (state_insts s) /\
      compile_get_target_ptr compile_expr ce bt s = ((op,loc,pt),s') ==>
      EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
    EVERY (\op. ~is_label_operand op) vals /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_store_all ce tys targets vals s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> Induct >> Cases_on `targets` >> Cases_on `vals` >>
  simp[NoAsms, Once compile_tuple_store_all_def, comp_return_def] >>
  rpt gen_tac >> rename1 `compile_tuple_store_all ce (_::tys) (tg::tgs) (v::vs)` >>
  Cases_on `tg` >>
  simp[NoAsms, Once compile_tuple_store_all_def, comp_ignore_bind_def,
       storage_copy_bind_eq, comp_return_def] >>
  rpt strip_tac
  >~ [`compile_get_target_ptr compile_expr ce b s = (result,s1)`]
  >- (PairCases_on `result` >>
      qpat_assum `!bt s op loc pt s'. _` (qspec_then `b` mp_tac) >>
      simp[NoAsms] >> disch_then drule_all >> strip_tac >>
      `EVERY runtime_sym_inst (state_insts s1')` by
        (qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
         rpt IF_CASES_TAC >> strip_tac
         >~ [`emit_void INVALID [] _ = _`]
         >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
             simp[NoAsms] >> disch_then drule_all >> simp[NoAsms]) >>
         rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST,pairTheory.SND]) >>
         first_assum drule_all >> simp[NoAsms]) >>
      first_x_assum (qspecl_then [`tgs`,`vs`,`s1'`,`()`,`s'`] mp_tac) >>
      impl_tac >- (simp[NoAsms] >> metis_tac[]) >> simp[NoAsms]) >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[NoAsms] >>
  disch_then drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[NoAsms]
QED

(* The staging buffer boundary is owned by C1.1.3.2. *)
Theorem runtime_sym_tuple_stage[local]:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) ==>
  !stage n src s op s'. ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    (if stage then
      do b <- compile_alloc_buffer n;
         p <- return b.buf_operand;
         emit_void MCOPY [p; src; Lit (n2w n)];
         return p od
     else return src) s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  strip_tac >> rpt gen_tac >> Cases_on `stage` >>
  simp[NoAsms, comp_ignore_bind_def, storage_copy_bind_eq, comp_return_def]
  >- (strip_tac >> first_assum drule_all >> strip_tac >>
      reverse conj_tac >- metis_tac[] >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
      simp[NoAsms, is_label_operand_def] >>
      impl_tac >- metis_tac[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[NoAsms]
QED

(* Tuple load/store are local assignment boundaries (C1.1.5.2), not
   assumptions about arbitrary expression compilation. *)
Theorem runtime_sym_tuple_unpack_boundary:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_alloc_buffer n s = (b,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand) /\
  (!src tys off s ops s'. ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_load_all ce src tys off s = (ops,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    EVERY (\op. ~is_label_operand op) ops) /\
  (!tys vals s u s'. EVERY (\op. ~is_label_operand op) vals /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_store_all ce tys targets vals s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) ==>
  !ty stage src s u s'. ~is_label_operand src /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_tuple_unpack ce ty stage targets src s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >> rpt gen_tac >> simp[NoAsms, compile_tuple_unpack_def] >>
  IF_CASES_TAC
  >- (strip_tac >> drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
      simp[NoAsms, runtime_sym_inst_def, mk_inst_def] >>
      disch_then drule_all >> simp[NoAsms]) >>
  simp[NoAsms, storage_copy_bind_eq] >> strip_tac >>
  drule_all runtime_sym_tuple_stage >> strip_tac >>
  first_assum drule_all >> strip_tac >>
  first_assum drule_all >> simp[NoAsms]
QED
