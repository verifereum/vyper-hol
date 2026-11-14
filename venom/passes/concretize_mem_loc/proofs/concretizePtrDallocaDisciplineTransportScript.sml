Theory concretizePtrDallocaDisciplineTransport
Ancestors
  concretizePtrDallocaGhostInterface ptrDiscipline venomState venomInst
  contextCodegenRel codegenRel finite_map pred_set list arithmetic

(* These consumers are conditional: range reflection, dynamic retention and
   selector agreement must be supplied by the paired history invariant. *)
Theorem ptr_dalloca_literal_discipline:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Lit pos] ==>
  access_ok eom Gt ft inst t /\ taint_ok ft tnt inst t
Proof
  simp[access_ok_def, taint_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, op_taint_def]
QED

(* One range argument serves reads and writes. The second alternative is
   the erased-static case; it requires neither source/target offset equality
   nor retention of the erased site's provenance. *)
Theorem ptr_dalloca_range_transport:
  lo <= eom /\
  (!off len. MEM (off,len) rs /\ len <> 0 /\
    (lo < off + len \/ ?ops. mops = SOME ops /\
      op_prov G ops.iao_ofst <> NONE) ==>
    ?ops v b sz. mops = SOME ops /\ ops.iao_ofst = Var v /\
      FLOOKUP G v = SOME (b,sz) /\ b <= off /\ off + len <= b + sz) /\
  (!off len. MEM (off,len) rt /\ len <> 0 ==>
    ?off_s. MEM (off_s,len) rs /\
    ((off = off_s /\ (!ops. mops = SOME ops ==>
        op_prov G ops.iao_ofst = op_prov Gt ops.iao_ofst)) \/
     (off + len <= eom /\ (!ops. mops = SOME ops ==>
        op_prov Gt ops.iao_ofst = NONE)))) ==>
  !off len. MEM (off,len) rt /\ len <> 0 /\
    (eom < off + len \/ ?ops. mops = SOME ops /\
      op_prov Gt ops.iao_ofst <> NONE) ==>
    ?ops v b sz. mops = SOME ops /\ ops.iao_ofst = Var v /\
      FLOOKUP Gt v = SOME (b,sz) /\ b <= off /\ off + len <= b + sz
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qpat_x_assum `!off len. MEM (off,len) rt /\ _ ==> _`
    (drule_all_then strip_assume_tac)
  >- (fs[] >>
      `lo < off + len \/ ?ops. mops = SOME ops /\
        op_prov G ops.iao_ofst <> NONE` by
        (Cases_on `eom < off + len` >> fs[] >> metis_tac[]) >>
      qpat_x_assum `!off len. MEM (off,len) rs /\ _ ==> _`
        (drule_then strip_assume_tac) >>
      gvs[op_prov_def] >> metis_tac[]) >>
  metis_tac[NOT_LESS]
QED

Theorem ptr_dalloca_compare_transport[local]:
  access_ok lo G fn inst s /\
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  (!v b sz. FLOOKUP Gt v = SOME (b,sz) ==> dyn <= b) /\
  (!v b sz. FLOOKUP G v = SOME (b,sz) /\ dyn <= b ==>
    FLOOKUP Gt v = SOME (b,sz)) ==>
  !u w. (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
         inst.inst_opcode = EQ) /\ inst.inst_operands = [Var u; Var w] /\
    (u IN FDOM Gt \/ w IN FDOM Gt) ==>
    ?b sz x y. FLOOKUP Gt u = SOME (b,sz) /\ FLOOKUP Gt w = SOME (b,sz) /\
      0 < sz /\ eval_operand (Var u) t = SOME x /\
      eval_operand (Var w) t = SOME y /\
      b <= w2n x /\ w2n x <= b + sz /\
      b <= w2n y /\ w2n y <= b + sz
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  `FDOM Gt SUBSET FDOM G` by
    (simp[SUBSET_DEF, TO_FLOOKUP] >> gen_tac >>
     Cases_on `FLOOKUP Gt x` >> simp[] >>
     drule_all ptr_dalloca_ghost_prov >> simp[]) >>
  `?b sz x y. FLOOKUP G u = SOME (b,sz) /\ FLOOKUP G w = SOME (b,sz) /\
      0 < sz /\ eval_operand (Var u) s = SOME x /\
      eval_operand (Var w) s = SOME y /\
      b <= w2n x /\ w2n x <= b + sz /\
      b <= w2n y /\ w2n y <= b + sz` by
    (fs[access_ok_def, SUBSET_DEF] >> metis_tac[]) >>
  `dyn <= b` by
    (Cases_on `FLOOKUP Gt u`
     >- (fs[TO_FLOOKUP] >> Cases_on `FLOOKUP Gt w` >> fs[] >>
         rename1 `FLOOKUP Gt w = SOME site` >> PairCases_on `site` >>
         drule_all ptr_dalloca_ghost_prov >> strip_tac >> fs[] >> metis_tac[]) >>
     rename1 `FLOOKUP Gt u = SOME site` >> PairCases_on `site` >>
     drule_all ptr_dalloca_ghost_prov >> strip_tac >> fs[] >> metis_tac[]) >>
  `FLOOKUP Gt u = SOME (b,sz) /\ FLOOKUP Gt w = SOME (b,sz)` by metis_tac[] >>
  fs[ptr_dalloca_ghost_vars_def, eval_operand_def] >> metis_tac[]
QED

Theorem ptr_dalloca_access_transport:
  access_ok lo G fn inst s /\ lo <= eom /\
  ptr_dalloca_ghost_vars G tn.t_var s Gt tnt.t_var t /\
  (in_revert_forward fn s ==> in_revert_forward ft t) /\
  (!v b sz. FLOOKUP Gt v = SOME (b,sz) ==> dyn <= b) /\
  (!v b sz. FLOOKUP G v = SOME (b,sz) /\ dyn <= b ==>
    FLOOKUP Gt v = SOME (b,sz)) /\
  (!off len. MEM (off,len) (source_memory_read_ranges inst t) /\ len <> 0 ==>
    ?off_s. MEM (off_s,len) (source_memory_read_ranges inst s) /\
    ((off = off_s /\ (!ops. mem_read_ops inst = SOME ops ==>
        op_prov G ops.iao_ofst = op_prov Gt ops.iao_ofst)) \/
     (off + len <= eom /\ (!ops. mem_read_ops inst = SOME ops ==>
        op_prov Gt ops.iao_ofst = NONE)))) /\
  (!off len. MEM (off,len) (source_memory_write_ranges inst t) /\ len <> 0 ==>
    ?off_s. MEM (off_s,len) (source_memory_write_ranges inst s) /\
    ((off = off_s /\ (!ops. mem_write_ops inst = SOME ops ==>
        op_prov G ops.iao_ofst = op_prov Gt ops.iao_ofst)) \/
     (off + len <= eom /\ (!ops. mem_write_ops inst = SOME ops ==>
        op_prov Gt ops.iao_ofst = NONE)))) ==>
  access_ok eom Gt ft inst t
Proof
  strip_tac >> rewrite_tac[access_ok_def] >> reverse conj_tac
  >- (rpt gen_tac >> disch_tac >> irule ptr_dalloca_compare_transport >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `~in_revert_forward fn s` by metis_tac[] >>
  qpat_x_assum `access_ok _ _ _ _ _`
    (mp_tac o REWRITE_RULE[access_ok_def]) >>
  disch_then (CONJUNCTS_THEN2 (drule_then strip_assume_tac) kall_tac) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> irule ptr_dalloca_range_transport >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`G`, `source_memory_write_ranges inst s`,
                   `source_memory_write_ranges inst t`] >> fs[] >> gvs[]) >>
  rpt gen_tac >> disch_tac >> irule ptr_dalloca_range_transport >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G`, `source_memory_read_ranges inst s`,
               `source_memory_read_ranges inst t`] >> fs[] >> gvs[]
QED

Theorem ptr_dalloca_taint_transport:
  taint_ok fn tn inst s /\
  (!op. MEM op inst.inst_operands ==>
    op_taint tnt op SUBSET op_taint tn op) /\
  tnt.t_stor SUBSET tn.t_stor /\ tnt.t_trans SUBSET tn.t_trans /\
  (about_to_revert fn inst s ==> about_to_revert ft inst t) /\
  (inst.inst_opcode = MUL ==>
    !op. MEM op inst.inst_operands /\ op_taint tn op = {} ==>
      eval_operand op t = eval_operand op s) /\
  (~about_to_revert ft inst t ==>
    !off len i. MEM (off,len) (source_memory_read_ranges inst t) /\
      off <= i /\ i < off + len /\ i IN tnt.t_mem ==>
      ?off_s j. MEM (off_s,len) (source_memory_read_ranges inst s) /\
        off_s <= j /\ j < off_s + len /\ j IN tn.t_mem) ==>
  taint_ok ft tnt inst t
Proof
  strip_tac >>
  `!op. MEM op inst.inst_operands /\ op_taint tn op = {} ==>
    op_taint tnt op = {}` by metis_tac[SUBSET_EMPTY] >>
  qpat_x_assum `taint_ok _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[taint_ok_def]) >>
  rewrite_tac[taint_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `op_taint tn op <> {}` by metis_tac[SUBSET_EMPTY] >>
      qpat_x_assum `!op. MEM op _ /\ _ ==> _` (drule_all_then strip_assume_tac) >>
      simp[] >> fs[] >> metis_tac[MEM]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~about_to_revert fn inst s` by metis_tac[] >>
      qpat_x_assum `~about_to_revert ft inst t ==> _`
        (drule_then (drule_all_then strip_assume_tac)) >>
      metis_tac[]) >>
  metis_tac[SUBSET_EMPTY]
QED
