Theory bodyIntCallStageSnocMods
Ancestors
  bodyIntCallStagePacketMods venomOperandProps venomState venomInst
  ptrDiscipline loweringStateRelDefs vyperContext vyperTypeSystem
  list arithmetic

Theorem snoc_index_limit[local]:
  i < n + 1 <=> i < n \/ i = n
Proof
  decide_tac
QED

Theorem intcall_stage_ops_nil_mods:
  intcall_stage_ops_mods (lo,func) cenv cx sa cut pin ([],[],[],[],[])
Proof
  PairCases_on `cut` >> simp[intcall_stage_ops_mods_def, eval_operands_def]
QED

(* Both packets are certified at the same, new endpoint. Only the mixed
   pair needs a separate disjointness premise. *)
Theorem intcall_stage_ops_snoc_mods:
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops,ws,vals,ptys,pflags) /\
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    ([op],[w],[v],[ty],[flag]) /\
  (!i b k c l. i < LENGTH ops /\ ~EL i pflags /\ ~flag /\
    op_prov G (EL i ops) = SOME (b,k) /\ op_prov G op = SOME (c,l) ==>
    regions_disjoint b k c l) ==>
  intcall_stage_ops_mods (lo,func) cenv cx sa (si,esi,s,G,tn) pin
    (ops ++ [op],ws ++ [w],vals ++ [v],ptys ++ [ty],pflags ++ [flag])
Proof
  rewrite_tac[intcall_stage_ops_mods_def] >> strip_tac >>
  simp[eval_operands_append, EVERY_APPEND, MEM_APPEND] >>
  conj_tac
  >- (qx_gen_tac `x` >> strip_tac
      >- (qpat_assum `!x. MEM (Var x) ops ==> _` irule >> simp[]) >>
      qpat_assum `!x. MEM (Var x) [op] ==> _` irule >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `j` >> Cases_on `j < LENGTH ops`
      >- (simp[EL_APPEND_EQN] >>
          qpat_assum `!j. j < LENGTH ops /\ _ ==> _` (qspec_then `j` mp_tac) >>
          simp[]) >>
      simp[snoc_index_limit] >> strip_tac >>
      qpat_x_assum `j = LENGTH ops` SUBST_ALL_TAC >>
      qpat_x_assum `~EL _ _` mp_tac >> simp[EL_APPEND_EQN] >> disch_tac >>
      qpat_assum `!j. j < LENGTH [op] /\ _ ==> _`
        (qspec_then `0` (mp_tac o SIMP_RULE (srw_ss()) [])) >>
      simp[]) >>
  conj_tac
  >- (rpt gen_tac >> Cases_on `i < LENGTH ops`
      >- (Cases_on `j < LENGTH ops`
          >- (simp[EL_APPEND_EQN] >> strip_tac >>
              qpat_assum `!i j b k c l. i < j /\ j < LENGTH ops /\ _ ==> _` irule >>
              qexistsl_tac [`i`,`j`] >> simp[]) >>
          Cases_on `j = LENGTH ops` >> simp[EL_APPEND_EQN,snoc_index_limit] >>
          strip_tac >>
          qpat_assum `!i b k c l. i < LENGTH ops /\ _ ==> _` irule >>
          simp[] >> qexists_tac `i` >> simp[]) >>
      strip_tac >>
      qpat_assum `~(i < LENGTH ops)` mp_tac >>
      qpat_assum `j < LENGTH ops + 1` mp_tac >>
      qpat_assum `i < j` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  rpt gen_tac >> Cases_on `j < LENGTH ops`
  >- (simp[EL_APPEND_EQN] >> disch_tac >>
      qpat_assum `!j rt. j < LENGTH ops /\ _ ==> _` (qspecl_then [`j`,`rt`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> gvs[AC ADD_COMM ADD_ASSOC]) >>
  Cases_on `j = LENGTH ops` >> simp[EL_APPEND_EQN,snoc_index_limit] >>
  disch_tac >>
  qpat_assum `!j rt. j < LENGTH [op] /\ _ ==> _`
    (qspecl_then [`0`,`rt`] (mp_tac o SIMP_RULE (srw_ss()) [])) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[AC ADD_COMM ADD_ASSOC]
QED
