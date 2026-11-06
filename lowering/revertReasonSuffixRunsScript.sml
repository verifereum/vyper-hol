(* Ordinary suffix witnesses and structural allocation separation. *)
Theory revertReasonSuffixRuns
Ancestors
  revertReasonRuns revertReasonLayout allocaSiteResource exprLoweringProps
  localPtrsProps venomExecSemantics venomMemDefs venomInst venomState
  words arithmetic finite_map

Theorem mk_inst_alloca_fields[local]:
  (mk_inst id ALLOCA [Lit n] [out]).inst_id = id /\
  (mk_inst id ALLOCA [Lit n] [out]).inst_opcode = ALLOCA /\
  (mk_inst id ALLOCA [Lit n] [out]).inst_operands = [Lit n] /\
  (mk_inst id ALLOCA [Lit n] [out]).inst_outputs = [out]
Proof
  simp[mk_inst_def]
QED

Theorem revert_reason_size_cell_allocate:
  alloca_inv s /\ alloca_room ctx fn s /\
  MEM (mk_inst (id+5) ALLOCA [Lit 32w] [out]) (fn_insts fn) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\
  parent <> id+5 /\ 32 <= ms ==>
  ?sa c.
    step_inst_base (mk_inst (id+5) ALLOCA [Lit 32w] [out]) s = OK sa /\
    FLOOKUP sa.vs_allocas (id+5) = SOME (c,32) /\
    (w2n Q+32 <= c \/ c+32 <= w2n Q) /\
    (FLOOKUP s.vs_allocas (id+5) = NONE ==>
      s.vs_alloca_next+32 < dimword(:256)) /\
    (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==>
      sz=32 /\ a+32 < dimword(:256))
Proof
  strip_tac >>
  `32 MOD dimword(:256) = 32` by
    simp_tac (srw_ss()) [dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  drule_at (Pat `MEM _ _`) alloca_site32_execute >>
  disch_then (qspecl_then [`s`,`out`,`ctx`] mp_tac) >>
  pure_rewrite_tac[mk_inst_alloca_fields] >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `FLOOKUP t.vs_allocas parent = SOME (w2n Q,ms)` by metis_tac[] >>
  `regions_disjoint (w2n Q,ms) (b,32)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
  qexistsl_tac [`t`,`b`] >>
  conj_tac >-
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_alloca_fields] >> simp_tac (srw_ss()) [] >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (qpat_x_assum `regions_disjoint _ _` mp_tac >>
     pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  reverse conj_tac >-
    (rpt strip_tac >>
     `a+sz <= s.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
     `s.vs_alloca_next < dimword(:256)` by metis_tac[alloca_room_next_lt] >>
     metis_tac[LESS_EQ_LESS_TRANS]) >>
  strip_tac >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  pure_rewrite_tac[exec_alloca_def, mk_inst_alloca_fields] >>
  asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [LET_THM] >>
  disch_then (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ < dimword(:256)` mp_tac >>
  simp[update_var_def]

QED
