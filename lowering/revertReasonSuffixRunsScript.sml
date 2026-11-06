(* Ordinary suffix witnesses and structural allocation separation. *)
Theory revertReasonSuffixRuns
Ancestors
  stmtSimReason revertReasonRuns revertReasonLayout allocaSiteResource exprLoweringProps
  localPtrsProps venomExecProps venomExecSemantics venomMemDefs venomInst venomState
  words arithmetic finite_map list rich_list

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

Theorem revert_reason_suffix_certificate:
  reason_operand ds b /\ reason_operand ds p /\ reason_operand ds q ==>
  ?es. reason_prefix ds (TAKE 22 (revert_reason_suffix id v b p q)) es /\
    reason_operand es (Var (STRING #"%" (toString (v+19)))) /\
    reason_operand es (Var (STRING #"%" (toString (v+20))))
Proof
  strip_tac >>
  simp[revert_reason_suffix_def, TAKE_def, reason_prefix_def, mk_inst_def] >>
  rpt conj_tac >>
  simp[reason_step_def, mk_inst_def, reason_operand_def] >>
  Cases_on `b` >> Cases_on `p` >> Cases_on `q` >>
  gvs[reason_operand_def]
QED

Theorem revert_reason_suffix_split:
  revert_reason_suffix id v b p q =
    TAKE 22 (revert_reason_suffix id v b p q) ++
    [mk_inst (id+27) REVERT
      [Var (STRING #"%" (toString (v+19)));
       Var (STRING #"%" (toString (v+20))) ] []]
Proof
  simp[revert_reason_suffix_def, TAKE_def]
QED

Theorem revert_reason_suffix_run:
  reason_operand ds b /\ reason_operand ds p /\ reason_operand ds q /\
  reason_known ds s ==>
  ?t z. run_inst_seq (TAKE 22 (revert_reason_suffix id v b p q)) s = OK t /\
    run_inst_seq (revert_reason_suffix id v b p q) s = Abort Revert_abort z
Proof
  strip_tac >>
  `?es. reason_prefix ds (TAKE 22 (revert_reason_suffix id v b p q)) es /\
    reason_operand es (Var (STRING #"%" (toString (v+19)))) /\
    reason_operand es (Var (STRING #"%" (toString (v+20))))` by
      metis_tac[revert_reason_suffix_certificate] >>
  drule_all reason_prefix_sound >> strip_tac >>
  `?ow. lookup_var (STRING #"%" (toString (v+19))) t = SOME ow` by
    metis_tac[reason_operand_def, reason_known_def] >>
  `?lw. lookup_var (STRING #"%" (toString (v+20))) t = SOME lw` by
    metis_tac[reason_operand_def, reason_known_def] >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  once_rewrite_tac[revert_reason_suffix_split] >>
  drule run_inst_seq_append >>
  disch_then (qspec_then `[mk_inst (id+27) REVERT
    [Var (STRING #"%" (toString (v+19)));
     Var (STRING #"%" (toString (v+20))) ] []]` mp_tac) >>
  simp[run_inst_seq_def] >> disch_then SUBST1_TAC >>
  simp[mk_inst_def] >>
  `?z. step_inst_base (mk_inst (id+27) REVERT
    [Var (STRING #"%" (toString (v+19)));
     Var (STRING #"%" (toString (v+20))) ] []) t = Abort Revert_abort z` by
    (simp[mk_inst_def] >> metis_tac[step_revert_behavior, eval_operand_def]) >>
  gvs[mk_inst_def]
QED

Theorem revert_reason_suffix_witnesses:
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\
  lookup_var q s = SOME Q /\
  alloca_inv s /\ alloca_room ctx fn s /\
  MEM (mk_inst (id+5) ALLOCA [Lit 32w]
    [STRING #"%" (toString (v+4))]) (fn_insts fn) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\
  parent <> id+5 /\ 32 <= ms ==>
  ?sa c t z.
    step_inst_base (mk_inst (id+5) ALLOCA [Lit 32w]
      [STRING #"%" (toString (v+4))]) s = OK sa /\
    FLOOKUP sa.vs_allocas (id+5) = SOME (c,32) /\
    (w2n Q+32 <= c \/ c+32 <= w2n Q) /\
    (FLOOKUP s.vs_allocas (id+5) = NONE ==>
      s.vs_alloca_next+32 < dimword(:256)) /\
    (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==>
      sz=32 /\ a+32 < dimword(:256)) /\
    run_inst_seq (TAKE 22 (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK t /\
    run_inst_seq (revert_reason_suffix id v (Var b) (Var p) (Var q)) s =
      Abort Revert_abort z
Proof
  strip_tac >>
  `reason_operand [b;p;q] (Var b) /\ reason_operand [b;p;q] (Var p) /\
   reason_operand [b;p;q] (Var q) /\ reason_known [b;p;q] s` by
    (simp[reason_operand_def, reason_known_def] >> metis_tac[]) >>
  `?t z. run_inst_seq (TAKE 22
      (revert_reason_suffix id v (Var b) (Var p) (Var q))) s = OK t /\
    run_inst_seq (revert_reason_suffix id v (Var b) (Var p) (Var q)) s =
      Abort Revert_abort z` by metis_tac[revert_reason_suffix_run] >>
  drule_all revert_reason_size_cell_allocate >> strip_tac >>
  metis_tac[]
QED
