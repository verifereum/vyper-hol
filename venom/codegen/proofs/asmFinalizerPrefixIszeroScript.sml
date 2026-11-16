Theory asmFinalizerPrefixIszero
Ancestors
  asmOptMergeIszero asmSplice asmSymPc finalizerContract asmSymSem
  asmOptimizer asmWf asmSem vfmExecution list asmFinalizerPrefixCompose

Theorem iszero_pair_prefix_window:
  !pre x rest env ss.
    asm_returns_zero_or_one x /\ ss.sym_base.as_pc = LENGTH pre /\
    ss.sym_base.as_stack = [] ==>
    (!i a. i < 3 /\ sym_steps (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) env i ss = SymOK
      a ==>
       ~(a.sym_base.as_pc < LENGTH (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) /\ EL
         a.sym_base.as_pc (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) = AsmOp "GAS")) /\
    (!a. sym_steps (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) env 3 ss = SymOK a ==>
       sym_steps (pre ++ [x] ++ rest) env 1 ss =
         SymOK (sym_with_pc (splice_pc (LENGTH pre) 3 1 a.sym_base.as_pc) a) /\
       LENGTH pre + 3 <= a.sym_base.as_pc)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
  `x <> AsmOp "JUMP" /\ x <> AsmOp "JUMPI" /\ x <> AsmOp "GAS"`
    by gvs[asm_returns_zero_or_one_def] >>
  qabbrev_tac `p = pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest` >>
  qabbrev_tac `q = pre ++ [x] ++ rest` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = x /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmOp "ISZERO" /\
   LENGTH pre + 2 < LENGTH p /\ EL (LENGTH pre + 2) p = AsmOp "ISZERO" /\
   LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = x`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `sym_step q env x ss = sym_step p env x ss`
    by (irule sym_step_prog_cong >> simp[Abbr `p`, Abbr `q`]) >>
  Cases_on `sym_step p env x ss`
  >- (rename1 `sym_step p env x ss = SymOK s1` >>
      drule_all sym_step_zero_or_one >>
      disch_then (qx_choosel_then [`w`, `stk`] (CONJUNCTS_THEN assume_tac)) >>
      `s1.sym_base.as_pc = LENGTH pre + 1`
        by (drule_at (Pos last) sym_step_pc_next >> simp[]) >>
      drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
      qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") s1 = SymOK s2` >>
      `s2.sym_stack = Val (b2w (w = 0w)) :: stk /\
       s2.sym_base.as_pc = LENGTH pre + 2`
        by simp[Abbr `s2`, asm_next_def] >>
      drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
          gvs[sym_steps_pos, sym_steps_def]) >>
      `s1.sym_base.as_stack = []`
        by metis_tac[sym_step_base_stack] >>
      simp[sym_steps_pos, sym_steps_def] >> rpt strip_tac >> gvs[] >>
      simp[Abbr `s2`, asm_next_def, splice_pc_def, sym_with_pc_def,
           sym_state_component_equality, asm_state_component_equality,
           wordsTheory.n2w_11, wordsTheory.ONE_LT_dimword,
           b2w_def]) >>
  (conj_tac
   >- (rpt gen_tac >> strip_tac >>
       `i = 0 \/ i = 1 \/ i = 2` by decide_tac >>
       gvs[sym_steps_pos, sym_steps_def]) >>
   simp[sym_steps_pos])
QED

Theorem iszero_jumpi_prefix_window:
  !pre l rest env ss.
    ss.sym_base.as_pc = LENGTH pre /\ ss.sym_base.as_stack = [] ==>
    (!i a. i < 4 /\ sym_steps (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                    AsmPushLabel l :: AsmOp "JUMPI" :: rest) env i ss = SymOK a ==>
       ~(a.sym_base.as_pc < LENGTH (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                    AsmPushLabel l :: AsmOp "JUMPI" :: rest) /\ EL a.sym_base.as_pc (pre ++ [AsmOp
                      "ISZERO"; AsmOp "ISZERO"] ++
                    AsmPushLabel l :: AsmOp "JUMPI" :: rest) = AsmOp "GAS")) /\
    (!a. sym_steps (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                    AsmPushLabel l :: AsmOp "JUMPI" :: rest) env 4 ss = SymOK a ==>
       sym_steps (pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest) env 2 ss =
         SymOK (sym_with_pc (splice_pc (LENGTH pre) 2 0 a.sym_base.as_pc) a) /\
       (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + 2 <= a.sym_base.as_pc))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [LET_THM] >>
  qabbrev_tac `p = pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                       AsmPushLabel l :: AsmOp "JUMPI" :: rest` >>
  qabbrev_tac `q = pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmOp "ISZERO" /\
   LENGTH pre + 1 < LENGTH p /\ EL (LENGTH pre + 1) p = AsmOp "ISZERO" /\
   LENGTH pre + 2 < LENGTH p /\ EL (LENGTH pre + 2) p = AsmPushLabel l /\
   LENGTH pre + 3 < LENGTH p /\ EL (LENGTH pre + 3) p = AsmOp "JUMPI" /\
   LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = AsmPushLabel l /\
   LENGTH pre + 1 < LENGTH q /\ EL (LENGTH pre + 1) q = AsmOp "JUMPI"`
    by simp[Abbr `p`, Abbr `q`, EL_APPEND_EQN] >>
  `INDEX_OF (AsmLabel l) q =
     OPTION_MAP (splice_pc (LENGTH pre) 2 0) (INDEX_OF (AsmLabel l) p) /\
   (!j. INDEX_OF (AsmLabel l) p = SOME j ==> j < LENGTH pre \/ LENGTH pre + 2 <= j)`
    by (mp_tac (Q.INST [`pfx` |-> `pre`,
                        `pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                        `repl` |-> `[]`,
                        `sfx` |-> `AsmPushLabel l :: AsmOp "JUMPI" :: rest`]
                  splice_index_of_label) >> simp[Abbr `p`, Abbr `q`]) >>
  qspecl_then [`ss`, `p`, `env`] strip_assume_tac
    (GEN_ALL sym_step_iszero_cases)
  >~ [`SymError`] >-
    (conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
         gvs[sym_steps_pos, sym_steps_def]) >> simp[sym_steps_pos])
  >~ [`SymBad`] >-
    (conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
         gvs[sym_steps_pos, sym_steps_def]) >> simp[sym_steps_pos]) >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") ss = SymOK s1` >>
  `s1.sym_stack = Val (b2w (w = 0w)) :: stk /\ s1.sym_base.as_pc = LENGTH pre + 1`
    by simp[Abbr `s1`, asm_next_def] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step p env (AsmOp "ISZERO") s1 = SymOK s2` >>
  `s2.sym_stack = Val (b2w (b2w (w = 0w) = (0w:bytes32))) :: stk /\
   s2.sym_base.as_pc = LENGTH pre + 2`
    by simp[Abbr `s2`, asm_next_def] >>
  qabbrev_tac `s3 = s2 with <|sym_base := asm_next s2.sym_base;
                             sym_stack := Lab l 0 :: s2.sym_stack|>` >>
  `sym_step p env (AsmPushLabel l) s2 = SymOK s3`
    by simp[Abbr `s3`, sym_step_push_label] >>
  `s3.sym_stack = Lab l 0 :: Val (b2w (b2w (w = 0w) = (0w:bytes32))) :: stk /\
   s3.sym_base.as_pc = LENGTH pre + 3`
    by simp[Abbr `s3`, asm_next_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
      gvs[sym_steps_pos, sym_steps_def]) >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_jumpi_label >>
  qabbrev_tac `t1 = ss with <|sym_base := asm_next ss.sym_base;
                             sym_stack := Lab l 0 :: ss.sym_stack|>` >>
  `sym_step q env (AsmPushLabel l) ss = SymOK t1`
    by simp[Abbr `t1`, sym_step_push_label] >>
  `t1.sym_stack = Lab l 0 :: Val w :: stk /\ t1.sym_base.as_pc = LENGTH pre + 1`
    by simp[Abbr `t1`, asm_next_def] >>
  drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_jumpi_label >>
  `((b2w (b2w (w = 0w) = (0w:bytes32)) = (0w:bytes32)) = (w = 0w))`
    by (Cases_on `w = 0w` >> simp[b2w_def, wordsTheory.n2w_11,
                                wordsTheory.ONE_LT_dimword]) >>
  simp[sym_steps_pos, sym_steps_def] >>
  Cases_on `w = 0w`
  >- (simp[] >> rpt strip_tac >> gvs[] >>
      simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t1`, asm_next_def,
           splice_pc_def, sym_with_pc_def, sym_state_component_equality,
           asm_state_component_equality]) >>
  Cases_on `INDEX_OF (AsmLabel l) p` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `t1`, asm_next_def,
       splice_pc_def, sym_with_pc_def, sym_state_component_equality,
       asm_state_component_equality] >>
  metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem merge_iszero_pairs_relation[local]:
  !R. (!p. R p p) /\
      (!p q r. R p q /\ R q r ==> R p r) /\
      (!pre x rest. asm_returns_zero_or_one x /\
         asm_static_wf (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) ==>
         R (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest)
           (pre ++ x :: rest)) ==>
      !sfx pre. asm_static_wf (pre ++ sfx) ==>
        R (pre ++ sfx) (pre ++ FST (merge_iszero_pairs sfx))
Proof
  gen_tac >> strip_tac >> ho_match_mp_tac merge_iszero_pairs_ind >>
  reverse (rpt conj_tac)
  >- simp[merge_iszero_pairs_def]
  >- simp[merge_iszero_pairs_def]
  >- simp[merge_iszero_pairs_def] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_pairs_fst] >>
  reverse IF_CASES_TAC
  >- (rpt strip_tac >> fs[] >>
      qpat_x_assum `!pre. asm_static_wf (pre ++ y::z::rest) ==> _`
        (qspec_then `pre ++ [x]` mp_tac) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  gvs[] >> rpt strip_tac >>
  `?name. x = AsmOp name` by gvs[asm_returns_zero_or_one_def] >>
  gvs[] >>
  `asm_static_wf (pre ++ AsmOp name :: rest)`
    by (mp_tac (Q.INST [`pfx` |-> `pre`,
                        `pat` |-> `[AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                        `repl` |-> `[AsmOp name]`, `sfx` |-> `rest`]
                  asm_splice_static_wf) >>
        simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
             symbolResolveTheory.asm_inst_size_def] >>
        pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >> simp[]) >>
  qpat_x_assum `!pre'. asm_static_wf (pre' ++ AsmOp name::rest) ==> _`
    (qspec_then `pre` assume_tac) >>
  qpat_x_assum `!p q r. _` irule >>
  qexists_tac `pre ++ AsmOp name :: rest` >>
  conj_tac
  >- (qpat_x_assum `!pre x rest. asm_returns_zero_or_one x /\ _ ==> _` mp_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      disch_then irule >> simp[]) >> simp[]
QED

Theorem merge_iszero_jumpi_relation[local]:
  !R. (!p. R p p) /\
      (!p q r. R p q /\ R q r ==> R p r) /\
      (!pre l rest. asm_static_wf
         (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
          AsmPushLabel l :: AsmOp "JUMPI" :: rest) ==>
         R (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
            AsmPushLabel l :: AsmOp "JUMPI" :: rest)
           (pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest)) ==>
      !sfx pre. asm_static_wf (pre ++ sfx) ==>
        R (pre ++ sfx) (pre ++ FST (merge_iszero_jumpi sfx))
Proof
  gen_tac >> strip_tac >> ho_match_mp_tac merge_iszero_jumpi_ind >>
  reverse (rpt conj_tac)
  >- simp[merge_iszero_jumpi_def]
  >- simp[merge_iszero_jumpi_def]
  >- simp[merge_iszero_jumpi_def]
  >- simp[merge_iszero_jumpi_def] >>
  rpt gen_tac >> strip_tac >> simp[merge_iszero_jumpi_fst] >>
  reverse IF_CASES_TAC
  >- (rpt strip_tac >> fs[] >>
      qpat_x_assum `!pre. asm_static_wf (pre ++ b::c::d::rest) ==> _`
        (qspec_then `pre ++ [a]` mp_tac) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  Cases_on `c` >> gvs[asm_is_push_label_def] >>
  rename1 `AsmPushLabel lbl` >> rpt strip_tac >>
  `asm_static_wf (pre ++ AsmPushLabel lbl :: AsmOp "JUMPI" :: rest)`
    by (mp_tac (Q.INST [`pfx` |-> `pre`,
                        `pat` |-> `[AsmOp "ISZERO"; AsmOp "ISZERO"]`,
                        `repl` |-> `[]`,
                        `sfx` |-> `AsmPushLabel lbl :: AsmOp "JUMPI" :: rest`]
                  asm_splice_static_wf) >>
        simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
             symbolResolveTheory.asm_inst_size_def] >>
        pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
  qpat_x_assum `!pre'. asm_static_wf (pre' ++ AsmPushLabel lbl::_) ==> _`
    (qspec_then `pre` assume_tac) >>
  qpat_x_assum `!p q r. _` irule >>
  qexists_tac `pre ++ AsmPushLabel lbl :: AsmOp "JUMPI" :: rest` >>
  conj_tac
  >- (qpat_x_assum `!pre l rest. asm_static_wf _ ==> _` mp_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      disch_then irule >> simp[]) >> simp[]
QED

(* Quotation abbreviations only; all three propositions expand in theorem headers. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m + 1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
      ?m b. sym_steps q env m (sym_init s) = SymOK b /\
            b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
            b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

val single_site = ``!pre pat repl post D.
  asm_splice_ok pat repl /\ asm_static_wf (pre ++ pat ++ post) /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  (!env u. u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        ~(a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
          EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp "GAS")) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. sym_steps (pre ++ repl ++ post) env e u =
            SymOK (sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)
                               a.sym_base.as_pc) a) /\
            (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
            (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc))) ==>
  ^transport (pre ++ pat ++ post) (pre ++ repl ++ post)``;

val transitive_transport = ``!p q r.
  ^transport p q /\ ^transport q r ==> ^transport p r``;

Theorem iszero_pair_site_conditional[local]:
  ^single_site ==> !pre x rest.
    asm_returns_zero_or_one x /\
    asm_static_wf (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) ==>
    ^transport (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest)
               (pre ++ [x] ++ rest)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  `?name. x = AsmOp name` by gvs[asm_returns_zero_or_one_def] >>
  qpat_x_assum `x = AsmOp name` SUBST_ALL_TAC >>
  qpat_x_assum `!pre pat repl post D. _` irule >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
       symbolResolveTheory.asm_inst_size_def] >> qexists_tac `3` >>
  rpt gen_tac >> strip_tac >> qexists_tac `3` >> simp[] >>
  mp_tac (Q.SPECL [`pre`, `AsmOp name`, `rest`, `env`, `u`]
                 iszero_pair_prefix_window) >>
  simp_tac bool_ss [LET_THM] >> (impl_tac >- simp[]) >> strip_tac >> fs[] >>
  conj_tac >- gvs[] >> rpt strip_tac >>
  qexists_tac `1` >> simp[] >> metis_tac[]
QED

Theorem iszero_jumpi_site_conditional[local]:
  ^single_site ==> !pre l rest.
    asm_static_wf (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                         AsmPushLabel l :: AsmOp "JUMPI" :: rest) ==>
    ^transport (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                      AsmPushLabel l :: AsmOp "JUMPI" :: rest)
               (pre ++ [] ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest)
Proof
  BETA_TAC >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!pre pat repl post D. _` irule >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
       symbolResolveTheory.asm_inst_size_def] >> qexists_tac `4` >>
  rpt gen_tac >> strip_tac >> qexists_tac `4` >> simp[] >>
  mp_tac (Q.SPECL [`pre`, `l`, `rest`, `env`, `u`]
                 iszero_jumpi_prefix_window) >>
  simp_tac bool_ss [LET_THM] >> (impl_tac >- simp[]) >> strip_tac >> fs[] >>
  conj_tac >- gvs[] >> rpt strip_tac >>
  qexists_tac `2` >> simp[] >> metis_tac[]
QED

Theorem merge_iszero_prefix_transport_conditional:
  ^single_site /\ ^transitive_transport ==>
  !p. asm_static_wf p ==> ^transport p (FST (merge_iszero p))
Proof
  strip_tac >>
  drule iszero_pair_site_conditional >> disch_then assume_tac >>
  drule iszero_jumpi_site_conditional >> disch_then assume_tac >>
  qpat_x_assum `!pre pat repl post D. _` kall_tac >>
  `!sfx pre. asm_static_wf (pre ++ sfx) ==>
      ^transport (pre ++ sfx) (pre ++ FST (merge_iszero_pairs sfx))`
    by (qspec_then `^transport` mp_tac merge_iszero_pairs_relation >>
        impl_tac
        >- (conj_tac >- ACCEPT_TAC prefix_transport_refl >>
            conj_tac >- first_assum ACCEPT_TAC >>
            pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
            qpat_x_assum `!pre x rest. asm_returns_zero_or_one x /\ _ ==> _` mp_tac >>
            pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
        simp[]) >>
  `!sfx pre. asm_static_wf (pre ++ sfx) ==>
      ^transport (pre ++ sfx) (pre ++ FST (merge_iszero_jumpi sfx))`
    by (qspec_then `^transport` mp_tac merge_iszero_jumpi_relation >>
        impl_tac
        >- (conj_tac >- ACCEPT_TAC prefix_transport_refl >>
            conj_tac >- first_assum ACCEPT_TAC >>
            pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
            qpat_x_assum `!pre l rest. asm_static_wf _ ==> _` mp_tac >>
            pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]) >>
        simp[]) >>
  rpt gen_tac >> strip_tac >> rewrite_tac[merge_iszero_fst] >>
  `asm_static_wf (FST (merge_iszero_pairs p))`
    by (mp_tac (Q.SPECL [`p`, `[]`] merge_iszero_pairs_refines_under) >>
        simp[asm_refines_def] >> metis_tac[]) >>
  qpat_x_assum `!p q r. _` irule >>
  qexists_tac `FST (merge_iszero_pairs p)` >>
  conj_tac
  >- (qpat_x_assum `!sfx pre. _ ==> ^transport _ (_ ++ FST (merge_iszero_pairs _))`
        (qspecl_then [`p`, `[]`] mp_tac) >> simp[]) >>
  qpat_x_assum `!sfx pre. _ ==> ^transport _ (_ ++ FST (merge_iszero_jumpi _))`
    (qspecl_then [`FST (merge_iszero_pairs p)`, `[]`] mp_tac) >> simp[]
QED
