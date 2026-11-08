(* Shared concrete witnesses for compatibility and effect-bearing field copies.
   Descendant execution lemmas are supplied, never imported here. *)
structure typedCopyBytesFieldsLib =
struct
open HolKernel boolLib bossLib
open typedCopyFieldsPtrTheory typedCopyBytesRobustPtrTheory typedCopyOffsetPtrTheory
     typedCopyAgreementTheory exprLoweringPropsTheory contextCodegenRelPropsTheory
     bodyPtrDefsTheory fragExecPtrTheory wordsTheory finite_mapTheory listTheory
     arithmeticTheory contextCodegenRelTheory compileEnvTheory abiEncoderInputTheory

fun field (offset, robust, next_var) =
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  drule_all offset >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `lookup_var p s1 = SOME (n2w (w2n b+doff))` >>
  rename1 `ptr_covers G1 tn1 p s1 n` >>
  `not_fresh_at sb src /\ lookup_var src s1 = SOME a /\
   ptr_covers G1 tn1 src s1 stotal` by
    (qpat_assum `!q. not_fresh_at sa q ==> _` (qspec_then `src` strip_assume_tac) >>
     conj_tac >-
       (`sa.cs_next_var <= sb.cs_next_var` by metis_tac[next_var] >>
        fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
     simp[] >> gvs[ptr_covers_def]) >>
  qpat_x_assum `compile_with_byte_offset (Var src) soff sb = _` assume_tac >>
  drule_all offset >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `lookup_var q s2 = SOME (n2w (w2n a+soff))` >>
  rename1 `ptr_covers G2 tn2 q s2 n` >>
  `not_fresh_at sc p /\ lookup_var p s2 = SOME (n2w (w2n b+doff)) /\
   ptr_covers G2 tn2 p s2 n` by suspend "destination_offset" >>
  `compile_store_bytestring (Var q) (Var p) sc = ((),sd)` by
    (gvs[compile_store_memory_typed_bytes]) >>
  `!m. mem_agree_outside tn2.t_mem s2.vs_memory m ==>
     val_in_memory stv v (w2n (n2w (w2n a+soff):bytes32)) m` by
    (gvs[w2n_n2w, LESS_MOD]) >>
  drule_all robust >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  suspend "package";

fun destination_offset next_var =
  markerLib.RESUME_TAC >>
  qpat_assum `!q. not_fresh_at sb q ==> _` (qspec_then `p` strip_assume_tac) >>
  conj_tac >-
    (`sb.cs_next_var <= sc.cs_next_var` by metis_tac[next_var] >>
     gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  simp[] >> gvs[ptr_covers_def];

fun package shape =
  markerLib.RESUME_TAC >>
  drule shape >> strip_tac >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac >-
    (irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sb _ _ _` (irule_at Any) >>
     simp[] >> conj_tac >- metis_tac[cs_extends_trans] >>
     irule frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sb sc _ _ _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ sa sb _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ sb sc _ _ _` kall_tac >>
  qpat_x_assum `frag_exec_ptr _ _ _ sc sd _ _ _` kall_tac >>
  qpat_x_assum `sf.vs_memory = _` kall_tac >>
  qpat_x_assum `n = _` kall_tac >>
  qpat_x_assum `(?bs. _) \/ _` kall_tac >>
  gvs[w2n_n2w, LESS_MOD, AC ADD_ASSOC ADD_COMM] >>
  asm_rewrite_tac[] >> suspend "old_vars";

fun old_vars next_var =
  markerLib.RESUME_TAC >>
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var` by
    metis_tac[next_var] >>
  qx_gen_tac `z` >> strip_tac >>
  `not_fresh_at sb z /\ not_fresh_at sc z` by
    (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  qpat_x_assum `!q. not_fresh_at sa q ==> _` (qspec_then `z` mp_tac) >>
  qpat_x_assum `!q. not_fresh_at sb q ==> _` (qspec_then `z` mp_tac) >>
  qpat_x_assum `!q. not_fresh_at sc q ==> _` (qspec_then `z` mp_tac) >> simp[];

fun fields_head field_execution =
  markerLib.RESUME_TAC >>
  qpat_assum `compile_with_byte_offset (Var dst) doff sa = _`
    (mp_then Any mp_tac (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] field_execution)) >>
  disch_then drule >> disch_then drule >>
  disch_then (mp_tac o SRULE []) >>
  qpat_assum `ptr_covers G tn dst s dtotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `ptr_covers G tn src s stotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var dst s = SOME b`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var src s = SOME a`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `evaluate_type tenv st = SOME stv`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `evaluate_type tenv dt = SOME dtv`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `value_has_type stv v`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] mp_tac) >>
  disch_then (qspec_then `len` mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     asm_simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> decide_tac)) >>
  strip_tac >> suspend "field_endpoint";

fun fields_endpoint (shape, next_var) =
  markerLib.RESUME_TAC >>
  rename1 `frag_exec_ptr cx ctx PG sa sm _
    (\g t v. g = G1 /\ t = tn1 /\ v = s1) R` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     `compile_store_bytestring src_ptr dst_ptr cs'' = ((),sm)` by
       metis_tac[compile_store_memory_typed_bytes] >>
     drule shape >> strip_tac >> metis_tac[next_var, LESS_EQ_TRANS]) >>
  `not_fresh_at sm dst /\ not_fresh_at sm src /\
   lookup_var dst s1 = SOME b /\ lookup_var src s1 = SOME a /\
   ptr_covers G1 tn1 dst s1 dtotal /\ ptr_covers G1 tn1 src s1 stotal` by
    (qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` kall_tac >>
     conj_tac >- metis_tac[not_fresh_at_def, LESS_EQ_TRANS] >>
     conj_tac >- metis_tac[not_fresh_at_def, LESS_EQ_TRANS] >>
     full_simp_tac std_ss [ptr_covers_def] >> metis_tac[optionTheory.SOME_11]) >>
  `!i. i < LENGTH dts ==> !m.
     mem_agree_outside tn1.t_mem s1.vs_memory m ==>
     val_in_memory (EL i stvs') (EL i vals')
       (w2n a + (soff + type_memory_bytes cenv st +
         SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))) m` by
    (qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _` kall_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> _` (qspec_then `i` mp_tac) >>
     asm_simp_tac bool_ss [] >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
     `SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
        type_memory_bytes cenv (EL i sts) <=
        SUM (MAP (type_memory_bytes cenv) sts)` by
       (irule abi_encoder_prefix_sum_bound >> asm_rewrite_tac[]) >>
     qpat_x_assum `!ft fv p. _` (qspec_then `EL i stvs'` mp_tac) >>
     disch_then (qspec_then `EL i vals'` mp_tac) >>
     disch_then (qspec_then
       `w2n a + (soff + type_memory_bytes cenv st +
          SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))` mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     (impl_tac >- decide_tac) >>
     (impl_tac >-
       (`w2n a + (soff + type_memory_bytes cenv st +
           SUM (MAP (type_memory_bytes cenv) (TAKE i sts))) =
         soff + (SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) +
           (w2n a + type_memory_bytes cenv st))` by decide_tac >>
        asm_rewrite_tac[])) >> simp[]) >> suspend "tail";

val fields_tail =
  markerLib.RESUME_TAC >>
  qpat_x_assum `!sts dtvs stvs vals lens tenv cx ctx PG R cenv dst src sa sz a b G tn s dtotal stotal doff soff. _`
    (qspecl_then [`sts`, `dtvs'`, `stvs'`, `vals'`, `lens'`, `tenv`,
                  `cx`, `ctx`, `PG`, `R`] mp_tac) >>
  disch_then (mp_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  qpat_assum `compile_typed_copy_fields _ _ _ _ _ _ _ sm = _`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `ptr_covers G1 tn1 dst s1 dtotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `ptr_covers G1 tn1 src s1 stotal`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var dst s1 = SOME b`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  qpat_assum `lookup_var src s1 = SOME a`
    (fn fact => disch_then (fn th => mp_then Any mp_tac th fact)) >>
  (impl_tac >-
    (ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH dts ==> is_bytestring_type _ /\ _`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
     qpat_x_assum `!i. i < LENGTH dts ==> !m. _` (qspec_then `i` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
     ntac 13 (conj_tac >- first_assum ACCEPT_TAC) >>
     ntac 8 (conj_tac >- decide_tac) >>
     `soff + type_memory_bytes cenv st +
        (SUM (MAP (type_memory_bytes cenv) (TAKE i sts)) + w2n a) =
      w2n a + (soff + type_memory_bytes cenv st +
        SUM (MAP (type_memory_bytes cenv) (TAKE i sts)))` by decide_tac >>
     asm_rewrite_tac[])) >>
  strip_tac >> suspend "fields_package";

fun fields_package effects =
  markerLib.RESUME_TAC >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >>
  conj_tac >- metis_tac[frag_exec_ptr_seq] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  (if effects then
     (conj_tac >- asm_rewrite_tac[] >> conj_tac >- asm_rewrite_tac[])
   else all_tac) >>
  conj_tac >-
    (qx_gen_tac `p` >> strip_tac >>
     `not_fresh_at sm p` by metis_tac[not_fresh_at_def, LESS_EQ_TRANS] >>
     metis_tac[]) >> suspend "fields_memory";

val fields_memory =
  markerLib.RESUME_TAC >>
  conj_tac >-
    (qx_gen_tac `i` >> strip_tac >>
     `mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s1.vs_memory` by
       (qpat_x_assum `!i. _ ==> mem_bytes_at _ _ sf.vs_memory = _`
          (qspec_then `i` mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
     `mem_bytes_at i 1 s1.vs_memory = mem_bytes_at i 1 s.vs_memory` by
       (qpat_x_assum `!i. _ ==> mem_bytes_at _ _ s1.vs_memory = _`
          (qspec_then `i` mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
     metis_tac[]) >>
  conj_tac >-
    (qx_gen_tac `i` >> strip_tac >>
     `i IN tnf.t_mem <=> i IN tn1.t_mem` by
       (qpat_x_assum `!i. _ ==> (i IN tnf.t_mem <=> _)`
          (qspec_then `i` mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
     `i IN tn1.t_mem <=> i IN tn.t_mem` by
       (qpat_x_assum `!i. _ ==> (i IN tn1.t_mem <=> _)`
          (qspec_then `i` mp_tac) >> (impl_tac >- decide_tac) >> simp[]) >>
     metis_tac[]) >> suspend "fields_elements";

val fields_elements =
  markerLib.RESUME_TAC >>
  conj_tac >-
    (qx_gen_tac `i` >> strip_tac >> Cases_on `i`
     >- (pure_rewrite_tac [EL, TAKE_def, MAP, SUM, ADD_CLAUSES] >>
         qpat_x_assum `!ft fv p. _ ==> _ ==> _ ==> !m.
           mem_agree_outside tnf.t_mem _ _ ==> _`
           (qspecl_then [`dtv`, `v`, `doff + w2n b`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> (impl_tac >- decide_tac) >>
         (impl_tac >-
           (`doff + w2n b = w2n b + doff` by decide_tac >> asm_rewrite_tac[])) >>
         simp[]) >>
     rename1 `SUC j < SUC (LENGTH dts)` >>
     simp_tac (srw_ss()) [EL, TAKE_def, MAP, SUM, TL] >>
     qpat_x_assum `!i. i < LENGTH dts ==> !m.
       mem_agree_outside tnf.t_mem _ _ ==> _` (qspec_then `j` mp_tac) >>
     (impl_tac >- decide_tac) >>
     `doff + (type_memory_bytes cenv dt +
        SUM (MAP (type_memory_bytes cenv) (TAKE j dts)) + w2n b) =
      doff + type_memory_bytes cenv dt +
        (SUM (MAP (type_memory_bytes cenv) (TAKE j dts)) + w2n b)` by decide_tac >>
     asm_rewrite_tac[]) >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_x_assum `!ft fv p. _ ==> _ ==> _ ==> !m.
    mem_agree_outside tnf.t_mem _ _ ==> _` (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> (impl_tac >- decide_tac) >>
  (impl_tac >-
    (qpat_x_assum `!ft fv p. _ ==> _ ==> _ ==> !m.
       mem_agree_outside tn1.t_mem _ _ ==> _` (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> (impl_tac >- decide_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[])) >> simp[];
end
