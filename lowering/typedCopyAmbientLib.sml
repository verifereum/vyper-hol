(* Shared concrete witness construction.  Local theorem dependencies are
   parameters so this library can also be used by descendant frame theories. *)
structure typedCopyAmbientLib =
struct
open HolKernel boolLib bossLib
open venomExecSemanticsTheory emitHelperTheory contextTheory compileEnvTheory fragExecTheory venomStateTheory
     venomInstTheory ptrDisciplineTheory ptrSafeRunTheory bodyPtrDefsTheory
     finite_mapTheory

fun emit_binop (fragment, ghost_frame) =
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;right] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id opc [left;right] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id opc [left;right] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (irule fragment >> simp[mk_inst_def] >> qexists_tac `f` >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`, mk_inst_def]) >>
  `opc = ADD \/ opc = AND` by metis_tac[] >>
  `tnf.t_imm = tn.t_imm` by
    (gvs[Abbr `tnf`, step_taint_def, set_var_taint_def,
         adopt_reset_def, imm_taint_def, mk_inst_def]) >>
  simp[Abbr `tnf`, Abbr `Gf`, Abbr `t`, ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE];

fun emit_mload (fragment, ghost_clean) =
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (irule fragment >> simp[mk_inst_def] >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`, mk_inst_def]) >>
  `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule ghost_clean >>
     simp[eval_operand_def]) >>
  `tnf.t_imm = tn.t_imm` by
    simp[Abbr `tnf`, step_taint_def, set_var_taint_def, adopt_reset_def, imm_taint_def, mk_inst_def] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE];

fun copy_len (load, binop, extends_trans) =
  rpt strip_tac >>
  qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
  simp[contextTheory.compile_bytestring_copy_len_def, comp_bind_def] >>
  ntac 3 (pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def]) >>
  strip_tac >>
  `?v1. src_len = Var v1` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  `?v2. padded_len = Var v2` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  `?v3. rounded = Var v3` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  `?v4. count_op = Var v4` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def]) >>
  gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (Var v1,sc1)` >>
  rename1 `emit_op ADD [Var v1; Lit 31w] sc1 = (Var v2,sc2)` >>
  rename1 `emit_op AND [Var v2; Lit (i2w (-32))] sc2 = (Var v3,sc3)` >>
  drule_all load >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand (Var v1) s1 = SOME (mload (w2n a) s) /\
   eval_operand (Lit 31w) s1 = SOME 31w /\ op_taint tn1 (Lit 31w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.SPECL [`ADD`, `word_add`] binop)) >>
  disch_then (qspecl_then [`G1`, `cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `eval_operand (Var v2) s2 = SOME (mload (w2n a) s + 31w) /\
   eval_operand (Lit (i2w (-32))) s2 = SOME (i2w (-32)) /\
   op_taint tn2 (Lit (i2w (-32))) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.SPECL [`AND`, `word_and`] binop)) >>
  disch_then (qspecl_then [`G2`, `cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G3` (qx_choose_then `tn3` (qx_choose_then `s3` strip_assume_tac)))) >>
  `eval_operand (Var v3) s3 = SOME (mload (w2n a) s + 31w && i2w (-32)) /\
   eval_operand (Lit 32w) s3 = SOME 32w /\ op_taint tn3 (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.SPECL [`ADD`, `word_add`] binop)) >>
  disch_then (qspecl_then [`G3`, `cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G4` (qx_choose_then `tn4` (qx_choose_then `s4` strip_assume_tac)))) >>
  qexistsl_tac [`G4`, `tn4`, `s4`] >>
  `cs_extends sa sc1 /\ cs_extends sc1 sc2 /\
   cs_extends sc2 sc3 /\ cs_extends sc3 sb` by
    (imp_res_tac exprLoweringPropsTheory.emit_op_extends >>
     fs[cs_extends_def, exprLoweringPropsTheory.same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  conj_tac >-
    (irule fragExecPtrTheory.frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sa sc1 _ _ _` (irule_at Any) >>
     simp[] >> conj_tac >- metis_tac[extends_trans] >>
     irule fragExecPtrTheory.frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sc1 sc2 _ _ _` (irule_at Any) >>
     simp[] >> conj_tac >- metis_tac[extends_trans] >>
     irule fragExecPtrTheory.frag_exec_ptr_seq >>
     qpat_assum `frag_exec_ptr _ _ _ sc2 sc3 _ _ _` (irule_at Any) >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sc1 p /\
       not_fresh_at sc2 p /\ not_fresh_at sc3 p` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  simp[eval_operand_def] >> gen_tac >> strip_tac >>
  `not_fresh_at sc1 p /\ not_fresh_at sc2 p /\ not_fresh_at sc3 p` by metis_tac[] >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc1 p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc2 p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc3 p ==> _` (qspec_then `p` mp_tac) >>
  simp[];

val store_compose =
  `cs_extends sa sc /\ cs_extends sc sb` by
    (qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[contextTheory.compile_bytestring_copy_len_def, emit_op_def,
          emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, LET_THM,
          pairTheory.pair_case_def] >> rpt strip_tac >> gvs[] >>
     rewrite_tac[cs_extends_def] >> qexists_tac `[]` >> simp[] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qpat_assum `frag_exec_ptr _ _ _ sa sc _ _ _` (irule_at Any) >>
  simp[] >> first_assum ACCEPT_TAC;

fun store_bytestring_with_effects effects (length_fragment, copy_fragment, copy_ghost,
                      round_size, copy_exterior) =
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[contextTheory.compile_store_bytestring_def, comp_bind_def] >>
  pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def] >> strip_tac >>
  rename1 `compile_bytestring_copy_len (Var src) sa = (count_op,sc)` >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
                                  arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all length_fragment >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand count_op s1 = SOME (n2w n)` by
    (fs[] >> qspec_then `len` mp_tac round_size >>
     simp[vfmConstantsTheory.word_size_def]) >>
  `lookup_var src s1 = SOME a /\ lookup_var dst s1 = SOME b /\
   ptr_covers G1 tn1 src s1 n /\ ptr_covers G1 tn1 dst s1 n` by
    (qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` strip_assume_tac) >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `sb.cs_current_bb = sc.cs_current_bb /\
   sb.cs_current_insts = sc.cs_current_insts ++
      [mk_inst sc.cs_next_id MCOPY [Var dst; Var src; count_op] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
        emit_def, comp_return_def] >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) n s1` >>
  qabbrev_tac `Gf = step_prov PG G1
    (mk_inst sc.cs_next_id MCOPY [Var dst; Var src; count_op] []) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sc.cs_next_id MCOPY [Var dst; Var src; count_op] []) s1 t tn1` >>
  `frag_exec_ptr cx ctx PG sc sb
    (\g tt v. g = G1 /\ tt = tn1 /\ v = s1)
    (\g tt v. g = Gf /\ tt = tnf /\ v = t with vs_inst_idx := SUC s1.vs_inst_idx) R` by
    (irule (Q.SPECL [`cx`, `ctx`, `PG`, `sc`, `sb`, `sc.cs_next_id`,
                      `dst`, `src`, `count_op`] copy_fragment) >> simp[] >>
     qexistsl_tac [`count_op`, `dst`, `src`] >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`] >> gvs[]) >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s1.vs_inst_idx`] >>
  conj_tac >- store_compose >>
  `Gf = G1 /\ tnf.t_var = tn1.t_var /\
   tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
   tnf.t_mem = (tn1.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
              {w2n b + i | i < n /\ w2n a + i IN tn1.t_mem}` by
    (qspecl_then [`PG`, `G1`, `tn1`, `s1`, `sc.cs_next_id`,
                  `Var dst`, `Var src`, `count_op`, `a`, `b`, `n2w n`]
       mp_tac copy_ghost >>
     simp[eval_operand_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
     simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`] >> gvs[]) >>
  `tnf.t_imm = tn1.t_imm` by
    simp[Abbr `tnf`, step_taint_def, imm_taint_def, mk_inst_def] >>
  (if effects then
     (conj_tac >- simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def]) >>
     (conj_tac >- simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def])
   else all_tac) >>
  conj_tac >- simp[Abbr `t`, mcopy_def, read_memory_def,
                   write_memory_with_expansion_def, write_memory_def] >>
  conj_tac >-
    (simp[Abbr `t`] >> rpt strip_tac >>
     `mem_bytes_at i 1 (mcopy (w2n b) (w2n a) n s1).vs_memory =
      mem_bytes_at i 1 s1.vs_memory` by
       (irule copy_exterior >> decide_tac) >> gvs[]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
  conj_tac >- (rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >> decide_tac) >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  simp[lookup_var_def, mcopy_def, write_memory_with_expansion_def,
       write_memory_def, op_taint_def];
val store_bytestring = store_bytestring_with_effects false;
end
