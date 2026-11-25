(* Shared preparation of the selected Range cons round, independent of
   which simulation (full outcome or request prefix) consumes the body. *)
structure rangeRoundEntryLib =
struct
open HolKernel boolLib bossLib
open arithmeticTheory integerTheory wordsTheory listTheory finite_mapTheory
     compileEnvTheory loweringStateRelDefsTheory loweringPostsTheory
     vyperASTTheory vyperStateTheory vyperTypeSystemTheory exprSimHypsDefsTheory
     vyperStorageFootprintTheory exprLoweringPropsTheory
     venomInstTheory venomStateTheory venomExecSemanticsTheory ptrDisciplineTheory
     bodyPtrDefsTheory bodySimTheory bodySimFullTheory bodyFullPredsTheory
     fragGasOriginPtrTheory

val layout_names =
  [`st`, `bc`, `body_cenv`, `body_env'`, `sb0`, `sb1`, `shadow_sb0`, `shadow_sb1`,
   `p`, `sz`, `ainst`, `cv`, `ev`, `dv`, `nv`, `entry_lbl`, `cond_lbl`, `exit_lbl`,
   `body_lbl`, `incr_lbl`, `j1`, `j2`, `j3`, `bbb`, `i1`, `i2`, `i3`, `sj`,
   `op1`, `s1`, `op2`, `rv`, `g1`, `z1`, `g2`, `z2`]

(* The layout package ends with its cons-entry implication. This selector
   works both for a chosen existential package and an assumed package on
   already fixed layout witnesses. Keep those witnesses named as above. *)
fun assume_layout pkg =
  let val clauses = CONJUNCTS pkg in
    EVERY (map assume_tac (Lib.butlast clauses)) >>
    mk_asm "enter_cons" (List.last clauses)
  end

val choose_layout = qx_choosel_then layout_names assume_layout

  val enter_round =
    asm_x "enter_cons" (drule_all_then
      (strip_assume_tac o CONV_RULE (TOP_DEPTH_CONV BETA_CONV) o
       PURE_REWRITE_RULE [LET_THM]));

  val name_frame =
    qmatch_asmsub_abbrev_tac `expr_sim_inv bc cx (extend_local env id typ F) ep` >>
    qmatch_asmsub_abbrev_tac `ret_pc_ok bc sb0 t` >>
    qabbrev_tac `s_eq = update_var dv (bool_to_word F) s` >>
    qabbrev_tac `s_jnz = jump_to body_lbl (s_eq with vs_inst_idx := 1)` >>
    qabbrev_tac `s_store = mstore (w2n w) (i2w (n1 + &k)) s_jnz` >>
    qabbrev_tac `Gentry = step_prov PG
      (step_prov PG (step_prov PG G (mk_inst j1 EQ [Var cv;Var ev] [dv]) s_eq)
         (mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] []) s_jnz)
      (mk_inst j3 MSTORE [Var p;Var cv] []) s_store` >>
    qabbrev_tac `tt = step_taint (mk_inst j3 MSTORE [Var p;Var cv] []) s_jnz s_store
      (step_taint (mk_inst j2 JNZ [Var dv;Label exit_lbl;Label body_lbl] [])
         (s_eq with vs_inst_idx := 1) s_jnz
         (step_taint (mk_inst j1 EQ [Var cv;Var ev] [dv]) s s_eq tn))` >>
    `ep.storage_trace = es.storage_trace /\ ep.scopes <> [] /\ ep.gas_obs = []` by
      simp[Abbr `ep`];

  val frame_at_horizons =
    `!H. valid_horizon cx st0 H ep.storage_trace ==>
       stmt_state_rel H ctx func bc cx ep t /\ storage_well_formed_on cx ep (FST H) /\
       ghost_inv_at (DF H) lo d bc cx ep Gentry tt t` by
      (qx_gen_tac `H` >> strip_tac >>
       qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
         gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt) /\ _`
         (qspec_then `H` mp_tac) >>
       impl_tac >- (qpat_assum `ep.storage_trace = es.storage_trace`
                      (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
       strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC);

  fun prepare_locals separation_path allocated_local =
    `return_buf_sep d bc ep t` by
      (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
         gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt) /\ _`
         (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
       (impl_tac >- simp[GSYM storage_trace_domain_def]) >> strip_tac >>
       `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
         (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gentry,tt)`
            (mp_then (Pos hd) mp_tac separation_path) >>
          disch_then (qspecl_then [`sb0`,`es`,`d`,`cenv`] mp_tac) >>
          qpat_assum `return_buf_frame d cenv sb0 s` (fn frame =>
            qpat_assum `return_buf_sep d cenv es s` (fn sep => rewrite_tac [frame,sep]))) >>
       `cenv.ce_alloca_locals` by
         (qpat_assum `body_inv tops ctx cenv cx`
            (ACCEPT_TAC o MATCH_MP bodyInvExecutionPropsTheory.contract_inv_alloca_locals o
             MATCH_MP body_inv_contract)) >>
       drule_all_then strip_assume_tac stmtSimPropsTheory.declare_local_ptr >>
       `p <> dv` by
         (Cases_on `?a1 m1 a2 m2. e1 = Literal a1 (IntL m1) /\ e2 = Literal a2 (IntL m2)`
          >- (qpat_x_assum `?a1 m1 a2 m2. _` strip_assume_tac >>
              qpat_assum `!a1 m1 a2 m2. _ ==> st = sa /\ _`
                (drule_all_then strip_assume_tac) >>
              qpat_assum `dv = _` (fn dv_eq => qpat_assum `p = _` (fn p_eq =>
                qpat_assum `st = sa` (fn st_eq =>
                  simp[NoAsms, dv_eq, p_eq, st_eq, ASCIInumbersTheory.toString_inj])))) >>
          qpat_assum `~(?a1 m1 a2 m2. _) ==> _` (drule_then strip_assume_tac) >>
          qpat_assum `dv = _` (fn dv_eq => qpat_assum `p = _` (fn p_eq =>
            simp[NoAsms, dv_eq, p_eq, ASCIInumbersTheory.toString_inj]))) >>
       `!x. x <> dv ==> lookup_var x t = lookup_var x s` by
         simp[NoAsms, Abbr `t`, Abbr `s_store`, Abbr `s_jnz`, Abbr `s_eq`,
              lookup_var_def, update_var_def, jump_to_def, mstore_def, FLOOKUP_UPDATE] >>
       `t.vs_allocas = s.vs_allocas` by
         simp[NoAsms, Abbr `t`, Abbr `s_store`, Abbr `s_jnz`, Abbr `s_eq`,
              update_var_def, jump_to_def, mstore_def] >>
       irule (INST_TYPE [alpha |-> ``:256``] allocated_local) >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `t.vs_allocas = s.vs_allocas` (fn maps =>
         qpat_assum `FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n w,sz)`
           (irule_at Any o PURE_REWRITE_RULE [GSYM maps])) >>
       qpat_assum `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s`
         (irule_at Any) >>
       qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
       `FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz)` by
         (qpat_assum `p = _` SUBST1_TAC >> qpat_assum `sz = _` SUBST1_TAC >>
          first_assum ACCEPT_TAC) >>
       pop_assum (irule_at Any) >>
       `lookup_var p t = SOME w` by
         (qpat_assum `!x. x <> dv ==> lookup_var x t = _` (drule_then SUBST1_TAC) >>
          first_assum ACCEPT_TAC) >>
       pop_assum (irule_at Any) >>
       conj_tac
       >- (qx_gen_tac `x'` >> qx_gen_tac `v'` >> strip_tac >>
           `x' <> dv` by
             (disch_then (fn eq =>
                qpat_assum `not_fresh_at sa x'` (assume_tac o REWRITE_RULE [eq])) >>
              qpat_assum `~not_fresh_at sa dv` (fn th => first_assum (CONTR_TAC o MATCH_MP th))) >>
           qpat_assum `!x. x <> dv ==> lookup_var x t = _` (drule_then SUBST1_TAC) >>
           first_assum ACCEPT_TAC) >>
       conj_tac
       >- (qx_gen_tac `nm` >> gen_tac >>
           simp[NoAsms, Abbr `ep`, lookup_scopes_def, FLOOKUP_UPDATE, EQ_SYM_EQ,
                SF CONJ_ss] >> strip_tac >>
           qpat_assum `SOME _ = lookup_scopes nm es.scopes` (SUBST1_TAC o SYM) >> simp[]) >>
       rpt conj_tac >> first_assum ACCEPT_TAC) >>
    `body_const_cells_agree [(NONE,tops)] cx env ep` by
      (irule (iffLR body_const_cells_agree_immutables) >>
       qexists_tac `es` >> simp[Abbr `ep`]);
  (* In addition to the selected layout and static facts, the caller has
     the counter/list invariant Inv on (a::rs,es,G,tn,s), its equality to
     the full Range invariant, and the trace domain for es. The continuation
     sees the actual scoped body start ep,t,Gentry,tt, the empty-marks path
     under valid horizons, and the accompanying source and fragment facts. *)
  val establish_invariant =
    qabbrev_tac `k = N - LENGTH (a::rs)` >>
    `!j. j + LENGTH (a::rs) = N ==> j = k` by
      (simp[Abbr `k`] >> decide_tac) >>
    qpat_assum `Inv = _` (fn inv_def =>
      qpat_x_assum `!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es G tn s`
        (mk_asm "inv_cons" o BETA_RULE o PURE_REWRITE_RULE [inv_def])) >>
    asm "inv_cons" (qspec_then `storage_trace_horizon es.storage_trace`
      (drule_then (qx_choose_then `j` strip_assume_tac) o
        PURE_ONCE_REWRITE_RULE [GSYM storage_trace_domain_def])) >>
    `j = k` by
      (qpat_assum `!j. j + LENGTH (a::rs) = N ==> j = k` irule >>
       first_assum ACCEPT_TAC) >> pop_assum SUBST_ALL_TAC >>
    `!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es s /\
         storage_well_formed_on cx es (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx es G tn s` by
      (qx_gen_tac `H` >> strip_tac >>
       asm "inv_cons" (qspec_then `H` (drule_then strip_assume_tac)) >>
       rpt conj_tac >> first_assum ACCEPT_TAC);

  fun from_invariant separation_path allocated_local continuation =
    establish_invariant >> enter_round >> name_frame >> frame_at_horizons >>
    prepare_locals separation_path allocated_local >> continuation
end
