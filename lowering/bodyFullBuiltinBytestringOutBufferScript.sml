(* The slice buffer and its data pointer share one execution and ghost state. *)
Theory bodyFullBuiltinBytestringOutBuffer
Ancestors
  bodyFullBuiltinBytestringBuffer bodyFullAllocaFresh bodyFullUnwrapRun
  bodyPtrBytestringBuiltinsBuffer fragGasOriginPtr exprLoweringProps
  emitHelper emitHelperProps fragExec freshWrites bodyPtrDefs ptrDiscipline venomState venomInst
  venomExecSemantics context compileEnv loweringStateRelDefs allocaHistory finite_map words list

Theorem bytestring_out_buffer_full_run:
  compile_slice_out_buf n sa = ((root,data),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ 32 <= n /\ n < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r p w t G' tn'.
    root = Var r /\ data = Var p /\
    not_fresh_at sb r /\ not_fresh_at sb p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,G',tn')) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
          stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    lookup_var r t = SOME w /\ lookup_var p t = SOME (w+32w) /\
    ptr_covers G' tn' r t n /\ ptr_covers G' tn' p t (n-32) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= t.vs_alloca_next /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
             FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sa.cs_next_id /\
                 FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
                  regions_disjoint (w2n w) n b len) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!i. i IN tn'.t_mem <=>
         i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < w2n w + n)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule compile_slice_out_buf_compiler_parts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  (fn (asl,w) =>
    let
      fun horizon tm = is_forall tm andalso
        fst (dest_var (fst (dest_forall tm))) = "H'"
      val provider = alloc_buffer_origin_ptr_path
      val post = fst (dest_forall (find_term horizon (concl provider)))
      val target = fst (dest_forall (find_term horizon w))
      val formal = first (fn v => fst (dest_var v) = "H") (free_vars (concl provider))
    in
      qpat_assum `stmt_state_rel H ctx func cenv cx es s` (fn hyp =>
        let
          val actual = hd (snd (strip_comb (concl hyp)))
          val tys = match_type (type_of (pairSyntax.mk_pair (formal,post)))
            (type_of (pairSyntax.mk_pair (actual,target)))
        in mp_tac (Q.INST [`sb` |-> `sm`]
          (INST [inst tys formal |-> actual] (INST_TYPE tys provider))) end) (asl,w)
    end) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `q` (qx_choose_then `w`
    (qx_choose_then `u` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac))))) >>
  `q = r` by gvs[] >> qpat_x_assum `q = r` SUBST_ALL_TAC >>
  `~u.vs_halted` by
    (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s`
       (mp_tac o Q.AP_TERM `\st. st.vs_halted`) >> simp[]) >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  mp_tac (bytestring_data_offset_full_run |> Q.INST
    [`sa` |-> `sm`, `root` |-> `r`, `data` |-> `p`,
     `s` |-> `u`, `b` |-> `w`, `N` |-> `n`,
     `G` |-> `G1`, `tn` |-> `tn1`]) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `t` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sb.cs_next_var` by
    (conj_tac
     >- (qspecl_then [`n`,`sa`] mp_tac
           exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >>
         simp[ci_mono_def]) >>
     drule emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sm x ==> x <> p` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def, not_fresh_at_def] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes p` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  (fn (asl,w) =>
    let
      val horizon = find_term (fn tm => is_forall tm andalso
        fst (dest_var (fst (dest_forall tm))) = "H'") w
      val endpoint = last (snd (strip_comb (snd (dest_imp
        (snd (dest_forall horizon))))))
    in qpat_assum `t = _` (fn th =>
      sg [ANTIQUOTE (subst [endpoint |-> lhs (concl th)] horizon)]) (asl,w) end)
  >-
    (rpt strip_tac >>
     qpat_assum `t = _` SUBST1_TAC >> simp[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_update_var >> simp[] >>
     (fn (asl,w) =>
       qpat_assum `!h. _ ==> stmt_state_rel _ _ _ _ _ _ _`
         (match_mp_tac o ISPEC (hd (snd (strip_comb w)))) (asl,w)) >>
     simp[]) >>
  `alloca_history func t` by
    (drule emitted_insts_emit_op >> strip_tac >>
     fs[] >>
     qspecl_then [`sm`,`sb`,`func`,
       `[mk_inst sm.cs_next_id ADD [Var r;Lit 32w] [p]]`]
       mp_tac fn_has_code_same_block >> simp[] >> strip_tac >>
     `get_instruction bb u.vs_inst_idx =
        SOME (mk_inst sm.cs_next_id ADD [Var r;Lit 32w] [p])` by
       (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     `alloca_history func (u with vs_inst_idx := SUC u.vs_inst_idx)` by
       (irule history_nonalloca_advance >> simp[] >>
        qexists_tac `mk_inst sm.cs_next_id ADD [Var r;Lit 32w] [p]` >>
        simp[mk_inst_def]) >>
     irule alloca_history_frame >>
     qexists_tac `u with vs_inst_idx := SUC u.vs_inst_idx` >>
     qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def]) >>
  `t with <| vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
              vs_alloca_next := s.vs_alloca_next;
              vs_inst_idx := s.vs_inst_idx |> = s` by
    (qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def] >>
     qpat_assum `u with <| vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _ |> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK t,G2,tn2)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[]) >>
  qexistsl_tac [`r`,`p`,`w`,`t`,`G2`,`tn2`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac
  >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[])
  >- (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >>
      rpt strip_tac >> gvs[not_fresh_at_def])
  >- (qpat_assum `t = _` SUBST1_TAC >> simp[allocas_from_def, update_var_def] >>
      qpat_assum `allocas_from lo u`
        (ACCEPT_TAC o REWRITE_RULE[allocas_from_def]))
  >- (qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def])
  >- (qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def])
  >- (qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def])
  >- (qpat_assum `t = _` SUBST1_TAC >> simp[update_var_def])
  >- (rpt strip_tac >>
      qpat_assum `!aid b len. _ /\ _ ==> regions_disjoint _ _ _ _`
        (qspecl_then [`aid`,`b`,`len`] match_mp_tac) >> simp[])
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ u _ _ _ ==> _` irule >>
      fs[local_region_def, lookup_var_def, not_local_ptr_def, update_var_def] >>
       rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local) len)` >>
       `local <> p` by
         (qpat_assum `!name entry sz. _ ==> FLOOKUP _ _ <> _` mp_tac >>
          qpat_assum `lookup_scopes name es.scopes = SOME entry` mp_tac >>
          qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var local) len)` mp_tac >>
          rpt (pop_assum kall_tac) >> metis_tac[]) >>
       qexistsl_tac [`name`,`entry`,`local`] >> fs[FLOOKUP_UPDATE]) >>
  rpt strip_tac >> metis_tac[]
QED
