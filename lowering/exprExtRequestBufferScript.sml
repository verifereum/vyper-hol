(* Request-buffer capacity and immutable separation boundary. *)
Theory exprExtRequestBuffer
Ancestors
  exprSimAlloc exprLoweringProps context compileEnv loweringStateRelDefs words

Theorem extrequest_alloc_capacity:
  !ctx func cenv cx es sa sb buf sz cap s.
    compile_alloc_buffer sz sa = (buf,sb) /\ fn_has_code sa sb func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\ cap <= sz ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      w2n w + cap < dimword (:256) /\
      (cenv.ce_is_ctor ==> !name tv v off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
          SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                   NONE => FEMPTY
                 | SOME imms => get_source_immutables cenv.ce_module imms)
          name = SOME (tv,v) ==>
        regions_disjoint (w2n w) cap off (type_memory_size tv))
Proof
  rpt strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  rpt strip_tac >>
  `immutable_alloca_sep func cenv cx es t` by
    gvs[stmt_state_rel_def] >>
  gvs[immutable_alloca_sep_def] >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  qpat_x_assum `!inst b sz. _` (qspec_then
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
  simp[venomInstTheory.mk_inst_def] >>
  simp[regions_disjoint_def] >> decide_tac
QED
