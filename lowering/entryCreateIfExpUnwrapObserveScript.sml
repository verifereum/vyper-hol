(* Observe the owned unwrap at the endpoint chosen by the scoped producer.
   The guard tests are local to this unwrap interval in the installed function. *)
Theory entryCreateIfExpUnwrapObserve
Ancestors
  bodyFullIfExpObserve bodyFullUnwrap entryStageUnwrapScoped
  entryCreateFocusSpec entryCreateCompletedCut abiEncoderProps venomExecSemantics

Theorem ifexp_owned_unwrap_observation:
  (!a b. guard a b ==>
     (!bb. lookup_block b.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
     (!bb i. lookup_block b.cs_current_bb func.fn_blocks = SOME bb /\
             get_instruction bb (LENGTH b.cs_current_insts) = SOME i ==>
             i.inst_id NOTIN frag_ids a b)) /\
  (!a b s z.
     (guard a b ==> create_operand_at a s /\
        create_operand_full_scope a b explicit ctx func s [] (OK z)) ==>
     obs ctx func a b s z) ==>
  ifexp_observed_unwrap T obs DF lo explicit ctx func PG d cenv cx
Proof
  strip_tac >> pure_rewrite_tac [ifexp_observed_unwrap_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `guard sb sc`
  >- (qpat_assum `!a b. guard a b ==> _` (drule_then strip_assume_tac) >>
      mp_tac stage_unwrap_origin_ptr_scoped >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`]
        (map_every assume_tac o CONJUNCTS)) >>
      qexistsl [`v`,`z`,`G'`,`tn'`] >> conj_tac
      >- (first_x_assum irule >>
          fs[create_operand_at_def,create_operand_full_scope_def]) >>
      pure_rewrite_tac [IMP_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac unwrap_value_origin_ptr >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`v`,`z`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`v`,`z`,`G'`,`tn'`] >> conj_tac
  >- (first_x_assum irule >> simp[]) >>
  pure_rewrite_tac [IMP_CLAUSES] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
