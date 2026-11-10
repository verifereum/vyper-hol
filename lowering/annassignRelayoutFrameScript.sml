(* Install a reserved declaration after an arbitrary multi-block typed copy. *)
Theory annassignRelayoutFrame
Ancestors
  stmtSimDeclStore placeMemoryCopyEffect localPtrsProps loweringSlice
  exprLoweringProps venomState valueEncoding compileEnv loweringStateRelDefs

Theorem stmt_state_rel_declare_copy_effect:
  !func cenv cx es s t id p sz w inst v tyv sc rest a ctx sa sb.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
    typed_copy_effect ctx func sa sb s t (w2n w) sz /\
    (!q. q = p \/ ~not_local_ptr cenv es.scopes q ==> not_fresh_at sa q) /\
    type_memory_size tyv <= sz /\ val_wf tyv v /\
    val_in_memory tyv v (w2n w) t.vs_memory ==>
    stmt_state_rel ctx func cenv cx
      (es with scopes :=
        (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t
Proof
  rpt gen_tac >> strip_tac >>
  drule typed_copy_effect_record >>
  simp[venom_state_component_equality] >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[typed_copy_effect_length] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac
     >- fs[stmt_state_rel_def, state_rel_def] >>
     simp[] >> reverse conj_tac
     >- fs[stmt_state_rel_def, state_rel_def] >>
     fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
     rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at Any) >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. _` drule_all >>
     simp[regions_disjoint_def]) >>
  irule stmt_state_rel_declare_memory >>
  simp[] >> goal_assum (drule_at Any) >>
  qexistsl_tac [`inst`, `s`] >>
  simp[] >> reverse conj_tac
  >- metis_tac[typed_copy_effect_lookup] >>
  rpt strip_tac >>
  `regions_disjoint (w2n w) sz b sz'` by
    (irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at Any) >>
     fs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  sym_tac >> irule typed_copy_effect_bytes >>
  goal_assum (drule_at Any) >> fs[regions_disjoint_def]
QED
