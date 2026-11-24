(* Linked array target step, with both suffix routes discharged. *)
Theory bodyWriteArrayStageMods
Ancestors
  bodyWriteArrayBindMods bodyWriteSubscriptCutsMods bodyWriteSubscriptSourceMods
  bodyWriteArrayImmutableSuffixMods bodyWriteArrayOrdinarySuffixMods
  vyperInterpreter supportedExprs list

Theorem write_array_index_stage_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  alloc_limits_target cenv (SubscriptTarget bt e) /\
  (!i s. MEM i (target_indices (SubscriptTarget bt e)) /\
         expr_sim_inv_mods mods cenv cx env s ==>
         expr_body_pre_mods mods cenv cx env i s) /\
  body_base_target_full_ok_mods mods exps cx (SubscriptTarget bt e) /\
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> irule write_array_index_bind_mods >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all_then strip_assume_tac write_subscript_paired_cuts_mods >>
      qexistsl_tac [`rb`,`sm`,`ix`,`sn`,`shadow_sm`,`shadow_sn`] >> simp[]) >>
  simp[] >> qexistsl_tac [`exps`,`mods`,`src`,`tops`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> irule write_base_reached_source_mods >>
      qexistsl_tac [`bt`,`pv`,`st`] >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all_then strip_assume_tac write_index_read_source_mods >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `?owner id path. pv = PlaceR (ImmutablePlace owner id path)`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      irule write_array_immutable_suffix_mods >> simp[]) >>
  irule write_array_ordinary_suffix_mods >> gvs[]
QED
