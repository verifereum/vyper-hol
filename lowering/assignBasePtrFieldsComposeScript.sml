(* List composition with child correctness left as an explicit contract. *)
Theory assignBasePtrFieldsCompose
Ancestors context compileEnv emitHelper contextCodegenRelProps
  fragExec fragGasPathPtr list arithmetic venomState

Theorem assign_base_typed_copy_fields_counted:
  !cenv dst src D ctx PG I.
    (!dt ds st ss doff soff a b c d dp sp.
       compile_with_byte_offset dst doff a = (dp,b) /\
       compile_with_byte_offset src soff b = (sp,c) /\
       compile_store_memory_typed cenv dp dt sp st c = ((),d) ==>
       cs_extends a d /\
       (!fn G tn s.
         fn_has_code a d fn /\ s.vs_current_bb = a.cs_current_bb /\
         s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
         I (dt::ds) (st::ss) doff soff a G tn s ==>
         ?G' tn' u.
           gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u) /\
           u.vs_current_bb = d.cs_current_bb /\
           u.vs_inst_idx = LENGTH d.cs_current_insts /\ ~u.vs_halted /\
           I ds ss (doff+type_memory_bytes cenv dt)
             (soff+type_memory_bytes cenv st) d G' tn' u)) ==>
    !dts sts doff soff a z.
      LENGTH dts = LENGTH sts /\
      compile_typed_copy_fields cenv dst src dts sts doff soff a = ((),z) ==>
      cs_extends a z /\
      (!fn G tn s.
        fn_has_code a z fn /\ s.vs_current_bb = a.cs_current_bb /\
        s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
        I dts sts doff soff a G tn s ==>
        ?G' tn' u.
          gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK u) /\
          u.vs_current_bb = z.cs_current_bb /\
          u.vs_inst_idx = LENGTH z.cs_current_insts /\ ~u.vs_halted /\
          I [] [] (doff+SUM (MAP (type_memory_bytes cenv) dts))
            (soff+SUM (MAP (type_memory_bytes cenv) sts)) z G' tn' u)
Proof
  rpt gen_tac >> disch_tac >> Induct_on `dts`
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `sts` >> gvs[] >>
      qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def, comp_return_def] >>
      strip_tac >> gvs[] >>
      simp[cs_extends_refl] >> rpt strip_tac >>
      qexistsl_tac [`G`, `tn`, `s`] >> simp[cj 1 gas_path_ptr_rules]) >>
  rpt gen_tac >> Cases_on `sts` >> simp[] >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory_typed cenv dp h sp h' sc = (u,sd)` >>
  Cases_on `u` >>
  qpat_x_assum `!sts doff soff a z. _` drule_all >> strip_tac >>
  qpat_x_assum `!dt ds st ss doff soff a b c d dp sp. _` drule_all >>
  disch_then (qspecl_then [`dts`, `t`] strip_assume_tac) >>
  conj_tac >- metis_tac[cs_extends_trans] >>
  suspend "cons"
QED

Resume assign_base_typed_copy_fields_counted[cons]:
  rpt gen_tac >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `!fn G tn s. fn_has_code a sd fn /\ _ ==> _` drule_all >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK q)` >>
  qpat_x_assum `!fn G tn s. fn_has_code sd z fn /\ _ ==> _` drule_all >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gm tm q 0 Gf tf (OK u)` >>
  qexistsl_tac [`Gf`, `tf`, `u`] >>
  conj_tac
  >- (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >>
      disch_then drule >> simp[]) >>
  simp[] >> qpat_x_assum `_ [] [] _ _ z Gf tf u` mp_tac >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Finalise assign_base_typed_copy_fields_counted
