(* The ordinary array suffix joins the memory and storage locations. *)
Theory bodyWriteArrayOrdinarySuffixMods
Ancestors
  bodyWriteArrayPacketMods bodyWriteArrayOperandsMods bodyWriteArrayMemoryMods bodyWriteArrayStorageMods
  bodyWriteArrayFinishMods bodyWriteArraySelectMods bodyFullTargetDefs bodyWriteTargetStageMods
  bodyFullPostsMods loweringPosts vyperInterpreter vyperState venomState
  vyperStorageFootprint

Theorem write_array_ordinary_suffix_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  (~?owner id path. pv = PlaceR (ImmutablePlace owner id path)) ==>
  write_array_suffix_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2))
Proof
  strip_tac >> Cases_on `pv`
  >- (qpat_x_assum `write_array_reached_mods _`
        (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
      qabbrev_tac `H0 = storage_trace_horizon mid2.storage_trace` >>
      `valid_horizon cx st0 H0 mid2.storage_trace` by
        simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >>
      drule write_target_post_view_mods >> strip_tac >>
      qhdtm_x_assum `write_target_location_mods`
        (strip_assume_tac o REWRITE_RULE [write_target_location_mods_def,
          place_readable_def, read_place_def, place_ptr_rel_def]) >>
      gvs[])
  >- (Cases_on `p`
      >- (rename1 `StoragePlace tr slot tv` >>
          qpat_assum `write_array_reached_mods _`
            (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
          qabbrev_tac `H0 = storage_trace_horizon mid2.storage_trace` >>
          `valid_horizon cx st0 H0 mid2.storage_trace` by
            simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> _`
            (drule_then strip_assume_tac) >>
          drule write_target_storage_view_mods >> strip_tac >>
          drule_all_then strip_assume_tac write_array_reached_operands_mods >>
          drule write_array_storage_length_mods >>
          strip_tac >>
          qpat_x_assum `!H. _ ==> _`
            (qspec_then `H0` assume_tac) >>
          gvs[] >>
          qabbrev_tac `nw = case bd of Fixed n => n2w n | Dynamic n =>
            lookup_storage b (get_storage cx mid2 tr)` >>
          `!n. bd = Fixed n ==> nw = n2w n` by
            (rpt strip_tac >> simp[Abbr `nw`]) >>
          `!cap len sl. bd = Dynamic cap /\
              compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (slot_loc tr)
                (FST rb) sn = (len,sl) ==> ?ul Gl tl.
                array_length_loader_ok cenv.ce_is_ctor cenv.ce_imm_alloca
                  (slot_loc tr) (FST rb) nw sn len sl lo ctx func PG t2 G2 tn2 ul Gl tl /\
                op_prov Gl len = NONE /\ op_taint tl len = {}` by
            (rpt strip_tac >>
             unabbrev_all_tac >>
             simp[] >>
             qpat_assum `!cap len sl. _ ==> _`
               (qspecl_then [`cap`,`len`,`sl`] (fn h => irule h)) >>
             simp[]) >>
          `?t3 G3 tn3. write_array_select_frame
            ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
             (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
             (st0,es,sa,s0,G0,tn0),
             (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
             (base_gas,mid1,PlaceR (StoragePlace tr b tv),t1,G1,tn1),
             (index_gas,mid2,IntV (if is_signed_type (expr_type e) then
                 w2i iw else (&w2n iw)),t2,G2,tn2))
            (slot_loc tr,b,iw,nw) (t3,G3,tn3)` by
            (irule write_array_select_run_mods >> simp[]) >>
          rename1 `write_array_select_frame _ _ (t3,G3,tn3)` >>
          drule write_array_storage_extend_mods >>
          disch_then (drule_at Any) >>
          disch_then (qspecl_then [`if is_signed_type (expr_type e) then
             w2i iw else (&w2n iw)`,`H0`] mp_tac) >>
          simp[Abbr `nw`] >> strip_tac >>
          `mid2 with gas_obs := mid2.gas_obs = mid2` by
            simp[evaluation_state_component_equality] >>
          qpat_x_assum `!gs. extend_place _ _ _ _ = _`
            (qspec_then `mid2.gas_obs` mp_tac) >>
          simp[] >> strip_tac >>
          irule write_array_finish_mods >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl [`G3`,`b`,`iw`,`slot_loc tr`,
                    `case bd of Fixed n => n2w n | Dynamic _ =>
                       lookup_storage b (get_storage cx mid2 tr)`,
                    `if idx_in_range (is_signed_type (expr_type e)) iw
                         (case bd of Fixed n => n2w n | Dynamic _ =>
                            lookup_storage b (get_storage cx mid2 tr))
                     then INL child else INR (Error (RuntimeError msg))`,
                    `t3`,`tn3`] >>
          Cases_on `idx_in_range (is_signed_type (expr_type e)) iw
                       (case bd of Fixed n => n2w n | Dynamic _ =>
                          lookup_storage b (get_storage cx mid2 tr))` >> gvs[])
      >- (rename1 `MemoryPlace id path` >>
          qpat_assum `write_array_reached_mods _`
            (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
          qabbrev_tac `H0 = storage_trace_horizon mid2.storage_trace` >>
          `valid_horizon cx st0 H0 mid2.storage_trace` by
            simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> _`
            (drule_then strip_assume_tac) >>
          drule_all_then strip_assume_tac write_array_reached_operands_mods >>
          drule_all_then strip_assume_tac write_array_memory_length_mods >>
          qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
          rename1 `eval_operand (FST rb) t1 = SOME b` >>
          rename1 `eval_operand iop t2 = SOME iw` >>
          rename1 `!n. bd = Fixed n ==> nw = n2w n` >>
          `?t3 G3 tn3. write_array_select_frame
            ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
             (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
             (st0,es,sa,s0,G0,tn0),
             (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
             (base_gas,mid1,PlaceR (MemoryPlace id path),t1,G1,tn1),
             (index_gas,mid2,IntV i,t2,G2,tn2))
            (LocMemory,b,iw,nw) (t3,G3,tn3)` by
            (irule write_array_select_run_mods >> simp[]) >>
          rename1 `write_array_select_frame _ _ (t3,G3,tn3)` >>
          drule_all write_array_memory_extend_mods >> simp[LET_THM] >> strip_tac >>
          qpat_x_assum `i = if _ then _ else _` SUBST_ALL_TAC >>
          irule write_array_finish_mods >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexistsl [`G3`,`b`,`iw`,`LocMemory`,`nw`,
                    `if idx_in_range (is_signed_type (expr_type e)) iw nw then
                       INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript
                         (IntV (if is_signed_type (expr_type e) then w2i iw else (&w2n iw)))])))
                     else INR (Error (RuntimeError "evaluate_subscripts array_index"))`,
                    `t3`,`tn3`] >>
          Cases_on `idx_in_range (is_signed_type (expr_type e)) iw nw` >> gvs[])
      >- gvs[])
  >- (qpat_x_assum `write_array_reached_mods _`
        (strip_assume_tac o REWRITE_RULE [write_array_reached_mods_def]) >>
      qabbrev_tac `H0 = storage_trace_horizon mid2.storage_trace` >>
      `valid_horizon cx st0 H0 mid2.storage_trace` by
        simp[Abbr `H0`, GSYM storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >>
      drule write_target_mapping_view_mods >> simp[])
QED
