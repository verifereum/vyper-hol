(* Recover a compiled immutable location from linked state ownership. *)
Theory linkedOwnedImmutableLocation
Ancestors
  bodyInvSplit compileEnv compileUnit vyperTypeContract vyperSubscriptOverlap
  vyperAST finite_map alist list pair

Theorem linked_owned_immutable_location:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME tops /\
  MEM (VariableDecl vis Immutable id ty slot) tops /\
  (mods = [(NONE,tops)] \/ linked_state_ref_allocated layouts addr mods (src,id)) /\
  immutable_section_layout_mods mods ce ==>
  ?off. FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
  `ALL_DISTINCT (FLAT (MAP (self_member_keys_toplevel src) tops))` by
    (irule contract_keys_module_distinct >>
     qexists_tac `mods` >> fs[contract_namespaces_ok_def]) >>
  qpat_assum `MEM (VariableDecl vis Immutable id ty slot) tops`
    (qx_choosel_then [`pre`,`post`] assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  `!tl. MEM tl tops /\ MEM (src,id) (self_member_keys_toplevel src tl) ==>
        tl = VariableDecl vis Immutable id ty slot` by
    (qpat_assum `tops = _ ++ _ :: _` (fn split =>
       qpat_assum `ALL_DISTINCT (FLAT (MAP (self_member_keys_toplevel src) tops))`
         (mp_tac o PURE_REWRITE_RULE [split]) >>
       PURE_REWRITE_TAC [split]) >>
     simp[ALL_DISTINCT_APPEND, self_member_keys_toplevel_def] >>
     simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `!ts name. constant_decl name ts ==>
      ?vis init ty slot. MEM (VariableDecl vis (Constant init) name ty slot) ts` by
    (Induct >> simp[constant_decl_def] >>
     Cases_on `h` >> simp[constant_decl_def] >>
     Cases_on `v0` >> simp[constant_decl_def] >> metis_tac[]) >>
  `~constant_decl id tops` by
    (strip_tac >>
     qpat_assum `!ts name. constant_decl name ts ==> _`
       (drule_then (qx_choosel_then [`const_vis`,`init`,`const_ty`,`const_slot`] assume_tac)) >>
     qpat_assum `!tl. MEM tl tops /\ _ ==> _`
       (qspec_then `VariableDecl const_vis (Constant init) id const_ty const_slot` mp_tac) >>
     simp[self_member_keys_toplevel_def]) >>
  `?off size. immutable_region_mods mods src id off size` by
    (Cases_on `mods = [(NONE,tops)]`
     >- (qexistsl_tac [
           `compute_immutables_len (get_struct_fields (make_struct_fields_map_mods mods)) pre`,
           `type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods)) ty`] >>
         PURE_REWRITE_TAC [immutable_region_mods_def] >>
         qexistsl_tac [`tops`,`pre`,`post`,`vis`,`ty`,`slot`] >> simp[]) >>
     `IS_SOME slot` by
       (`linked_state_ref_allocated layouts addr mods (src,id)` by
          (qpat_x_assum `mods = [(NONE,tops)] \/ _` mp_tac >> asm_rewrite_tac[]) >>
        qpat_assum `ALOOKUP mods src = SOME tops` (fn lookup =>
          qpat_assum `~constant_decl id tops` (fn not_const =>
            qpat_x_assum `linked_state_ref_allocated layouts addr mods (src,id)`
              (mp_tac o SIMP_RULE (srw_ss())
                [linked_state_ref_allocated_def, lookup, not_const, EXISTS_MEM]))) >>
        disch_then (CONJUNCTS_THEN2
          (qx_choose_then `tl` (map_every assume_tac o CONJUNCTS)) (K ALL_TAC)) >>
        qpat_assum `!decl. MEM decl tops /\ _ ==> _`
          (qspec_then `tl` (fn unique =>
             qpat_assum `MEM tl tops` (fn member =>
               qpat_assum `MEM (src,id) (self_member_keys_toplevel src tl)`
                 (assume_tac o MATCH_MP unique o CONJ member)))) >>
        fs[linked_toplevel_allocated_def]) >>
     Cases_on `slot` >> fs[] >>
     qexistsl_tac [`x`,
         `type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods)) ty`] >>
     PURE_REWRITE_TAC [immutable_region_mods_def] >>
     qexistsl_tac [`tops`,`pre`,`post`,`vis`,`ty`,`SOME x`] >> simp[]) >>
  qexists_tac `off` >>
  qpat_assum `immutable_section_layout_mods mods ce`
    (mp_tac o REWRITE_RULE [immutable_section_layout_mods_def]) >>
  simp[] >> strip_tac >>
  qpat_assum `immutable_region_mods mods src id off _` (irule_at Any)
QED
