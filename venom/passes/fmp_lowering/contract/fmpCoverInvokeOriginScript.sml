Theory fmpCoverInvokeOrigin
Ancestors
  fmpStageRel fmpLowerInvokeProps fmpLowerDefs fmpLowerProps
  venomFnInstsProofs venomInst finite_map list rich_list
  fmpStepRestrictionClosure fmpStepPredicateTransport o1PassContract

Theorem fmp_cover_lower_inst_origin[local]:
  (!callee info args. fmp_resolve_invoke infos ctx i = SOME (callee,info,args)
     ==> ~info.fi_publishes_fmp) /\
  fmp_lower_inst infos ctx runner sp i = SOME (out,sp') /\
  MEM j out /\ j.inst_opcode = INVOKE ==>
  i.inst_opcode = INVOKE /\ j.inst_id = i.inst_id /\
  j.inst_outputs = i.inst_outputs
Proof
  simp[fmp_lower_inst_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[mk_inst_def, AllCaseEqs()] >>
  gvs[fmp_resolve_invoke_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_cover_indexed_origin[local]:
  (!i callee info args. MEM i insts /\
     fmp_resolve_invoke infos ctx i = SOME (callee,info,args)
     ==> ~info.fi_publishes_fmp) /\
  fmp_lower_indexed infos ctx runner label k sp restores insts =
    SOME (out,leftover,sp') /\ MEM j out /\ j.inst_opcode = INVOKE ==>
  ?i. MEM i insts /\ i.inst_opcode = INVOKE /\
      j.inst_id = i.inst_id /\ j.inst_outputs = i.inst_outputs
Proof
  map_every qid_spec_tac [`sp'`,`leftover`,`out`,`restores`,`sp`,`k`] >>
  Induct_on `insts`
  >- simp[fmp_lower_indexed_def] >>
  rpt gen_tac >>
  Cases_on `fmp_select_point_restores (label,k) restores` >>
  simp[fmp_lower_indexed_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[MEM_APPEND] >>
  imp_res_tac fmp_emit_restores_restrictions >>
  gvs[EVERY_MEM] >> metis_tac[fmp_cover_lower_inst_origin]
QED

Theorem fmp_cover_blocks_origin[local]:
  (!b i callee info args. MEM b bbs /\ MEM i b.bb_instructions /\
     fmp_resolve_invoke infos ctx i = SOME (callee,info,args)
     ==> ~info.fi_publishes_fmp) /\
  fmp_lower_blocks infos ctx runner sp restores bbs =
    SOME (FmpBlocksResult out leftover sp') /\
  MEM bb out /\ MEM j bb.bb_instructions /\ j.inst_opcode = INVOKE ==>
  ?b i. MEM b bbs /\ MEM i b.bb_instructions /\ i.inst_opcode = INVOKE /\
        j.inst_id = i.inst_id /\ j.inst_outputs = i.inst_outputs
Proof
  map_every qid_spec_tac [`sp'`,`leftover`,`out`,`restores`,`sp`] >>
  Induct_on `bbs` >> simp[fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_at (Pat `fmp_lower_indexed _ _ _ _ _ _ _ _ = _`)
        fmp_cover_indexed_origin >> disch_then (qspec_then `j` mp_tac) >> simp[] >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qexistsl [`h`,`i`] >> simp[]) >>
  qpat_x_assum `!sp restores out leftover sp'. _`
    (drule_at (Pat `fmp_lower_blocks _ _ _ _ _ _ = _`)) >>
  (impl_tac >- metis_tac[]) >> metis_tac[]
QED

(* Nonpublishing analysis leaves every call's output list unchanged.
   Identity is retained as well, so callers can identify its source occurrence. *)
Theorem fmp_cover_invoke_origin:
  fmp_stage_lowered infos ctx runner fn fn' /\
  (!i callee info args. MEM i (fn_insts fn) /\
     fmp_resolve_invoke infos ctx i = SOME (callee,info,args)
     ==> ~info.fi_publishes_fmp) /\
  MEM j (fn_insts fn') /\ j.inst_opcode = INVOKE ==>
  ?i. MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
      j.inst_id = i.inst_id /\ j.inst_outputs = i.inst_outputs
Proof
  Cases_on `fn.fn_fmp_signature`
  >- (simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def,
            AllCaseEqs()] >> rpt strip_tac >>
      gvs[fmp_checked_seal_def, fmp_seal_def, AllCaseEqs()]
      >- (qexists `j` >> gvs[fn_insts_def]) >>
      Cases_on `root_layout` >> gvs[] >>
  rename1 `fmp_make_root_layout _ _ _ _ _ = SOME (FmpRootLayout _ root pc _)` >>
  `!b i callee info args. MEM b fn.fn_blocks /\ MEM i b.bb_instructions /\
     fmp_resolve_invoke infos ctx i = SOME (callee,info,args) ==>
     ~info.fi_publishes_fmp` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i callee info args. _`
       (drule_at (Pat `fmp_resolve_invoke _ _ _ = _`)) >>
     simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `EVERY (\bb. EVERY (\j. j.inst_opcode = INVOKE ==>
     ?i. MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
         j.inst_id = i.inst_id /\ j.inst_outputs = i.inst_outputs)
     bb.bb_instructions) blocks` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all fmp_cover_blocks_origin >> strip_tac >>
     rename1 `MEM src b.bb_instructions` >>
     qexists `src` >> simp[] >>
     simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists `b` >> simp[]) >>
  drule fmp_make_root_layout_restrictions >> strip_tac >>
  drule fmp_install_root_every >>
  disch_then (drule_at (Pat `fmp_install_root _ _ _ _ = _`)) >>
  (impl_tac >- (gvs[EVERY_APPEND, EVERY_MEM] >> metis_tac[])) >>
  gvs[EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[]) >>
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >> rpt strip_tac >> qexists `j` >> gvs[]
QED
