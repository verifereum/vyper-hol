(* The raw-jump boundary used when specializing the selected IfExp arm. *)
Theory bodyFullIfExpReach
Ancestors
  fragGasOriginPtr fragGasPathPtr contextRawReachable contextCodegenRel venomExecProofs
  venomExecSemantics venomInst venomState fragExec
  ctorDeployMemoryRunMemEntryFirstEmission compilerFirstEmission
  exprLoweringProps exprLowering compileEnv
  fragGasPath gasOutcomeFull bodySim bodyInvSplit compileUnit vyperCompiler list
  contractInvContextProps
Libs
  monadsyntax

Theorem ifexp_enter_non_phi[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  s.vs_inst_idx = 0 /\ inst.inst_opcode <> PHI ==>
  enters_block fn s s
Proof
  rw[active_inst_def, enters_block_def] >>
  Cases_on `bb.bb_instructions` >> gvs[get_instruction_def] >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem ifexp_ptr_edge_first[local]:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' r ==>
  ?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI
Proof
  rw[gas_path_ptr_edge_def] >>
  qexistsl [`bb`,`inst`] >> simp[] >>
  strip_tac >> gvs[step_inst_phi_error, exit_result_def]
QED

Theorem ifexp_ptr_path_first[local]:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !t. r = OK t /\ (?bb inst. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI) ==>
      ?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[ifexp_ptr_edge_first, exit_result_def]
QED

Theorem ifexp_ptr_edge_reachable[local]:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  (?bb inst. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI) ==>
  !i. active_inst fn i t ==> frag_reachable ctx fn s fn i t
Proof
  rw[gas_path_ptr_edge_def] >>
  `active_inst fn inst s` by metis_tac[contextCodegenRelPropsTheory.lookup_instruction_active] >>
  `frag_reachable ctx fn s fn inst s` by metis_tac[frag_reachable_rules]
  >- metis_tac[frag_reachable_next]
  >- metis_tac[frag_reachable_block, enters_block_def]
  >- (gvs[] >>
      `enters_block fn (jump_to lbl s) (jump_to lbl s)` by
        (irule ifexp_enter_non_phi >> simp[jump_to_def] >>
         gvs[jump_to_def] >> metis_tac[]) >>
      `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
      irule frag_reachable_block >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `OK t = _` (fn th => fs[GSYM th, exit_result_def])
QED

Theorem ifexp_ptr_path_reachable:
  !D lo ctx fn PG G tn s n G' tn' r.
    gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
    !t. r = OK t /\ (?bb inst.
      lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst /\ inst.inst_opcode <> PHI) ==>
    !i. active_inst fn i t ==> frag_reachable ctx fn s fn i t
Proof
  ho_match_mp_tac gas_path_ptr_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- metis_tac[frag_reachable_rules]
  >- (drule ifexp_ptr_path_first >>
      disch_then (qspec_then `t` mp_tac) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      metis_tac[ifexp_ptr_edge_reachable, frag_reachable_trans]) >>
  gvs[exit_result_def]
QED

Theorem ifexp_arm_first_emission[local]:
  !ce rt ty vv a x b. compile_ifexp_arm ce rt ty vv a = (x,b) ==>
    cs_extends a b /\
    ((a.cs_blocks = b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb /\
      a.cs_current_insts = b.cs_current_insts) \/
     (!fn. fn_has_code a b fn ==> ?bb i.
       lookup_block a.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (a.cs_current_insts ++ [i]) bb.bb_instructions /\ i.inst_opcode <> PHI))
Proof
  ntac 4 gen_tac >> rewrite_tac[compile_ifexp_arm_def] >> IF_CASES_TAC
  >- metis_tac[ctor_unwrap_value_first_emission] >>
  ho_match_mp_tac first_emission_strong >>
  ho_match_mp_tac first_emission_strong_bind >> conj_tac
  >- metis_tac[ctor_alloc_buffer_first_emission] >>
  gen_tac >> rewrite_tac[GSYM cs_appends_def] >>
  irule cs_appends_bind >> reverse conj_tac
  >- metis_tac[ctor_ci_mono_appends, ci_mono_unwrap_value] >>
  gen_tac >> BETA_TAC >> rewrite_tac[comp_ignore_bind_def] >>
  irule cs_appends_bind >> reverse conj_tac
  >- metis_tac[ctor_ci_mono_appends, ci_mono_compile_store_memory] >>
  simp[cs_appends_def, comp_return_def, cs_extends_refl]
QED

Theorem ifexp_selected_entry_first:
  compile_expr ce ty e se = (vv,sm) /\
  compile_ifexp_arm ce rt (lowered_value_type ce e) vv sm = (op,sx) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  fn_has_code se sm fn /\ fn_has_code sm sx fn /\ fn_has_code sx sy fn /\
  se.cs_current_insts = [] ==>
  ?bb i. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME i /\ i.inst_opcode <> PHI
Proof
  strip_tac >> drule ctor_compile_expr_first_emission >> strip_tac
  >- (drule ifexp_arm_first_emission >> strip_tac
      >- (drule_at Any (cj 1 first_emission_emit_helpers) >>
          simp[] >> strip_tac >> first_x_assum drule >> strip_tac >>
          gvs[] >> Cases_on `bb.bb_instructions` >>
          gvs[get_instruction_def]) >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      Cases_on `bb.bb_instructions` >> gvs[get_instruction_def]) >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `bb.bb_instructions` >> gvs[get_instruction_def]
QED

Theorem ifexp_selected_entry_reachable:
  compile_expr ce ty e se = (vv,sm) /\
  compile_ifexp_arm ce rt (lowered_value_type ce e) vv sm = (op,sx) /\
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  fn_has_code se sm fn /\ fn_has_code sm sx fn /\ fn_has_code sx sy fn /\
  se.cs_current_insts = [] /\ se.cs_current_bb = lbl /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s0,G0,tn0) marks (OK z,G,tn) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (z,G,tn) [] (OK (jump_to lbl z),G,tn) ==>
  !i. active_inst fn i (jump_to lbl z) ==>
    frag_reachable ctx fn s0 fn i (jump_to lbl z)
Proof
  strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s0,G0,tn0) marks (OK (jump_to lbl z),G,tn)` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks _`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`z`,`G`,`tn`,`[]`] mp_tac) >>
     simp[]) >>
  `?bb i. lookup_block lbl fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME i /\ i.inst_opcode <> PHI` by
    metis_tac[ifexp_selected_entry_first] >>
  drule_all gas_origin_ptr_path_projections >> strip_tac >>
  drule ifexp_ptr_path_reachable >>
  disch_then (qspec_then `jump_to lbl z` mp_tac) >>
  simp[jump_to_def] >> metis_tac[]
QED

Theorem gas_path_edge_reach:
  gas_path_edge ctx fn s n (OK t) /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!i. active_inst fn i s ==> frag_reachable ctx fn0 s0 fn i s) /\
  active_inst fn j t ==>
  frag_reachable ctx fn0 s0 fn j t
Proof
  strip_tac >>
  qpat_x_assum `gas_path_edge _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_path_edge_def]) >>
  `active_inst fn inst s` by metis_tac[contextCodegenRelPropsTheory.lookup_instruction_active] >>
  `frag_reachable ctx fn0 s0 fn inst s` by metis_tac[] >>
  gvs[exit_result_def]
  >- metis_tac[cj 2 contextRawReachableTheory.frag_reachable_rules]
  >- (`enters_block fn t'
         (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
        (simp[contextCodegenRelTheory.enters_block_def] >> metis_tac[]) >>
      metis_tac[cj 3 contextRawReachableTheory.frag_reachable_rules])
  >- (`?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
        (qpat_assum `active_inst fn j (jump_to lbl s)` mp_tac >>
         simp[NoAsms,contextCodegenRelTheory.active_inst_def,venomStateTheory.jump_to_def] >>
         strip_tac >>
         `!bbs label. (?b. MEM b bbs /\ b.bb_label = label) ==>
           ?bb. lookup_block label bbs = SOME bb` by
           (Induct >> simp[lookup_block_def, listTheory.FIND_thm] >>
            rpt strip_tac >> gvs[] >>
            Cases_on `label = h.bb_label` >> gvs[] >>
            metis_tac[lookup_block_def]) >>
         first_x_assum irule >> qexists_tac `bb'` >> simp[]) >>
      rename1 `lookup_block lbl fn.fn_blocks = SOME target` >>
      `phi_prefix_length target.bb_instructions = 0` by
        metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
      `enters_block fn (jump_to lbl s) (jump_to lbl s)` by
        (simp[contextCodegenRelTheory.enters_block_def,venomStateTheory.jump_to_def,eval_phis_no_phi] >> metis_tac[]) >>
      `~(jump_to lbl s).vs_halted` by simp[venomStateTheory.jump_to_def] >>
      metis_tac[cj 3 contextRawReachableTheory.frag_reachable_rules])
  >> Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def]
QED

Theorem gas_path_reach:
  !ctx fn s n r.
    gas_path ctx fn s n r ==>
    !fn0 s0 t.
      r = OK t /\
      (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
      (!i. active_inst fn i s ==> frag_reachable ctx fn0 s0 fn i s) ==>
      !j. active_inst fn j t ==> frag_reachable ctx fn0 s0 fn j t
Proof
  ho_match_mp_tac gas_path_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> gvs[exit_result_def] >>
  metis_tac[gas_path_edge_reach]
QED

Theorem gas_origin_ptr_path_erase:
  gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (OK t,G1,tn1)
  ==> gas_path ctx fn s (LENGTH marks) (OK t)
Proof
  strip_tac >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_projections >> strip_tac >>
  drule fragGasOriginTheory.gas_origin_path_erase >>
  metis_tac[fragGasModeTheory.gas_marked_path_exec]
QED

Theorem body_inv_no_phi_mods:
  contract_inv mods exps ctx cenv cx /\ MEM fn ctx.ctx_functions ==>
  !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule contract_inv_lowering_context >> strip_tac >>
  rpt strip_tac >> irule venomExecProofsTheory.no_phis_phi_prefix_length_zero >>
  fs[vyperCompilerTheory.lowering_context_ok_def,vyperCompilerTheory.ptr_ok_check_def,EVERY_MEM] >>
  metis_tac[venomFnInstsProofsTheory.MEM_fn_insts]
QED

Theorem body_inv_no_phi:
  body_inv tops ctx cenv cx /\ MEM fn ctx.ctx_functions ==>
  !bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0
Proof
  metis_tac[body_inv_contract, body_inv_no_phi_mods]
QED

Theorem gas_origin_ptr_path_dalloca_no_wrap:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s0,G0,tn0) marks (OK s1,G1,tn1) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_no_wrap inst s) ==>
  !fn inst s. frag_reachable ctx func s1 fn inst s ==> dalloca_no_wrap inst s
Proof
  strip_tac >> drule gas_origin_ptr_path_erase >> strip_tac >>
  `!i. active_inst func i s1 ==> frag_reachable ctx func s0 func i s1` by
    (drule gas_path_reach >>
     disch_then (qspecl_then [`func`,`s0`,`s1`] mp_tac) >>
     simp[frag_reachable_start]) >>
  metis_tac[frag_reachable_trans]
QED

(* Keep the actual path available to a continuation. *)
Theorem gas_outcome_full_post_path:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R /\
  (!marks H res ee G' tn' t.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK t,G',tn') /\ Q H res ee G' tn' t ==>
    Q' H res ee G' tn' t) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- fs[] >- fs[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `marks` >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED
