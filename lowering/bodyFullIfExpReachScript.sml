(* The raw-jump boundary used when specializing the selected IfExp arm. *)
Theory bodyFullIfExpReach
Ancestors
  fragGasOriginPtr fragGasPathPtr contextRawReachable contextCodegenRel venomExecProofs
  venomExecSemantics venomInst venomState fragExec
  ctorDeployMemoryRunMemEntryFirstEmission compilerFirstEmission
  exprLoweringProps exprLowering compileEnv
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
