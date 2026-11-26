(* Protected caller-byte and ghost fields of the completed selected callee. *)
Theory bodySelectedCalleeProtectedExitMods
Ancestors
  bodyFullIntCallCallee bodyFullIntCallByteFrame bodyFullShadowBodyInv
  contractInvContextProps bodyInvMetadataProps bodyInvCodeProps
  immutableRegionDeadProps fragGasFocus fragGasOriginPtrExec
  ptrSafeRun ptrOkCheck lowerDloadMaskBounds venomExecSemantics
  venomExecProofs venomInst valueEncodingProofs vyperCompiler list ptrDiscipline
  exprLoweringProps fragExec loweringStateRelDefs venomState valueEncodingDefs
  bodyInvSplit bodyPtrDefs finite_map compileEnv words codegenRel

Theorem selected_pre_fmp_opcodes[local]:
  contract_inv mods exps ctx cenv cx ==> intcall_ghost_opcodes ctx
Proof
  strip_tac >> drule_then mp_tac contract_inv_lowering_context >>
  simp[lowering_context_ok_def] >> strip_tac >>
  drule ptr_ok_check_sound >>
  simp[EVERY_MEM, intcall_ghost_opcodes_def, fn_ptr_ok_def] >> metis_tac[]
QED

Theorem selected_entered_byte_frame[local]:
  setup_callee callee argv t = SOME setup /\
  eval_phis setup first.bb_instructions = OK ph /\
  fmp_room ctx callee setup ==>
  ph.vs_memory = t.vs_memory /\
  !x. x < t.vs_alloca_next ==>
    ptr_byte_frame_inv (ctx,x) FEMPTY
      (ph with vs_inst_idx := phi_prefix_length first.bb_instructions)
Proof
  strip_tac >>
  drule_then (once_rewrite_tac o single) eval_phis_only_updates_vs_vars >>
  gvs[setup_callee_def, ptr_byte_frame_inv_def] >>
  rpt strip_tac >> fs[fmp_room_def] >> decide_tac
QED

Theorem selected_clean_return_path[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir u,J,N) /\
  intcall_ghost_opcodes ctx /\ MEM callee ctx.ctx_functions /\
  ptr_byte_frame_inv (ctx,x) FEMPTY entered /\ lo <= x /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  x NOTIN tn.t_mem ==> x NOTIN N.t_mem
Proof
  strip_tac >>
  drule_then (qx_choose_then `fuel` strip_assume_tac o SRULE [exit_result_def])
    gas_origin_ptr_path_exec >>
  Cases_on `lookup_block entered.vs_current_bb callee.fn_blocks` >>
  gvs[run_from_def, ptr_safe_run_def, ghost_run_def, GSYM block_run_def] >>
  mp_tac intcall_callee_protected_ghost_run_rules >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
                 drule_all_then ACCEPT_TAC intcall_callee_protected_ordinary_step)) >>
  disch_then (assume_tac o cj 2) >>
  rename1 `lookup_block entered.vs_current_bb callee.fn_blocks = SOME bb` >>
  `x NOTIN (SND (ghost_block fuel ctx callee PG FEMPTY
     (tn with t_var := FEMPTY) bb entered)).t_mem` by
    (qpat_assum `!fuel ctx func PG G tn bb s. _` irule >>
     simp[ld_var_taint_bound_iff] >> qexistsl_tac [`D`, `lo`] >> simp[]) >>
  qpat_x_assum `x NOTIN (SND (ghost_block _ _ _ _ _ _ _ _)).t_mem` mp_tac >> simp[]
QED

Theorem staged_pointer_sites_miss_byte[local]:
  (!b sz. MEM (SOME (b,sz)) PG ==>
     ?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ n <= aid /\ aid < m) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ n <= aid /\ aid < m ==>
     x < b \/ b + sz <= x) /\ MEM (SOME (off,asz)) PG ==>
  x < off \/ off + asz <= x
Proof
  strip_tac >> first_x_assum drule >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem selected_intret_bytes[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,PG)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir u,J,N) /\
  MEM callee ctx.ctx_functions /\ entered.vs_memory = t.vs_memory /\
  (!x. x < t.vs_alloca_next ==> ptr_byte_frame_inv (ctx,x) FEMPTY entered) /\
  (!b sz. MEM (SOME (b,sz)) PG ==>
     ?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ n <= aid /\ aid < m) /\
  lo <= b /\ b + sz <= t.vs_alloca_next /\
  (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> regions_disjoint b sz off asz) ==>
  mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  strip_tac >> irule LIST_EQ >>
  simp[LENGTH_mem_bytes_at_proof] >> rpt strip_tac >> simp[EL_mem_bytes_at] >>
  rename1 `x < sz` >>
  `lo <= b + x /\ b + x < t.vs_alloca_next` by decide_tac >>
  `!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ n <= aid /\ aid < m ==>
     b + x < off \/ off + asz <= b + x` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!aid off asz. _ ==> regions_disjoint _ _ _ _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!off asz. MEM (SOME (off,asz)) PG ==> b + x < off \/ off + asz <= b + x` by
    (rpt gen_tac >> disch_tac >> irule staged_pointer_sites_miss_byte >>
     qexistsl_tac [`PG`, `m`, `n`, `t`] >> asm_rewrite_tac[]) >>
  `ptr_byte_frame_inv (ctx,b + x) FEMPTY entered` by simp[] >>
  `read_byte (b + x) u.vs_memory = read_byte (b + x) entered.vs_memory` by
    (qpat_assum `gas_origin_ptr_path _ _ _ _`
       (mp_then Any mp_tac ptr_byte_frame_completed_path) >>
     disch_then irule >> asm_rewrite_tac[]) >>
  qpat_x_assum `read_byte _ _ = _` mp_tac >> simp[read_byte_def]
QED

Theorem unit_dead_section_transport[local]:
  contract_inv mods exps ctx cenv cx /\ contract_inv mods exps ctx body_ce p /\
  imm_section_dead_mods body_ce sec i ==> imm_section_dead_mods cenv sec i
Proof
  strip_tac >>
  imp_res_tac contract_inv_cenv_modules >>
  Cases_on `?tops. mods = [(NONE,tops)]`
  >- gvs[imm_section_dead_mods_def] >>
  `(!tops. cenv.ce_modules <> [(NONE,tops)]) /\
   (!tops. body_ce.ce_modules <> [(NONE,tops)])` by gvs[] >>
  fs[imm_section_dead_mods_other] >>
  imp_res_tac contract_inv_immutable_section_layout >>
  fs[immutable_section_layout_mods_def] >>
  rename1 `ALOOKUP mods src = SOME tops` >>
  qexistsl_tac [`src`, `tops`, `vis`, `id`, `ty`, `slot`, `off`, `tv`] >>
  simp[] >> goal_assum drule
QED

(* The return convention supplies the low-byte and storage post at this very
   IntRet. The completed path protects the rest of the caller's memory. *)
Theorem selected_callee_protected_exit_mods:
  contract_inv mods exps ctx cenv cx /\ contract_inv mods exps ctx body_ce p /\
  dead_lo_ok_mods H D lo cenv cx /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\ eval_operands arg_ops t = SOME argv /\
  (!setup. setup_callee callee argv t = SOME setup ==> fmp_room ctx callee setup) /\
  (!b sz. MEM (SOME (b,sz)) (MAP (op_prov G) arg_ops) ==>
    ?aid. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ n <= aid /\ aid < m) /\
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir u,J,N) /\
  stor_taint_ok_at D N u /\
  (!i. i < lo /\ i IN N.t_mem ==>
       imm_section_dead_mods body_ce (mem_bytes_at 0 lo u.vs_memory) i) ==>
  (!b sz. (cenv.ce_is_ctor ==> imm_len_mods mods <= b) /\
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  stor_taint_ok_at D N u /\
  (!i. i < lo /\ i IN N.t_mem ==>
       imm_section_dead_mods cenv (mem_bytes_at 0 lo u.vs_memory) i) /\
  (!i. lo <= i /\ i < t.vs_alloca_next /\ i IN N.t_mem /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      n <= aid /\ aid < m ==> i < off \/ off + asz <= i) ==> i IN tn.t_mem)
Proof
  strip_tac >>
  qpat_x_assum `gas_invoke_entry _ _ _ _` (strip_assume_tac o REWRITE_RULE[gas_invoke_entry_def]) >>
  gvs[] >>
  `MEM callee ctx.ctx_functions` by (drule lookup_function_MEM >> simp[]) >>
  rename1 `eval_phis setup first.bb_instructions = OK phi_state` >>
  drule_all_then strip_assume_tac selected_entered_byte_frame >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `lo <= b` by
        (qpat_assum `contract_inv _ _ _ cenv cx`
           (assume_tac o MATCH_MP contract_inv_cenv_modules) >>
         qpat_x_assum `dead_lo_ok_mods _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [dead_lo_ok_mods_def]) >>
         Cases_on `cenv.ce_is_ctor` >> gvs[]) >>
      qpat_assum `gas_origin_ptr_path _ _ _ _`
        (mp_then Any mp_tac selected_intret_bytes) >>
      disch_then irule >> simp[] >> qexistsl_tac [`m`, `n`] >> asm_rewrite_tac[]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> irule unit_dead_section_transport >>
      qexistsl_tac [`body_ce`, `ctx`, `cx`, `exps`, `mods`, `p`] >>
      asm_rewrite_tac[] >> first_x_assum irule >> simp[]) >>
  gen_tac >> strip_tac >> CCONTR_TAC >>
  `intcall_ghost_opcodes ctx` by (drule selected_pre_fmp_opcodes >> simp[]) >>
  `ptr_byte_frame_inv (ctx,i) FEMPTY (phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions)` by simp[] >>
  `!b sz. MEM (SOME (b,sz)) (MAP (op_prov G) arg_ops) ==> i < b \/ b + sz <= i` by
    (rpt gen_tac >> disch_tac >> irule staged_pointer_sites_miss_byte >>
     qexistsl_tac [`MAP (op_prov G) arg_ops`, `m`, `n`, `t`] >>
     asm_rewrite_tac[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `i NOTIN N.t_mem` by
    (qpat_assum `gas_origin_ptr_path _ _ _ _`
       (mp_then Any mp_tac selected_clean_return_path) >>
     disch_then irule >> asm_rewrite_tac[]) >>
  fs[]
QED
