(* Caller-byte separation at the full internal-call entry. *)
Theory bodyFullIntCallByteFrame
Ancestors
  bodyFullIntCallDefs bodyIntCallSeams compileUnit bodyPtrDefs ptrDiscipline ptrSafeRun
  stepWriteFootprintBase loweringStateRelDefs valueEncodingDefs
  codegenRel contextCodegenRel venomExecProofs venomExecSemantics venomState
  runtimeProvenanceSources ctxLookupAgreeHelpers venomMemProofs venomFnInstsProofs venomInst
  venomMemDefs venomInstProofs venomInstProofs1 calleeTransport stepWriteFootprintForward
  fragGasOriginPtrExec fragGasFocus fragExec valueEncodingProofs exprLoweringProps
  finite_map list arithmetic words

Theorem intcall_entry_full_provenance_disjoint:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
    regions_disjoint b sz off asz) ==>
  !off asz. MEM (SOME (off,asz)) (MAP (op_prov G) arg_ops) ==>
    regions_disjoint b sz off asz
Proof
  rw[intcall_entry_full_def] >> metis_tac[]
QED



fun intcall_entry_fmp_room_tac entry_definition package =
  rw[entry_definition] >>
  qpat_x_assum `lookup_function lbl _ = SOME callee` mp_tac >>
  qpat_x_assum `setup_callee callee argv t = SOME setup` mp_tac >>
  qpat_x_assum `lookup_block _ _ = SOME bb` mp_tac >>
  qpat_x_assum `lookup_block _ _ = SOME bb'` mp_tac >>
  qpat_x_assum `get_instruction bb _ = SOME inst` mp_tac >>
  qpat_x_assum `get_instruction bb' _ = SOME inst'` mp_tac >>
  qpat_x_assum `decode_invoke inst = _` mp_tac >>
  qpat_x_assum `decode_invoke inst' = _` mp_tac >>
  qpat_x_assum `eval_operands arg_ops t = _` mp_tac >>
  qpat_x_assum `eval_operands arg_ops' t = _` mp_tac >>
  qpat_x_assum `!callee setup use_trans nkeys imm_len dflts lbl' ce params has_rb
    is_nr key trans view ctor imm_len' ss' rt. _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!use_trans nkeys imm_len dflts lbl' ce params has_rb
    is_nr key trans view ctor imm_len' ss' rt. _`
    (qspecl_then [`F`, `\x:string. 0`, `0`, `([]:expr list)`] mp_tac) >>
  simp[] >>
  qabbrev_tac `pack = ^package` >>
  PairCases_on `pack` >>
  disch_then (qspecl_then [`pack0`,`pack1`,`pack2`,`pack3`,`pack4`,`pack5`,
    `pack6`,`pack7`,`pack8`,`pack9`,`pack10`,`pack11`] mp_tac) >>
  simp[] >> strip_tac >> metis_tac[];

Theorem intcall_entry_full_fmp_room:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup ==>
  fmp_room ctx callee setup
Proof
  intcall_entry_fmp_room_tac intcall_entry_full_def
    ``set_internal_package_target cenv.ce_target
      (package_internal_fn tops F (\x:string. 0) cenv.ce_is_ctor 0
        (mut,nr,rr,name,args,([]:expr list),ret,ss))``
QED

Theorem intcall_entry_full_fmp_room_mods:
  intcall_entry_full_mods (DF, lo, d) H mods src tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lookup_function lbl ctx.ctx_functions = SOME callee /\
  setup_callee callee argv t = SOME setup ==>
  fmp_room ctx callee setup
Proof
  intcall_entry_fmp_room_tac intcall_entry_full_mods_def
    ``set_internal_package_target cenv.ce_target
      (package_internal_fn_unit mods F (\x:string. 0) cenv.ce_is_ctor 0
        (src,(mut,nr,rr,name,args,([]:expr list),ret,ss)))``
QED

(* Every pointer site and allocation misses x; a fresh allocation starts
   above x. Dynamic allocations start above the immutable initial FMP. *)
Definition ptr_byte_frame_inv_def:
  ptr_byte_frame_inv (ctx,x) (G:string |-> num # num) s <=>
    x < s.vs_alloca_next /\
    (!v b sz. FLOOKUP G v = SOME (b,sz) ==> x < b \/ b + sz <= x) /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
       x < b \/ b + sz <= x) /\
    (ctx_has_dalloca ctx ==> x < w2n s.vs_initial_fmp)
End

Theorem ptr_byte_frame_inv_inst_idx:
  ptr_byte_frame_inv (ctx,x) G (s with vs_inst_idx := k) <=>
  ptr_byte_frame_inv (ctx,x) G s
Proof
  simp[ptr_byte_frame_inv_def]
QED



Theorem ptr_byte_frame_entry_prov:
  (!v b sz. FLOOKUP G v = SOME (b,sz) ==> x < b \/ b + sz <= x) ==>
  !v b sz. FLOOKUP (entry_prov func s G) v = SOME (b,sz) ==>
    x < b \/ b + sz <= x
Proof
  simp[entry_prov_def] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks`
  >- (simp[] >> metis_tac[]) >> simp[] >>
  rpt strip_tac >> drule phis_prov_source >> strip_tac
  >- metis_tac[] >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem ptr_byte_frame_step_prov[local]:
  (!v b sz. FLOOKUP G v = SOME (b,sz) ==> x < b \/ b + sz <= x) /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    x < b \/ b + sz <= x) /\
  (inst.inst_opcode = DALLOCA ==> !v w.
    inst.inst_outputs = [v] /\ lookup_var v t = SOME w ==> x < w2n w) ==>
  !v b sz. FLOOKUP (step_prov PG G inst t) v = SOME (b,sz) ==>
    x < b \/ b + sz <= x
Proof
  rpt strip_tac >> fs[step_prov_def] >>
  drule set_prov_source >> strip_tac >- metis_tac[] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[out_prov_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (gvs[out_prov_def, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[out_prov_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  gvs[out_prov_def, AllCaseEqs()] >>
  drule first_prov_origin >> metis_tac[]
QED

Theorem access_ok_protected_byte[local]:
  access_ok lo G func inst s /\ ~in_revert_forward func s /\ lo <= x /\
  (!v off sz. FLOOKUP G v = SOME (off,sz) ==> x < off \/ off + sz <= x) ==>
  !off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
    ~(off <= x /\ x < off + len)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `len <> 0 /\ lo < off + len` by decide_tac >>
  fs[access_ok_def] >>
  qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges _ _) /\ _ ==> _`
    (qspecl_then [`off`, `len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!v off sz. _` drule >> decide_tac
QED

Theorem ptr_safe_noninvoke_protected_byte[local]:
  ptr_safe_step D lo fuel ctx func PG G tn inst s /\
  inst.inst_opcode <> INVOKE /\ ~in_revert_forward func s /\ lo <= x /\
  (!v off sz. FLOOKUP G v = SOME (off,sz) ==> x < off \/ off + sz <= x) /\
  (step_inst fuel ctx inst s = OK t \/
   step_inst fuel ctx inst s = IntRet ir t) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >>
  `access_ok lo G func inst s` by
    metis_tac[ptr_safe_step_inst_ok, ptr_inst_ok_def] >>
  `!off len. MEM (off,len) (source_memory_write_ranges inst s) ==>
     ~(off <= x /\ x < off + len)` by metis_tac[access_ok_protected_byte] >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_OK_byte_frame, step_inst_base_IntRet_byte_frame, ADD_COMM]
QED

Theorem exec_alloca_protected_byte_sites:
  x < s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    x < b \/ b + sz <= x) /\ exec_alloca inst s n = OK t ==>
  x < t.vs_alloca_next /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    x < b \/ b + sz <= x)
Proof
  rw[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  res_tac >> decide_tac
QED

Theorem noninvoke_protected_byte_sites[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  x < t.vs_alloca_next /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    x < b \/ b + sz <= x) /\
  (ctx_has_dalloca ctx ==> x < w2n t.vs_initial_fmp)
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  `t.vs_initial_fmp = s.vs_initial_fmp` by
    metis_tac[step_inst_base_initial_fmp] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >>
      fs[ptr_byte_frame_inv_def] >>
      metis_tac[exec_alloca_protected_byte_sites, ADD_COMM]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_fields] >>
  fs[ptr_byte_frame_inv_def] >> metis_tac[]
QED

Theorem dalloca_protected_byte_output[local]:
  ptr_byte_frame_inv (ctx,x) G s /\ allocas_below_fmp s /\
  ctx_has_dalloca ctx /\ inst.inst_opcode = DALLOCA /\
  step_inst fuel ctx inst s = OK t /\
  inst.inst_outputs = [v] /\ lookup_var v t = SOME w ==>
  x < w2n w
Proof
  strip_tac >>
  `x < w2n s.vs_fmp` by
    (fs[ptr_byte_frame_inv_def, allocas_below_fmp_def] >> decide_tac) >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(),
      update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ptr_byte_frame_noninvoke[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  (inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx) /\
  ptr_safe_step D lo fuel ctx func PG G tn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  ptr_byte_frame_inv (ctx,x) (step_prov PG G inst t) t
Proof
  strip_tac >> drule_all noninvoke_protected_byte_sites >> strip_tac >>
  `inst.inst_opcode = DALLOCA ==> !v w.
     inst.inst_outputs = [v] /\ lookup_var v t = SOME w ==> x < w2n w` by
    metis_tac[dalloca_protected_byte_output, ptr_safe_step_inst_ok, ptr_inst_ok_def] >>
  fs[ptr_byte_frame_inv_def] >>
  mp_tac (Q.INST [`G` |-> `G`, `x` |-> `x`, `PG` |-> `PG`,
                   `t` |-> `t`, `inst` |-> `inst`] ptr_byte_frame_step_prov) >>
  simp[] >> metis_tac[]
QED

Theorem ptr_byte_frame_invoke_params:
  (!v b sz. FLOOKUP G v = SOME (b,sz) ==> x < b \/ b + sz <= x) ==>
  !b sz. MEM (SOME (b,sz)) (MAP (op_prov G) ops) ==>
    x < b \/ b + sz <= x
Proof
  simp[MEM_MAP] >> rpt strip_tac >>
  rename1 `MEM operand ops` >>
  Cases_on `operand` >> gvs[op_prov_def] >> metis_tac[]
QED

Theorem ptr_byte_frame_setup[local]:
  ptr_byte_frame_inv (ctx,x) G s /\ setup_callee func args s = SOME cs ==>
  ptr_byte_frame_inv (ctx,x) FEMPTY cs /\ cs.vs_memory = s.vs_memory
Proof
  rw[setup_callee_def, ptr_byte_frame_inv_def] >> gvs[]
QED

Theorem block_run_intret_not_forward[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  block_run fuel ctx func bb s = IntRet ir t ==>
  ~in_revert_forward func s
Proof
  strip_tac >> CCONTR_TAC >> fs[in_revert_forward_def] >>
  Cases_on `exec_block fuel ctx bb s` >> gvs[block_run_def] >>
  metis_tac[revert_forward_at_no_normal]
QED

Theorem ptr_byte_frame_inv_phis[local]:
  ptr_byte_frame_inv (ctx,x) G s /\ eval_phis s insts = OK t ==>
  ptr_byte_frame_inv (ctx,x) G (t with vs_inst_idx := k) /\
  t.vs_memory = s.vs_memory /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> drule eval_phis_only_updates_vs_vars >>
  disch_then (fn th => once_rewrite_tac[th]) >> fs[ptr_byte_frame_inv_def] >>
  metis_tac[]
QED

Theorem ptr_byte_frame_terminator_entry[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  ptr_byte_frame_inv (ctx,x) (entry_prov func t G) t
Proof
  strip_tac >> drule_all noninvoke_protected_byte_sites >> strip_tac >>
  fs[ptr_byte_frame_inv_def] >> metis_tac[ptr_byte_frame_entry_prov]
QED

Theorem current_dalloca_in_context[local]:
  MEM func ctx.ctx_functions /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = DALLOCA ==>
  ctx_has_dalloca ctx
Proof
  rw[ctx_has_dalloca_def, EXISTS_MEM] >>
  qexists_tac `func` >> simp[] >> qexists_tac `inst` >> simp[] >>
  simp[fn_insts_def] >> irule mem_fn_insts_blocks >>
  qexists_tac `bb` >> simp[] >>
  gvs[get_instruction_def] >> metis_tac[lookup_block_MEM, EL_MEM]
QED

Theorem ptr_byte_frame_merge[local]:
  ptr_byte_frame_inv (ctx,x) G s /\
  bind_outputs outs vals (adopt_return_fmp ir (merge_callee_state s cs)) = SOME t ==>
  ptr_byte_frame_inv (ctx,x) (DRESTRICT G (COMPL (set outs))) t /\
  t.vs_memory = cs.vs_memory
Proof
  strip_tac >>
  `ptr_byte_frame_inv (ctx,x) (DRESTRICT G (COMPL (set outs))) t =
   ptr_byte_frame_inv (ctx,x) (DRESTRICT G (COMPL (set outs)))
     (adopt_return_fmp ir (merge_callee_state s cs))` by
    (irule bind_outputs_preserves >>
     simp[update_var_def, ptr_byte_frame_inv_def] >> metis_tac[]) >>
  drule bind_outputs_shared_fields >> strip_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[ptr_byte_frame_inv_def, adopt_return_fmp_def, merge_callee_state_def,
      FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ptr_byte_frame_run[local]:
  (!fuel ctx PG G tn inst s. !D lo func x t.
    ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    (inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx) /\
    ptr_safe_step D lo fuel ctx func PG G tn inst s /\
    ~in_revert_forward func s /\ step_inst fuel ctx inst s = OK t ==>
    ptr_byte_frame_inv (ctx,x) (FST (ghost_step fuel ctx PG G tn inst s)) t /\
    read_byte x t.vs_memory = read_byte x s.vs_memory) /\
  (!fuel ctx func PG G tn bb s. !D lo x ir t.
    ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    MEM func ctx.ctx_functions /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    ptr_safe_block D lo fuel ctx func PG G tn bb s /\
    block_run fuel ctx func bb s = IntRet ir t ==>
    read_byte x t.vs_memory = read_byte x s.vs_memory) /\
  (!fuel ctx func PG G tn s. !D lo x ir t.
    ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
    (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
    MEM func ctx.ctx_functions /\
    ptr_safe_blocks D lo fuel ctx func PG G tn s /\
    run_blocks fuel ctx func s = IntRet ir t ==>
    read_byte x t.vs_memory = read_byte x s.vs_memory)
Proof
  ho_match_mp_tac ghost_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume ptr_byte_frame_run[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[Once ghost_step_def] >>
  conj_tac >- metis_tac[ptr_byte_frame_noninvoke] >>
  fs[ptr_byte_frame_inv_def] >> metis_tac[ptr_safe_noninvoke_protected_byte]
QED

Resume ptr_byte_frame_run[invoke]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_all ptr_byte_frame_setup >> strip_tac >>
  `!b sz. MEM (SOME (b,sz)) (MAP (op_prov G) arg_ops) ==> x < b \/ b + sz <= x` by
    (fs[ptr_byte_frame_inv_def] >> metis_tac[ptr_byte_frame_invoke_params]) >>
  `ptr_safe_blocks D lo fuel ctx callee_fn (MAP (op_prov G) arg_ops)
     FEMPTY (tn with t_var := FEMPTY) callee_s` by
    (qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once ptr_safe_step_def]) >>
  `MEM callee_fn ctx.ctx_functions` by
    metis_tac[lookup_function_MEM] >>
  `read_byte x callee_s'.vs_memory = read_byte x callee_s.vs_memory` by
    (qpat_x_assum `!D' lo' x'. _`
       (qspecl_then [`D`, `lo`, `x`] mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all ptr_byte_frame_merge >> strip_tac >>
  simp[Once ghost_step_def] >> metis_tac[]
QED

Resume ptr_byte_frame_run[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `~in_revert_forward func s` by metis_tac[block_run_intret_not_forward] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- gvs[block_run_def, Once exec_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `ptr_safe_step D lo fuel ctx func PG G tn inst s` by
    metis_tac[ptr_safe_block_head] >>
  `inst.inst_opcode = DALLOCA ==> ctx_has_dalloca ctx` by
    metis_tac[current_dalloca_in_context] >>
  Cases_on `step_inst fuel ctx inst s`
  >~ [`step_inst fuel ctx inst s = OK u`]
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- suspend "terminator" >>
      `ptr_byte_frame_inv (ctx,x)
         (FST (ghost_step fuel ctx PG G tn inst s)) u /\
       read_byte x u.vs_memory = read_byte x s.vs_memory` by metis_tac[] >>
      `u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_control_flow] >>
      `ptr_byte_frame_inv (ctx,x)
         (FST (ghost_step fuel ctx PG G tn inst s))
         (u with vs_inst_idx := SUC s.vs_inst_idx)` by
        metis_tac[ptr_byte_frame_inv_inst_idx] >>
      `ptr_safe_block D lo fuel ctx func PG
         (FST (ghost_step fuel ctx PG G tn inst s))
         (SND (ghost_step fuel ctx PG G tn inst s)) bb
         (u with vs_inst_idx := SUC s.vs_inst_idx)` by
        metis_tac[ptr_safe_block_step] >>
      `block_run fuel ctx func bb
         (u with vs_inst_idx := SUC s.vs_inst_idx) = IntRet ir t` by
        metis_tac[block_run_step] >>
      qpat_x_assum `!inst' s''. _ /\ _ /\ ~is_terminator inst'.inst_opcode ==> _`
        (qspecl_then [`inst`,`u`] mp_tac) >> simp[] >>
      disch_then (qspecl_then [`D`,`lo`,`x`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  qpat_x_assum `block_run _ _ _ _ _ = _` mp_tac >>
  simp[block_run_def, Once exec_block_def] >> strip_tac >> gvs[] >>
  `inst.inst_opcode <> INVOKE` by metis_tac[step_inst_intret_not_invoke] >>
  fs[ptr_byte_frame_inv_def] >> metis_tac[ptr_safe_noninvoke_protected_byte]
QED

Resume ptr_byte_frame_run[terminator]:
  `~u.vs_halted` by
    (qpat_x_assum `block_run _ _ _ _ _ = _` mp_tac >>
     simp[block_run_def, Once exec_block_def] >>
     Cases_on `u.vs_halted` >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `read_byte x u.vs_memory = read_byte x s.vs_memory` by
    (qpat_x_assum `ptr_byte_frame_inv (ctx,x) G s`
       (strip_assume_tac o REWRITE_RULE [ptr_byte_frame_inv_def]) >>
     metis_tac[ptr_safe_noninvoke_protected_byte]) >>
  `ptr_byte_frame_inv (ctx,x) (entry_prov func u G) u` by
    metis_tac[ptr_byte_frame_terminator_entry] >>
  `ptr_safe_blocks D lo fuel ctx func PG (entry_prov func u G)
     (entry_taint_vars func u tn) u` by metis_tac[ptr_safe_block_terminator] >>
  `run_blocks fuel ctx func u = IntRet ir t` by metis_tac[block_run_terminator] >>
  qpat_x_assum `!inst' s''. _ /\ _ /\ is_terminator inst'.inst_opcode /\
    ~s''.vs_halted ==> _` (qspecl_then [`inst`,`u`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`D`,`lo`,`x`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume ptr_byte_frame_run[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks`
  >- gvs[Once run_blocks_def] >>
  rename1 `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      drule_all ptr_byte_frame_inv_phis >>
      disch_then (qspec_then `phi_prefix_length bb.bb_instructions` strip_assume_tac) >>
      `block_run n ctx func bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
       IntRet ir t` by metis_tac[run_blocks_block_run] >>
      `ptr_safe_block D lo n ctx func PG G tn bb
         (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
        metis_tac[ptr_safe_blocks_block] >>
      qpat_x_assum `!fuel' bb' s_phi. _`
        (qspecl_then [`n`,`bb`,`sp`] mp_tac) >> simp[] >>
      disch_then (qspecl_then [`D`,`lo`,`x`] mp_tac) >>
      simp[] >> metis_tac[ptr_byte_frame_inv_inst_idx]) >>
  gvs[Once run_blocks_def]
QED
Finalise ptr_byte_frame_run

Theorem ptr_byte_frame_completed_path:
  ptr_byte_frame_inv (ctx,x) G s /\ lo <= x /\
  (!b sz. MEM (SOME (b,sz)) PG ==> x < b \/ b + sz <= x) /\
  MEM func ctx.ctx_functions /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) marks (IntRet ir t,G',tn') ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >> drule gas_origin_ptr_path_exec >>
  simp[exit_result_def] >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >>
  gvs[run_from_def, ptr_safe_run_def, GSYM block_run_def] >>
  metis_tac[cj 2 ptr_byte_frame_run]
QED

fun intcall_entry_completed_byte_tac entry_pattern entry_definition fmp_room_theorem =
  strip_tac >> fs[gas_invoke_entry_def] >> gvs[] >>
  `fmp_room ctx callee setup` by metis_tac[fmp_room_theorem] >>
  `ptr_byte_frame_inv (ctx,x) FEMPTY setup` by
    (gvs[setup_callee_def, ptr_byte_frame_inv_def] >>
     rpt strip_tac >> fs[fmp_room_def] >> decide_tac) >>
  `ptr_byte_frame_inv (ctx,x) FEMPTY
     (phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions) /\
   phi_state.vs_memory = setup.vs_memory` by
    metis_tac[ptr_byte_frame_inv_phis] >>
  `!b sz. MEM (SOME (b,sz)) (MAP (op_prov G) arg_ops) ==>
     x < b \/ b + sz <= x` by
    (qpat_x_assum entry_pattern
       (mp_tac o last o CONJUNCTS o REWRITE_RULE [entry_definition]) >>
     disch_then (qspecl_then [`bb`,`inst`,`lbl`,`arg_ops`,`argv`] mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!b bsz. MEM (SOME (b,bsz)) (MAP (op_prov G) arg_ops) ==> _` mp_tac >>
     qpat_x_assum `!aid off asz.
       FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  qpat_x_assum `ptr_byte_frame_inv _ _ setup` kall_tac >>
  drule_all ptr_byte_frame_completed_path >> simp[] >> strip_tac >>
  gvs[setup_callee_def];

Theorem intcall_entry_full_completed_byte[local]:
  intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lo <= x /\ x < t.vs_alloca_next /\
  (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> x < off \/ off + asz <= x) /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir s',G',tn') ==>
  read_byte x s'.vs_memory = read_byte x t.vs_memory
Proof
  intcall_entry_completed_byte_tac
    `intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb
       vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn`
    intcall_entry_full_def intcall_entry_full_fmp_room
QED

Theorem intcall_entry_full_completed_byte_mods[local]:
  intcall_entry_full_mods (DF, lo, d) H mods src tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  lo <= x /\ x < t.vs_alloca_next /\
  (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> x < off \/ off + asz <= x) /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir s',G',tn') ==>
  read_byte x s'.vs_memory = read_byte x t.vs_memory
Proof
  intcall_entry_completed_byte_tac
    `intcall_entry_full_mods (DF,lo,d) H mods src tops ctx func cenv cx tenv name es sa sb
       vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn`
    intcall_entry_full_mods_def intcall_entry_full_fmp_room_mods
QED

(* This uses only the stage's entry, dead-byte bound and actual INVOKE
   hypotheses. The path is the completed-run witness of gas_outcome_full. *)
fun intcall_callee_caller_memory_bytes_tac entry_tac completed_byte byte_bound_tac =
  strip_tac >>
  entry_tac >>
  rpt gen_tac >> strip_tac >> irule LIST_EQ >>
  simp[LENGTH_mem_bytes_at_proof] >> rpt strip_tac >> simp[EL_mem_bytes_at] >>
  `lo <= b + x /\ b + x < t.vs_alloca_next` by byte_bound_tac >>
  `!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
     sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
     b + x < off \/ off + asz <= b + x` by
    (rpt strip_tac >> res_tac >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `read_byte (b + x) s'.vs_memory = read_byte (b + x) t.vs_memory` by
    metis_tac[completed_byte] >>
  fs[read_byte_def];

Theorem intcall_callee_caller_memory_bytes:
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    intcall_entry_full (DF, lo, d) H tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  valid_horizon cx st0 H es1.storage_trace /\
  gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
    MAP (op_prov G) arg_ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir s',G',tn') ==>
  !b sz. (cenv.ce_is_ctor ==> imm_len_mods cenv.ce_modules <= b) /\
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  intcall_callee_caller_memory_bytes_tac
    (`intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
      (qpat_assum `!K. valid_horizon cx st0 K es1.storage_trace ==> _`
         (mp_tac o Q.SPEC `H`) >> simp[]))
    intcall_entry_full_completed_byte
    (`lo = if cenv.ce_is_ctor then imm_len_mods cenv.ce_modules else 0` by
       metis_tac[dead_lo_ok_def] >>
     Cases_on `cenv.ce_is_ctor` >> gvs[] >> decide_tac)
QED


Theorem intcall_callee_caller_memory_bytes_mods:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    intcall_entry_full_mods (DF, lo, d) H mods src tops ctx func cenv cx tenv name es sa sb
      vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn) /\
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  eval_operands arg_ops t = SOME argv /\
  valid_horizon cx st0 H es1.storage_trace /\
  gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,callee,
    MAP (op_prov G) arg_ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir s',G',tn') ==>
  !b sz. lo <= b /\
    b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==>
      regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  intcall_callee_caller_memory_bytes_tac
    (`intcall_entry_full_mods (DF,lo,d) H mods src tops ctx func cenv cx tenv name es sa sb
    vv s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn` by
      (qpat_assum `!K. valid_horizon cx st0 K es1.storage_trace ==> _`
         (mp_tac o Q.SPEC `H`) >> simp[]))
    intcall_entry_full_completed_byte_mods decide_tac
QED
