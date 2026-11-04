(*
 * LowerDload against the O1 pass contract: the runs of the input and the
 * output match up to the dead bytes D.
 * Kept in its own theory so its proof can be worked on apart from the
 * other rows; o1ContractLowerDloadStage assembles them.
 *
 * TOP-LEVEL:
 *   lower_dload_stage_sim
 *)
Theory o1ContractLowerDloadSim
Ancestors
  o1ContractLowerDload o1PassContract ptrDiscipline unitMemInv
  lowerDloadDefs venomPassSchedule list venomFnScheduleRunner
  venomCompilerTypes irSupply venomPassDispatcher venomInst

(* The runner supplies a covering supply separately for each function. *)
Theorem lower_dload_stage_supply_rel:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' ==>
  LIST_REL (\f g. ?s t. ir_supply_covers_fn s f /\
                         lower_dload_function_supply s f = (g,t))
    C.ctx_functions C'.ctx_functions
Proof
  rw[ctx_pass_stage_def] >>
  irule LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[fn_pass_step_def, AllCaseEqs()] >>
  rename1 `lower_dload_function_supply s f = (g,t)` >>
  `MEM f observed.cu_context.ctx_functions` by
    (gvs[lookup_unique_function_def, AllCaseEqs()] >>
     `MEM f (FILTER (\g. g.fn_name = f.fn_name)
                observed.cu_context.ctx_functions)` by simp[] >>
     gvs[MEM_FILTER]) >>
  qexistsl [`s`, `t`] >> simp[] >>
  gvs[ir_supply_covers_unit_def, ir_supply_covers_fn_def, list_subset_def,
      unit_ir_inst_ids_def, unit_ir_vars_def, unit_ir_labels_def,
      EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem lower_dload_stage_lookup_supply:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  lookup_function name C.ctx_functions = SOME f ==>
  ?g s t. lookup_function name C'.ctx_functions = SOME g /\
          ir_supply_covers_fn s f /\
          lower_dload_function_supply s f = (g,t)
Proof
  strip_tac >> drule lower_dload_stage_supply_rel >>
  qpat_x_assum `ctx_pass_stage _ _ _ _ _` kall_tac >>
  qpat_x_assum `lookup_function _ _ = _` mp_tac >>
  qid_spec_tac `f` >>
  Q.SPEC_TAC (`C'.ctx_functions`, `gs`) >>
  Q.SPEC_TAC (`C.ctx_functions`, `fs`) >>
  Induct >> Cases_on `gs` >>
  simp[lookup_function_def, FIND_thm] >> rpt strip_tac >>
  rename1 `lower_dload_function_supply supply src = (dst,supply')` >>
  drule lower_dload_function_supply_labels >> strip_tac >>
  Cases_on `src.fn_name = name` >> gvs[] >>
  fs[GSYM lookup_function_def] >> metis_tac[]
QED

(* Zero-size allocation provenance cannot license a pointer comparison. *)
Theorem access_ok_zero_size_comparison:
  access_ok lo G fn inst s /\
  (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/ inst.inst_opcode = EQ) /\
  inst.inst_operands = [Var u; Var w] /\ FLOOKUP G u = SOME (b,0)
  ==> F
Proof
  strip_tac >>
  `u IN FDOM G` by metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  fs[access_ok_def] >>
  first_x_assum (qspecl_then [`u`, `w`] mp_tac) >> simp[]
QED

(* Allocation boundary equations: no memory is initialized by ALLOCA. *)
Theorem lower_dload_alloca_fresh:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
  exec_alloca inst s amount =
    OK (update_var out (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
                    (inst.inst_id, (s.vs_alloca_next, w2n amount));
                vs_alloca_next := s.vs_alloca_next + w2n amount|>))
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_alloca_repeated:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (addr,sz) ==>
  exec_alloca inst s amount = OK (update_var out (n2w addr) s)
Proof
  simp[venomExecSemanticsTheory.exec_alloca_def]
QED

Theorem lower_dload_merge_allocation_memory:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas /\
  (merge_callee_state caller callee).vs_alloca_next = caller.vs_alloca_next /\
  (merge_callee_state caller callee).vs_memory = callee.vs_memory
Proof
  simp[venomExecSemanticsTheory.merge_callee_state_def]
QED

Theorem lower_dload_translate_add:
  !x z b c. ((x:bytes32) + n2w c - n2w b) + z =
             (x + z) + n2w c - n2w b
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem lower_dload_translate_sub:
  !x z b c. ((x:bytes32) + n2w c - n2w b) - z =
             (x - z) + n2w c - n2w b
Proof
  wordsLib.WORD_DECIDE_TAC
QED

Theorem lower_dload_translate_endpoint:
  !x b c sz.
    b <= w2n (x:bytes32) /\ w2n x <= b+sz /\
    b+sz < dimword (:256) /\ c+sz < dimword (:256) ==>
    w2n (x + n2w c - n2w b) = c + (w2n x - b)
Proof
  rpt strip_tac >>
  `w2n x = b + (w2n x - b)` by decide_tac >>
  `x = n2w b + n2w (w2n x - b)` by
    (pure_rewrite_tac[wordsTheory.word_add_n2w] >>
     qpat_x_assum `w2n x = _` (SUBST1_TAC o GSYM) >>
     pure_rewrite_tac[wordsTheory.n2w_w2n] >> REFL_TAC) >>
  qpat_x_assum `w2n x = _` kall_tac >>
  `x + n2w c - n2w b = n2w (c + (w2n x - b))` by
    (pure_rewrite_tac[GSYM wordsTheory.word_add_n2w] >>
     qpat_x_assum `x = _`
       (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     qabbrev_tac `p = (n2w b:bytes32)` >>
     qabbrev_tac `q = (n2w (w2n x - b):bytes32)` >>
     qabbrev_tac `r = (n2w c:bytes32)` >>
     POP_ASSUM_LIST (K ALL_TAC) >> wordsLib.WORD_DECIDE_TAC) >>
  `c + (w2n x - b) < dimword (:256)` by decide_tac >>
  qpat_x_assum `x + _ - _ = _`
    (fn th => pure_rewrite_tac[th, wordsTheory.w2n_n2w]) >>
  irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC
QED

Theorem lower_dload_translate_comparisons:
  !x y b c sz.
    b <= w2n (x:bytes32) /\ w2n x <= b+sz /\
    b <= w2n (y:bytes32) /\ w2n y <= b+sz /\
    b+sz < dimword (:256) /\ c+sz < dimword (:256) ==>
    ((x = y) <=> (x + n2w c - n2w b = y + n2w c - n2w b)) /\
    ((w2n x < w2n y) <=>
      (w2n (x + n2w c - n2w b) < w2n (y + n2w c - n2w b))) /\
    ((w2n y < w2n x) <=>
      (w2n (y + n2w c - n2w b) < w2n (x + n2w c - n2w b)))
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (x + n2w c - n2w b) = c + (w2n x - b)` by
    (irule lower_dload_translate_endpoint >> asm_rewrite_tac[] >>
     qexists_tac `sz` >> asm_rewrite_tac[]) >>
  `w2n (y + n2w c - n2w b) = c + (w2n y - b)` by
    (irule lower_dload_translate_endpoint >> asm_rewrite_tac[] >>
     qexists_tac `sz` >> asm_rewrite_tac[]) >>
  pure_rewrite_tac[GSYM wordsTheory.w2n_11] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem lower_dload_frontier_credit_bound:
  !n m k q. m = n + 32*k /\ k <= q /\
    n + 32*q < dimword (:256) ==> m < dimword (:256)
Proof
  rpt strip_tac >> decide_tac
QED

Theorem lower_dload_frontier_credit_step:
  !n m k a:num. m = n + 32*k ==>
    m+a = (n+a) + 32*k /\ m+32 = n + 32*(k+1)
Proof
  rpt strip_tac >> decide_tac
QED

(* One effect equation covers fresh, repeated and target-only scratch sites. *)
Theorem lower_dload_alloca_frontier:
  exec_alloca inst s amount = OK t ==>
  t.vs_alloca_next = s.vs_alloca_next +
    (if FLOOKUP s.vs_allocas inst.inst_id = NONE then w2n amount else 0)
Proof
  Cases_on `inst.inst_outputs` >>
  simp[venomExecSemanticsTheory.exec_alloca_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (simp[venomStateTheory.update_var_def] >> strip_tac >> gvs[]) >>
  PairCases_on `x` >> simp[venomStateTheory.update_var_def] >>
  strip_tac >> gvs[]
QED

Theorem lower_dload_alloca_credit:
  exec_alloca i s (amount:bytes32) = OK t /\
  exec_alloca j s' amount = OK t' /\
  (FLOOKUP s.vs_allocas i.inst_id = NONE <=>
   FLOOKUP s'.vs_allocas j.inst_id = NONE) /\
  s'.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  t'.vs_alloca_next = t.vs_alloca_next + 32*k
Proof
  strip_tac >>
  qpat_x_assum `exec_alloca i _ _ = _`
    (mp_then Any assume_tac lower_dload_alloca_frontier) >>
  qpat_x_assum `exec_alloca j _ _ = _`
    (mp_then Any assume_tac lower_dload_alloca_frontier) >>
  Cases_on `FLOOKUP s.vs_allocas i.inst_id = NONE` >> gvs[] >> decide_tac
QED

Theorem lower_dload_scratch_credit:
  exec_alloca i s' (32w:bytes32) = OK t' /\
  FLOOKUP s'.vs_allocas i.inst_id = NONE /\
  s'.vs_alloca_next = s.vs_alloca_next + 32*k ==>
  t'.vs_alloca_next = s.vs_alloca_next + 32*(k+1)
Proof
  strip_tac >> drule lower_dload_alloca_frontier >>
  simp[] >> strip_tac >> decide_tac
QED

Theorem lower_dload_merge_credit:
  caller'.vs_alloca_next = caller.vs_alloca_next + 32*k /\
  R caller.vs_allocas caller'.vs_allocas ==>
  (merge_callee_state caller' callee').vs_alloca_next =
    (merge_callee_state caller callee).vs_alloca_next + 32*k /\
  R (merge_callee_state caller callee).vs_allocas
    (merge_callee_state caller' callee').vs_allocas
Proof
  simp[lower_dload_merge_allocation_memory]
QED

(* The simulation: every terminating run of C is matched by a run of C'
   up to the dead bytes D.  The DLOAD offset bound (in o1_src_inv) keeps
   the code_end-relative CODECOPY offset from wrapping; code_layout_valid
   (in o1_run_state_ok) binds "code_end" to the code/data boundary; the
   headroom bound (in o1_src_inv) and the callee-first order keep the
   shifted alloca sites from wrapping; the pointer discipline and the
   taint bound (in o1_src_inv) keep the shifted alloca addresses out of
   what the run observes. *)
Theorem lower_dload_stage_sim:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    ctx_sim D C C' vs vs
Proof
  cheat
QED
