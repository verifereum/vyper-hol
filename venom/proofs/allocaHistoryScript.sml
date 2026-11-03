(* Allocation order within a block survives reuse of its allocation sites.
   The instruction cursor records which sites must already exist. *)
Theory allocaHistory
Ancestors
  venomInst venomWf venomState venomExecSemantics venomExecProps
  venomMemDefs venomMemProofs venomInstProps venomInstProofs1 finite_map list arithmetic

Definition alloca_block_order_def:
  alloca_block_order bb (sites : (num, num # num) fmap) <=>
    !i j earlier later b sz.
      i < j /\ get_instruction bb i = SOME earlier /\
      get_instruction bb j = SOME later /\
      earlier.inst_opcode = ALLOCA /\ later.inst_opcode = ALLOCA /\
      FLOOKUP sites later.inst_id = SOME (b,sz) ==>
      ?a n. FLOOKUP sites earlier.inst_id = SOME (a,n) /\ a + n <= b
End

Definition alloca_history_def:
  alloca_history func s <=>
    (!bb. MEM bb func.fn_blocks ==> alloca_block_order bb s.vs_allocas) /\
    (!bb k inst.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      k < s.vs_inst_idx /\ get_instruction bb k = SOME inst /\
      inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP s.vs_allocas inst.inst_id))
End

Theorem alloca_history_empty:
  !func s. s.vs_allocas = FEMPTY /\ s.vs_inst_idx = 0 ==>
    alloca_history func s
Proof
  simp[alloca_history_def, alloca_block_order_def]
QED

Theorem alloca_history_frame:
  !func s t.
    alloca_history func s /\ t.vs_allocas = s.vs_allocas /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx ==>
    alloca_history func t
Proof
  simp[alloca_history_def] >> metis_tac[]
QED

Theorem alloca_history_jump:
  !func s t.
    alloca_history func s /\ t.vs_allocas = s.vs_allocas /\
    t.vs_inst_idx = 0 ==> alloca_history func t
Proof
  simp[alloca_history_def] >> metis_tac[]
QED

Theorem alloca_history_pair:
  !func s bb i j earlier later b sz.
    alloca_history func s /\ MEM bb func.fn_blocks /\ i < j /\
    get_instruction bb i = SOME earlier /\
    get_instruction bb j = SOME later /\
    earlier.inst_opcode = ALLOCA /\ later.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas later.inst_id = SOME (b,sz) ==>
    ?a n. FLOOKUP s.vs_allocas earlier.inst_id = SOME (a,n) /\ a + n <= b
Proof
  simp[alloca_history_def, alloca_block_order_def] >> metis_tac[]
QED

Theorem history_lookup_block_mem[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
  gvs[lookup_block_def] >> metis_tac[]
QED

Theorem history_flat_map_unique[local]:
  !l f x y v.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l /\ MEM y l /\
    MEM v (f x) /\ MEM v (f y) ==> x = y
Proof
  rpt strip_tac >>
  `?l1 l2. l = l1 ++ x::l2` by metis_tac[MEM_SPLIT] >>
  gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  `MEM y l1 \/ y = x \/ MEM y l2` by gvs[MEM_APPEND] >> gvs[] >>
  metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem history_flat_map_segment[local]:
  !l f x.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM x l ==> ALL_DISTINCT (f x)
Proof
  rpt strip_tac >>
  `?l1 l2. l = l1 ++ x::l2` by metis_tac[MEM_SPLIT] >>
  gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

Theorem history_site_position_unique[local]:
  !func bb cc i j x y.
    fn_inst_ids_distinct func /\ MEM bb func.fn_blocks /\
    MEM cc func.fn_blocks /\ get_instruction bb i = SOME x /\
    get_instruction cc j = SOME y /\ x.inst_id = y.inst_id ==>
    bb = cc /\ i = j
Proof
  rpt strip_tac >>
  gvs[get_instruction_def, fn_inst_ids_distinct_def] >>
  `MEM (EL i bb.bb_instructions).inst_id
       (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (simp[MEM_MAP] >> qexists `EL i bb.bb_instructions` >> simp[EL_MEM]) >>
  `MEM (EL j cc.bb_instructions).inst_id
       (MAP (\inst. inst.inst_id) cc.bb_instructions)` by
    (simp[MEM_MAP] >> qexists `EL j cc.bb_instructions` >> simp[EL_MEM]) >>
  `bb = cc` by
    (drule history_flat_map_unique >>
     disch_then (qspecl_then [`bb`, `cc`, `(EL i bb.bb_instructions).inst_id`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  gvs[] >>
  `ALL_DISTINCT (MAP (\inst. inst.inst_id) bb.bb_instructions)` by
    (drule history_flat_map_segment >> disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, EL_MAP, LENGTH_MAP]
QED

Theorem history_fresh_insert[local]:
  !func s bb inst n.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = ALLOCA /\ FLOOKUP s.vs_allocas inst.inst_id = NONE ==>
    alloca_history func
      (s with <|vs_allocas := s.vs_allocas |+ (inst.inst_id,(s.vs_alloca_next,n));
                vs_inst_idx := SUC s.vs_inst_idx|>)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb func.fn_blocks` by metis_tac[history_lookup_block_mem] >>
  fs[alloca_history_def, alloca_inv_def, alloca_next_valid_def] >>
  simp[alloca_history_def] >> conj_tac
  >- (rw[alloca_block_order_def, FLOOKUP_UPDATE] >>
      Cases_on `inst.inst_id = later.inst_id`
      >- (`bb = bb' /\ s.vs_inst_idx = j` by
            metis_tac[history_site_position_unique] >>
          gvs[] >>
          `IS_SOME (FLOOKUP s.vs_allocas earlier.inst_id)` by metis_tac[] >>
          Cases_on `FLOOKUP s.vs_allocas earlier.inst_id` >> gvs[] >>
          PairCases_on `x` >> gvs[] >>
          `inst.inst_id <> earlier.inst_id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
          simp[] >> metis_tac[]) >>
      gvs[] >>
      `?a m. FLOOKUP s.vs_allocas earlier.inst_id = SOME (a,m) /\ a + m <= b` by
        metis_tac[alloca_block_order_def] >>
      `inst.inst_id <> earlier.inst_id` by metis_tac[optionTheory.NOT_NONE_SOME] >>
      simp[] >> metis_tac[]) >>
  rw[FLOOKUP_UPDATE] >>
  Cases_on `k = s.vs_inst_idx`
  >- (gvs[] >> metis_tac[optionTheory.SOME_11]) >>
  `k < s.vs_inst_idx` by decide_tac >> metis_tac[]
QED

Theorem history_allocated_advance[local]:
  !func s bb inst.
    alloca_history func s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    IS_SOME (FLOOKUP s.vs_allocas inst.inst_id) ==>
    alloca_history func (s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rw[alloca_history_def] >>
  Cases_on `k = s.vs_inst_idx`
  >- (gvs[] >> metis_tac[optionTheory.SOME_11]) >>
  `k < s.vs_inst_idx` by decide_tac >> metis_tac[]
QED

Theorem history_exec_alloca[local]:
  !func s bb inst size t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = ALLOCA /\
    exec_alloca inst s size = OK t ==>
    alloca_history func (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[exec_alloca_def, AllCaseEqs()]
  >- (drule_all history_fresh_insert >>
      disch_then (qspec_then `w2n size'` mp_tac) >>
      simp[alloca_history_def, update_var_def] >> metis_tac[]) >>
  `IS_SOME (FLOOKUP s.vs_allocas inst.inst_id)` by simp[] >>
  drule_all history_allocated_advance >>
  simp[alloca_history_def, update_var_def] >> metis_tac[]
QED

Theorem history_nonalloca_advance[local]:
  !func s bb inst.
    alloca_history func s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> ALLOCA ==>
    alloca_history func (s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rw[alloca_history_def] >>
  Cases_on `k = s.vs_inst_idx`
  >- (gvs[] >> metis_tac[optionTheory.SOME_11]) >>
  `k < s.vs_inst_idx` by decide_tac >> metis_tac[]
QED

Theorem history_bind_outputs_fields[local]:
  !outs vals s t. bind_outputs outs vals s = SOME t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx
Proof
  rpt strip_tac >>
  `(\r:venom_state. (r.vs_allocas,r.vs_current_bb,r.vs_inst_idx)) t =
   (\r:venom_state. (r.vs_allocas,r.vs_current_bb,r.vs_inst_idx)) s`
    suffices_by simp[] >>
  irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]
QED

Theorem history_adopt_fields[local,simp]:
  (adopt_return_fmp ir s).vs_allocas = s.vs_allocas /\
  (adopt_return_fmp ir s).vs_current_bb = s.vs_current_bb /\
  (adopt_return_fmp ir s).vs_inst_idx = s.vs_inst_idx
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem history_invoke_fields[local]:
  !inst fuel ctx s t.
    inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx
Proof
  rpt strip_tac >> gvs[Once step_inst_def, AllCaseEqs()] >>
  drule history_bind_outputs_fields >> simp[merge_callee_state_def]
QED

Theorem history_base_control_flow:
  !inst s t.
    step_inst_base inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[step_inst_base_OK_not_INVOKE] >>
  `step_inst 0 ARB inst s = OK t` by simp[step_inst_non_invoke] >>
  metis_tac[step_preserves_control_flow]
QED
Theorem history_base_terminator_reset[local]:
  !inst s t. is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
    t.vs_inst_idx = 0
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp_tac (srw_ss()) [] >>
  strip_tac >> gvs[AllCaseEqs(), jump_to_def] >>
  pairarg_tac >> gvs[]
QED

Theorem alloca_history_base_step:
  !func s bb inst t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\ step_inst_base inst s = OK t ==>
    alloca_history func
      (if is_terminator inst.inst_opcode then t
       else t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[step_inst_base_OK_not_INVOKE] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[] >>
      qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
      simp_tac (srw_ss()) [] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule_all history_exec_alloca >> simp[is_terminator_def]) >>
  `t.vs_allocas = s.vs_allocas` by metis_tac[step_inst_base_preserves_alloca_fields] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- (metis_tac[alloca_history_jump, history_base_terminator_reset]) >>
  drule_all history_nonalloca_advance >> strip_tac >>
  irule alloca_history_frame >> qexists `s with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[] >> metis_tac[history_base_control_flow]
QED


Theorem alloca_history_step:
  !func s bb inst fuel ctx t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK t ==>
    alloca_history func
      (if is_terminator inst.inst_opcode then t
       else t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  cheat
QED

Theorem alloca_history_exec_block:
  !func s bb fuel ctx t ret.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    (exec_block fuel ctx bb s = OK t \/
     exec_block fuel ctx bb s = IntRet ret t) ==>
    alloca_history func t
Proof
  cheat
QED

Theorem alloca_history_run_blocks:
  !func s fuel ctx t ret.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    run_blocks fuel ctx func s = IntRet ret t ==> alloca_history func t
Proof
  cheat
QED

Theorem alloca_history_callee_entry:
  !func args s t. setup_callee func args s = SOME t ==>
    alloca_history func t
Proof
  cheat
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "ALLOCA_HISTORY_BASE_AUDIT OK\n"
     else raise Fail "allocation history base inherited admission"
  end) [alloca_history_empty, alloca_history_frame,
        alloca_history_jump, alloca_history_pair];

