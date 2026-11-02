(* Allocation order within a block survives reuse of its allocation sites.
   The instruction cursor records which sites must already exist. *)
Theory allocaHistory
Ancestors
  venomInst venomWf venomState venomExecSemantics venomExecProps
  venomMemDefs venomMemProofs finite_map list arithmetic

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

