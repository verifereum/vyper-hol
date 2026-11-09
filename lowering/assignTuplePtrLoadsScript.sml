(* Counted pointer-safe loads of a suffix at an arbitrary offset. *)
Theory assignTuplePtrLoads
Ancestors
  assignTuplePtrMemberLoad assignTuplePtrBoundary stmtSimReturn stmtLowering
  context compileEnv exprLoweringProps exprSimProps fragExec fragGasPathPtr
  valueEncoding valueTypingMemoryProps bodyPtrDefs venomState list words arithmetic

Theorem compile_tuple_load_all_offset_path_ptr:
  !tys cenv p off sa elems sb cx tvs vals s w G tn b cap ctx func d es PG D.
  compile_tuple_load_all cenv (Var p) tys off sa = (elems,sb) /\
  not_fresh_at sa p /\ lookup_var p s = SOME w /\ op_taint tn (Var p) = {} /\
  FLOOKUP G p = SOME (b,cap) /\ b <= w2n w /\
  w2n w + off + type_memory_size_list tvs <= b+cap /\
  w2n w + off + type_memory_size_list tvs < dimword (:256) /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vals /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       tuple_in_memory vals tvs (w2n w+off) m) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sb x) elems /\
  local_ptrs_reserved cenv sb /\
  ?t G' tn'. gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q)) /\
    (!i. i < LENGTH tys ==>
      ptr_val_ok cx (EL i tys) (EL i vals) (EL i elems) G' tn' t /\
      (?u. eval_operand (EL i elems) t = SOME u /\
        (if is_word_type (EL i tys) then u = typed_val_to_w256 (EL i tvs) (EL i vals)
         else w2n u = w2n w+off+SUM (MAP type_memory_size (TAKE i tvs)))) /\
      (~is_word_type (EL i tys) ==>
        ?q. EL i elems = Var q /\ FLOOKUP G' q = SOME (b,cap)))
Proof
  Induct
  >- (rpt gen_tac >> simp[compile_tuple_load_all_def, comp_return_def] >>
      strip_tac >> gvs[] >> qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_path_ptr_rules]) >>
  pop_assum (mk_asm "ih") >> rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >- fs[] >> Cases_on `vals` >- fs[vyperTypingTheory.value_has_type_def] >>
  fs[vyperTypingTheory.value_has_type_def] >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_tuple_load_all_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  simp[comp_return_def] >> strip_tac >>
  qpat_x_assum `_ = elems` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = sb` SUBST_ALL_TAC >>
  rename1 `emit_op ADD _ sa = (pv,sm)` >>
  rename1 `compile_load_memory pv _ sm = (hop,sh)` >>
  rename1 `evaluate_type _ h = SOME tv` >>
  rename1 `values_have_types tvs vals` >>
  rename1 `value_has_type tv v` >>
  suspend "step"
QED

Resume compile_tuple_load_all_offset_path_ptr[step]:
  `cs_extends sa sm` by
    (qspec_then `ADD` (qspec_then `[Var p; Lit (n2w off)]` (qspec_then `sa` mp_tac))
      ci_mono_emit_op >> asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sm sh` by
    (Cases_on `is_word_type h`
     >- (qspec_then `MLOAD` (qspec_then `[pv]` (qspec_then `sm` mp_tac))
           ci_mono_emit_op >> fs[compile_load_memory_def, ci_mono_def]) >>
     fs[compile_load_memory_def, comp_return_def] >> simp[cs_extends_def]) >>
  `cs_extends sa sh` by metis_tac[cs_extends_trans] >>
  `cs_extends sh sb` by metis_tac[compile_tuple_load_all_grows] >>
  `fn_has_code sa sh func /\ fn_has_code sh sb func` by
    metis_tac[fn_has_code_split] >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (w + n2w off) = w2n w + off` by
    (`w2n w + off < dimword (:256)` by decide_tac >>
     `w + n2w off = n2w (w2n w + off)` by
       metis_tac[word_add_n2w, n2w_w2n] >> simp[]) >>
  `b <= w2n w + off` by decide_tac >>
  `w2n w+off+type_memory_size tv <= b+cap` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `w2n w+off+type_memory_size tv < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory tv v (w2n w+off) m` by
    (rpt strip_tac >> first_x_assum drule >> simp[val_in_memory_def]) >>
  drule_all compile_tuple_member_load_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "tail"
QED

Resume compile_tuple_load_all_offset_path_ptr[tail]:
  qpat_x_assum `state_frame _ = _` kall_tac >>
  `sa.cs_next_var <= sh.cs_next_var` by
    (qpat_assum `emit_op ADD _ _ = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op_local) >> strip_tac >>
     Cases_on `is_word_type h`
     >- (fs[compile_load_memory_def] >>
         qpat_assum `emit_op MLOAD _ _ = _`
           (mp_tac o MATCH_MP emitted_insts_emit_op_local) >>
         strip_tac >> decide_tac) >>
     gvs[compile_load_memory_def, comp_return_def]) >>
  `!q. not_fresh_at sa q ==> not_fresh_at sh q` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  `not_fresh_at sh p /\ lookup_var p t = SOME w /\
    op_taint tn' (Var p) = {} /\ FLOOKUP G' p = SOME (b,cap)` by
    (qpat_assum `!p. not_fresh_at sa p ==> lookup_var p t = _ /\ _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `local_ptrs_reserved cenv sh` by
    (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x`
    by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x`
    by metis_tac[] >>
  `w2n w + (off + type_memory_size tv) + type_memory_size_list tvs <= b+cap`
    by (fs[type_memory_size_def] >> decide_tac) >>
  `w2n w + (off + type_memory_size tv) + type_memory_size_list tvs < dimword (:256)`
    by (fs[type_memory_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
       tuple_in_memory vals tvs (w2n w + (off + type_memory_size tv)) m` by
    (rpt strip_tac >>
     `mem_agree_outside tn.t_mem s.vs_memory m` by metis_tac[] >>
     qpat_x_assum `!m. _ ==> tuple_in_memory (v::vals) _ _ m` drule >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac[val_in_memory_def] >>
     pure_rewrite_tac[list_case_def, LET_THM, pairTheory.pair_case_thm] >>
     `off + w2n w + type_memory_size tv = w2n w + (off + type_memory_size tv)`
       by decide_tac >> simp[]) >>
  asm_x "ih" drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume compile_tuple_load_all_offset_path_ptr[assemble]:
  qpat_x_assum `!m. _ ==> tuple_in_memory (v::vals) _ _ m` kall_tac >>
  qpat_x_assum `!m. _ ==> val_in_memory _ _ _ m` kall_tac >>
  qpat_x_assum `!m. _ ==> tuple_in_memory vals _ _ m` kall_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` kall_tac >>
  qpat_x_assum `compile_load_memory _ _ _ = _` kall_tac >>
  `sh.cs_next_var <= sb.cs_next_var` by metis_tac[compile_tuple_load_all_grows] >>
  `not_fresh_at sb out` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  qpat_x_assum `compile_tuple_load_all _ _ _ _ _ = _` kall_tac >>
  simp [EVERY_DEF] >>
  qexistsl_tac [`t'`, `G''`, `tn''`] >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  simp[] >>
  suspend "indexed"
QED

Resume compile_tuple_load_all_offset_path_ptr[indexed]:
  gen_tac >> Cases_on `i`
  >- (simp[] >>
      `lookup_var out t' = lookup_var out t /\ FLOOKUP G'' out = FLOOKUP G' out /\
       op_taint tn'' (Var out) = op_taint tn' (Var out)` by metis_tac[] >>
      `ptr_val_ok cx h v (Var out) G'' tn'' t'` by
        (qpat_x_assum `ptr_val_ok cx h v hop G' tn' t` mp_tac >>
         simp[ptr_val_ok_def, ptr_mem_ok_def, eval_operand_def, ptrDisciplineTheory.op_prov_def]) >>
      simp[] >> Cases_on `is_word_type h` >>
      gvs[eval_operand_def] >> simp[]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i. i < LENGTH tys ==> _` drule >>
  POP_ASSUM_LIST (K all_tac) >>
  `w2n w + (off + type_memory_size tv) + SUM (MAP type_memory_size (TAKE n tvs)) =
   off + (SUM (MAP type_memory_size (TAKE n tvs)) + (type_memory_size tv + w2n w))`
    by decide_tac >>
  metis_tac[]
QED

Finalise compile_tuple_load_all_offset_path_ptr

(* Public zero-offset interface: retain the source site witness so that
   downstream stores can track each non-word member's inherited site. *)
Theorem compile_tuple_load_all_typed_path_ptr:
  !cenv bop tys sa elems sb cx tvs vals s w G tn ctx func d es PG D.
  compile_tuple_load_all cenv bop tys 0 sa = (elems,sb) /\
  (!p. bop = Var p ==> not_fresh_at sa p) /\
  eval_operand bop s = SOME w /\
  (?p b cap. bop = Var p /\ op_taint tn bop = {} /\
    FLOOKUP G p = SOME (b,cap) /\ b <= w2n w /\
    w2n w + type_memory_size_list tvs <= b+cap) /\
  w2n w + type_memory_size_list tvs < dimword (:256) /\
  LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys tvs /\
  values_have_types tvs vals /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       tuple_in_memory vals tvs (w2n w) m) /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  LENGTH elems = LENGTH tys /\ EVERY (\op. ?x. op = Var x) elems /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sb x) elems /\
  local_ptrs_reserved cenv sb /\
  ?p b cap t G' tn'. bop = Var p /\ FLOOKUP G p = SOME (b,cap) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es G' tn' t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP G' q = FLOOKUP G q /\
      op_taint tn' (Var q) = op_taint tn (Var q)) /\
    tuple_in_memory vals tvs (w2n w) t.vs_memory /\
    (!n base sz. local_region cenv es.scopes t n base sz <=>
                 local_region cenv es.scopes s n base sz) /\
    (!i. i < LENGTH tys ==>
      ptr_val_ok cx (EL i tys) (EL i vals) (EL i elems) G' tn' t /\
      (?u. eval_operand (EL i elems) t = SOME u /\
        (if is_word_type (EL i tys) then u = typed_val_to_w256 (EL i tvs) (EL i vals)
         else w2n u = w2n w+SUM (MAP type_memory_size (TAKE i tvs)))) /\
      (~is_word_type (EL i tys) ==>
        ?q. EL i elems = Var q /\ FLOOKUP G' q = SOME (b,cap)))
Proof
  rpt gen_tac >> strip_tac >> gvs[eval_operand_def] >>
  drule compile_tuple_load_all_offset_path_ptr >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 Gout tnout (OK tout)` >>
  simp[] >> qexistsl_tac [`tout`, `Gout`, `tnout`] >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `!m. mem_agree_outside _ _ m ==> _` irule >>
      simp[mem_agree_outside_def]) >>
  rpt gen_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >>
      conj_tac
      >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`sa`, `es.scopes`, `tout`] >> simp[]) >>
  strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `sa`, `es.scopes`] >> simp[]
QED
