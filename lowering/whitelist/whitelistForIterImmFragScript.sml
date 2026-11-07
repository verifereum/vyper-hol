(* Static readiness and fragment composition for immutable array iteration. *)
Theory whitelistForIterImmFrag
Ancestors
  whitelistForIterImmLoop whitelistForIterDynFrag stmtSimForArrayFrag
  loweringPosts stmtLowering stmtSimProps context emitHelper compileEnv exprLoweringProps
  localPtrsProps emitHelperProps fragExec venomInst list finite_map arithmetic
  allocationPtr stmtSimForArrayLoop words
Libs
  monadsyntax

Theorem immutable_optional_load_ready:
  (if dyn then
     compile_imm_load_word cenv.ce_is_ctor cenv.ce_imm_alloca (Lit (n2w off))
   else return (Lit (n2w cap))) st = (lvo,st1) /\
  local_ptrs_reserved cenv st ==>
  st.cs_next_var <= st1.cs_next_var /\
  local_ptrs_reserved cenv st1 /\
  (!x. not_fresh_at st x ==> not_fresh_at st1 x) /\
  (!x. lvo = Var x ==> not_fresh_at st1 x) /\
  (!l. lvo <> Label l)
Proof
  strip_tac >>
  `st.cs_next_var <= st1.cs_next_var /\
   (!x. lvo = Var x ==> not_fresh_at st1 x) /\ (!l. lvo <> Label l)` by
    (qpat_x_assum `_ st = (lvo,st1)` mp_tac >>
     Cases_on `dyn` >> simp[comp_return_def] >>
     simp[compile_imm_load_word_def] >>
     Cases_on `cenv.ce_is_ctor` >> simp[] >>
     Cases_on `cenv.ce_imm_alloca` >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  simp[] >> conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  simp[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]
QED


(* The unused Fixed header dummy is intentionally absent from the distinct
   live-register list: it may coincide with a later copy temporary. *)
Theorem immutable_register_frame:
  local_ptrs_reserved cenv st1 /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_var <= sj.cs_next_var /\
  p = STRING #"%" (toString st1.cs_next_var) /\
  idx = STRING #"%" (toString (st1.cs_next_var + 1)) /\
  dv = STRING #"%" (toString (st1.cs_next_var + (if dyn then 4 else 2))) /\
  ov = STRING #"%" (toString (st1.cs_next_var + (if dyn then 5 else 3))) /\
  ep = STRING #"%" (toString (st1.cs_next_var + (if dyn then 7 else 4))) /\
  tot = STRING #"%" (toString (st1.cs_next_var + 6)) /\
  nv = STRING #"%" (toString sj.cs_next_var) ==>
  ALL_DISTINCT [p; idx; dv; ov; ep; nv] /\
  p <> tot /\ idx <> tot /\ ov <> tot /\
  (!scs. not_local_ptr cenv scs p /\ not_local_ptr cenv scs idx /\
         not_local_ptr cenv scs dv /\ not_local_ptr cenv scs ov /\
         not_local_ptr cenv scs tot /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv) /\
  (!x. not_fresh_at st1 x ==>
    not_fresh_at sa x /\ ~MEM x [p; idx; dv; ov; tot; ep; nv]) /\
  not_fresh_at sa p /\ not_fresh_at sa idx /\ not_fresh_at sa ep
Proof
  strip_tac >>
  `!scs. not_local_ptr cenv scs p /\ not_local_ptr cenv scs idx /\
         not_local_ptr cenv scs dv /\ not_local_ptr cenv scs ov /\
         not_local_ptr cenv scs tot /\ not_local_ptr cenv scs ep /\
         not_local_ptr cenv scs nv` by
    (gen_tac >> rpt conj_tac >> simp[] >>
     irule local_ptrs_reserved_fresh >> qexists_tac `st1` >>
     Cases_on `dyn` >> gvs[]) >>
  Cases_on `dyn` >> gvs[not_fresh_at_def]
QED

Theorem immutable_allocation_ready:
  declare_local cenv id et st1 =
    (bc, st1 with cs_next_var := st1.cs_next_var + 1) /\
  cenv.ce_alloca_locals /\ local_ptrs_reserved cenv st1 /\
  sa.cs_next_var = st1.cs_next_var + (if dyn then 8 else 5) /\
  sa.cs_next_var <= sb0.cs_next_var ==>
  local_ptrs_reserved bc sa /\ local_ptrs_reserved bc sb0 /\
  bc.ce_return_pc = cenv.ce_return_pc /\
  bc.ce_imm_alloca = cenv.ce_imm_alloca /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar
    (Var (STRING #"%" (toString st1.cs_next_var)))
    (type_memory_bytes cenv et)) /\
  (!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP cenv.ce_vars name)
Proof
  strip_tac >>
  `st1.cs_next_var + 1 <= sa.cs_next_var` by
    (Cases_on `dyn` >> gvs[]) >>
  drule_all array_declared_reserved >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = cenv` mp_tac >>
  disch_then (fn th =>
    mp_tac (AP_TERM ``\c. c.ce_return_pc`` th) >>
    mp_tac (AP_TERM ``\c. c.ce_imm_alloca`` th)) >> simp[]
QED

(* Transport the two kinds of reserved callers through the generated prefix.
   ret_pc_ok supplies the old return-PC register; local_ptrs_reserved is not
   incorrectly used to reserve that register. *)
Theorem immutable_return_pc_ready:
  bc.ce_return_pc = cenv.ce_return_pc /\ ret_pc_ok cenv st s /\
  st.cs_next_var <= st1.cs_next_var /\
  sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at st1 x ==>
    not_fresh_at sa x /\ ~MEM x [p; idx; dv; ov; tot; ep; nv]) ==>
  (!x z. bc.ce_return_pc = SOME (PtrVar (Var x) z) \/
         cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep) /\
  (!t. ret_pc_ok cenv st t ==> ret_pc_ok bc sb0 t) /\
  (!x. not_fresh_at st x ==>
    not_fresh_at sa x /\ x <> ov /\ x <> tot /\ x <> ep)
Proof
  strip_tac >>
  `!x. not_fresh_at st x ==> not_fresh_at st1 x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  fs[ret_pc_ok_def, MEM] >> metis_tac[]
QED

(* The counted invariant retains the allocation site, not an explicit address
   bound.  Its state relation recovers that bound at every body entry. *)
Theorem immutable_entry_allocation_bound:
  array_loop_inv ctx func cenv cx P vs id idx (Lit (n2w off)) (n2w off)
    p dst sz ainst bod st k es s /\
  ainst = mk_inst aid ALLOCA [Lit (n2w sz)] [p] /\
  MEM ainst (fn_insts func) /\ sz < dimword (:256) ==>
  w2n dst + sz < dimword (:256)
Proof
  strip_tac >> gvs[array_loop_inv_def, mk_inst_def] >>
  drule_all (SRULE [mk_inst_def] stmt_state_rel_alloca_site_bound) >> simp[]
QED
