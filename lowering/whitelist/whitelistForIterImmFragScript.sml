(* Static readiness and fragment composition for immutable array iteration. *)
Theory whitelistForIterImmFrag
Ancestors
  whitelistForIterImmLoop whitelistForIterDynFrag stmtSimForArrayFrag
  stmtLowering stmtSimProps context emitHelper compileEnv exprLoweringProps
  localPtrsProps emitHelperProps fragExec venomInst list finite_map arithmetic
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

(* Normalize only the optional header register; Fixed uses ov, not tot. *)
Theorem immutable_prefix_operand:
  (do bc <- declare_local cenv id et;
      emit_local_alloca bc id;
      entry <- fresh_label "iter_entry";
      cond <- fresh_label "iter_cond";
      bod <- fresh_label "iter_body";
      incr <- fresh_label "iter_incr";
      exit <- fresh_label "iter_exit";
      emit_inst JMP [Label entry] [];
      new_block entry;
      idx <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [idx];
      (if dyn then
         do invalid <- emit_op GT [lvo; Lit (n2w cap)];
            valid <- emit_op ISZERO [invalid];
            emit_void ASSERT [valid] od
       else return ());
      emit_inst JMP [Label cond] [];
      new_block cond;
      done <- emit_op EQ [Var idx; lvo];
      emit_inst JNZ [done; Label exit; Label bod] [];
      new_block bod;
      offv <- emit_op MUL [Var idx;
                 Lit (n2w (elem_size_in_location cenv LocCode et))];
      tot <- (if dyn then emit_op ADD [Lit 32w; offv] else return offv);
      ep <- emit_op ADD [Lit (n2w off); tot];
      return (bc,entry,cond,bod,incr,exit,idx,offv,tot,ep)
   od) st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa) /\
  cenv.ce_alloca_locals ==>
  toto = Var (STRING #"%" (toString
    (st1.cs_next_var + (if dyn then 6 else 3))))
Proof
  strip_tac >>
  Cases_on `declare_local cenv id et st1` >>
  rename1 `declare_local cenv id et st1 = (bc0,st2)` >>
  drule_all declare_local_ptr >> strip_tac >>
  qpat_x_assum `_ st1 = ((bc,entry,cond,bod,incr,exit,idx,offo,toto,epo),sa)` mp_tac >>
  Cases_on `dyn` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emit_local_alloca_def, fresh_label_def, emit_inst_def, emit_op_def,
       emit_void_def, fresh_id_def, emit_def, new_block_def, fresh_var_def,
       comp_get_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       LET_THM] >> strip_tac >> gvs[]
QED
