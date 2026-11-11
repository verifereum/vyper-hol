(* Same-state memory views preserve provenance and widen compiler windows. *)
Theory bodyIntCallMemoryView
Ancestors
  bodyIntCallProducerInterface context arithmetic

Theorem intcall_vv_provenance_memory_view:
  intcall_vv_provenance ce cx ty sa sb es raw vv s /\
  ((?a. vv = StackValue a op /\ ~is_word_type ty) \/
   (?a p. vv = LocatedValue a p /\ p.ptr_location = LocMemory /\
          op = p.ptr_operand)) /\
  eval_operand op' s = eval_operand op s /\
  (!v. read_result cx raw' es = (INL v,es) ==>
       read_result cx raw es = (INL v,es)) /\
  origin.cs_next_id <= sa.cs_next_id /\
  sb.cs_next_id <= final_st.cs_next_id ==>
  intcall_vv_provenance ce cx ty origin final_st es raw'
    (LocatedValue out_ty (mk_ptr op' LocMemory)) s
Proof
  strip_tac >>
  gvs[intcall_vv_provenance_def, mk_ptr_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists_tac `w` >> simp[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
    disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC)
  >>~- ([`local_val_at ce cx n (w2n w - b) tvt v`],
    ntac 2 disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]) >>
  ntac 3 disj2_tac >>
  rename1 `FLOOKUP ce.ce_vars n = SOME (PtrVar (Var pv) sz)` >>
  rename1 `lookup_var pv s = SOME bv` >>
  qexistsl_tac [`n`,`sz`,`entry`,`pv`,`bv`,`k`] >> simp[]
QED
