(* Zero-sized typed copies via a proof-only value witness. *)
Theory externalReturnZeroCopy
Ancestors externalReturnZeroWitness typedMemoryCopy valueEncodingProofs
  compileEnv context valueEncoding vyperTypeSystem
  words finite_map

Theorem return_zero_copy_memory_frame[local]:
  (!a len. a + len <= p \/ p <= a ==>
    mem_bytes_at a len m' = mem_bytes_at a len m) ==>
  !a len. mem_bytes_at a len m' = mem_bytes_at a len m
Proof
  rpt strip_tac >>
  Cases_on `a + len <= p \/ p <= a` >- metis_tac[] >>
  `len = (p - a) + (a + len - p)` by decide_tac >>
  `a + (p - a) = p` by decide_tac >>
  once_asm_rewrite_tac[] >>
  rewrite_tac[mem_bytes_at_split_padded] >>
  BINOP_TAC >> first_x_assum irule >> decide_tac
QED

Theorem return_zero_typed_copy_run:
  !cenv tenv dst dty src sty dtv stv sa sb ctx func s dw sw.
    compile_store_memory_typed cenv dst dty src sty sa = ((), sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields.
       FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv.
         evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv dty = SOME dtv /\
    type_memory_size stv = 0 /\ type_memory_size dtv = 0 /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
    fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all return_zero_widening_witness >> strip_tac >>
  drule compile_store_memory_typed_run >>
  disch_then (qspecl_then [`tenv`,`dtv`,`stv`,`z`,`ctx`,`func`,`s`,`dw`,`sw`] mp_tac) >>
  simp[w2n_lt] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule return_zero_copy_memory_frame >> metis_tac[]
QED
