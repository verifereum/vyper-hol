(* Actual zero-layout values, independently of physical source ownership. *)
Theory externalReturnBufferlessNormalize
Ancestors externalReturnZeroCopy externalReturnZeroWitness runFromGasPath valueEncoding valueEncodingDefs vyperValue venomState fragExec

Theorem return_zero_kvs_memory[local]:
  (!v. val_wf tv v ==> !p mem. val_in_memory tv v p mem) ==>
  !kvs n. kvs_val_wf kvs tv n ==> !p mem. kvs_in_memory kvs p tv mem
Proof
  strip_tac >> Induct >> simp[val_wf_def, val_in_memory_def] >>
  Cases_on `h` >> simp[val_wf_def, val_in_memory_def] >> metis_tac[]
QED

Theorem return_zero_bound_kvs[local]:
  kvs_val_wf kvs tv 0 ==> kvs = []
Proof
  Cases_on `kvs` >> simp[val_wf_def] >> Cases_on `h` >> simp[val_wf_def]
QED

Theorem return_zero_wf_memory_mutual:
  (!tv. !v. type_memory_size tv = 0 /\ val_wf tv v ==>
    !p mem. val_in_memory tv v p mem) /\
  (!ts. !vs. type_memory_size_list ts = 0 /\ tuple_val_wf vs ts ==>
    !p mem. tuple_in_memory vs ts p mem) /\
  (!fs. !vs. type_memory_size_fields fs = 0 /\ fields_val_wf vs fs ==>
    !p mem. fields_in_memory vs fs p mem)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[type_memory_size_def] >>
  conj_tac
  >- (Cases >> simp[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> simp[val_wf_def]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> Cases >>
      simp[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[val_wf_def, val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      `type_memory_size (ArrayTV tv (Fixed n)) = 0` by
        (fs[type_memory_size_def]) >>
      Cases_on `v` >> gvs[val_wf_def, val_in_memory_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[val_wf_def, val_in_memory_def]
      >- (drule return_zero_bound_kvs >> simp[val_in_memory_def]) >>
      drule return_zero_kvs_memory >> disch_then drule >>
      metis_tac[return_zero_default]) >>
  conj_tac
  >- (gen_tac >> strip_tac >> Cases >>
      simp[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      simp[val_wf_def, val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (Cases >> simp[val_wf_def, val_in_memory_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases >>
      simp[val_wf_def, val_in_memory_def] >> metis_tac[]) >>
  conj_tac
  >- (Cases >> simp[val_wf_def, val_in_memory_def] >>
      Cases_on `h` >> simp[val_wf_def, val_in_memory_def]) >>
  rpt gen_tac >> strip_tac >> Cases >>
  simp[val_wf_def, val_in_memory_def] >>
  Cases_on `h` >> simp[val_wf_def, val_in_memory_def] >> metis_tac[]
QED

Theorem return_zero_wf_memory:
  type_memory_size tv = 0 /\ val_wf tv v ==>
  !p mem. val_in_memory tv v p mem
Proof
  metis_tac[return_zero_wf_memory_mutual]
QED

Theorem return_zero_typed_copy_value_run:
  !cenv tenv dst dty src sty dtv stv sa sb ctx func s dw sw v.
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
    val_wf dtv v /\
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
      eval_operand dst t = SOME dw /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
        ?fuel'. run_from fuel' ctx func s = r)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all return_zero_typed_copy_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  conj_tac
  >- (`t.vs_labels = s.vs_labels` by
        (qpat_x_assum `_ with <| vs_vars := _; vs_memory := _; vs_prev_bb := _;
             vs_current_bb := _; vs_inst_idx := _ |> = _` mp_tac >>
         simp[venom_state_component_equality]) >>
      Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  metis_tac[return_zero_wf_memory]
QED

(* Bufferless IntCall normalization: count the copy only together with an exit. *)
Theorem return_zero_buffer_copy_exit:
  !cenv tenv buf dty sty dtv stv sa sb ctx func s dw v R.
    compile_store_memory_typed cenv buf.buf_operand dty (Lit 0w) sty sa = ((), sb) /\
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
    val_wf dtv v /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sa x) /\
    eval_operand buf.buf_operand s = SOME dw /\
    fn_has_code sa sb func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!t. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
                vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
                vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!a len. mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
      LENGTH s.vs_memory <= LENGTH t.vs_memory /\
      eval_operand buf.buf_operand t = SOME dw /\
      val_in_memory dtv v (w2n dw) t.vs_memory ==>
      ?fuel r. run_from fuel ctx func t = r /\ exit_result r /\ R r) ==>
    ?n r. gas_path ctx func s n r /\ exit_result r /\ R r
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. Lit 0w = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all return_zero_typed_copy_value_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  first_x_assum drule_all >> strip_tac >>
  `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
  first_x_assum drule_all >> strip_tac >>
  drule_all run_from_gas_path >> metis_tac[]
QED
