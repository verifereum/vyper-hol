Theory exprSimBopRestWordStorageLoads
Ancestors
  exprSimBopRestWordStorage exprSimBopRestWordLoadPath context
  fragExec venomState vyperValue valueEncoding
  list finite_map arithmetic

Theorem rest_word_storage_array_load_path:
  storage_holds cx tr (ArrayT ty bd) r w es s /\
  read_result cx r es = (INL (ArrayV av), es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  compile_ptr_load ctor imm (if tr then LocTransient else LocStorage) addr sa = (op,sb) /\
  eval_operand addr s = SOME (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME (typed_val_to_w256 tv v) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_storage_array_load >> strip_tac >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    (Cases_on `tr` >> gvs[] >>
     drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`,
       `w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)`] mp_tac) >>
     simp[]) >>
  `(if tr then LocTransient else LocStorage) <> LocCalldata` by
    (Cases_on `tr` >> simp[]) >>
  drule_all rest_word_ptr_load_path >> simp[]
QED

Theorem rest_word_storage_array_length_path:
  storage_holds cx tr (ArrayT ty (Dynamic cap)) r w es s /\
  read_result cx r es = (INL (ArrayV av), es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  compile_ptr_load ctor imm (if tr then LocTransient else LocStorage) addr sa = (op,sb) /\
  eval_operand addr s = SOME w /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  array_length (ArrayTV tv (Dynamic cap)) av <= cap /\
  ?u. gas_path ctx func s 0 (OK u) /\
      eval_operand op u = SOME (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u = s with <|vs_vars := u.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. (!inst. MEM inst (emitted_insts sa sb) ==> ~MEM x inst.inst_outputs) ==>
           FLOOKUP u.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all rest_word_storage_array_length >> strip_tac >>
  simp[] >>
  `?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (n2w (array_length (ArrayTV tv (Dynamic cap)) av))` by
    (Cases_on `tr` >> gvs[] >>
     drule (Q.INST [`b` |-> `0w`] rest_word_ptr_load_run) >> simp[] >>
     disch_then (qspecl_then [`s`, `w`] mp_tac) >> simp[]) >>
  `(if tr then LocTransient else LocStorage) <> LocCalldata` by
    (Cases_on `tr` >> simp[]) >>
  drule_all rest_word_ptr_load_path >> simp[]
QED

Theorem rest_word_storage_fixed_array_length:
  decode_value st off (ArrayTV tv (Fixed cap)) = SOME (ArrayV av) ==>
  array_length (ArrayTV tv (Fixed cap)) av = cap
Proof
  simp[Once vyperStorageTheory.decode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[vyperValueOperationTheory.array_length_def]
QED
