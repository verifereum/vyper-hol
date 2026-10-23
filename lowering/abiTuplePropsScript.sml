Theory abiTupleProps
Ancestors
  exprLowering exprLoweringProps contextProps emitHelperProps
  valueEncoding valueEncodingProps compileEnv context venomExecSemantics words
Libs
  wordsLib

(* Word inputs carry a typed encoding, not the untyped BytesV heuristic. *)
Definition abi_tuple_word_def:
  abi_tuple_word tv v =
    ((?b. v = BoolV b) \/ (?n. v = IntV n) \/
     (?k. v = FlagV k) \/ (?n. v = DecimalV n) \/
     (?bs n. tv = BaseTV (BytesT (Fixed n)) /\ v = BytesV bs) \/
     (?bs. tv = BaseTV AddressT /\ v = BytesV bs))
End

Definition abi_tuple_input_def:
  abi_tuple_input cenv ty tv v op ss =
    (val_wf tv v /\ type_memory_bytes cenv ty = type_memory_size tv /\
     if is_word_type ty then
       type_memory_size tv = 32 /\ abi_tuple_word tv v /\
       eval_operand op ss = SOME (typed_val_to_w256 tv v)
     else
       ?p. eval_operand op ss = SOME p /\
           val_in_memory tv v (w2n p) ss.vs_memory)
End

Theorem abi_tuple_word_mstore:
  abi_tuple_word tv v ==>
  val_in_memory tv v dst (mstore dst (typed_val_to_w256 tv v) ss).vs_memory
Proof
  rw[abi_tuple_word_def] >>
  simp[val_in_memory_def, typed_val_to_w256_def,
       mstore_mem_word_at_same] >>
  Cases_on `tv` >> simp[typed_val_to_w256_def] >>
  rename1 `BaseTV bt` >> Cases_on `bt` >> simp[typed_val_to_w256_def]
QED

Theorem compile_copy_memory_extends:
  compile_copy_memory dst src sz st = ((),st') ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  same_blocks st st'
Proof
  Cases_on `sz`
  >- simp[compile_copy_memory_def, comp_return_def, emitted_insts_def, same_blocks_def] >>
  simp[compile_copy_memory_def] >> metis_tac[emit_void_extends]
QED

(* The write half of a slot; ADD is composed separately below. *)
Theorem abi_tuple_write_correct:
  (if is_word_type ty then emit_void MSTORE [dst; op]
   else compile_copy_memory dst op (type_memory_bytes cenv ty)) st = ((),st') /\
  eval_operand dst ss = SOME (n2w d) /\ d < dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  abi_tuple_input cenv ty tv v op ss /\ fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory tv v d ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= d \/ d+type_memory_bytes cenv ty <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  strip_tac >>
  Cases_on `is_word_type ty` >> gvs[abi_tuple_input_def]
  >- (drule_all emit_void_MSTORE_correct >> strip_tac >>
      drule emit_void_extends >> strip_tac >>
      qexists_tac `mstore d (typed_val_to_w256 tv v) ss` >>
      gvs[w2n_n2w, abi_tuple_word_mstore] >>
      metis_tac[mstore_mem_bytes_at_disjoint, arithmeticTheory.ADD_COMM]) >>
  Cases_on `type_memory_bytes cenv ty = 0`
  >- (gvs[contextTheory.compile_copy_memory_def, comp_return_def] >>
      qexists_tac `ss` >> simp[emitted_insts_def, run_inst_seq_def, same_blocks_def] >>
      irule val_in_memory_relocate >> simp[] >>
      qexistsl_tac [`ss.vs_memory`, `0`, `w2n p`] >>
      simp[mem_bytes_at_def]) >>
  `type_memory_size tv > 0` by simp[] >>
  drule_all compile_copy_memory_correct >> strip_tac >>
  drule compile_copy_memory_extends >> strip_tac >>
  qexists_tac `mcopy d (w2n p) (type_memory_size tv) ss` >>
  gvs[w2n_n2w, mcopy_establishes_val_in_memory] >>
  metis_tac[mcopy_mem_bytes_at_disjoint, arithmeticTheory.ADD_COMM]
QED

Definition compile_abi_tuple_slot_def:
  compile_abi_tuple_slot cenv buf off op ty =
    do dst <- emit_op ADD [buf; Lit (n2w off)];
       if is_word_type ty then emit_void MSTORE [dst; op]
       else compile_copy_memory dst op (type_memory_bytes cenv ty)
    od
End

Theorem abi_tuple_input_memory_cong:
  ss'.vs_memory = ss.vs_memory /\
  (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
  abi_tuple_input cenv ty tv v op ss ==>
  abi_tuple_input cenv ty tv v op ss'
Proof
  rw[abi_tuple_input_def] >> metis_tac[]
QED

Theorem abi_tuple_add_correct[local]:
  emit_op ADD [buf; Lit (n2w off)] st = (dst,st1) /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss ==>
  ?ss1. run_inst_seq (emitted_insts st st1) ss = OK ss1 /\
    eval_operand dst ss1 = SOME (n2w (baddr+off)) /\
    same_blocks st st1 /\ fresh_vars_wrt st1 ss1 /\
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 /\
    ss1.vs_memory = ss.vs_memory /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss1 = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit (n2w off)) ss = SOME (n2w off)` by simp[eval_operand_lit] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qexists_tac `ss'` >> simp[word_add_n2w] >>
  simp[listTheory.LIST_EQ] >> metis_tac[]
QED

Theorem compile_abi_tuple_slot_correct:
  compile_abi_tuple_slot cenv buf off op ty st = ((),st') /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr+off < dimword (:256) /\
  baddr+off+type_memory_bytes cenv ty <= dimword (:256) /\
  type_memory_bytes cenv ty < dimword (:256) /\
  abi_tuple_input cenv ty tv v op ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory tv v (baddr+off) ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= baddr+off \/ baddr+off+type_memory_bytes cenv ty <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_tuple_slot_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  drule_all abi_tuple_add_correct >> strip_tac >>
  `abi_tuple_input cenv ty tv v op ss1` by
    (irule abi_tuple_input_memory_cong >> metis_tac[]) >>
  drule_all abi_tuple_write_correct >> strip_tac >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss'` >> gvs[] >>
  metis_tac[same_blocks_def]
QED

(* Check all public boundaries, including their transitive proof dependencies. *)
val _ = List.app (fn name =>
  if null (List.filter (fn x => x <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag (DB.fetch "abiTupleProps" name)))))
  then () else raise Fail ("oracle in " ^ name))
  ["abi_tuple_word_mstore", "compile_copy_memory_extends",
   "abi_tuple_write_correct", "abi_tuple_input_memory_cong",
   "compile_abi_tuple_slot_correct"];

(* Aligned operands, compiler types, semantic types and values.  Source
   separation is from the entire destination, not just the current slot. *)
Definition abi_tuple_inputs_def:
  abi_tuple_inputs cenv [] tvs vs ss lo hi = (tvs = [] /\ vs = []) /\
  abi_tuple_inputs cenv ((op,ty)::xs) tvs vs ss lo hi =
    (?tv ts v ws. tvs = tv::ts /\ vs = v::ws /\
      abi_tuple_input cenv ty tv v op ss /\
      type_memory_bytes cenv ty < dimword (:256) /\
      (~is_word_type ty ==>
        !p. eval_operand op ss = SOME p ==>
          w2n p + type_memory_bytes cenv ty <= lo \/ hi <= w2n p) /\
      abi_tuple_inputs cenv xs ts ws ss lo hi)
End

Definition abi_tuple_bytes_def:
  abi_tuple_bytes cenv xs = SUM (MAP (type_memory_bytes cenv o SND) xs)
End

(* Explicitly rule out a wrapped ADD, including zero-sized trailing slots. *)
Definition abi_tuple_starts_def:
  abi_tuple_starts cenv d [] = T /\
  abi_tuple_starts cenv d ((op,ty)::xs) =
    (d < dimword (:256) /\
     abi_tuple_starts cenv (d + type_memory_bytes cenv ty) xs)
End

Theorem abi_tuple_inputs_frame[local]:
  !xs tvs vs ss ss' lo hi.
  abi_tuple_inputs cenv xs tvs vs ss lo hi /\
  (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
  (!p k. p+k <= lo \/ hi <= p ==>
    mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory) ==>
  abi_tuple_inputs cenv xs tvs vs ss' lo hi
Proof
  Induct >- simp[abi_tuple_inputs_def] >>
  gen_tac >> PairCases_on `h` >> simp[abi_tuple_inputs_def] >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  conj_tac
  >- (Cases_on `is_word_type h1`
      >- (gvs[abi_tuple_input_def] >> metis_tac[]) >>
      gvs[abi_tuple_input_def] >> qexists_tac `p` >> simp[] >>
      irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
      simp[] >> qexistsl_tac [`type_memory_size tv`, `ss.vs_memory`] >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!tvs vs ss ss' lo hi. _` kall_tac >>
      Cases_on `is_word_type h1` >> gvs[abi_tuple_input_def] >>
      `eval_operand h0 ss' = SOME p` by metis_tac[] >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem compile_store_abi_tuple_step[local]:
  compile_store_abi_tuple cenv buf off ((op,ty)::xs) st =
  (do compile_abi_tuple_slot cenv buf off op ty;
      compile_store_abi_tuple cenv buf (off+type_memory_bytes cenv ty) xs od) st
Proof
  simp[compile_store_abi_tuple_def, compile_abi_tuple_slot_def,
       comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] st` >> simp[]
QED

Theorem abi_tuple_inputs_narrow[local]:
  !xs tvs vs ss lo hi lo' hi'.
    abi_tuple_inputs cenv xs tvs vs ss lo hi /\ lo <= lo' /\ hi' <= hi ==>
    abi_tuple_inputs cenv xs tvs vs ss lo' hi'
Proof
  Induct >- simp[abi_tuple_inputs_def] >>
  gen_tac >> PairCases_on `h` >> simp[abi_tuple_inputs_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  conj_tac >- (rpt strip_tac >> gvs[] >>
    qpat_x_assum `!p. eval_operand h0 ss = SOME p ==> _` (qspec_then `p` mp_tac) >>
    simp[] >> decide_tac) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem abi_tuple_inputs_sizes:
  !xs tvs vs ss lo hi.
    abi_tuple_inputs cenv xs tvs vs ss lo hi ==>
    abi_tuple_bytes cenv xs = type_memory_size_list tvs
Proof
  Induct >- simp[abi_tuple_inputs_def, abi_tuple_bytes_def, type_memory_size_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_inputs_def, abi_tuple_bytes_def] >> rpt strip_tac >>
  gvs[type_memory_size_def, abi_tuple_input_def] >>
  first_x_assum drule >> simp[abi_tuple_bytes_def]
QED

Theorem compile_store_abi_tuple_correct:
  !xs cenv buf off st st' ss baddr tvs vs.
  compile_store_abi_tuple cenv buf off xs st = ((),st') /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr+off+abi_tuple_bytes cenv xs <= dimword (:256) /\
  abi_tuple_starts cenv (baddr+off) xs /\
  abi_tuple_inputs cenv xs tvs vs ss (baddr+off)
    (baddr+off+abi_tuple_bytes cenv xs) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    tuple_in_memory vs tvs (baddr+off) ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= baddr+off \/ baddr+off+abi_tuple_bytes cenv xs <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_inputs_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `ss` >>
      simp[emitted_insts_def, run_inst_seq_def, same_blocks_def, val_in_memory_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[compile_store_abi_tuple_step, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  gvs[abi_tuple_inputs_def, abi_tuple_starts_def] >>
  qpat_x_assum `!cenv buf off st st' ss baddr tvs vs. _` (mk_asm "ih") >>
  `baddr+off+type_memory_bytes cenv h1 <= dimword (:256)` by
    (gvs[abi_tuple_bytes_def] >> decide_tac) >>
  drule compile_abi_tuple_slot_correct >>
  disch_then (qspecl_then [`v`, `tv`, `ss`, `baddr`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  `abi_tuple_inputs cenv xs ts ws ss1 (baddr+off)
     (baddr+off+abi_tuple_bytes cenv ((h0,h1)::xs))` by
    (irule abi_tuple_inputs_frame >> qexists_tac `ss` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     gvs[abi_tuple_bytes_def] >> decide_tac) >>
  `abi_tuple_inputs cenv xs ts ws ss1 (baddr+(off+type_memory_bytes cenv h1))
     (baddr+(off+type_memory_bytes cenv h1)+abi_tuple_bytes cenv xs)` by
    (irule abi_tuple_inputs_narrow >>
     qexistsl_tac [`baddr+off+abi_tuple_bytes cenv ((h0,h1)::xs)`, `baddr+off`] >>
     simp[abi_tuple_bytes_def]) >>
  `eval_operand buf ss1 = SOME (n2w baddr)` by metis_tac[] >>
  asm_x "ih" drule >>
  disch_then (qspecl_then [`ss1`, `baddr`, `ts`, `ws`] mp_tac) >>
  (impl_tac >- gvs[abi_tuple_bytes_def]) >>
  disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  `val_wf tv v /\ type_memory_bytes cenv h1 = type_memory_size tv` by
    fs[abi_tuple_input_def] >>
  `val_in_memory tv v (baddr+off) ss2.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_mem_agree >> simp[] >>
     qexistsl_tac [`type_memory_size tv`, `ss1.vs_memory`] >> simp[]) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss2` >>
  simp[val_in_memory_def] >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  conj_tac >- gvs[same_blocks_def] >>
  rpt strip_tac >>
  `mem_bytes_at p k ss2.vs_memory = mem_bytes_at p k ss1.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k ss2.vs_memory = _` irule >>
     gvs[abi_tuple_bytes_def] >> decide_tac) >>
  `mem_bytes_at p k ss1.vs_memory = mem_bytes_at p k ss.vs_memory` by
    (qpat_x_assum `!p k. _ ==> mem_bytes_at p k ss1.vs_memory = _` irule >>
     gvs[abi_tuple_bytes_def] >> decide_tac) >> simp[]
QED

Theorem abi_tuple_inputs_lengths:
  !xs tvs vs ss lo hi.
    abi_tuple_inputs cenv xs tvs vs ss lo hi ==>
    LENGTH xs = LENGTH tvs /\ LENGTH tvs = LENGTH vs
Proof
  Induct >- simp[abi_tuple_inputs_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_inputs_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem compile_store_abi_tuple_value_correct:
  compile_store_abi_tuple cenv buf off xs st = ((),st') /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr+off+abi_tuple_bytes cenv xs <= dimword (:256) /\
  abi_tuple_starts cenv (baddr+off) xs /\
  abi_tuple_inputs cenv xs tvs vs ss (baddr+off)
    (baddr+off+abi_tuple_bytes cenv xs) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (baddr+off) ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= baddr+off \/ baddr+off+abi_tuple_bytes cenv xs <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  rewrite_tac[val_in_memory_tuple] >>
  MATCH_ACCEPT_TAC compile_store_abi_tuple_correct
QED

(* This is the fresh-buffer use site: all nonword sources are explicitly
   separated from [baddr,baddr+size), as recorded by abi_tuple_inputs. *)
Theorem compile_store_abi_tuple_zero_correct:
  compile_store_abi_tuple cenv buf 0 (ZIP (ops,tys)) st = ((),st') /\
  LENGTH ops = LENGTH tys /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr+abi_tuple_bytes cenv (ZIP (ops,tys)) <= dimword (:256) /\
  abi_tuple_starts cenv baddr (ZIP (ops,tys)) /\
  abi_tuple_inputs cenv (ZIP (ops,tys)) tvs vs ss baddr
    (baddr+abi_tuple_bytes cenv (ZIP (ops,tys))) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) baddr ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= baddr \/ baddr+abi_tuple_bytes cenv (ZIP (ops,tys)) <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  strip_tac >> fs[] >>
  drule compile_store_abi_tuple_value_correct >>
  disch_then (qspecl_then [`vs`, `tvs`, `ss`, `baddr`] mp_tac) >> simp[]
QED

Theorem compile_store_abi_tuple_nil:
  compile_store_abi_tuple cenv buf off [] st = ((),st) /\
  run_inst_seq (emitted_insts st st) ss = OK ss /\
  val_in_memory (TupleTV []) (ArrayV (TupleV [])) d ss.vs_memory
Proof
  simp[compile_store_abi_tuple_def, comp_return_def, emitted_insts_def,
       run_inst_seq_def, val_in_memory_def]
QED

Theorem abi_tuple_inputs_singleton:
  abi_tuple_inputs cenv [(op,ty)] [tv] [v] ss lo hi <=>
  abi_tuple_input cenv ty tv v op ss /\
  type_memory_bytes cenv ty < dimword (:256) /\
  (~is_word_type ty ==> !p. eval_operand op ss = SOME p ==>
    w2n p + type_memory_bytes cenv ty <= lo \/ hi <= w2n p)
Proof
  simp[abi_tuple_inputs_def]
QED

val _ = List.app (fn name =>
  if null (List.filter (fn x => x <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag (DB.fetch "abiTupleProps" name)))))
  then () else raise Fail ("oracle in " ^ name))
  ["compile_store_abi_tuple_correct", "compile_store_abi_tuple_value_correct",
   "compile_store_abi_tuple_zero_correct", "compile_store_abi_tuple_nil",
   "abi_tuple_inputs_lengths", "abi_tuple_inputs_singleton"];

(* Singleton staging still emits ADD at zero and uses the same framed
   execution boundary for word and nonword inputs. *)
Theorem compile_store_abi_tuple_singleton_correct:
  compile_store_abi_tuple cenv buf 0 [(op,ty)] st = ((),st') /\
  eval_operand buf ss = SOME (n2w baddr) /\ fresh_vars_wrt st ss /\
  baddr < dimword (:256) /\
  baddr+type_memory_bytes cenv ty <= dimword (:256) /\
  abi_tuple_inputs cenv [(op,ty)] [tv] [v] ss baddr
    (baddr+type_memory_bytes cenv ty) ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    val_in_memory (TupleTV [tv]) (ArrayV (TupleV [v])) baddr ss'.vs_memory /\
    same_blocks st st' /\ fresh_vars_wrt st' ss' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
    (!p k. p+k <= baddr \/ baddr+type_memory_bytes cenv ty <= p ==>
      mem_bytes_at p k ss'.vs_memory = mem_bytes_at p k ss.vs_memory)
Proof
  strip_tac >> fs[] >> drule compile_store_abi_tuple_value_correct >>
  disch_then (qspecl_then [`[v]`, `[tv]`, `ss`, `baddr`] mp_tac) >>
  simp[abi_tuple_bytes_def, abi_tuple_starts_def]
QED

val _ = List.app (fn name =>
  if null (List.filter (fn x => x <> "DISK_THM")
    (#1 (Tag.dest_tag (Thm.tag (DB.fetch "abiTupleProps" name)))))
  then () else raise Fail ("oracle in " ^ name))
  ["abi_tuple_inputs_sizes", "compile_store_abi_tuple_singleton_correct"];
