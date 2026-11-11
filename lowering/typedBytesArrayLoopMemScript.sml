(* Prefix invariant for the actual Bytes1-to-Bytes33 array loop. *)
Theory typedBytesArrayLoopMem
Ancestors
  typedArrayLoopLayoutMem typedBytesArrayMem typedArrayLoopControlMem
  memContinuation fragExec fragExecMem instMemFrontier exprSimAggregateEncoding valueEncoding valueEncodingProps
  venomState venomInst venomExecSemantics compileEnv exprLoweringProps emitHelperProps
  vyperValue vyperTyping words arithmetic list rich_list vfmConstants

Definition typed_bytes_array_prefix_def:
  typed_bytes_array_prefix bss addr stride cap i mem <=>
    !j. j < i ==>
      val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV (EL j bss))
        (addr + stride*j) mem
End

Theorem typed_bytes_array_prefix_zero[local]:
  typed_bytes_array_prefix bss addr stride cap 0 mem
Proof
  simp[typed_bytes_array_prefix_def]
QED

Theorem typed_bytes_array_prefix_suc[local]:
  typed_bytes_array_prefix bss addr stride cap i mem /\
  val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV (EL i bss))
    (addr + stride*i) mem ==>
  typed_bytes_array_prefix bss addr stride cap (SUC i) mem
Proof
  simp[typed_bytes_array_prefix_def, prim_recTheory.LESS_THM] >> metis_tac[]
QED

Theorem typed_bytes_array_prefix_preserved[local]:
  typed_bytes_array_prefix bss addr 96 33 i mem /\
  i <= LENGTH bss /\ EVERY (\bs. LENGTH bs <= 1) bss /\
  mem_bytes_at addr (96*i) mem = mem_bytes_at addr (96*i) mem' ==>
  typed_bytes_array_prefix bss addr 96 33 i mem'
Proof
  rw[typed_bytes_array_prefix_def] >>
  `j < LENGTH bss` by decide_tac >>
  `LENGTH (EL j bss) <= 1` by
    (fs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  irule val_in_memory_relocate >>
  conj_tac >- simp[val_wf_def, type_memory_size_def, word_size_def] >>
  qexistsl_tac [`mem`, `96`, `addr + 96*j`] >>
  simp[type_memory_size_def, word_size_def] >>
  irule mem_bytes_at_translated_window >>
  qexists_tac `96*i` >> simp[]
QED

Theorem typed_bytes_array_prefix_array:
  typed_bytes_array_prefix bss addr 96 33 (LENGTH bss) mem ==>
  val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 33))) (Fixed (LENGTH bss)))
    (ArrayV (make_array_value (BaseTV (BytesT (Dynamic 33)))
      (Fixed (LENGTH bss)) (MAP BytesV bss))) addr mem
Proof
  strip_tac >> irule fixed_array_from_dense >> simp[] >>
  irule elems_in_memory_intro >>
  fs[typed_bytes_array_prefix_def, EL_MAP, type_memory_size_def,
     word_size_def]
QED

Theorem typed_bytes_array_source_element[local]:
  typed_bytes_array_prefix bss addr 64 1 (LENGTH bss) mem /\
  EVERY (\bs. LENGTH bs <= 1) bss /\ j < LENGTH bss /\
  mem_bytes_at addr (64 * LENGTH bss) mem =
    mem_bytes_at addr (64 * LENGTH bss) mem' ==>
  val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV (EL j bss))
    (addr + 64*j) mem'
Proof
  strip_tac >>
  `LENGTH (EL j bss) <= 1` by
    (fs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  irule val_in_memory_relocate >>
  conj_tac >- simp[val_wf_def, type_memory_size_def, word_size_def] >>
  qexistsl_tac [`mem`, `64`, `addr + 64*j`] >>
  fs[typed_bytes_array_prefix_def, type_memory_size_def, word_size_def] >>
  irule mem_bytes_at_translated_window >>
  qexists_tac `64 * LENGTH bss` >> simp[]
QED

Definition typed_bytes_array_loop_inv_def:
  typed_bytes_array_loop_inv sa bss source_addr dest_addr initial i s <=>
    i <= LENGTH bss /\ ~s.vs_halted /\
    s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
    s.vs_inst_idx = 0 /\
    eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
    mem_bytes_at source_addr (64 * LENGTH bss) s.vs_memory =
      mem_bytes_at source_addr (64 * LENGTH bss) initial.vs_memory /\
    typed_bytes_array_prefix bss dest_addr 96 33 i s.vs_memory /\
    (s with <|vs_vars := initial.vs_vars; vs_memory := initial.vs_memory;
      vs_current_bb := initial.vs_current_bb; vs_inst_idx := initial.vs_inst_idx;
      vs_prev_bb := initial.vs_prev_bb|>) = initial /\
    (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x initial)
End

Theorem typed_bytes_array_loop_init[local]:
  ~s.vs_halted ==>
  typed_bytes_array_loop_inv sa bss source_addr dest_addr s 0
    (jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
      (update_var ("%" ++ toString sa.cs_next_var) 0w s))
Proof
  strip_tac >>
  simp[typed_bytes_array_loop_inv_def, typed_bytes_array_prefix_zero,
       jump_to_def, update_var_def, lookup_var_def, eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> "%" ++ toString sa.cs_next_var` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >> gvs[]
QED

Theorem typed_bytes_array_loop_start[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. typed_bytes_array_loop_inv sa bss source_addr dest_addr s 0 u /\
      mem_cont_sim ctx fn s u
Proof
  strip_tac >> drule_all typed_bytes_array_initial_cont >> strip_tac >>
  qexists_tac `jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
    (update_var ("%" ++ toString sa.cs_next_var) 0w s)` >>
  simp[typed_bytes_array_loop_init]
QED

Theorem typed_bytes_array_loop_exit_cont[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  typed_bytes_array_loop_inv sa bss source_addr dest_addr initial (LENGTH bss) u /\
  LENGTH bss < dimword(:256) /\
  lookup_block (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
    fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  mem_cont_sim ctx fn u
    (jump_to (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) (LENGTH bss) (LENGTH bss) u))
Proof
  strip_tac >> drule_all typed_bytes_array_loop_code >> simp[] >> strip_tac >>
  fs[typed_bytes_array_loop_inv_def] >>
  irule (SRULE [] (Q.INST [`i` |-> `LENGTH bss`, `ncount` |-> `LENGTH bss`]
    (SPEC_ALL typed_sa_header_sim))) >> simp[] >>
  qexistsl_tac [`fresh_label_output "typed_sa_body" (sa.cs_next_label+1)`,
    `"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >> simp[]
QED

Theorem typed_bytes_array_loop_body_prefix[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w source_addr) /\
  eval_operand dst s = SOME (n2w dest_addr) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) ==>
  ?u. mem_cont_sim ctx fn s u /\ u.vs_inst_idx = 4 /\
    u.vs_current_bb = s.vs_current_bb /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+5))) u =
      SOME (n2w (source_addr + 64*i)) /\
    eval_operand (Var ("%" ++ toString (sa.cs_next_var+6))) u =
      SOME (n2w (dest_addr + 96*i)) /\
    (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var ==>
      lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  qabbrev_tac `ctr = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `so = "%" ++ toString (sa.cs_next_var+3)` >>
  qabbrev_tac `dso = "%" ++ toString (sa.cs_next_var+4)` >>
  qabbrev_tac `sp = "%" ++ toString (sa.cs_next_var+5)` >>
  qabbrev_tac `dp = "%" ++ toString (sa.cs_next_var+6)` >>
  `ALL_DISTINCT [so;dso;sp;dp] /\ ~MEM ctr [so;dso;sp;dp]` by
    simp[Abbr `so`, Abbr `dso`, Abbr `sp`, Abbr `dp`, Abbr `ctr`] >>
  `!x. src = Var x \/ dst = Var x ==> ~MEM x [so;dso;sp;dp]` by
    (gen_tac >> disch_tac >> first_x_assum drule >>
     simp[not_fresh_at_def, Abbr `so`, Abbr `dso`, Abbr `sp`, Abbr `dp`] >>
     metis_tac[DECIDE ``n < n+k+1``]) >>
  drule_all typed_sa_pointer_run >>
  disch_then (qspecl_then [`64`, `sa.cs_next_id+5`, `96`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code s = OK q` >>
  `mem_cont_sim ctx fn s (q with vs_inst_idx := 4)` by
    (drule typed_bytes_array_loop_counters >> strip_tac >>
     `lookup_block (HD sb.cs_blocks).bb_label fn.fn_blocks = SOME (HD sb.cs_blocks)` by
       (fs[fn_has_code_def, emitted_blocks_def] >>
        first_x_assum irule >> Cases_on `sb.cs_blocks` >> gvs[]) >>
     drule typed_bytes_array_loop_blocks >> simp_tac bool_ss [LET_THM] >> strip_tac >>
     `LENGTH code = 4` by simp[Abbr `code`] >>
     qpat_x_assum `LENGTH code = 4` (fn th => once_rewrite_tac [GSYM th]) >>
     irule typed_array_prefix_cont >> simp[] >> conj_tac
     >- simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
     qexists_tac `HD sb.cs_blocks` >>
     fs[Abbr `code`, Abbr `ctr`, Abbr `so`, Abbr `dso`, Abbr `sp`, Abbr `dp`]) >>
  qexists_tac `q with vs_inst_idx := 4` >>
  fs[venom_state_component_equality, lookup_var_def] >> simp[] >>
  gen_tac >> disch_tac >> first_x_assum irule >>
  fs[not_fresh_at_def, Abbr `ctr`, Abbr `so`, Abbr `dso`, Abbr `sp`, Abbr `dp`] >>
  metis_tac[DECIDE ``n < n+k+1``]
QED

Theorem typed_bytes_array_body_copy[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w source_addr) /\
  eval_operand dst s = SOME (n2w dest_addr) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
  i < LENGTH bss /\ EVERY (\bs. LENGTH bs <= 1) bss /\
  source_addr + 64 * LENGTH bss <= s.vs_alloca_next /\
  dest_addr + 96 * LENGTH bss <= s.vs_alloca_next /\
  source_addr + 64 * LENGTH bss < dimword(:256) /\
  dest_addr + 96 * LENGTH bss < dimword(:256) /\
  (source_addr + 64 * LENGTH bss <= dest_addr \/
   dest_addr + 96 * LENGTH bss <= source_addr) /\
  typed_bytes_array_prefix bss source_addr 64 1 (LENGTH bss) s.vs_memory /\
  typed_bytes_array_prefix bss dest_addr 96 33 i s.vs_memory ==>
  ?v. mem_cont_sim ctx fn s v /\ v.vs_inst_idx = 10 /\
    v.vs_current_bb = s.vs_current_bb /\
    typed_bytes_array_prefix bss dest_addr 96 33 (SUC i) v.vs_memory /\
    mem_bytes_at source_addr (64 * LENGTH bss) v.vs_memory =
      mem_bytes_at source_addr (64 * LENGTH bss) s.vs_memory /\
    (v with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var ==>
      lookup_var x v = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_bytes_array_loop_body_prefix >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all typed_bytes_array_child_code >> strip_tac >>
  `LENGTH (EL i bss) <= 1` by
    (fs[EVERY_EL] >> first_x_assum irule >> simp[]) >>
  `w2n (n2w (source_addr + 64*i):256 word) = source_addr + 64*i /\
   w2n (n2w (dest_addr + 96*i):256 word) = dest_addr + 96*i` by
    (simp[w2n_n2w] >> conj_tac >> irule LESS_MOD >> decide_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted` by
    fs[venom_state_component_equality] >>
  `val_in_memory (BaseTV (BytesT (Dynamic 1))) (BytesV (EL i bss))
     (source_addr + 64*i) u.vs_memory` by
    fs[typed_bytes_array_prefix_def] >>
  `!x. Var ("%" ++ toString (sa.cs_next_var+5)) = Var x \/
       Var ("%" ++ toString (sa.cs_next_var+6)) = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> gvs[]) >>
  drule typed_bytes_array_child_cont >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`source_addr`, `LENGTH bss`, `i`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`fn`, `ctx`, `EL i bss`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `typed_bytes_array_prefix bss dest_addr 96 33 (SUC i) q.vs_memory` by
    (irule typed_bytes_array_prefix_suc >> simp[] >>
     irule typed_bytes_array_prefix_preserved >>
     conj_tac >- decide_tac >> conj_tac >- simp[] >>
     qexists_tac `s.vs_memory` >> simp[]) >>
  qexists_tac `q with vs_inst_idx := 10` >> simp[] >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `q with <|vs_memory := _; vs_vars := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  conj_tac >-
    (qpat_x_assum `q with <|vs_memory := _; vs_vars := _|> = u` mp_tac >>
     qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `not_fresh_at sc ("%" ++ toString sa.cs_next_var)` by
    (simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac) >>
  gvs[] >> rpt strip_tac >>
  `lookup_var x q = lookup_var x u` by metis_tac[] >>
  simp[lookup_var_def] >> gvs[lookup_var_def]
QED

Theorem typed_bytes_array_backedge_cont[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_inst_idx = 10 /\
  s.vs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) ==>
  mem_cont_sim ctx fn s
    (jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
      (typed_sa_backedge_state ("%" ++ toString sa.cs_next_var)
        ("%" ++ toString (sa.cs_next_var+12)) i s))
Proof
  strip_tac >> drule_all typed_bytes_array_loop_code >> simp[] >> strip_tac >>
  gvs[] >> irule typed_sa_backedge_sim >> simp[] >>
  conj_tac >- (qexists_tac `ncount` >> simp[]) >>
  simp[typed_sa_header_insts_def, phi_prefix_length_def, mk_inst_def] >>
  qexistsl_tac [`sa.cs_next_id+15`, `TAKE 10 body_bb.bb_instructions`] >>
  simp[] >> metis_tac[TAKE_DROP]
QED

Theorem typed_bytes_array_header_cont[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) ncount sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = fresh_label_output "typed_sa_cond" sa.cs_next_label /\
  eval_operand (Var ("%" ++ toString sa.cs_next_var)) s = SOME (n2w i) /\
  i < ncount /\ ncount < dimword(:256) ==>
  ?u. mem_cont_sim ctx fn s u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1) /\
    (u with <|vs_vars := s.vs_vars; vs_current_bb := s.vs_current_bb;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x \/ x = "%" ++ toString sa.cs_next_var ==>
      lookup_var x u = lookup_var x s)
Proof
  strip_tac >> drule_all typed_bytes_array_loop_code >> simp[] >> strip_tac >>
  gvs[] >>
  `mem_cont_sim ctx fn s
    (jump_to (if i < ncount then fresh_label_output "typed_sa_body" (sa.cs_next_label+1)
              else fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
      (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
        ("%" ++ toString (sa.cs_next_var+2)) i ncount s))` by
    (irule typed_sa_header_sim >> simp[] >>
     qexistsl_tac [`"%" ++ toString sa.cs_next_var`, `sa.cs_next_id+2`] >> simp[]) >>
  gvs[] >> goal_assum (drule_at Any) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]
QED

Theorem typed_bytes_array_loop_successor[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src initial = SOME (n2w source_addr) /\
  eval_operand dst initial = SOME (n2w dest_addr) /\
  EVERY (\bs. LENGTH bs <= 1) bss /\ LENGTH bss < dimword(:256) /\
  source_addr + 64 * LENGTH bss <= initial.vs_alloca_next /\
  dest_addr + 96 * LENGTH bss <= initial.vs_alloca_next /\
  source_addr + 64 * LENGTH bss < dimword(:256) /\
  dest_addr + 96 * LENGTH bss < dimword(:256) /\
  (source_addr + 64 * LENGTH bss <= dest_addr \/
   dest_addr + 96 * LENGTH bss <= source_addr) /\
  typed_bytes_array_prefix bss source_addr 64 1 (LENGTH bss) initial.vs_memory /\
  typed_bytes_array_loop_inv sa bss source_addr dest_addr initial i s /\
  i < LENGTH bss ==>
  ?t. mem_cont_sim ctx fn s t /\
      typed_bytes_array_loop_inv sa bss source_addr dest_addr initial (SUC i) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `typed_bytes_array_loop_inv _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [typed_bytes_array_loop_inv_def]) >>
  drule_all typed_bytes_array_header_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `u.vs_labels = initial.vs_labels /\
   u.vs_memory = s.vs_memory /\ u.vs_alloca_next = initial.vs_alloca_next` by
    (qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s` mp_tac >>
     qpat_x_assum `s with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = initial` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src u = SOME (n2w source_addr) /\
   eval_operand dst u = SOME (n2w dest_addr)` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Var ("%" ++ toString sa.cs_next_var)) u = SOME (n2w i)` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `typed_bytes_array_prefix bss source_addr 64 1 (LENGTH bss) u.vs_memory` by
    (pure_rewrite_tac[typed_bytes_array_prefix_def] >> gen_tac >> disch_tac >>
     irule typed_bytes_array_source_element >> simp[] >>
     qexists_tac `initial.vs_memory` >> simp[]) >>
  drule typed_bytes_array_body_copy >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`i`, `ctx`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `~v.vs_halted` by fs[venom_state_component_equality] >>
  `eval_operand (Var ("%" ++ toString sa.cs_next_var)) v = SOME (n2w i)` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `v.vs_current_bb = fresh_label_output "typed_sa_body" (sa.cs_next_label+1)` by simp[] >>
  drule_all typed_bytes_array_backedge_cont >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `jump_to (fresh_label_output "typed_sa_cond" sa.cs_next_label)
    (typed_sa_backedge_state ("%" ++ toString sa.cs_next_var)
      ("%" ++ toString (sa.cs_next_var+12)) i v)` >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[] >>
    irule mem_cont_sim_trans >> qexists_tac `v` >> gvs[]) >>
  simp[typed_bytes_array_loop_inv_def, jump_to_def, typed_sa_backedge_state_def,
    update_var_def, eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >-
    (qpat_x_assum `v with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u` mp_tac >>
     qpat_x_assum `u with <|vs_vars := _; vs_current_bb := _; vs_prev_bb := _|> = s` mp_tac >>
     qpat_x_assum `s with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = initial` mp_tac >>
     simp[venom_state_component_equality]) >>
  rpt strip_tac >>
  `x <> "%" ++ toString sa.cs_next_var /\ x <> "%" ++ toString (sa.cs_next_var+12)` by
    (gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     metis_tac[DECIDE ``n <= n /\ n <= n+12``]) >>
  gvs[lookup_var_def] >> metis_tac[]
QED

Theorem typed_bytes_array_loop_iterate[local]:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src initial = SOME (n2w source_addr) /\
  eval_operand dst initial = SOME (n2w dest_addr) /\
  EVERY (\bs. LENGTH bs <= 1) bss /\ LENGTH bss < dimword(:256) /\
  source_addr + 64 * LENGTH bss <= initial.vs_alloca_next /\
  dest_addr + 96 * LENGTH bss <= initial.vs_alloca_next /\
  source_addr + 64 * LENGTH bss < dimword(:256) /\
  dest_addr + 96 * LENGTH bss < dimword(:256) /\
  (source_addr + 64 * LENGTH bss <= dest_addr \/
   dest_addr + 96 * LENGTH bss <= source_addr) /\
  typed_bytes_array_prefix bss source_addr 64 1 (LENGTH bss) initial.vs_memory /\
  typed_bytes_array_loop_inv sa bss source_addr dest_addr initial 0 s ==>
  ?t. typed_bytes_array_loop_inv sa bss source_addr dest_addr initial (LENGTH bss) t /\
      mem_cont_sim ctx fn s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule mem_cont_sim_finite_iteration >>
  qexistsl_tac [`LENGTH bss`, `0`,
    `typed_bytes_array_loop_inv sa bss source_addr dest_addr initial`] >>
  simp[] >> conj_tac >-
    (rpt strip_tac >> drule_all typed_bytes_array_loop_successor >>
     disch_then (qspec_then `ctx` mp_tac) >> metis_tac[]) >>
  metis_tac[mem_cont_sim_refl]
QED

Theorem typed_bytes_array_copy_cont:
  compile_copy_sarray_typed ce dst (BaseT (BytesT (Dynamic 33)))
    src (BaseT (BytesT (Dynamic 1))) (LENGTH bss) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME (n2w source_addr) /\
  eval_operand dst s = SOME (n2w dest_addr) /\
  EVERY (\bs. LENGTH bs <= 1) bss /\ LENGTH bss < dimword(:256) /\
  source_addr + 64 * LENGTH bss <= s.vs_alloca_next /\
  dest_addr + 96 * LENGTH bss <= s.vs_alloca_next /\
  source_addr + 64 * LENGTH bss < dimword(:256) /\
  dest_addr + 96 * LENGTH bss < dimword(:256) /\
  (source_addr + 64 * LENGTH bss <= dest_addr \/
   dest_addr + 96 * LENGTH bss <= source_addr) /\
  typed_bytes_array_prefix bss source_addr 64 1 (LENGTH bss) s.vs_memory /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_block (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
    fn.fn_blocks = SOME exit_bb /\ phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory (ArrayTV (BaseTV (BytesT (Dynamic 33))) (Fixed (LENGTH bss)))
      (ArrayV (make_array_value (BaseTV (BytesT (Dynamic 33)))
        (Fixed (LENGTH bss)) (MAP BytesV bss))) dest_addr t.vs_memory /\
    mem_bytes_at source_addr (64 * LENGTH bss) t.vs_memory =
      mem_bytes_at source_addr (64 * LENGTH bss) s.vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_bytes_array_loop_start >>
  disch_then (qspecl_then [`source_addr`, `dest_addr`, `ctx`] strip_assume_tac) >>
  drule_all typed_bytes_array_loop_iterate >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all typed_bytes_array_loop_exit_cont >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `jump_to (fresh_label_output "typed_sa_exit" (sa.cs_next_label+2))
    (typed_sa_header_state ("%" ++ toString (sa.cs_next_var+1))
      ("%" ++ toString (sa.cs_next_var+2)) (LENGTH bss) (LENGTH bss) t)` >>
  conj_tac >- (irule mem_cont_sim_trans >> qexists_tac `u` >> simp[] >>
    irule mem_cont_sim_trans >> qexists_tac `t` >> gvs[]) >>
  drule typed_bytes_array_loop_counters >> strip_tac >>
  qpat_x_assum `typed_bytes_array_loop_inv _ _ _ _ _ (LENGTH bss) _`
    (strip_assume_tac o PURE_REWRITE_RULE [typed_bytes_array_loop_inv_def]) >>
  simp[jump_to_def, typed_sa_header_state_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- (irule typed_bytes_array_prefix_array >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_current_bb := _;
       vs_inst_idx := _; vs_prev_bb := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  rpt strip_tac >>
  `x <> "%" ++ toString (sa.cs_next_var+1) /\ x <> "%" ++ toString (sa.cs_next_var+2)` by
    (gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     metis_tac[DECIDE ``n <= n+1 /\ n <= n+2``]) >>
  gvs[lookup_var_def]
QED
