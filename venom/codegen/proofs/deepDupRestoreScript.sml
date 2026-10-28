(* Physical restoration used by deep duplication.  A restored word is placed
   immediately below the current top, keeping the duplicated word on top.
   The statements allow repeated values and do not use operand ownership. *)
Theory deepDupRestore
Ancestors
  doSwapSim stackOpSim stackOpAsmSim asmSem planExec stackPlanTypes
  list rich_list arithmetic

Theorem asm_swap_one_cons:
  !lo o2pc st top value rest.
    st.as_stack = top::value::rest ==>
    asm_step lo o2pc (AsmOp "SWAP1") st =
      AsmOK (st with <|as_stack := value::top::rest;
                      as_pc := st.as_pc + 1|>)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`lo`,`o2pc`,`1n`,`st`] asm_step_swap_ok) >>
  simp[swap_name_def, asm_next_def] >>
  `LUPDATE top 1 (LUPDATE value 0 (top::value::rest)) =
     value::top::rest` by
    (simp[LIST_EQ_REWRITE, EL_LUPDATE] >> gen_tac >>
     Cases_on `x` >> simp[] >> Cases_on `n` >> simp[]) >>
  simp[]
QED

Theorem restore_below_top_code_length[simp]:
  !offsets.
    LENGTH (execute_plan initial_fmp
      (FLAT (MAP (\off. [SORestore off; SOSwap 1]) offsets))) =
    3 * LENGTH offsets
Proof
  Induct >> simp[execute_plan_append] >>
  fs[execute_plan_def, exec_stack_op_def]
QED

Theorem restore_below_top_step:
  !lo o2pc prog off st top rest.
    st.as_stack = top::rest /\ off < dimword(:256) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp [SORestore off; SOSwap 1]) ==>
    asm_steps lo o2pc prog 3 st =
      AsmOK (st with <|
        as_stack := top ::
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP off st.as_memory)) :: rest;
        as_memory := asm_expand_memory (off + 32) st.as_memory;
        as_pc := st.as_pc + 3|>)
Proof
  rpt gen_tac >> strip_tac >>
  fs[execute_plan_def, exec_stack_op_def, swap_name_def,
     asm_block_at_append, asm_block_at_cons] >>
  qspecl_then [`lo`,`o2pc`,`prog`,`off`,`st`] mp_tac
    raw_restore_asm_steps >>
  (impl_tac >- (simp[asm_block_at_def] >> rpt strip_tac >>
    `j = 0 \/ j = 1` by decide_tac >> gvs[])) >>
  strip_tac >>
  rewrite_tac [DECIDE ``(3:num) = 2 + 1``, asm_steps_add] >>
  asm_rewrite_tac [] >>
  rewrite_tac [DECIDE ``1 = SUC 0``, Once asm_steps_def] >>
  simp[asm_steps_def] >>
  qmatch_goalsub_abbrev_tac `asm_step lo o2pc _ mid` >>
  qspecl_then [`lo`,`o2pc`,`mid`,
    `word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off st.as_memory))`,
    `top`,`rest`] mp_tac asm_swap_one_cons >>
  simp[Abbr `mid`] >> strip_tac >>
  asm_rewrite_tac [] >> simp[asm_state_component_equality]
QED

Theorem execute_plan_restore_below_cons[local]:
  execute_plan initial_fmp (SORestore off::SOSwap 1::ops) =
  execute_plan initial_fmp [SORestore off; SOSwap 1] ++
    execute_plan initial_fmp ops
Proof
  simp[execute_plan_def, exec_stack_op_def]
QED

Theorem restore_below_top_steps:
  !offsets lo o2pc prog st top rest.
    st.as_stack = top::rest /\
    EVERY (\off. off < dimword(:256)) offsets /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp
        (FLAT (MAP (\off. [SORestore off; SOSwap 1]) offsets))) ==>
    asm_steps lo o2pc prog (3 * LENGTH offsets) st =
      AsmOK (st with <|
        as_stack := top ::
          REVERSE (MAP (\off. word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP off st.as_memory))) offsets) ++ rest;
        as_memory :=
          FOLDL (\mem off. asm_expand_memory (off + 32) mem)
            st.as_memory offsets;
        as_pc := st.as_pc + 3 * LENGTH offsets|>)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[asm_steps_def, asm_state_component_equality] >>
  fs[] >>
  qpat_x_assum `asm_block_at prog st.as_pc _` mp_tac >>
  simp_tac std_ss [Once execute_plan_restore_below_cons,
                  asm_block_at_append] >> strip_tac >>
  qspecl_then [`lo`,`o2pc`,`prog`,`h`,`st`,`top`,`rest`] mp_tac
    restore_below_top_step >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum (qspecl_then [`lo`,`o2pc`,`prog`,
    `st with <|
      as_stack := top :: word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP h st.as_memory)) :: rest;
      as_memory := asm_expand_memory (h + 32) st.as_memory;
      as_pc := st.as_pc + 3|>`, `top`,
    `word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP h st.as_memory)) :: rest`] mp_tac) >>
  simp[execute_plan_def, exec_stack_op_def, raw_restore_map_reads_expand] >>
  strip_tac >>
  pure_once_rewrite_tac [DECIDE
    ``3 * SUC (LENGTH offsets) = 3 + 3 * LENGTH offsets``] >>
  pure_once_rewrite_tac [asm_steps_add] >>
  gvs[execute_plan_def, exec_stack_op_def,
      asm_state_component_equality, APPEND_ASSOC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed duplication restore theorem: " ^ name)
  end) (DB.thms "deepDupRestore")
