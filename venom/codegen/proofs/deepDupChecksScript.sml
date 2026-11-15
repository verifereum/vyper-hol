(* Execute generated deep-DUP assembly at both restore-strategy boundaries.
   Check the physical stack, pre-existing memory, and the external state frame. *)
Theory deepDupChecks
Ancestors
  stackPlanOps stackPlanTypes stackModel planExec asmSem words list byte
  doSwapSim finite_map
Libs wordsLib

val () = computeLib.upd_compset (computeLib.add_thms [set_byte_bit_field_insert])

(* Reduce one actual interpreter step, leaving its recursive continuation
   opaque. Bounded groups keep each proof fragment within the normal timeout. *)
val asm_runner = ``run_asm_aux``;
fun DEEP_DUP_STEP_CONV tm =
  let val (head,args) = strip_comb tm
  in if same_const head asm_runner andalso length args = 5 then
       let val unfolded = REWR_CONV run_asm_aux_def tm
       in TRANS unfolded (computeLib.RESTR_EVAL_CONV [asm_runner]
            (rhs (concl unfolded))) end
     else ALL_CONV tm
  end;
fun DEEP_DUP_CASE_CONV tm =
  let val (_,args) = strip_comb tm
  in (funpow (length args - 1) RATOR_CONV
        (RAND_CONV DEEP_DUP_STEP_CONV)) tm end;
val DEEP_DUP_STEP_TAC =
  CONV_TAC (BINDER_CONV DEEP_DUP_CASE_CONV);

Definition deep_dup_input_stack_def:
  deep_dup_input_stack = GENLIST (\n. n2w n : bytes32) 40
End

Definition deep_dup_input_memory_def:
  deep_dup_input_memory = GENLIST (\n. n2w n : byte) 64
End

Definition deep_dup_probe_def:
  deep_dup_probe dist seed <=>
    let ps = (init_plan_state 64) with ps_stack := MAP Lit deep_dup_input_stack in
    let (ops,ps') = do_dup dist ps in
    let initial = seed with <| as_pc := 0;
      as_stack := REVERSE deep_dup_input_stack;
      as_memory := deep_dup_input_memory |> in
    case run_asm 500 (execute_plan 0 ops) initial of
      AsmHalt result =>
        result.as_stack = EL dist (REVERSE deep_dup_input_stack) ::
          REVERSE deep_dup_input_stack /\
        TAKE 64 result.as_memory = deep_dup_input_memory /\
        result with <| as_pc := seed.as_pc; as_stack := seed.as_stack;
                       as_memory := seed.as_memory |> = seed
    | _ => F
End

Theorem deep_dup_first_inaccessible:
  !seed. deep_dup_probe 16 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

Theorem deep_dup_two_spills:
  !seed. deep_dup_probe 17 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

Theorem deep_dup_last_single_swap:
  !seed. deep_dup_probe 31 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

Theorem deep_dup_multiple_restore_swaps:
  !seed. deep_dup_probe 32 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

(* Structural boundaries and witnesses that spill layout alone does not
   guarantee alignment with the planner result. *)
Theorem do_dup_boundary_ops:
  EVERY (\dist.
    let ps = (init_plan_state 0) with ps_stack := REPLICATE 50 (Var "probe");
        ops = FST (do_dup dist ps);
        spills = FLAT (MAP (\op. case op of SOSpill off => [off] | _ => []) ops);
        restores = FLAT (MAP (\op. case op of SORestore off => [off] | _ => []) ops)
    in
      LENGTH spills = dist - 15 /\
      ALL_DISTINCT restores /\
      EVERY (\off. MEM off spills) restores /\
      EVERY (\off. MEM off restores) spills /\
      FILTER (\op. case op of SODup _ => T | _ => F) ops = [SODup 16] /\
      EVERY (\op. case op of
        SODup n => 1 <= n /\ n <= 16
      | SOSwap n => 1 <= n /\ n <= 16
      | _ => T) ops)
    [15; 16; 31; 32; 40]
Proof
  CONV_TAC EVAL
QED

Theorem do_dup_overlap_alignment_probe:
  !lo.
    let ps = (init_plan_state 0) with <|
          ps_stack := Var "deep" :: REPLICATE 15 (Var "middle") ++ [Var "old"];
          ps_spilled := FEMPTY |+ (Var "old", 0);
          ps_alloc := (init_spill_alloc 0) with sa_next_offset := 32 |>;
        ops = FST (do_dup 16 ps)
    in
      spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
      prefix_spill_wf initial_fmp lo ops ps /\
      (apply_prefix_ops initial_fmp lo ops ps).ps_spilled <>
        (SND (do_dup 16 ps)).ps_spilled
Proof
  gen_tac >> CONV_TAC (computeLib.RESTR_EVAL_CONV [``spill_lookup``]) >>
  simp[FLOOKUP_UPDATE, DOMSUB_FUPDATE_THM, FLOOKUP_DEF] >>
  simp[spill_lookup_def, FLOOKUP_UPDATE, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED

Theorem emit_one_input_overlap_alignment_probe:
  !lo.
    let ps = (init_plan_state 0) with <|
          ps_stack := Var "deep" :: REPLICATE 15 (Var "middle") ++ [Var "old"];
          ps_spilled := FEMPTY |+ (Var "old", 0);
          ps_alloc := (init_spill_alloc 0) with sa_next_offset := 32 |>;
        result = emit_one_input ADD ["deep"] (Var "deep") ps;
        ops = FST result;
        ps' = SND result
    in
      spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
      prefix_spill_wf initial_fmp lo ops ps /\
      ~(?l. Var "deep" = Label l /\ ADD = INVOKE) /\
      (apply_prefix_ops initial_fmp lo ops ps).ps_spilled <> ps'.ps_spilled
Proof
  gen_tac >> CONV_TAC (computeLib.RESTR_EVAL_CONV [``spill_lookup``]) >>
  simp[FLOOKUP_UPDATE, DOMSUB_FUPDATE_THM, FLOOKUP_DEF] >>
  simp[spill_lookup_def, FLOOKUP_UPDATE, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``]
QED
