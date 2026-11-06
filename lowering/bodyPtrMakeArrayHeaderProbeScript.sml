(* Abstract endpoint test only: no claim of child reachability. *)
Theory bodyPtrMakeArrayHeaderProbe
Ancestors
  bodyPtrMakeArraySourceLayoutProbe valueEncodingProofs ptrDiscipline
  finite_map words list bodyPtrDefs valueEncoding valueEncodingProps compileEnv

Theorem displaced_header_sizes:
  type_memory_size
    (TupleTV [BaseTV (BytesT (Dynamic 32));
              ArrayTV (BaseTV (UintT 256)) (Dynamic 1)]) = 128 /\
  type_memory_size
    (TupleTV [BaseTV (BytesT (Dynamic 64));
              ArrayTV (BaseTV (UintT 256)) (Dynamic 1)]) = 160 /\
  type_memory_size (BaseTV (BytesT (Dynamic 32))) = 64 /\
  type_memory_size (BaseTV (BytesT (Dynamic 64))) = 96
Proof
  EVAL_TAC
QED

Theorem displaced_header_clean_window[local]:
  mem_agree_outside {96} mem m /\ (off + len <= 96 \/ 97 <= off) ==>
  mem_bytes_at off len mem = mem_bytes_at off len m
Proof
  strip_tac >> irule LIST_EQ >>
  simp[LENGTH_mem_bytes_at] >> rpt strip_tac >>
  `mem_bytes_at (off+x) 1 mem = mem_bytes_at (off+x) 1 m` by
    (fs[mem_agree_outside_def] >> first_x_assum irule >> simp[] >> decide_tac) >>
  pop_assum (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[EL_mem_bytes_at]
QED

Theorem displaced_header_narrow_robust:
  !m. mem_agree_outside {96} (REPLICATE 160 (0w:word8)) m ==>
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 32));
              ArrayTV (BaseTV (UintT 256)) (Dynamic 1)])
    (ArrayV (TupleV [BytesV []; ArrayV (DynArrayV [])])) 0 m
Proof
  rpt strip_tac >>
  `mem_bytes_at 0 32 (REPLICATE 160 (0w:word8)) = mem_bytes_at 0 32 m` by
    (irule displaced_header_clean_window >> simp[]) >>
  `mem_bytes_at 64 32 (REPLICATE 160 (0w:word8)) = mem_bytes_at 64 32 m` by
    (irule displaced_header_clean_window >> simp[]) >>
  simp[val_in_memory_def, type_memory_size_def, vfmConstantsTheory.word_size_def,
       mem_word_at_def, GSYM mem_bytes_at_def] >>
  qpat_x_assum `mem_bytes_at 0 32 _ = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `mem_bytes_at 64 32 _ = _` (SUBST1_TAC o SYM) >>
  EVAL_TAC >> simp[]
QED

Theorem displaced_header_wide_coverage:
  ptr_covers (FEMPTY |+ ("p",0,160))
    (entry_taint with t_mem := {96}) "p"
    (s with <| vs_vars := FEMPTY |+ ("p",0w);
               vs_memory := REPLICATE 160 (0w:word8) |>) 160
Proof
  simp[FLOOKUP_UPDATE, ptr_covers_def, op_taint_def,
       entry_taint_def, venomStateTheory.lookup_var_def]
QED

Theorem displaced_header_load_taint:
  0 IN op_taint
    (step_taint
      (inst with <| inst_opcode := MLOAD; inst_operands := [Lit 96w];
                    inst_outputs := ["h"] |>) s s'
      (entry_taint with t_mem := {96})) (Var "h")
Proof
  simp[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
       venomStateTheory.eval_operand_def, mem_word_taint_def, FLOOKUP_UPDATE,
       dimword_def]
QED

Theorem displaced_header_gt_unsafe:
  0 IN op_taint tn (Var "h") ==>
  ~taint_ok fn tn
    (inst with <| inst_opcode := GT; inst_operands := [Var "h"; Lit 1w] |>) s
Proof
  simp[taint_ok_def] >> strip_tac >>
  disj1_tac >> qexists_tac `Var "h"` >> simp[] >>
  metis_tac[pred_setTheory.NOT_IN_EMPTY]
QED
