(*
 * Assembly Parse Correctness — ML Precomputation Helpers
 *
 * parse_opcode / parse_code helper lemmas for assembly → bytecode.
 * Uses ML precomputation for opcode table enumeration.
 *
 * EXPORTS:
 *   evm_byte_bridge          — parse_opcode on any opcode table byte
 *   parse_opcode_push        — parse_opcode on Push n encoding
 *   opcode_length_pos        — opcode always non-empty
 *   parse_code_preserves_below — parse_code preserves earlier FLOOKUP
 *   parse_code_entry         — parse_code records parse result at pc
 *   parse_code_step          — entry + preserves combined
 *   pad_bytes_length         — pad_bytes produces correct length
 *   non_data_inst_size_pos   — non-data instructions have positive size
 *   take_pad_0_prefix        — take_pad_0 with exact-length prefix
 *)


Theory asmParseProofs
Ancestors
  symbolResolve asmSem asmWf codegenRel
  vfmContext vfmOperation vfmTypes
  words list rich_list finite_map alist pair

(* ===== Basic Helpers ===== *)

val opcode_length_pos = store_thm("opcode_length_pos",
  ``!op. 0 < LENGTH (opcode op)``,
  Cases >> simp[opcode_def]);

val parse_code_preserves_below = store_thm("parse_code_preserves_below",
  ``!pc m code k v.
      FLOOKUP m k = SOME v /\ k < pc ==>
      FLOOKUP (parse_code pc m code) k = SOME v``,
  ho_match_mp_tac parse_code_ind >> rpt strip_tac >>
  once_rewrite_tac [parse_code_def] >>
  Cases_on `NULL code` >> simp[] >>
  first_x_assum irule >> simp[FLOOKUP_UPDATE]);

val non_data_inst_size_pos = store_thm("non_data_inst_size_pos",
  ``!inst. ~is_data_inst inst ==> 0 < asm_inst_size inst``,
  Cases >> simp[is_data_inst_def, asm_inst_size_def] >>
  Cases_on `l` >> simp[]);

val pad_bytes_length = store_thm("pad_bytes_length",
  ``!n bytes. LENGTH bytes <= n ==> LENGTH (pad_bytes n bytes) = n``,
  rw[pad_bytes_def] >> simp[]);


val take_pad_0_prefix = store_thm("take_pad_0_prefix",
  ``!n (xs : byte list) ys.
      LENGTH xs = n ==> take_pad_0 n (xs ++ ys) = xs``,
  simp[take_pad_0_def, PAD_RIGHT, TAKE_LENGTH_APPEND]);

(* ===== evm_byte_bridge: parse_opcode on opcode table bytes ===== *)

(* Custom tactic: for a goal with concrete byte, evaluate parse_opcode *)
local
  fun parse_opcode_eval_tac (g as (asms, goal)) = let
    val (op_var, body) = dest_exists goal
    val (eq1, eq2) = dest_conj body
    val parse_tm = lhs eq1
    val parse_thm = SIMP_CONV (srw_ss())
      [parse_opcode_cond_thm, dimword_8] parse_tm
    val result = rhs (concl parse_thm)
    val op_tm = rand result
    val opcode_tm = mk_comb(``opcode``, op_tm)
    val opcode_thm = SIMP_CONV (srw_ss())
      [opcode_def, word_add_n2w, dimword_8] opcode_tm
  in
    (EXISTS_TAC op_tm >> simp[parse_thm, opcode_thm, word_add_n2w, dimword_8]) g
  end
in
val evm_byte_bridge = store_thm("evm_byte_bridge",
  ``!name b. evm_opcode_byte name = SOME b ==>
    !rest. ?op. parse_opcode (b :: rest) = SOME op /\ opcode op = [b]``,
  rpt strip_tac >>
  `MEM (name, b) evm_opcode_table` by (
    fs[evm_opcode_byte_def] >> imp_res_tac ALOOKUP_MEM) >>
  gvs[evm_opcode_table_def, MEM] >>
  parse_opcode_eval_tac)
end;

(* ===== parse_opcode_push: parse_opcode on Push n encoding ===== *)

local
  (* Build n <= 32 ==> n=0 \/ n=1 \/ ... \/ n=32 via pure inference *)
  fun mk_split k = DECIDE (mk_imp(
    numSyntax.mk_leq(``n:num``, numSyntax.term_of_int k),
    mk_disj(mk_eq(``n:num``, numSyntax.term_of_int k),
            numSyntax.mk_leq(``n:num``, numSyntax.term_of_int (k-1)))));
  val base = DECIDE ``n <= 0n ==> (n = 0n)``;
  fun step split prev = let
    val h = fst (dest_imp (concl split))
    val assume_h = ASSUME h
    val disj = MP split assume_h
    val (eq_tm, le_tm) = dest_disj (snd (dest_imp (concl split)))
    val eq_case = ASSUME eq_tm
    val le_case = MP prev (ASSUME le_tm)
    val combined_concl = mk_disj(eq_tm, concl le_case)
  in DISCH h (DISJ_CASES disj (DISJ1 eq_case (concl le_case)) (DISJ2 eq_tm le_case))
  end;
  val splits = List.tabulate(32, fn i => mk_split (i+1));
  val n_le_32 = foldl (fn (split, acc) => step split acc) base splits;
  val take_len_app = prove(
    ``!xs ys n. LENGTH (xs:'a list) = n ==> TAKE n (xs ++ ys) = xs``,
    Induct >> simp[]);
in
val parse_opcode_push = store_thm("parse_opcode_push",
  ``!n args rest. n <= 32 /\ LENGTH (args:byte list) = n ==>
    parse_opcode (n2w(95+n) :: args ++ rest) = SOME (Push n args) /\
    opcode (Push n args) = n2w(95+n) :: args``,
  rpt strip_tac >> imp_res_tac n_le_32 >> gvs[] >>
  simp[parse_opcode_cond_thm, take_pad_0_def, PAD_RIGHT, opcode_def,
       word_add_n2w, dimword_8] >> TRY (irule take_len_app >> simp[]))
end;

(* ===== parse_code Stepping Lemmas ===== *)

val parse_code_entry = store_thm("parse_code_entry",
  ``!code pc m op.
      code <> [] /\
      parse_opcode code = SOME op ==>
      FLOOKUP (parse_code pc m code) pc = SOME op``,
  rpt strip_tac >>
  once_rewrite_tac [parse_code_def] >>
  `~NULL code` by (Cases_on `code` >> fs[]) >>
  simp[] >>
  irule parse_code_preserves_below >>
  simp[FLOOKUP_UPDATE, opcode_length_pos]);

val parse_code_step = store_thm("parse_code_step",
  ``!segment rest pc m op.
      segment <> [] /\
      parse_opcode (segment ++ rest) = SOME op /\
      opcode op = segment ==>
      FLOOKUP (parse_code pc m (segment ++ rest)) pc = SOME op /\
      (!k v. FLOOKUP m k = SOME v /\ k < pc ==>
         FLOOKUP (parse_code pc m (segment ++ rest)) k = SOME v)``,
  rpt strip_tac
  >- (irule parse_code_entry >> simp[])
  >- (irule parse_code_preserves_below >> simp[]));
