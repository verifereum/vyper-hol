(*
 * Selector Dispatch Definitions
 *
 * Upstream: vyperlang/vyper@a7f7bf133
 *
 * Definitions connecting Vyper-level function dispatch (by name + args)
 * to Venom-level selector dispatch (by 4-byte method_id in calldata).
 *
 * The Venom selector dispatch CFG (produced by compile_selector_dispatch)
 * extracts method_id = shr(224, calldataload(0)) and routes to the
 * matching function's entry block. These definitions formalize the
 * relationship between calldata bytes and the selector table.
 *
 * TOP-LEVEL:
 *   calldata_method_id   -- extract 4-byte selector from calldata
 *   calldata_encodes     -- calldata = selector ++ abi_encode(args)
 *   selector_matches     -- selector table entry matches a function
 *
 * Jumptable utilities (dense_bucket, generate_dense_jumptable_info, etc.)
 * are in jumptableUtilsTheory.
 *)

Theory selectorDispatch
Ancestors
  jumptableUtils
  compileEnv
  vyperABI
  contractABI
  keccak list rich_list divides arithmetic
  venomExecSemantics
Libs
  dep_rewrite

(* ===== Evaluator-Friendly Keccak ===== *)

(* The imported Keccak specification represents the 25 lanes as a list and
   repeatedly indexes that list during each round.  This definition implements
   the same round by destructuring the fixed-width state once. *)
Definition keccak_theta25_def:
  keccak_theta25 (s : word64 list) =
    case s of
      [a0;a1;a2;a3;a4; a5;a6;a7;a8;a9;
       a10;a11;a12;a13;a14; a15;a16;a17;a18;a19;
       a20;a21;a22;a23;a24] =>
        let c0 = a0 ?? a5 ?? a10 ?? a15 ?? a20;
            c1 = a1 ?? a6 ?? a11 ?? a16 ?? a21;
            c2 = a2 ?? a7 ?? a12 ?? a17 ?? a22;
            c3 = a3 ?? a8 ?? a13 ?? a18 ?? a23;
            c4 = a4 ?? a9 ?? a14 ?? a19 ?? a24;
            d0 = word_rol c1 1 ?? c4;
            d1 = word_rol c2 1 ?? c0;
            d2 = word_rol c3 1 ?? c1;
            d3 = word_rol c4 1 ?? c2;
            d4 = word_rol c0 1 ?? c3
        in
          [a0 ?? d0; a1 ?? d1; a2 ?? d2; a3 ?? d3; a4 ?? d4;
           a5 ?? d0; a6 ?? d1; a7 ?? d2; a8 ?? d3; a9 ?? d4;
           a10 ?? d0; a11 ?? d1; a12 ?? d2; a13 ?? d3; a14 ?? d4;
           a15 ?? d0; a16 ?? d1; a17 ?? d2; a18 ?? d3; a19 ?? d4;
           a20 ?? d0; a21 ?? d1; a22 ?? d2; a23 ?? d3; a24 ?? d4]
    | _ => []
End

(* rho followed by pi, with the standard Keccak rotation counts in the
   resulting pi order. *)
Definition keccak_rhopi25_def:
  keccak_rhopi25 (s : word64 list) =
    case s of
      [a0;a1;a2;a3;a4; a5;a6;a7;a8;a9;
       a10;a11;a12;a13;a14; a15;a16;a17;a18;a19;
       a20;a21;a22;a23;a24] =>
        [a0;
         word_ror a6 20; word_ror a12 21; word_ror a18 43;
         word_ror a24 50; word_ror a3 36; word_ror a9 44;
         word_ror a10 61; word_ror a16 19; word_ror a22 3;
         word_ror a1 63; word_ror a7 58; word_ror a13 39;
         word_ror a19 56; word_ror a20 46; word_ror a4 37;
         word_ror a5 28; word_ror a11 54; word_ror a17 49;
         word_ror a23 8; word_ror a2 2; word_ror a8 9;
         word_ror a14 25; word_ror a15 23; word_ror a21 62]
    | _ => []
End

Definition keccak_chiiota25_def:
  keccak_chiiota25 (s : word64 list) (rc : word64) =
    case s of
      [a0;a1;a2;a3;a4; a5;a6;a7;a8;a9;
       a10;a11;a12;a13;a14; a15;a16;a17;a18;a19;
       a20;a21;a22;a23;a24] =>
        [rc ?? (a0 ?? (a2 && ~a1));
         a1 ?? (a3 && ~a2); a2 ?? (a4 && ~a3);
         a3 ?? (a0 && ~a4); a4 ?? (a1 && ~a0);
         a5 ?? (a7 && ~a6); a6 ?? (a8 && ~a7);
         a7 ?? (a9 && ~a8); a8 ?? (a5 && ~a9);
         a9 ?? (a6 && ~a5);
         a10 ?? (a12 && ~a11); a11 ?? (a13 && ~a12);
         a12 ?? (a14 && ~a13); a13 ?? (a10 && ~a14);
         a14 ?? (a11 && ~a10);
         a15 ?? (a17 && ~a16); a16 ?? (a18 && ~a17);
         a17 ?? (a19 && ~a18); a18 ?? (a15 && ~a19);
         a19 ?? (a16 && ~a15);
         a20 ?? (a22 && ~a21); a21 ?? (a23 && ~a22);
         a22 ?? (a24 && ~a23); a23 ?? (a20 && ~a24);
         a24 ?? (a21 && ~a20)]
    | _ => []
End

Definition keccak_round25_components_def:
  keccak_round25_components s round_const =
    keccak_chiiota25
      (keccak_rhopi25 (keccak_theta25 s)) round_const
End

(* Fuse theta, rho, pi, chi, and iota so logical evaluation does not construct
   and immediately destruct three intermediate 25-lane lists per round. *)
Definition keccak_round25_def:
  keccak_round25 (s : word64 list) (round_const : word64) =
    case s of
      [a0;a1;a2;a3;a4; a5;a6;a7;a8;a9;
       a10;a11;a12;a13;a14; a15;a16;a17;a18;a19;
       a20;a21;a22;a23;a24] =>
        let c0 = a0 ?? a5 ?? a10 ?? a15 ?? a20;
            c1 = a1 ?? a6 ?? a11 ?? a16 ?? a21;
            c2 = a2 ?? a7 ?? a12 ?? a17 ?? a22;
            c3 = a3 ?? a8 ?? a13 ?? a18 ?? a23;
            c4 = a4 ?? a9 ?? a14 ?? a19 ?? a24;
            d0 = word_ror c1 63 ?? c4;
            d1 = word_ror c2 63 ?? c0;
            d2 = word_ror c3 63 ?? c1;
            d3 = word_ror c4 63 ?? c2;
            d4 = word_ror c0 63 ?? c3;
            t0 = a0 ?? d0; t1 = a1 ?? d1; t2 = a2 ?? d2;
            t3 = a3 ?? d3; t4 = a4 ?? d4;
            t5 = a5 ?? d0; t6 = a6 ?? d1; t7 = a7 ?? d2;
            t8 = a8 ?? d3; t9 = a9 ?? d4;
            t10 = a10 ?? d0; t11 = a11 ?? d1; t12 = a12 ?? d2;
            t13 = a13 ?? d3; t14 = a14 ?? d4;
            t15 = a15 ?? d0; t16 = a16 ?? d1; t17 = a17 ?? d2;
            t18 = a18 ?? d3; t19 = a19 ?? d4;
            t20 = a20 ?? d0; t21 = a21 ?? d1; t22 = a22 ?? d2;
            t23 = a23 ?? d3; t24 = a24 ?? d4;
            b0 = t0;
            b1 = word_ror t6 20; b2 = word_ror t12 21;
            b3 = word_ror t18 43; b4 = word_ror t24 50;
            b5 = word_ror t3 36; b6 = word_ror t9 44;
            b7 = word_ror t10 61; b8 = word_ror t16 19;
            b9 = word_ror t22 3; b10 = word_ror t1 63;
            b11 = word_ror t7 58; b12 = word_ror t13 39;
            b13 = word_ror t19 56; b14 = word_ror t20 46;
            b15 = word_ror t4 37; b16 = word_ror t5 28;
            b17 = word_ror t11 54; b18 = word_ror t17 49;
            b19 = word_ror t23 8; b20 = word_ror t2 2;
            b21 = word_ror t8 9; b22 = word_ror t14 25;
            b23 = word_ror t15 23; b24 = word_ror t21 62
        in
          [round_const ?? (b0 ?? (b2 && ~b1));
           b1 ?? (b3 && ~b2); b2 ?? (b4 && ~b3);
           b3 ?? (b0 && ~b4); b4 ?? (b1 && ~b0);
           b5 ?? (b7 && ~b6); b6 ?? (b8 && ~b7);
           b7 ?? (b9 && ~b8); b8 ?? (b5 && ~b9);
           b9 ?? (b6 && ~b5);
           b10 ?? (b12 && ~b11); b11 ?? (b13 && ~b12);
           b12 ?? (b14 && ~b13); b13 ?? (b10 && ~b14);
           b14 ?? (b11 && ~b10);
           b15 ?? (b17 && ~b16); b16 ?? (b18 && ~b17);
           b17 ?? (b19 && ~b18); b18 ?? (b15 && ~b19);
           b19 ?? (b16 && ~b15);
           b20 ?? (b22 && ~b21); b21 ?? (b23 && ~b22);
           b22 ?? (b24 && ~b23); b23 ?? (b20 && ~b24);
           b24 ?? (b21 && ~b20)]
    | _ => []
End

Definition keccak_round_constants_def:
  keccak_round_constants : word64 list =
    [0x0000000000000001w; 0x0000000000008082w;
     0x800000000000808Aw; 0x8000000080008000w;
     0x000000000000808Bw; 0x0000000080000001w;
     0x8000000080008081w; 0x8000000000008009w;
     0x000000000000008Aw; 0x0000000000000088w;
     0x0000000080008009w; 0x000000008000000Aw;
     0x000000008000808Bw; 0x800000000000008Bw;
     0x8000000000008089w; 0x8000000000008003w;
     0x8000000000008002w; 0x8000000000000080w;
     0x000000000000800Aw; 0x800000008000000Aw;
     0x8000000080008081w; 0x8000000000008080w;
     0x0000000080000001w; 0x8000000080008008w]
End

Definition keccak_f25_fold_def:
  keccak_f25_fold s =
    FOLDL keccak_round25 s keccak_round_constants
End

(* The round schedule is fixed.  Unrolling it avoids constructing and reducing
   a FOLDL spine during every selector computation. *)
Definition keccak_f25_def:
  keccak_f25 s =
    let s1 = keccak_round25 s 0x0000000000000001w;
        s2 = keccak_round25 s1 0x0000000000008082w;
        s3 = keccak_round25 s2 0x800000000000808Aw;
        s4 = keccak_round25 s3 0x8000000080008000w;
        s5 = keccak_round25 s4 0x000000000000808Bw;
        s6 = keccak_round25 s5 0x0000000080000001w;
        s7 = keccak_round25 s6 0x8000000080008081w;
        s8 = keccak_round25 s7 0x8000000000008009w;
        s9 = keccak_round25 s8 0x000000000000008Aw;
        s10 = keccak_round25 s9 0x0000000000000088w;
        s11 = keccak_round25 s10 0x0000000080008009w;
        s12 = keccak_round25 s11 0x000000008000000Aw;
        s13 = keccak_round25 s12 0x000000008000808Bw;
        s14 = keccak_round25 s13 0x800000000000008Bw;
        s15 = keccak_round25 s14 0x8000000000008089w;
        s16 = keccak_round25 s15 0x8000000000008003w;
        s17 = keccak_round25 s16 0x8000000000008002w;
        s18 = keccak_round25 s17 0x8000000000000080w;
        s19 = keccak_round25 s18 0x000000000000800Aw;
        s20 = keccak_round25 s19 0x800000008000000Aw;
        s21 = keccak_round25 s20 0x8000000080008081w;
        s22 = keccak_round25 s21 0x8000000000008080w;
        s23 = keccak_round25 s22 0x0000000080000001w
    in keccak_round25 s23 0x8000000080008008w
End

Theorem rho_w64_shifts_explicit[local]:
  rho_w64_shifts =
    [63;2;36;37;28;20;58;9;44;61;54;21;
     39;25;23;19;49;43;56;46;62;3;8;50]
Proof
  EVAL_TAC
QED

Theorem keccak_theta25_eq:
  LENGTH s = 25 ==> keccak_theta25 s = theta_w64 s
Proof
  CONV_TAC (LAND_CONV (SIMP_CONV std_ss [listTheory.LENGTH_EQ_NUM_compute])) >>
  strip_tac >> simp[keccak_theta25_def, theta_w64_inlined]
QED

Theorem keccak_rhopi25_eq:
  LENGTH s = 25 ==> keccak_rhopi25 s = pi_w64 (rho_w64 s)
Proof
  CONV_TAC (LAND_CONV (SIMP_CONV std_ss [listTheory.LENGTH_EQ_NUM_compute])) >>
  strip_tac >>
  simp[keccak_rhopi25_def, rho_w64_MAP2,
       rho_w64_shifts_explicit, pi_w64_inlined]
QED

Theorem keccak_chiiota25_eq:
  LENGTH s = 25 ==>
  keccak_chiiota25 s round_const =
    iota_w64 (chi_w64 s) round_const
Proof
  CONV_TAC (LAND_CONV (SIMP_CONV std_ss [listTheory.LENGTH_EQ_NUM_compute])) >>
  strip_tac >>
  simp[keccak_chiiota25_def, chi_w64_inlined, iota_w64_def]
QED

Theorem LENGTH_keccak_theta25:
  LENGTH s = 25 ==> LENGTH (keccak_theta25 s) = 25
Proof
  strip_tac >> simp[keccak_theta25_eq]
QED

Theorem LENGTH_keccak_rhopi25:
  LENGTH s = 25 ==> LENGTH (keccak_rhopi25 s) = 25
Proof
  CONV_TAC (LAND_CONV (SIMP_CONV std_ss [listTheory.LENGTH_EQ_NUM_compute])) >>
  strip_tac >> simp[keccak_rhopi25_def]
QED

Theorem keccak_round25_components_eq:
  LENGTH s = 25 ==>
  keccak_round25 s round_const =
    keccak_round25_components s round_const
Proof
  CONV_TAC (LAND_CONV
    (SIMP_CONV std_ss [listTheory.LENGTH_EQ_NUM_compute])) >>
  strip_tac >>
  simp[keccak_round25_def, keccak_round25_components_def,
       keccak_theta25_def, keccak_rhopi25_def, keccak_chiiota25_def,
       wordsTheory.word_rol_def, wordsTheory.dimindex_64]
QED

Theorem keccak_round25_eq:
  LENGTH s = 25 ==>
  keccak_round25 s round_const = Rnd_w64 s round_const
Proof
  strip_tac >>
  `LENGTH (keccak_theta25 s) = 25` by simp[LENGTH_keccak_theta25] >>
  `LENGTH (keccak_rhopi25 (keccak_theta25 s)) = 25` by
    simp[LENGTH_keccak_rhopi25] >>
  simp[keccak_round25_components_eq, keccak_round25_components_def,
       keccak_chiiota25_eq, keccak_rhopi25_eq, keccak_theta25_eq,
       Rnd_w64_def]
QED

Theorem LENGTH_keccak_round25:
  LENGTH s = 25 ==> LENGTH (keccak_round25 s round_const) = 25
Proof
  simp[keccak_round25_eq, LENGTH_Rnd_w64]
QED

Theorem keccak_round_constants_eq:
  keccak_round_constants = iota_w64_RCz
Proof
  EVAL_TAC
QED

Theorem FOLDL_keccak_round25_eq:
  !rcs s. LENGTH s = 25 ==>
    FOLDL keccak_round25 s rcs = FOLDL Rnd_w64 s rcs
Proof
  Induct >> simp[keccak_round25_eq, LENGTH_keccak_round25]
QED

Theorem keccak_f25_unroll:
  keccak_f25 s = keccak_f25_fold s
Proof
  simp[keccak_f25_def, keccak_f25_fold_def,
       keccak_round_constants_def]
QED

Theorem keccak_f25_eq:
  LENGTH s = 25 ==> keccak_f25 s = Keccak_p_24_w64 s
Proof
  simp[keccak_f25_unroll, keccak_f25_fold_def,
       Keccak_p_24_w64_def, keccak_round_constants_eq,
       FOLDL_keccak_round25_eq]
QED

Theorem LENGTH_FOLDL_keccak_round25:
  !rounds s. LENGTH s = 25 ==>
    LENGTH (FOLDL keccak_round25 s rounds) = 25
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> simp[LENGTH_keccak_round25]
QED

Theorem LENGTH_keccak_f25:
  LENGTH s = 25 ==> LENGTH (keccak_f25 s) = 25
Proof
  simp[keccak_f25_unroll, keccak_f25_fold_def,
       LENGTH_FOLDL_keccak_round25]
QED

Definition keccak_short_block_def:
  keccak_short_block (bs : byte list) =
    let n = 136 - LENGTH bs;
        pad = if n = 1 then [0x81w]
              else 0x01w :: REPLICATE (n - 2) 0w ++ [0x80w]
    in MAP concat_word_list (chunks 8 (bs ++ pad)) ++ eight_zeros_w64
End

Theorem pad10s1_136_w64_short:
  LENGTH bs < 136 ==>
  pad10s1_136_w64 eight_zeros_w64 bs [] = [keccak_short_block bs]
Proof
  simp[Once pad10s1_136_w64_def, keccak_short_block_def]
QED

Theorem keccak_padded_blocks_length_25:
  EVERY (((=) 25) o LENGTH)
    (pad10s1_136_w64 eight_zeros_w64 bs [])
Proof
  mp_tac (Q.INST [`bytes` |-> `bs`]
    pad10s1_136_w64_sponge_init) >>
  rw[eight_zeros_w64_def] >>
  rw[EVERY_MEM, MEM_EL] >>
  gs[LIST_REL_EL_EQN] >>
  qmatch_goalsub_abbrev_tac `pad10s1_136_w64 r8` >>
  `r8 = REPLICATE 8 0w` by simp[Abbr `r8`, REPLICATE_GENLIST] >>
  gs[] >> first_x_assum drule >>
  rw[state_bools_w64_def] >>
  DEP_REWRITE_TAC[LENGTH_chunks] >>
  gs[NULL_LENGTH, divides_def, bool_to_bit_def] >>
  strip_tac >> fs[]
QED

Theorem LENGTH_keccak_short_block:
  LENGTH bs < 136 ==> LENGTH (keccak_short_block bs) = 25
Proof
  strip_tac >>
  mp_tac (Q.INST [`bs` |-> `bs`]
    keccak_padded_blocks_length_25) >>
  simp[pad10s1_136_w64_short]
QED

Theorem MAP2_word_xor_zero:
  !xs : word64 list.
    MAP2 $?? (REPLICATE (LENGTH xs) 0w) xs = xs
Proof
  Induct >> simp[wordsTheory.WORD_XOR_CLAUSES]
QED

Definition Keccak_256_w64_short_def:
  Keccak_256_w64_short bs =
    FLAT (MAP (flip word_to_bytes F)
      (TAKE 4 (keccak_f25 (keccak_short_block bs))))
End

Theorem Keccak_256_w64_short_eq:
  LENGTH bs < 136 ==>
  Keccak_256_w64_short bs = Keccak_256_w64 bs
Proof
  strip_tac >>
  `LENGTH (keccak_short_block bs) = 25` by
    simp[LENGTH_keccak_short_block] >>
  `MAP2 $?? (REPLICATE 25 0w) (keccak_short_block bs) =
   keccak_short_block bs` by
    (qspec_then `keccak_short_block bs` mp_tac MAP2_word_xor_zero >>
     simp[]) >>
  simp[Keccak_256_w64_short_def, Keccak_256_w64_def,
       absorb_w64_def,
       pad10s1_136_w64_short, keccak_f25_eq]
QED

(* Event IDs and other compiler hashes use the same one-block Keccak shape.
   The long branch spells out the imported definition, avoiding a recursive
   compute rewrite while preserving its behavior for arbitrary inputs. *)
Definition Keccak_256_w64_eval_def:
  Keccak_256_w64_eval bs =
    if LENGTH bs < 136 then Keccak_256_w64_short bs
    else
      FLAT (MAP (flip word_to_bytes F)
        (TAKE 4 (absorb_w64
          (pad10s1_136_w64 eight_zeros_w64 bs []))))
End

Theorem Keccak_256_w64_eval_eq:
  Keccak_256_w64_eval bs = Keccak_256_w64 bs
Proof
  rw[Keccak_256_w64_eval_def] >>
  simp[Keccak_256_w64_short_eq, Keccak_256_w64_def]
QED

Theorem Keccak_256_w64_compute[compute]:
  Keccak_256_w64 bs = Keccak_256_w64_eval bs
Proof
  simp[Keccak_256_w64_eval_eq]
QED

Definition keccak_selector_short_def:
  keccak_selector_short bs =
    TAKE 4 (word_to_bytes
      (HD (keccak_f25 (keccak_short_block bs))) F)
End

Theorem keccak_selector_short_eq:
  LENGTH bs < 136 ==>
  keccak_selector_short bs = TAKE 4 (Keccak_256_w64 bs)
Proof
  strip_tac >>
  `LENGTH (keccak_short_block bs) = 25` by
    simp[LENGTH_keccak_short_block] >>
  `LENGTH (keccak_f25 (keccak_short_block bs)) = 25` by
    simp[LENGTH_keccak_f25] >>
  qpat_x_assum `LENGTH (keccak_f25 _) = 25` mp_tac >>
  Cases_on `keccak_f25 (keccak_short_block bs)` >> gvs[] >>
  simp[keccak_selector_short_def, GSYM Keccak_256_w64_short_eq,
       Keccak_256_w64_short_def, TAKE_APPEND1,
       byteTheory.LENGTH_word_to_bytes,
       wordsTheory.dimindex_64]
QED

Definition function_selector_eval_def:
  function_selector_eval name args =
    let bs = MAP (n2w o ORD) (function_signature name args) in
    if LENGTH bs < 136 then keccak_selector_short bs
    else TAKE 4 (Keccak_256_w64 bs)
End

Theorem function_selector_eval_eq:
  function_selector_eval name args = function_selector name args
Proof
  simp[function_selector_eval_def, function_selector_def] >>
  rw[] >> simp[keccak_selector_short_eq]
QED

(* Evaluating the source-level selector now uses the proved fixed-lane round;
   long signatures retain the imported specification as a total fallback. *)
Theorem function_selector_compute[compute]:
  function_selector name args = function_selector_eval name args
Proof
  simp[function_selector_eval_eq]
QED

(* ===== Calldata Method ID Extraction ===== *)

(* Extract the 4-byte method_id from calldata as a 256-bit word.
   This mirrors the Venom dispatch: shr(224, calldataload(0)).
   calldataload pads with zeros if calldata is shorter than 32 bytes,
   then shr(224, ...) isolates the top 4 bytes as a uint32. *)
Definition calldata_method_id_def:
  calldata_method_id (cd : byte list) : bytes32 =
    if LENGTH cd < 4 then 0w
    else
      let b0 = w2n (EL 0 cd) in
      let b1 = w2n (EL 1 cd) in
      let b2 = w2n (EL 2 cd) in
      let b3 = w2n (EL 3 cd) in
      n2w (b0 * 2 ** 24 + b1 * 2 ** 16 + b2 * 2 ** 8 + b3)
End

(* The 4-byte selector as a word, from function_selector. *)
Definition selector_word_def:
  selector_word (sel_bytes : byte list) : bytes32 =
    calldata_method_id sel_bytes
End

(* ===== Calldata Encoding ===== *)

(* Calldata bytes correctly encode a call to func_name with values vals.
   Uses function_selector (keccak256 of ABI signature) and
   enc (ABI encoding). *)
Definition calldata_encodes_def:
  calldata_encodes tenv func_name arg_types vals cd <=>
    ?abi_types abi_vals.
      abi_types = vyper_to_abi_types tenv (TAKE (LENGTH vals) arg_types) /\
      vyper_to_abi_list tenv (TAKE (LENGTH vals) arg_types) vals =
        SOME abi_vals /\
      cd = function_selector func_name abi_types ++
           enc (Tuple abi_types) (ListV abi_vals)
End

(* ===== Selector Table Matching ===== *)

(* A selector table entry (selector_num, entry_label) matches function
   func_name with ABI types abi_types if the selector_num equals the
   method_id derived from function_selector. *)
Definition selector_matches_def:
  selector_matches sel_num func_name abi_types <=>
    let sel_bytes = function_selector func_name abi_types in
    sel_num = w2n (calldata_method_id sel_bytes)
End

(* Calldata method_id matches a selector if the first 4 bytes of
   calldata, interpreted as uint32, equal the selector number. *)
Definition calldata_hits_selector_def:
  calldata_hits_selector cd sel_num <=>
    LENGTH cd >= 4 /\
    w2n (calldata_method_id cd) = sel_num
End

(* ===== Dispatch Routing (per-strategy) ===== *)

(* The linear dispatch strategy: iterates through selectors and jumps
   to the matching label. If calldata matches selector sel with entry
   label fn_lbl, execution from the dispatch entry block reaches fn_lbl.

   This is the key correctness property for the linear strategy.
   The sparse and dense strategies have analogous properties but with
   different CFG structures (buckets, jumptables). *)
