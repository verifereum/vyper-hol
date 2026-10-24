(*
 * Native implementations of the HOL primitives that the generated compiler
 * (compilerNativeML.sml) calls: numbers, integers, words, characters, finite
 * maps and sets.  Each follows the HOL definition it replaces.  Where EVAL
 * leaves a term unevaluated (DIV by zero, fmap_to_alist of a non-empty map,
 * quantifiers), the native raises Stuck, so a fixture that EVAL could not
 * evaluate fails here too rather than producing bytes.
 *)
structure compilerNativeRuntime = struct
  exception Stuck of string
  fun stuck s = raise Stuck s

  type hn_num = IntInf.int
  type hn_int = IntInf.int

  (* ---------- num ---------- *)
  fun hn_SUC (n : IntInf.int) = n + 1
  fun hn_PRE (n : IntInf.int) = if n = 0 then 0 else n - 1
  fun hn_add (m : IntInf.int) n = m + n
  fun hn_sub (m : IntInf.int) n = if m < n then 0 else m - n
  fun hn_mul (m : IntInf.int) n = m * n
  fun hn_DIV (m : IntInf.int) n = if n = 0 then stuck "DIV 0" else IntInf.div (m, n)
  fun hn_MOD (m : IntInf.int) n = if n = 0 then stuck "MOD 0" else IntInf.mod (m, n)
  fun hn_EXP (m : IntInf.int) (n : IntInf.int) =
    if m = 2 then IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))
    else IntInf.pow (m, IntInf.toInt n)
  fun hn_lt (m : IntInf.int) n = m < n
  fun hn_le (m : IntInf.int) n = m <= n
  fun hn_gt (m : IntInf.int) n = m > n
  fun hn_ge (m : IntInf.int) n = m >= n
  fun hn_MAX (m : IntInf.int) n = if m < n then n else m
  fun hn_MIN (m : IntInf.int) n = if m < n then m else n
  fun hn_ODD (n : IntInf.int) = IntInf.rem (n, 2) = 1
  fun hn_EVEN (n : IntInf.int) = IntInf.rem (n, 2) = 0
  fun hn_DIV2 (n : IntInf.int) = IntInf.div (n, 2)
  fun hn_FUNPOW f (n : IntInf.int) x = if n <= 0 then x else hn_FUNPOW f (n - 1) (f x)

  (* ---------- int ---------- *)
  fun hn_int_of_num (n : IntInf.int) = n
  fun hn_int_neg (i : IntInf.int) = ~i
  fun hn_Num (i : IntInf.int) = IntInf.abs i
  fun hn_ABS (i : IntInf.int) = IntInf.abs i
  fun hn_int_lt (i : IntInf.int) j = i < j
  fun hn_int_le (i : IntInf.int) j = i <= j
  fun hn_int_gt (i : IntInf.int) j = i > j
  fun hn_int_ge (i : IntInf.int) j = i >= j
  fun hn_int_add (i : IntInf.int) j = i + j
  fun hn_int_sub (i : IntInf.int) j = i - j
  fun hn_int_mul (i : IntInf.int) j = i * j
  (* HOL's int_div and int_mod round towards negative infinity. *)
  fun hn_int_div (i : IntInf.int) j = if j = 0 then stuck "int_div 0" else IntInf.div (i, j)
  fun hn_int_mod (i : IntInf.int) j = if j = 0 then stuck "int_mod 0" else IntInf.mod (i, j)
  fun hn_int_quot (i : IntInf.int) j = if j = 0 then stuck "int_quot 0" else IntInf.quot (i, j)
  fun hn_int_rem (i : IntInf.int) j = if j = 0 then stuck "int_rem 0" else IntInf.rem (i, j)

  (* ---------- words: width and value in [0, 2^width) ---------- *)
  datatype hn_word = W of int * IntInf.int
  (* 2^w for the widths in use, computed once each. *)
  val pow2_table = Vector.tabulate (513, fn w => IntInf.<< (1, Word.fromInt w))
  fun pow2 w = if w <= 512 then Vector.sub (pow2_table, w) else IntInf.<< (1, Word.fromInt w)
  fun hn_n2w w (n : IntInf.int) = let val p = pow2 w in
    W (w, if n >= 0 andalso n < p then n else IntInf.mod (n, p)) end
  fun hn_w2n (W (_, v)) = v
  fun hn_w2w w (W (_, v)) = hn_n2w w v
  fun signed (W (w, v)) = if v >= pow2 (w - 1) then v - pow2 w else v
  fun hn_sw2sw w x = hn_n2w w (signed x)
  fun hn_w2i x = signed x
  fun hn_i2w w (i : IntInf.int) = hn_n2w w i
  fun hn_dimindex w () = IntInf.fromInt w
  fun hn_dimword w () = pow2 w
  fun lift2 f (W (w, a)) (W (_, b)) = hn_n2w w (f (a, b))
  (* Operands are in [0, 2^w), so these results need at most one correction. *)
  fun hn_word_add (W (w, a)) (W (_, b)) = let val r = a + b val p = pow2 w in
    W (w, if r >= p then r - p else r) end
  fun hn_word_sub (W (w, a)) (W (_, b)) = let val r = a - b in
    W (w, if r < 0 then r + pow2 w else r) end
  val hn_word_mul = lift2 IntInf.*
  fun hn_word_and (W (w, a)) (W (_, b)) = W (w, IntInf.andb (a, b))
  fun hn_word_or (W (w, a)) (W (_, b)) = W (w, IntInf.orb (a, b))
  fun hn_word_xor (W (w, a)) (W (_, b)) = W (w, IntInf.xorb (a, b))
  fun hn_word_2comp (W (w, v)) = hn_n2w w (~v)
  fun hn_word_1comp (W (w, v)) = W (w, pow2 w - 1 - v)
  fun hn_word_lsl (W (w, v)) (n : IntInf.int) =
    if n >= IntInf.fromInt w then W (w, 0) else hn_n2w w (IntInf.<< (v, Word.fromLargeInt n))
  fun hn_word_lsr (W (w, v)) (n : IntInf.int) =
    if n >= IntInf.fromInt w then W (w, 0) else W (w, IntInf.~>> (v, Word.fromLargeInt n))
  fun hn_word_ror (W (w, v)) (n : IntInf.int) =
    let val k = Word.fromLargeInt (IntInf.mod (n, IntInf.fromInt w))
    in hn_n2w w (IntInf.orb (IntInf.~>> (v, k), IntInf.<< (v, Word.fromInt w - k))) end
  fun hn_word_rol (x as W (w, _)) (n : IntInf.int) =
    hn_word_ror x (IntInf.fromInt w - IntInf.mod (n, IntInf.fromInt w))
  fun hn_word_msb (W (w, v)) = v >= pow2 (w - 1)
  fun hn_word_lo (W (_, a)) (W (_, b)) = a < b
  fun hn_word_lt x y = signed x < signed y
  fun hn_concat_word_list w (ws : hn_word list) =
    case ws of
      [] => W (w, 0)
    | (h as W (hw, _)) :: t =>
        hn_word_or (hn_w2w w h) (hn_word_lsl (hn_concat_word_list w t) (IntInf.fromInt hw))
  (* byte theory: byte_index, set_byte and word_of_bytes at any width. *)
  fun byte_index (W (w, a)) be =
    let val d = IntInf.fromInt w div 8
    in if be then 8 * ((d - 1) - IntInf.mod (a, d)) else 8 * IntInf.mod (a, d) end
  fun set_byte a (W (_, b)) (W (w, v)) be =
    let val i = Word.fromLargeInt (byte_index a be)
        val mask = IntInf.<< (255, i)
    in hn_n2w w (IntInf.orb (IntInf.andb (v, IntInf.notb mask), IntInf.<< (b, i))) end
  fun hn_word_of_bytes be a bs =
    case bs of
      [] => W (case a of W (w, _) => w, 0)
    | b :: rest => set_byte a b (hn_word_of_bytes be (hn_word_add a (hn_n2w (case a of W (w, _) => w) 1)) rest) be
  fun hn_word_of_bytes_be w bs = hn_word_of_bytes true (W (w, 0)) bs
  fun get_byte a (W (w, v)) be =
    hn_n2w 8 (IntInf.~>> (v, Word.fromLargeInt (byte_index a be)))
  fun hn_word_to_bytes (x as W (w, _)) be =
    List.tabulate (w div 8, fn n => get_byte (hn_n2w w (IntInf.fromInt n)) x be)
  fun hn_v2w w (bits : bool list) =
    hn_n2w w (List.foldl (fn (b, acc) => 2 * acc + (if b then 1 else 0)) 0 bits)

  (* ---------- characters ---------- *)
  fun hn_CHR (n : IntInf.int) = if n < 256 then Char.chr (IntInf.toInt n) else stuck "CHR"
  fun hn_ORD c = IntInf.fromInt (Char.ord c)

  (* ---------- strings: HOL's char lists, as ML strings ---------- *)
  fun hn_scons c s = String.str c ^ s
  (* list_CASE on a string; the nil branch is a thunk, as a case arm is lazy. *)
  fun hn_scase s n f =
    if s = "" then n () else f (String.sub (s, 0)) (String.extract (s, 1, NONE))
  fun hn_sAPPEND s t = s ^ t
  (* list_subset, ALL_DISTINCT and nub at elements with a total order: the
     same results as their MEM-based definitions, computed by sorting. *)
  fun msort cmp l = let
    fun merge (xs as x :: xt, ys as y :: yt) =
          if cmp (y, x) = LESS then y :: merge (xs, yt) else x :: merge (xt, ys)
      | merge ([], ys) = ys
      | merge (xs, []) = xs
    fun split (x :: y :: r) (a, b) = split r (x :: a, y :: b)
      | split [x] (a, b) = (x :: a, b)
      | split [] ab = ab
    fun go [] = []
      | go [x] = [x]
      | go l = let val (a, b) = split l ([], []) in merge (go a, go b) end
  in go l end
  (* Below this length, pairwise comparison beats sorting. *)
  val small = 8
  fun short l = let fun go (_ :: t) n = n < small andalso go t (n + 1) | go [] _ = true
                in go l 0 end
  fun subset_by cmp xs ys = if short ys
    then List.all (fn x => List.exists (fn y => cmp (x, y) = EQUAL) ys) xs else let
    val v = Vector.fromList (msort cmp ys)
    fun mem x = let
      fun bs (lo, hi) = lo < hi andalso (let val m = (lo + hi) div 2 in
        case cmp (x, Vector.sub (v, m)) of
          EQUAL => true | LESS => bs (lo, m) | GREATER => bs (m + 1, hi) end)
    in bs (0, Vector.length v) end
  in List.all mem xs end
  fun distinct_by cmp l = if short l then let
      fun go (x :: t) = not (List.exists (fn y => cmp (x, y) = EQUAL) t) andalso go t
        | go [] = true
    in go l end else let
    fun ok (x :: (rest as y :: _)) = cmp (x, y) <> EQUAL andalso ok rest
      | ok _ = true
  in ok (msort cmp l) end
  (* nub keeps the last occurrence of each element. *)
  fun nub_by cmp l = if short l then let
      fun go (x :: t) = if List.exists (fn y => cmp (x, y) = EQUAL) t then go t else x :: go t
        | go [] = []
    in go l end else let
    val n = length l
    val tagged = ListPair.zip (l, List.tabulate (n, fn i => i))
    val sorted = msort (fn ((a, i), (b, j)) => case cmp (a, b) of EQUAL => Int.compare (i, j)
                                                              | c => c) tagged
    val keep = Array.array (n, false)
    fun mark ((_, i) :: (rest as (b, _) :: _)) x =
          (if cmp (x, b) <> EQUAL then Array.update (keep, i, true) else (); mark rest b)
      | mark [(_, i)] _ = Array.update (keep, i, true)
      | mark [] _ = ()
    val () = case sorted of [] => () | (a, _) :: _ => mark sorted a
  in List.mapPartial (fn (x, i) => if Array.sub (keep, i) then SOME x else NONE) tagged end
  fun hn_list_subset_str xs ys = subset_by String.compare xs ys
  fun hn_list_subset_num xs ys = subset_by IntInf.compare xs ys
  fun hn_ALL_DISTINCT_str l = distinct_by String.compare l
  fun hn_ALL_DISTINCT_num l = distinct_by IntInf.compare l
  fun hn_nub_str l = nub_by String.compare l
  fun hn_nub_num l = nub_by IntInf.compare l
  fun hn_sLENGTH s = IntInf.fromInt (size s)
  fun hn_sFLAT l = String.concat l

  (* ---------- sets, represented by their characteristic functions ---------- *)
  fun hn_EMPTY _ = false
  fun hn_INSERT x s = fn y => y = x orelse s y
  fun hn_IN x s = s x
  fun hn_DIFF s t = fn x => s x andalso not (t x)
  fun hn_DELETE s y = fn x => x <> y andalso s x
  fun hn_COMPL s = fn x => not (s x)
  fun hn_LIST_TO_SET l = fn x => List.exists (fn y => y = x) l
  (* GENLIST's definition builds the list with SNOC, quadratically. *)
  fun hn_GENLIST f (n : IntInf.int) = List.tabulate (IntInf.toInt n, f o IntInf.fromInt)
  fun hn_SNOC x l = l @ [x]
  (* EL of an index past the end is HD [] in HOL, which EVAL leaves stuck. *)
  fun hn_EL (n : IntInf.int) l = List.nth (l, IntInf.toInt n) handle Subscript => stuck "EL"
  fun hn_LENGTH l = IntInf.fromInt (List.length l)
  (* EmitML prints x IN LIST_TO_SET l (the MEM overload) as listML.MEM. *)
  structure listML = struct fun MEM x l = List.exists (fn y => y = x) l end
  fun hn_SUBSET _ _ = stuck "SUBSET"
  fun hn_SET_TO_LIST _ = stuck "SET_TO_LIST"
  fun hn_forall site _ = stuck ("universal quantifier in " ^ site)
  fun hn_exists site _ = stuck ("existential quantifier in " ^ site)
  fun hn_exists1 site _ = stuck ("unique existential quantifier in " ^ site)
  fun hn_select site _ = stuck ("Hilbert choice in " ^ site)
  fun hn_RTC _ _ _ = stuck "RTC"
  fun hn_apto t = t
  fun hn_badeq site _ _ = stuck ("equality at a type with maps, sets or functions, in " ^ site)
  fun hn_paren x = x
  fun hn_arb site = stuck ("ARB in " ^ site)
  fun hn_nomatch site = stuck ("no equation matches in " ^ site)
  fun hn_imp a b = not a orelse b

  (* ---------- finite maps: bindings with distinct keys, newest first.
     ML equality on maps (also inside records) compares these lists, so two
     maps with the same bindings added in a different order compare unequal,
     where HOL says they are equal; direct map equality uses hn_fmap_eq,
     which is extensional. ---------- *)
  datatype ('a, 'b) hn_fmap = FM of ('a * 'b) list
  val hn_FEMPTY = FM []
  fun bindings (FM l) = l
  val mk = FM
  fun hn_FUPDATE m (k, v) = let val l = bindings m in
    if List.exists (fn (k', _) => k' = k) l
    then mk ((k, v) :: List.filter (fn (k', _) => k' <> k) l) else mk ((k, v) :: l) end
  fun hn_FLOOKUP m k =
    case List.find (fn (k', _) => k' = k) (bindings m) of
      SOME (_, v) => SOME v
    | NONE => NONE
  fun hn_FAPPLY m k = case hn_FLOOKUP m k of SOME v => v | NONE => stuck "FAPPLY"
  fun hn_FDOM m = fn k => isSome (hn_FLOOKUP m k)
  fun hn_FUNION m n = mk (bindings m @ List.filter (fn (k, _) => not (isSome (hn_FLOOKUP m k))) (bindings n))
  fun hn_fdomsub m k = mk (List.filter (fn (k', _) => k' <> k) (bindings m))
  fun hn_DRESTRICT m s = mk (List.filter (fn (k, _) => s k) (bindings m))
  fun hn_FUPDATE_LIST m kvs = List.foldl (fn (kv, m) => hn_FUPDATE m kv) m kvs
  fun distinct l = List.foldr (fn ((k, v), acc) =>
    (k, v) :: List.filter (fn (k', _) => k' <> k) acc) [] l
  fun hn_FEVERY p m = List.all p (distinct (bindings m))
  fun hn_fmap_eq m n = let val a = distinct (bindings m) in
    length a = length (distinct (bindings n)) andalso
    List.all (fn (k, v) => hn_FLOOKUP n k = SOME v) a end
  fun hn_fmap_to_alist m =
    case bindings m of [] => [] | _ => stuck "fmap_to_alist of a non-empty map"
end
