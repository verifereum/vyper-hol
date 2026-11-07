(* EmitML's numeral interface, backed by unbounded natural numbers. *)
structure numML = struct
  type num = IntInf.int
  val ZERO : num = 0
  val ONE : num = 1
  val TWO : num = 2
  fun fromString s =
    case IntInf.fromString s of
      SOME n => if n >= 0 then n else raise Fail "negative natural number"
    | NONE => raise Fail "invalid natural number"
  fun add (m : num) n = m + n
  fun sub (m : num) n = IntInf.max (0, m - n)
  fun mul (m : num) n = m * n
  fun divide (m : num) n = if n = 0 then 0 else m div n
  fun modulo (m : num) n = if n = 0 then m else m mod n
  fun less (m : num) n = m < n
  fun suc (m : num) = m + 1
end
