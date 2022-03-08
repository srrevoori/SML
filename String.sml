fun rollingHash s = 
  let
    val p = 1000000009
    open Vector
    val s' = map (fn x => Int.toLarge (ord(x) - 96)) (fromList (String.explode (s ^ "a")))
    val b = 31
    val r = scanl (fn (x, _) => b*x mod p) 1 (tabulate(length s', fn i => 1))
    val a = scanl (fn (x, y) => (b*x + y) mod p) 0 s'
  in
    fn (i, j) => (sub(a, j) - sub(a, i) * sub(r, j - i)) mod p
  end
  
fun hash s = rollingHash s (0, String.size s)

fun rabinKarp s t = 
  let
    val h = rollingHash s
    val ht = hash t
    val n = String.size t
  in
    List.filter (fn i => h(i, i + n) = ht handle _ => false) (List.tabulate(String.size s, fn i => i))
  end
