val maxSubArraySum = foldl (fn (i, (curr, max)) => (Int.max(curr + i, i), Int.max(Int.max(curr + i, i), max))) (0, valOf Int.minInt)
val maxSum = #2 o maxSubArraySum

fun lcs (S, T) = 
  let
    fun h (i, j) = Word.xorb (Word.fromInt i, Word.fromInt j)
    fun eq (x, y) = x = y
    val lcs' = memoize (h, eq) (fn lcs =>
        fn (i, j) => 
          if i = String.size S orelse j = String.size T then 0
          else if String.sub(S, i) = String.sub(T, j) then 1 + lcs(i + 1, j + 1) 
          else Int.max(lcs(i + 1, j), lcs(i, j + 1)))
  in
    lcs' (0, 0)
  end

fun minPathSum M = 
  let
    val m = Vector.length M
    fun sub (i, j) = Vector.sub(Vector.sub(M, i), j)
    val n = Vector.length (Vector.sub(M, 0))
    fun h (i, j) = Word.xorb (Word.fromInt i, Word.fromInt j)
    fun eq (x, y) = x = y
    val mps' = memoize (h, eq) (fn mps => 
        fn (i, j) => if i = 0 andalso j = 0 then sub(0, 0)
                     else if i = 0 then sub(i, j) + mps (i, j - 1)
                     else if j = 0 then sub(i, j) + mps (i - 1, j)
                     else sub(i, j) + Int.min(mps(i - 1, j), mps(i, j - 1)))
  in
    mps' (m - 1, n - 1)
  end

fun longestPrefixSuffix s = 
  let
    val n = String.size s
    val l = List.tabulate(n - 1, fn i => i + 1)
    val h = rollingHash s
    val x = foldl (fn (i, j) => if h(0, i) = h(n - i, n) then i else j) 0 l
  in
    String.substring(s, 0, x)
  end

structure Val : MONOID = 
  struct
    type t = int
    val I = 0
    val f = op+
  end
structure Key : ORDKEY  = 
  struct
    type t = int
    val equal = op=
    val compare = Int.compare
  end
structure Treap = Treap(structure Key = Key structure Val = Val)

fun inversions L = let
  fun loop ([], T) = []
    | loop (x::xs, T) = let
        val T' = if isSome $ Treap.find(T, x) then Treap.insert(T, (x, 1 + valOf $ Treap.find(T, x)))
                 else Treap.insert(T, (x, 1))
      in Treap.reduceVal $ #1 $ Treap.split(T', x) :: loop(xs, T') end
in List.rev $ loop (List.rev L, Treap.empty()) end 

fun reversePairs L = let
  fun loop ([], T) = 0
    | loop (x::xs, T) = let
        val T' = if isSome $ Treap.find(T, x) then Treap.insert(T, (x, 1 + valOf $ Treap.find(T, x)))
              else Treap.insert(T, (x, 1))
      in Treap.reduceVal $ #1 $ Treap.split(T', Real.ceil((Real.fromInt x) / 2.0)) + loop(xs, T') end
in loop (List.rev L, Treap.empty()) end

fun sortedInstructions L = let
  fun loop ([], T) = 0
    | loop (x::xs, T) = let
        val T' = if isSome (Treap.find(T, x)) then Treap.insert(T, (x, 1 + valOf (Treap.find(T, x))))
              else Treap.insert(T, (x, 1))
        val (lo, _, hi) = Treap.split(T', x)
      in Int.min(Treap.reduceVal lo, Treap.reduceVal hi) + loop(xs, T') end
in loop (L, Treap.empty()) end

fun lis L = 
  let
    val L' = enumerate L
    val T0 = Treap.empty() 
  in
    Treap.reduceVal $ foldl (fn ((i,a), b) => Treap.insert(b, ((i,a), Int.max(1, 1 + Treap.reduceVal $ #1 $ Treap.split(b, (i,a)))))) T0 L'
  end

fun rangeSumQuery L = 
  let
    val T = ref $ Treap.fromList $ ListPair.zip(List.tabulate(List.length L, fn i => i), L)
    fun query r = Treap.reduceVal $ Treap.getRange (!T) r
  in
    (query, fn x => T := Treap.insert(!T, x))
  end

fun validNumber s =
  let
    datatype symbol = sign | dot | digit | eE | garbage
    val F = [2,4,7]
    fun delta (0, sign) = 1
      | delta (0, dot) = 3
      | delta (0, digit) = 2
      | delta (1, digit) = 2
      | delta (1, dot) = 3
      | delta (2, digit) = 2
      | delta (2, eE) = 6
      | delta (2, dot) = 4
      | delta (3, digit) = 4
      | delta (4, digit) = 4
      | delta (4, eE) = 6
      | delta (6, sign) = 8
      | delta (6, digit) = 7
      | delta (7, digit) = 7
      | delta (8, digit) = 7
      | delta _ = raise Match
    fun convert (#"+" | #"-") = sign
      | convert (#"e" | #"E") = eE
      | convert #"." = dot
      | convert c = if Char.isDigit c then digit else garbage
    val L = map convert (explode s)
    fun delta2 (x, y) = delta (y, x)
  in
    (List.exists (fn c => c = (foldl delta2 0 L)) F) handle Match => false
  end

fun lca1 (Empty, a, b) = NONE
  | lca1 (Node(x, l, r), a, b) = if x = a orelse x = b then SOME x else let
    val lcal = lca1(l,a,b) 
    val lcar = lca1(r,a,b)
  in
    if isSome lcal andalso isSome lcar then SOME x else if isSome lcal then lcal else lcar
  end
  
fun lca2 (T, a, b) = 
  let
    fun lca (Empty, a, b) = (false, false, NONE)
      | lca (Node(x, l, r), a, b) = 
        let
          val (af1, bf1, lcal) = lca(l,a,b) 
          val (af2, bf2, lcar) = lca(r,a,b)
          val af = a = x orelse af1 orelse af2
          val bf = b = x orelse bf1 orelse bf2
        in
          if x = a orelse x = b orelse (isSome lcal andalso isSome lcar) then (af, bf, SOME x) else if isSome lcal then (af, bf, lcal) else (af, bf, lcar)
        end
    val (af, bf, res) = lca(T, a, b)
  in
    if af andalso bf then res else NONE
  end
