type graph = int list array


fun dfsAll G visit revisit finish s = 
  let
    fun dfs (v, (sigma, X)) = 
      if Array.sub(X, v) then (revisit(sigma, v), X)
      else let
        val sig' = visit(sigma, v)
        val _ = Array.update(X, v, true)
        val (sig'', X'') = foldl dfs (sig', X) (Array.sub(G, v))
      in (finish(sig'', v), X'') end
  in
    #1 (foldl dfs (s, Array.array(Array.length G, false)) (List.tabulate(Array.length G, fn i => i)))
  end

fun dfsNumbers G = 
  let
    val s0 = (0, [], [])
    fun visit ((i, Tv, Tf), v) = (i + 1, (v, i)::Tv, Tf)
    fun finish ((i, Tv, Tf), v) = (i + 1, Tv, (v, i)::Tf)
    val (_, Tv, Tf) = dfsAll G visit #1 finish s0
  in
    (Tv, Tf)
  end
  
fun topologicalSort G = 
  let
    fun finish (l, v) = v::l
  in
    dfsAll G #1 #1 finish []
  end

fun dfsReach (G, v) (L, X) = if Array.sub(X, v) then (L, X) else (Array.update(X, v, true); foldl (fn (a, b) => dfsReach (G, a) b) (v::L, X) (Array.sub(G, v)));

fun transpose G = 
  let
    val Gt = Array.array(Array.length G, [])
    val _ = Array.appi (fn (u, L) => foldl (fn (v, _) => Array.update(Gt, v, u::Array.sub(Gt, v))) () L) G
  in
    Gt
  end
  
fun autotranspose G = 
  let
    val Gt = transpose G
    val H = Array.array(Array.length G, [])
    val _ = map (fn i => Array.update(H, i, Array.sub(G, i) @ Array.sub(Gt, i))) (List.tabulate(Array.length G, fn i => i))
  in
    H
  end

fun scc G = 
  let
    val finish = topologicalSort G
    val Gt = transpose G
    fun sccOne (v, (X, sccs)) = 
      let
        val (comp, X') = dfsReach (Gt, v) ([], X)
      in
        case comp of 
          [] => (X', sccs)
        | _ => (X', comp::sccs)
      end
  in
    List.rev (#2 (foldl sccOne (Array.array(Array.length G, false), []) finish)) 
  end

fun bellmanford G v = 
  let
    val inf = valOf Int.maxInt
    val n = Vector.length G
    val V = Vector.tabulate(n, fn u => if u = v then 0 else inf)
  in
    iterate (fn (i, V) => Vector.mapi (fn (j, u) => Int.min(u, foldl (fn ((v, w), m) => Int.min(m, w + Vector.sub(V, v))) inf (Vector.sub(G, j)) )) V) V (1 until n)
  end

fun dijkstra G v = 
  let
    val n = Vector.length G
    val dist = Array.tabulate(n, fn i => NONE)
    fun iter pq = 
      case PQ.deleteMin pq of
        (NONE, _) => ()
      | (SOME (u, d), q) => if isSome (Array.sub(dist, u)) then iter q else let
          val _ = Array.update(dist, u, SOME d)
          val newq = PQ.meld (q, PQ.fromList (map (fn (w, wd) => (w, d + wd)) (Vector.sub(G, u))))
        in iter newq end
  in
    Array.vector dist before iter (PQ.$ (v, 0))
  end

fun floydwarshall G = 
  let
    val n = Vector.length G
    val dist = Array.tabulate(n, fn i => Array.tabulate(n, fn j => if i = j then 0 else Vector.sub(Vector.sub(G, i), j)))
  in
    dist before 
    for (0 until n)
      (fn k => 
        for (0 until n)
          (fn i => 
            for (0 until n)
              (fn j => 
                Array.update(Array.sub(dist, i), j, Int.min(Array.sub(Array.sub(dist, i), j), Array.sub(Array.sub(dist, i), k) + Array.sub(Array.sub(dist, i), k))))))
  end

fun johnsons G = 
  let
    val n = Vector.length G
    val Gp = Vector.tabulate(n + 1, fn i => if i = n then List.tabulate(n, fn i => (i, 0)) else (n, 0)::Vector.sub(G, i))
    val D = bellmanford Gp n
    val G' = Vector.mapi (fn (u, L) => map (fn (v, w) => (v, w + Vector.sub(D, u) - Vector.sub(D, v))) L) G
  in
    Vector.tabulate(n, fn u => Vector.mapi (fn (v, d) => Option.map (fn w => w - Vector.sub(D, u) + Vector.sub(D, v)) d) (dijkstra G' u))
  end

fun numberOfPaths G 1 = G
  | numberOfPaths G k = 
      let  
        val G' = numberOfPaths G (k div 2)
      in
        if k mod 2 = 0 then matrixmultiply(G', G') else matrixmultiply(G, matrixmultiply(G', G'))
      end

fun shortestpaths G 1 = G
  | shortestpaths G k = 
      let  
        fun minp (A, B, i, j) = iterate (fn (p, m) => Int.min(m, Vector.sub(Vector.sub(A, i), p) + Vector.sub(Vector.sub(B, p), j))) (valOf Int.maxInt) (0 until Vector.length G)
        fun modmult (A, B) = Vector.mapi (fn (i, V) => Vector.mapi (fn (j, _) => minp (A, B, i, j)) V) G
        val G' = shortestpaths G (k div 2)
      in
        if k mod 2 = 0 then modmult(G', G') else modmult(G, modmult(G', G'))
      end