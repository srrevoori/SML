functor Segtree(val n : int) =
struct 
    val T = Array.tabulate (2 * n, fn _ => 0)
    fun update i x = Y (fn u => fn i => if i = 0 then () else u (i div 2) before Array.update (T, i, Array.sub (T, 2 * i) + Array.sub (T, 2 * i + 1))) ((i + n) div 2) before Array.update (T, i + n, x)
    fun query l r = Y (fn f => fn (v, l, r, i, j) => if l = i andalso r = j then Array.sub (T, v) else let val m = (l + r) div 2 in (if i <= m then f (2 * v, l, m, i, Int.min (m, j)) else 0) + (if j > m then f (2 * v + 1, m + 1, r, Int.max (i, m + 1), j) else 0) end) (1, 0, n - 1, l, r)
end 
